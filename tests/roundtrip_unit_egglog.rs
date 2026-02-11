use llhd::assembly::parse_module_unchecked;
use llhd::ir::prelude::*;
use llhd_egglog::{unit_from_egglog_program, unit_to_egglog_program};
use rayon::prelude::*;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

mod common;
use common::units_equivalent;

#[cfg(feature = "egglog-debug")]
use llhd_egglog::dump_egglog_debug;
#[cfg(feature = "egglog-debug")]
use std::sync::Once;

fn collect_llhd_files(root: &Path, out: &mut Vec<PathBuf>) {
    let entries = match fs::read_dir(root) {
        Ok(entries) => entries,
        Err(_) => return,
    };

    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_llhd_files(&path, out);
        } else if path.extension().and_then(|ext| ext.to_str()) == Some("llhd") {
            out.push(path);
        }
    }
}

#[cfg(feature = "egglog-debug")]
fn maybe_dump_egglog_program(path: &Path, unit_index: usize, unit: Unit<'_>, program: &str) {
    static INIT: Once = Once::new();
    static NOTICE: Once = Once::new();
    let enabled = env::var("LLHD_EGGLOG_DEBUG").ok().as_deref() == Some("1");
    if !enabled {
        return;
    }

    let out_dir = Path::new("target").join("egglog");
    INIT.call_once(|| {
        let _ = fs::create_dir_all(&out_dir);
    });

    NOTICE.call_once(|| {
        println!("egglog debug dumps: {}", out_dir.display());
    });

    let file_stem = path
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or("llhd");
    let file_stem_label = sanitize_label(file_stem);
    let unit_label = sanitize_label(&unit.name().to_string());
    let file_name = format!(
        "{}__{}__{}.egglog.txt",
        if file_stem_label.is_empty() {
            "llhd"
        } else {
            file_stem_label.as_str()
        },
        if unit_label.is_empty() {
            "unit"
        } else {
            unit_label.as_str()
        },
        unit_index
    );
    let file_path = out_dir.join(file_name);
    let contents = dump_egglog_debug(&unit, program);
    let _ = fs::write(file_path, contents);
}

#[cfg(feature = "egglog-debug")]
fn sanitize_label(input: &str) -> String {
    let mut out = String::new();
    for ch in input.chars() {
        if ch.is_ascii_alphanumeric() || matches!(ch, '-' | '_' | '.') {
            out.push(ch);
        } else {
            out.push('_');
        }
    }
    out.trim_matches('_').to_string()
}

#[test]
fn roundtrip_unit_egglog() {
    let mut files = Vec::new();
    collect_llhd_files(Path::new("./tests"), &mut files);
    files.sort();
    let allow_large = env::var("LLHD_ROUNDTRIP_LARGE").ok().as_deref() == Some("1");
    let large_limit = 256 * 1024;

    files.par_iter().for_each(|path| {
        if !allow_large {
            if let Ok(meta) = fs::metadata(path) {
                if meta.len() > large_limit {
                    return;
                }
            }
        }
        let contents = fs::read_to_string(path).expect("read llhd test file");
        if contents.contains("; FAIL") {
            return;
        }

        let module = parse_module_unchecked(&contents)
            .unwrap_or_else(|err| panic!("parse failed for {}: {}", path.display(), err));

        let mut programs = Vec::new();
        for (_index, unit) in module.units().enumerate() {
            let program = unit_to_egglog_program(&unit).expect("egglog program");
            #[cfg(feature = "egglog-debug")]
            {
                maybe_dump_egglog_program(path, _index, unit, &program);
            }
            programs.push(program);
        }

        let mut rebuilt = Module::new();
        for decl in module.decls() {
            let data = DeclData {
                name: module[decl].name.clone(),
                sig: module[decl].sig.clone(),
                loc: module[decl].loc,
            };
            rebuilt.add_decl(data);
        }
        for program in programs {
            let data = unit_from_egglog_program(&program).unwrap_or_else(|err| {
                panic!("egglog parse failed for {}: {}", path.display(), err)
            });
            rebuilt.add_unit(data);
        }

        let mut right_units: Vec<_> = rebuilt.units().collect();
        for left_unit in module.units() {
            let position = right_units.iter().position(|right_unit| {
                left_unit.kind() == right_unit.kind()
                    && left_unit.sig() == right_unit.sig()
                    && left_unit.name() == right_unit.name()
            });
            let Some(index) = position else {
                panic!("unit not found after roundtrip for {}", path.display());
            };
            let right_unit = right_units.swap_remove(index);
            if let Err(err) = units_equivalent(left_unit, right_unit) {
                panic!(
                    "unit mismatch after roundtrip for {}: {}",
                    path.display(),
                    err
                );
            }
        }

        if !right_units.is_empty() {
            panic!("extra units after roundtrip for {}", path.display());
        }

        let mut right_decls: Vec<_> = rebuilt.decls().collect();
        for left_decl in module.decls() {
            let position = right_decls.iter().position(|right_decl| {
                module[left_decl].name == rebuilt[*right_decl].name
                    && module[left_decl].sig == rebuilt[*right_decl].sig
            });
            let Some(index) = position else {
                panic!("decl not found after roundtrip for {}", path.display());
            };
            right_decls.swap_remove(index);
        }
        if !right_decls.is_empty() {
            panic!("extra decls after roundtrip for {}", path.display());
        }
    });
}
