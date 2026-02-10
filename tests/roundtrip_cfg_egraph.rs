use llhd::assembly::parse_module_unchecked;
use llhd_egglog::UnitAnalysis;
use rayon::prelude::*;
use std::env;
use std::fs;
use std::path::{Path, PathBuf};

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

#[test]
fn roundtrip_cfg_skeleton_egraph() {
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

        for unit in module.units() {
            UnitAnalysis::build_from_unit(&unit)
                .unwrap_or_else(|err| panic!("analysis failed for {}: {}", path.display(), err));
        }
    });
}
