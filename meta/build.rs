use cargo::core::resolver::CliFeatures;
use cargo::core::Workspace;
use cargo::ops::{CompileOptions, Packages};
use cargo::util::command_prelude::CompileMode;
use cargo::{ops, Config};
use sha2::{Digest, Sha256};
use std::env;
use std::ffi::OsString;
use std::fs::{self, File};
use std::io::prelude::*;
use std::path::{Path, PathBuf};

fn display_digest(digest: &[u8]) -> String {
    digest.iter().map(|byte| format!("{:02x}", byte)).collect()
}

fn main() {
    println!("rerun-if-changed=src/grammar.pest");

    // Yes; build.rs is supposed to treat `src` as read-only; however:
    // We want to publish `grammar.rs` and not `grammar.pest`,
    // so putting it in `src` is the simplest way to do so.
    let manifest_dir = Path::new(env!("CARGO_MANIFEST_DIR"));
    let grammar_pest_path = manifest_dir.join("src/grammar.pest");
    let grammar_rs_path = manifest_dir.join("src/grammar.rs");
    let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
    let hash_path = out_dir.join("pest_hash.sha1");

    // If `grammar.pest` exists (we're building from git sources)
    if grammar_pest_path.exists() {
        let mut sha = Sha256::default();

        let old_hash = File::open(&hash_path).ok().map(|mut file| {
            let mut s = String::new();
            file.read_to_string(&mut s).unwrap();
            s
        });
        let current_grammar = fs::read_to_string(grammar_pest_path).unwrap();
        sha.update(current_grammar.as_bytes());
        let current_hash = display_digest(&sha.finalize());

        // If `grammar.pest` has changed
        if !grammar_rs_path.exists()
            || old_hash.as_ref().map(|it| it.trim()) != Some(current_hash.trim())
        {
            println!("Bootstrapping `meta/src/grammar.rs`");

            let mut hash_file = File::create(hash_path).unwrap();
            writeln!(hash_file, "{}", current_hash).unwrap();

            let config = Config::default().expect("cargo config");
            let workspace_manifest = manifest_dir
                .join("../Cargo.toml")
                .canonicalize()
                .expect("workspace manifest");
            let workspace = Workspace::new(&workspace_manifest, &config).expect("workspace");

            let mut opts =
                CompileOptions::new(&config, CompileMode::Build).expect("compile options");
            opts.spec = Packages::Packages(vec!["pest_bootstrap".to_owned()]);
            if should_bootstrap_in_src() {
                opts.cli_features =
                    CliFeatures::from_command_line(&["bootstrap-in-src".to_owned()], false, true)
                        .expect("cli features");
            } else {
                opts.cli_features =
                    CliFeatures::from_command_line(&[], false, false).expect("cli features");
            }

            let path = if should_bootstrap_in_src() {
                OsString::from(grammar_rs_path)
            } else {
                format!(
                    "{}/__pest_grammar.rs",
                    env::var("OUT_DIR").expect("OUT_DIR env var")
                )
                .parse::<OsString>()
                .expect("grammar path")
            };
            if let Err(e) = ops::run(&workspace, &opts, &[path]) {
                panic!(
                    "Bootstrap failed: {e}. \
                    Please run `cargo build --package pest_bootstrap` or `cargo bootstrap` \
                    and then try again."
                );
            }
        } else {
            println!("       Fresh `meta/src/grammar.rs`");
        }
    } else {
        assert!(
            grammar_rs_path.exists(),
            "package is broken; does not contain grammar.rs"
        );
    }
}

#[cfg(feature = "bootstrap-in-src")]
fn should_bootstrap_in_src() -> bool {
    true
}

#[cfg(not(feature = "bootstrap-in-src"))]
fn should_bootstrap_in_src() -> bool {
    false
}
