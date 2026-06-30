use std::env;
use std::path::PathBuf;
use verification_lib::{compute_verified_logic_hash_runtime, format_payload, verify_signature};

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: verification_cli <command> [args...]");
        std::process::exit(1);
    }

    let command = &args[1];
    match command.as_str() {
        "hash-tcb" => {
            if args.len() != 3 {
                eprintln!("Usage: verification_cli hash-tcb <repo_root>");
                std::process::exit(1);
            }
            let repo_root = PathBuf::from(&args[2]);
            match compute_verified_logic_hash_runtime(&repo_root) {
                Ok(hash) => println!("{}", hash),
                Err(e) => {
                    eprintln!("Error computing TCB hash: {}", e);
                    std::process::exit(1);
                }
            }
        }
        "format-payload" => {
            if args.len() != 9 {
                eprintln!("Usage: verification_cli format-payload <manifest_hash> <logic_hash> <branches> <min_log10> <max_log10> <trace_hash> <factorization_depth>");
                std::process::exit(1);
            }
            let payload = format_payload(
                &args[2],
                &args[3],
                args[4].parse().unwrap(),
                args[5].parse().unwrap(),
                args[6].parse().unwrap(),
                &args[7],
                args[8].parse().unwrap(),
            );
            println!("{}", payload);
        }
        "verify-signature" => {
            if args.len() != 5 {
                eprintln!("Usage: verification_cli verify-signature <pubkey_hex> <sig_hex> <payload>");
                std::process::exit(1);
            }
            match verify_signature(&args[2], &args[3], &args[4]) {
                Ok(true) => {
                    println!("true");
                    std::process::exit(0);
                }
                Ok(false) => {
                    println!("false");
                    std::process::exit(1);
                }
                Err(e) => {
                    eprintln!("Error verifying signature: {}", e);
                    std::process::exit(1);
                }
            }
        }
        _ => {
            eprintln!("Unknown command: {}", command);
            std::process::exit(1);
        }
    }
}
