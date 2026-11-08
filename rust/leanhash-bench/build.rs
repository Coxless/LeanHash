// CLHASH（C）を同じ計測器で比べるため、CLHASH_DIR があればそのソースをビルドしてリンクする。
// bench SDK は ~/.local/src/clhash に置く。
fn main() {
    println!("cargo::rustc-check-cfg=cfg(have_clhash)");
    println!("cargo::rerun-if-env-changed=CLHASH_DIR");
    let Ok(dir) = std::env::var("CLHASH_DIR") else { return };
    cc::Build::new()
        .file(format!("{dir}/src/clhash.c"))
        .include(format!("{dir}/include"))
        .flag("-msse4.2")
        .flag("-mpclmul")
        .flag("-march=native")
        .opt_level(3)
        .compile("clhash");
    println!("cargo::rustc-cfg=have_clhash");
}
