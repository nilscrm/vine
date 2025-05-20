#![allow(unexpected_cfgs)]

use std::{
  env, fs,
  io::{Read, Write},
  path::{Path, PathBuf},
  process::{Command, Stdio},
  thread::{self, JoinHandle},
};

use dyntest::{dyntest, DynTester};

#[cfg(not(rust_analyzer))]
dyntest!(tests);

fn tests(t: &mut DynTester) {
  env::set_current_dir("..").unwrap();

  // let fib_repl_input_iv = b"1\n2\n3\n4\n5\n6\n7\n8\n9\n10\n21\n100\n999999\n";

  t.group("ivy", |t| {
    test_iv(t, "ivy/examples/cat.iv", b"meow\n", ".txt");
    // test_iv(t, "ivy/examples/fib_repl.iv", fib_repl_input_iv, ".txt");
    // test_iv(t, "ivy/examples/fizzbuzz.iv", b"", ".txt");
    test_iv(t, "ivy/examples/hihi.iv", b"", ".txt");
    test_iv(t, "ivy/examples/add_ref/add_ref_ty.iv", b"", ".txt");
    test_iv(t, "ivy/examples/channels/channels_no_print_flow_labels_ty.iv", b"", ".txt");
    test_iv(t, "ivy/examples/inc_pair/inc_pair_ty.iv", b"", ".txt");
  });

  t.group("fail", |t| {
    test_iv_fail(t, "ivy/examples/vicious_cycles/swap_tuple_ty.iv");
    test_iv_fail(t, "ivy/examples/vicious_cycles/simple_dup_ty.iv");
    test_iv_fail(t, "ivy/examples/vicious_cycles/add_ref_incorrect/add_ref_incorrect_ty.iv");
  });
}

const IVY: &[&str] = &["ivy", "--release"];

fn test_iv(t: &mut DynTester, path: &'static str, input: &'static [u8], output_ext: &'static str) {
  let name = Path::file_stem(path.as_ref()).unwrap().to_str().unwrap();
  t.test(name, || {
    run_iv("ivy", name, path, input, output_ext);
  });
}

fn run_iv(group: &str, name: &str, path: &str, input: &[u8], output_ext: &str) {
  let (stdout, stderr) = exec(IVY, &["run", path], input, true);
  test_snapshot(&[group, name, &format!("output{output_ext}")], &stdout);
  let full_stats = String::from_utf8(stderr).unwrap();
  let stats = full_stats.split_once("\nPerformance").unwrap().0;
  test_snapshot(&[group, name, "stats.txt"], stats.as_bytes());
  fs::write(get_snapshot_path(&[group, name, "timing.txt"]), full_stats[stats.len()..].as_bytes())
    .unwrap();
}

fn test_iv_fail(t: &mut DynTester, path: &'static str) {
  let name = Path::file_stem(path.as_ref()).unwrap().to_str().unwrap();
  t.test(name, move || {
    let (_, stderr) = exec(IVY, &["run", path], &[], false);
    test_snapshot(&["ivy", "fail", &format!("{name}.txt")], &stderr);
  });
}

fn exec(bin: &[&str], args: &[&str], input: &[u8], success: bool) -> (Vec<u8>, Vec<u8>) {
  let mut child = Command::new(env!("CARGO"))
    .args(["run", "--quiet", "--bin"])
    .args(bin)
    .arg("--")
    .args(args)
    .stdin(Stdio::piped())
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .spawn()
    .unwrap();

  child.stdin.take().unwrap().write_all(input).unwrap();

  let stdout = parallel_read(child.stdout.take().unwrap());
  let stderr = parallel_read(child.stderr.take().unwrap());

  let status = child.wait().unwrap();
  if status.success() != success {
    let err = String::from_utf8(stderr.join().unwrap()).unwrap();
    eprintln!("{err}");
    panic!("{status}");
  }

  (stdout.join().unwrap(), stderr.join().unwrap())
}

fn test_snapshot(components: &[&str], contents: &[u8]) -> PathBuf {
  let path = get_snapshot_path(components);
  let existing = fs::read(&path).ok();
  if existing.is_none_or(|x| x != contents) {
    if should_write_snapshot() {
      println!("updating snapshot {:?}", path);
      fs::write(&path, contents).unwrap();
    } else {
      panic!("invalid snapshot {:?}", path);
    }
  }
  path
}

fn get_snapshot_path(components: &[&str]) -> PathBuf {
  let mut path = PathBuf::from("tests/snaps");
  path.extend(components);
  fs::create_dir_all(path.parent().unwrap()).unwrap();
  path
}

fn should_write_snapshot() -> bool {
  std::env::var("SNAP_CHECK").is_err()
}

fn parallel_read(mut read: impl Read + Send + 'static) -> JoinHandle<Vec<u8>> {
  thread::spawn(move || {
    let mut buf = Vec::new();
    read.read_to_end(&mut buf).unwrap();
    buf
  })
}
