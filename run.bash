bazel run //simple:hello-cpp
bazel run //simple:hello-rs
bazel test //simple:all
bazel run @rules_rust//:rustfmt
bazel build --config=rust-analyzer //...
bazel run @rules_rust//tools/rust_analyzer:setup -- vscode
