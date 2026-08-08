"""
Golden file test definitions.
"""

load("@rules_shell//shell:sh_test.bzl", "sh_test")

def hello_test(name, target):
    sh_test(
        name = name,
        srcs = ["diff_arg_out.bash"],
        args = ["hello", "$(rootpath {})".format(target)],
        data = [target],
        size = "small",
    )

def quine_test(name, src, target):
    sh_test(
        name = name,
        srcs = ["diff_file_out.bash"],
        args = ["$(rootpath {})".format(src), "$(rootpath {})".format(target)],
        data = [src, target],
        size = "small",
    )
