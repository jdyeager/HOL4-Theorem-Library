(*
open preamble compilationLib seldonianProgTheory

val _ = new_theory "seldonianCompile";

Theorem seldonian_filter_compiled = compile_x64 "seldonian_filter" seldonian_filter_prog_def

val _ = export_theory ();
*)

open preamble seldonianProgTheory eval_cake_compile_x64Lib;

val _ = new_theory "seldonianCompile";

Theorem seldonian_filter_compiled =
    eval_cake_compile_x64 "" seldonian_filter_prog_def "seldonian_filter.S";

val _ = export_theory ();
