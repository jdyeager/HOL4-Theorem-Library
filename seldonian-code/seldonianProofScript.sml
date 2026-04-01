(* Probably all ripped from the echoProofScript example *)

open preamble
     semanticsPropsTheory backendProofTheory x64_configProofTheory
     seldonianProgTheory seldonianCompileTheory;

val _ = new_theory "seldonianProof";

val seldonian_filter_io_events_def =
    new_specification("seldonian_filter_io_events_def",["seldonian_filter_io_events"],
        seldonian_filter_semantics
        |> SIMP_RULE bool_ss [SKOLEM_THM,GSYM RIGHT_EXISTS_IMP_THM]);

val (seldonian_filter_sem,seldonian_filter_output) =
    seldonian_filter_io_events_def |> SPEC_ALL |> UNDISCH |> CONJ_PAIR;

val (seldonian_filter_not_fail,seldonian_filter_sem_sing) =
    seldonian_filter_sem
    |> SRULE [seldonian_filter_compiled,ml_progTheory.prog_syntax_ok_semantics]
    |> MATCH_MP semantics_prog_Terminate_not_Fail |> CONJ_PAIR;

val seldonian_filter_compile_correct_applied =
    MATCH_MP compile_correct $ cj 1 seldonian_filter_compiled
    |> SIMP_RULE(srw_ss())[LET_THM,ml_progTheory.init_state_env_thm,GSYM AND_IMP_INTRO]
    |> C MATCH_MP seldonian_filter_not_fail
    |> C MATCH_MP x64_backend_config_ok
    |> REWRITE_RULE[seldonian_filter_sem_sing,AND_IMP_INTRO]
    |> REWRITE_RULE[Once (GSYM AND_IMP_INTRO)]
    |> C MATCH_MP (CONJ(UNDISCH x64_machine_config_ok)(UNDISCH x64_init_ok))
    |> DISCH(#1(dest_imp(concl x64_init_ok)))
    |> REWRITE_RULE[AND_IMP_INTRO];

Theorem seldonian_filter_compiled_thm =
    CONJ seldonian_filter_compile_correct_applied seldonian_filter_output
    |> DISCH_ALL
    |> check_thm;

(*
val seldonian_filter_compiled_thm =
    CONJ seldonian_filter_compile_correct_applied seldonian_filter_output
    |> DISCH_ALL
    |> check_thm
    |> curry save_thm "seldonian_filter_compiled_thm";
*)

val _ = export_theory();
