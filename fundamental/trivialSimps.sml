structure trivialSimps :> trivialSimps = struct

open HolKernel Parse boolLib bossLib;
open simpLib;
open probabilityTheory;
open trivialTheory;

val name_to_thname = fn t => fn s => ({Thy = t, Name = s}, DB.fetch t s);

val PROB_ss = named_rewrites_with_names "PROB" $ map (name_to_thname "probability") [
    "prob_space_def","p_space_def","events_def","prob_def",
    "real_random_variable_def","random_variable_def","expectation_def"];

val TRIVIAL_ss = named_rewrites_with_names "TRIVIAL" $ map (name_to_thname "trivial") [
    "Abbrev_T",
    "MEASURE_SPACE_SIGMA_ALGEBRA'",
    "PROB_SPACE_SIGMA_ALGEBRA"];

val _ = register_frag PROB_ss;

val _ = register_frag TRIVIAL_ss;

end
