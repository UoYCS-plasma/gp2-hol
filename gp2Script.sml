open HolKernel
open hostgraphTheory rulegraphTheory morphismTheory ruleTheory programTheory semTheory

val () = new_theory "gp2"
(* val _ = add_ML_dependency "gp2PP"; *)

val () = export_theory ()
