open HolKernel
open ruleTheory hostgraphTheory morphismTheory

val () = new_theory "program"

Type procid = ``:string``

(*
  Note: `term_TRY`, `term_IFTE`, and `term_TRTE` are used as intermediate steps while evaluation.
  These construct are not present while parsing.
*)
Datatype:
  term =
    term_seq term term
  | term_or term term
  | term_ifte term term term
  | term_trte term term term
  | term_rscall (ruleid set)
  | term_proc procid
  | term_alap term
  | term_skip
  | term_fail
  | term_break
  | term_TRY term term term
  | term_ITE term term term
End


(* Helper to enforce that no intermediate terms are present *)
Definition no_intermediate_terms_def:
  no_intermediate_terms (term_seq a b) = (no_intermediate_terms a /\ no_intermediate_terms b) /\
  no_intermediate_terms (term_or a b) = (no_intermediate_terms a /\ no_intermediate_terms b) /\
  no_intermediate_terms (term_ifte a b c) = (no_intermediate_terms a /\ no_intermediate_terms b /\ no_intermediate_terms c) /\
  no_intermediate_terms (term_trte a b c) = (no_intermediate_terms a /\ no_intermediate_terms b /\ no_intermediate_terms c) /\
  no_intermediate_terms (term_rscall rset) = T /\
  no_intermediate_terms (term_proc pid) = T /\
  no_intermediate_terms (term_alap t) = no_intermediate_terms t /\
  no_intermediate_terms term_skip = T /\
  no_intermediate_terms term_fail = T /\
  no_intermediate_terms term_break = T /\
  no_intermediate_terms (term_TRY a b c) = F /\
  no_intermediate_terms (term_ITE a b c) = F
End

(*
  Break
  The break statement must only appread within a loop. If the break is in the condition of a branching statement, its containing loop must occur within the same condition.
*)
Definition condition_break_def:
  condition_break (term_seq a b) = (condition_break a /\ condition_break b) /\
  condition_break (term_or a b) = (condition_break a /\ condition_break b) /\
  condition_break (term_ifte a b c) = (condition_break a /\ condition_break b /\ condition_break c) /\
  condition_break (term_trte a b c) = (condition_break a /\ condition_break b /\ condition_break c) /\
  condition_break (term_rscall rset) = T /\
  condition_break (term_proc pid) = T /\
  condition_break (term_alap t) = T /\
  condition_break term_skip = T /\
  condition_break term_fail = T /\
  condition_break term_break = F /\
  condition_break (term_TRY a b c) = F /\
  condition_break (term_ITE a b c) = F
End

(* Helper collecting procids *)
Definition collect_procids_def:
  collect_procids (term_seq a b) = collect_procids a UNION collect_procids b /\
  collect_procids (term_or a b) = collect_procids a UNION collect_procids b /\
  collect_procids (term_ifte a b c) = collect_procids a UNION collect_procids b UNION collect_procids c /\
  collect_procids (term_trte a b c) = collect_procids a UNION collect_procids b UNION collect_procids c /\
  collect_procids (term_rscall rset) = {} /\
  collect_procids (term_proc pid) = {pid} /\
  collect_procids (term_alap t) = collect_procids t /\
  collect_procids term_skip = {} /\
  collect_procids term_fail = {} /\
  collect_procids term_break = {} /\
  collect_procids (term_TRY a b c) = {} /\
  collect_procids (term_ITE a b c) = {}
End


(* Helper collecting procids *)
Definition collect_ruleids_def:
  collect_ruleids (term_seq a b) = collect_ruleids a UNION collect_ruleids b /\
  collect_ruleids (term_or a b) = collect_ruleids a UNION collect_ruleids b /\
  collect_ruleids (term_ifte a b c) = collect_ruleids a UNION collect_ruleids b UNION collect_ruleids c /\
  collect_ruleids (term_trte a b c) = collect_ruleids a UNION collect_ruleids b UNION collect_ruleids c /\
  collect_ruleids (term_rscall rset) = rset /\
  collect_ruleids (term_proc pid) = {} /\
  collect_ruleids (term_alap t) = collect_ruleids t /\
  collect_ruleids term_skip = {} /\
  collect_ruleids term_fail = {} /\
  collect_ruleids term_break = {} /\
  collect_ruleids (term_TRY a b c) = {} /\
  collect_ruleids (term_ITE a b c) = {}
End


Datatype:
  program =
  <| proc: procid |-> term
   ; rule: ruleid |-> rule
  |>
End

(*
  Procedure Call Validity
  Any name in a procedure call must belong to a procedure declared in a visible scope.
*)
Definition proc_call_validity_def:
  proc_call_validity p =
    let called = BIGUNION (IMAGE collect_procids (FRANGE p.proc))
    in called SUBSET (FDOM p.proc)
End

(*
  Rule Call Validity
  Any name in a rule call must belong to a rule declared in a visible scope.
*)
Definition rule_call_validity_def:
  rule_call_validity p =
    let called = BIGUNION (IMAGE collect_ruleids (FRANGE p.proc))
    in called SUBSET (FDOM p.rule)
End

(*
  Main Declaration
  There is exactly one main declaration in a single program.
*)
Definition has_main_entry_def:
  has_main_entry (p:program) <=> "Main" IN FDOM p.proc
End

Definition wf_program_def:
  wf_program (p:program) <=>
    FEVERY (condition_break o SND) p.proc /\
    FEVERY (no_intermediate_terms o SND) p.proc /\
    FEVERY (wf_rule o SND) p.rule /\
    proc_call_validity p /\
    rule_call_validity p /\
    has_main_entry p
End

val () = export_theory ()
