open HolKernel
open rulegraphTheory typingTheory

val () = new_theory "rule"

Datatype: ruleid = ruleid string
End

Definition dest_ruleid_def:
  dest_ruleid (ruleid r) = r
End

Datatype: cond =
  condEdgeTest nodeid nodeid (edgeattr option) |
  condSubtype ty varname |
  condLabelEq rulegraph$label rulegraph$label |
  condLabelNeq rulegraph$label rulegraph$label |
  condGt rulegraph$label rulegraph$label |
  condGteq rulegraph$label rulegraph$label |
  condLt rulegraph$label rulegraph$label |
  condLteq rulegraph$label rulegraph$label |
  condAnd cond cond |
  condOr cond cond |
  condNot cond
End

(* Helper: collecting all nodeids *)
Definition collect_nodeids_def:
  collect_nodeids (condSubtype ty v) = {} /\
  collect_nodeids (condEdgeTest n1 n2 opt) = {n1;n2} /\
  collect_nodeids (condLabelEq l1 l2) = {} /\
  collect_nodeids (condLabelNeq l1 l2) = {} /\
  collect_nodeids (condGt l1 l2) = {} /\
  collect_nodeids (condGteq l1 l2) = {} /\
  collect_nodeids (condLt l1 l2) = {} /\
  collect_nodeids (condLteq l1 l2) = {} /\
  collect_nodeids (condAnd c1 c2) = collect_nodeids c1 UNION collect_nodeids c2 /\
  collect_nodeids (condOr c1 c2) = collect_nodeids c1 UNION collect_nodeids c2 /\
  collect_nodeids (condNot c) = collect_nodeids c
End

Inductive cond_typeof:
[~subtype:]
  !vars ty sty x. FLOOKUP vars x = SOME sty /\ is_subtype_of sty ty ==> cond_typeof (vars, condSubtype ty x)
[~edgeTest:]
  !vars n1 n2 attr. cond_typeof (vars, condEdgeTest n1 n2 attr)
[~labelEq:]
  !vars l1 l2. cond_typeof (vars, condLabelEq l1 l2)
[~labelNeq:]
  !vars l1 l2. cond_typeof (vars, condLabelNeq l1 l2)
[~gt:]
  !vars l1 l2. label_typeof (vars, l1, tyInt) /\ label_typeof (vars, l2, tyInt) ==> cond_typeof (vars, condGt l1 l2)
[~gteq:]
  !vars l1 l2. label_typeof (vars, l1, tyInt) /\ label_typeof (vars, l2, tyInt) ==> cond_typeof (vars, condGteq l1 l2)
[~lt:]
  !vars l1 l2. label_typeof (vars, l1, tyInt) /\ label_typeof (vars, l2, tyInt) ==> cond_typeof (vars, condLt l1 l2)
[~lteq:]
  !vars l1 l2. label_typeof (vars, l1, tyInt) /\ label_typeof (vars, l2, tyInt) ==> cond_typeof (vars, condLteq l1 l2)
[~and:]
  !vars c1 c2. cond_typeof (vars, c1) /\ cond_typeof (vars, c2) ==> cond_typeof (vars, condAnd c1 c2)
[~or:]
  !vars c1 c2. cond_typeof (vars, c1) /\ cond_typeof (vars, c2) ==> cond_typeof (vars, condOr c1 c2)
[~not:]
  !vars c. cond_typeof (vars, c) ==> cond_typeof (vars, condNot c)
End

Datatype: rule =
  <| vars: varname |-> ty
   ; lhs: rulegraph
   ; rhs: rulegraph
   ; inf: nodeid set
   ; cond: cond option
  |>
End

Definition wf_interface_def:
  wf_interface r <=>
    r.inf SUBSET r.lhs.V /\
    r.inf SUBSET r.rhs.V
End

(*
(*
  Context Condition: Bidirectional Edge 1
  A right-hand side bidirectional edge must be incident to the same two nodes as a left-hand side bidirectional edge
*)
Definition bidir_edge_endpoint_agreement_def:
  bidir_Edge_endpoint_agreement (r:rule) <=>
    !e. e IN r.lhs.b INTER r.rhs.b ==>
      FLOOKUP r.lhs.s e = FLOOKUP r.rhs.s e /\ FLOOKUP r.lhs.t e = FLOOKUP r.rhs.t e
End *)

(*
  Wildcard Consistency
  A right-hand side item with the mark any must be in the interface of the rule and its counterpart in the left-hand side must be a wildcard.
*)
Definition wildcard_consistency_def:
  wildcard_consistency (r: rule) <=>
    let rhs_any = { n | n IN r.rhs.V /\ ?lbl. FLOOKUP r.rhs.l n = SOME (lbl, SOME nodemark_any) } in
    let lhs_any = { n | n IN r.lhs.V /\ ?lbl. FLOOKUP r.lhs.l n = SOME (lbl, SOME nodemark_any) } in
    rhs_any SUBSET r.inf /\ lhs_any SUBSET r.inf
End

Definition is_simple_rule_def:
  is_simple_rule (r:rule) <=>
    (!l. l IN rulegraph_labels r.lhs ==> is_simple_label r.vars l) /\
    (rulegraph_labels r.rhs SUBSET rulegraph_labels r.lhs) /\
    wildcard_consistency r
End


(*
  Variable Consistency 1
  Any variable in a rule must be declared in the variable list of the associated rule.
*)
Definition variable_consistency1_def:
  variable_consistency1 (r:rule) <=> let
    vars = rulegraph_vars r.lhs UNION rulegraph_vars r.rhs
    in vars SUBSET FDOM r.vars
End

(*
  Variable Consistency 2
  Any variable in the right-hand side must be present in the left-hand side of the same rule.
*)
Definition variable_consistency2_def:
  variable_consistency2 (r:rule) <=>
    rulegraph_vars r.rhs SUBSET rulegraph_vars r.lhs
End

Definition variable_consitency_def:
  variable_consistency (r:rule) <=>
    variable_consistency1 r /\ variable_consistency2 r
End


(*
  Degree Operators
  The argument of a degree operator (indeg or outdeg) must be a node ID occuring in the interface of its containing rule.
*)
Definition degree_op_consistency_def:
  degree_op_consistency (r:rule) <=>
    let lhs_nodeids = BIGUNION $ IMAGE collect_nodeids_expression (rulegraph_labels r.lhs) in
    let rhs_nodeids = BIGUNION $ IMAGE collect_nodeids_expression (rulegraph_labels r.rhs) in
    (lhs_nodeids UNION rhs_nodeids) SUBSET r.inf
End


Definition welltyped_rule_def:
  welltyped_rule r <=>
    welltyped_rulegraph r.vars r.lhs /\
    welltyped_rulegraph r.vars r.rhs
End

(*
  Edge Predicate
  Each node ID in an edge predicate must occur in the interface of its containing rule.
*)
Definition edge_pred_consistency_def:
  edge_pred_consistency (r: rule) <=> case r.cond of
    SOME cond => collect_nodeids cond SUBSET r.inf |
    NONE => T
End

(* Per thesis Definition 3.4.4/3.4.5, rule graphs L and R must be totally labelled.
   Also requires wf_rulegraph_labels for both LHS and RHS to ensure labels are well-formed. *)
Definition wf_rule_def:
  wf_rule r <=>
    totally_labelled_rulegraph r.lhs /\
    totally_labelled_rulegraph r.rhs /\
    wf_rulegraph_labels r.lhs /\
    wf_rulegraph_labels r.rhs /\
    wf_interface r /\
    welltyped_rule r /\
    variable_consistency r /\
    degree_op_consistency r /\
    edge_pred_consistency r
End


val () = export_theory ();
