open HolKernel boolLib bossLib
open finite_mapTheory stringLib integerTheory optionTheory

open graphTheory typingTheory

val () = new_theory "rulegraph";

monadsyntax.enable_monadsyntax();
monadsyntax.enable_monad "option";

Datatype: varname = varname string
End

Definition dest_varname_def:
  dest_varname (varname v) = v
End

Datatype: edgemark =
  edgemark_red | edgemark_green | edgemark_blue | edgemark_dashed | edgemark_any
End

Datatype: nodemark =
  nodemark_red | nodemark_green | nodemark_blue | nodemark_grey | nodemark_any
End

Datatype: label =
  label_integer int | label_string string | label_char char | label_nil | label_cons label label |
  label_variable varname | label_indeg nodeid | label_outdeg nodeid | label_length varname |
  label_add label label | label_sub label label | label_mult label label | label_div label label |
  label_concat label label | label_negate label
End

(* Well-formedness for rule labels.
   These predicates are used in proofs only - the parser and translation
   functions enforce this structure by construction. *)

(* An atom can appear in head position of label_cons *)
Definition is_rule_atom_def:
  is_rule_atom (label_integer _) = T /\
  is_rule_atom (label_string _) = T /\
  is_rule_atom (label_char _) = T /\
  is_rule_atom (label_variable _) = T /\
  is_rule_atom (label_indeg _) = T /\
  is_rule_atom (label_outdeg _) = T /\
  is_rule_atom (label_length _) = T /\
  is_rule_atom (label_add _ _) = T /\
  is_rule_atom (label_sub _ _) = T /\
  is_rule_atom (label_mult _ _) = T /\
  is_rule_atom (label_div _ _) = T /\
  is_rule_atom (label_concat _ _) = T /\
  is_rule_atom (label_negate _) = T /\
  is_rule_atom label_nil = F /\
  is_rule_atom (label_cons _ _) = F
End

(* Well-formed rule label: proper list with atoms in head positions,
   and sub-expressions also well-formed *)
Definition wf_rulelabel_def:
  wf_rulelabel (label_integer _) = T /\
  wf_rulelabel (label_string _) = T /\
  wf_rulelabel (label_char _) = T /\
  wf_rulelabel label_nil = T /\
  wf_rulelabel (label_variable _) = T /\
  wf_rulelabel (label_indeg _) = T /\
  wf_rulelabel (label_outdeg _) = T /\
  wf_rulelabel (label_length _) = T /\
  wf_rulelabel (label_add l1 l2) = (wf_rulelabel l1 /\ wf_rulelabel l2) /\
  wf_rulelabel (label_sub l1 l2) = (wf_rulelabel l1 /\ wf_rulelabel l2) /\
  wf_rulelabel (label_mult l1 l2) = (wf_rulelabel l1 /\ wf_rulelabel l2) /\
  wf_rulelabel (label_div l1 l2) = (wf_rulelabel l1 /\ wf_rulelabel l2) /\
  wf_rulelabel (label_concat l1 l2) = (wf_rulelabel l1 /\ wf_rulelabel l2) /\
  wf_rulelabel (label_negate l) = wf_rulelabel l /\
  wf_rulelabel (label_cons h t) = (is_rule_atom h /\ wf_rulelabel h /\ wf_rulelabel t)
End

(* A rule label is in "spine form" if it's either label_nil or
   label_cons with an atom in head position and a spine in tail.
   This is the canonical form that the parser produces.
   Note: Unlike host labels, spine form does NOT imply wf_rulelabel
   because atoms can contain sub-expressions (e.g., label_add a b). *)
Definition is_rulelabel_spine_def:
  is_rulelabel_spine label_nil = T /\
  is_rulelabel_spine (label_cons h t) = (is_rule_atom h /\ is_rulelabel_spine t) /\
  is_rulelabel_spine _ = F
End

Definition count_labels_def:
  count_labels (label_cons a b) = count_labels a + count_labels b /\
  count_labels label_nil = 0 /\
  count_labels _ = 1n
End

(* Split a label list after n elements (cons cells).
   split_label_list n l = SOME (prefix, suffix) where prefix has n elements.

   Note: For well-formed host labels where each element h in label_cons h t
   is an atom (count_labels h = 1), this correctly splits by atom count.
   The count_labels function counts atoms, which equals cons count for flat labels. *)
Definition split_label_list_def:
  split_label_list 0n l = SOME (label_nil, l) /\
  split_label_list n (label_cons h t) =
    (case split_label_list (n - 1) t of
      SOME (l1, l2) => SOME (label_cons h l1, l2) |
      NONE => NONE) /\
  split_label_list n l = NONE
End

(* This theorem holds for flat labels where each element has count_labels = 1 *)
Theorem split_label_list_preserve_count:
  !n l a b. split_label_list n l = SOME (a,b) ==>
    count_labels l = count_labels a + count_labels b
Proof
  Induct_on `n` >> rw[]
  >- (Cases_on `split_label_list 0 l`
      \\ gvs[split_label_list_def, count_labels_def])
  >- (Cases_on `l`
      \\ fs[split_label_list_def]
      \\ rename1 `label_cons l h`
      \\ fs[split_label_list_def]
      \\ Cases_on `split_label_list n h`
      \\ fs[]
      \\ PairCases_on `x`
      \\ fs []
      \\ first_x_assum drule
      \\ rw[]
      \\ fs [count_labels_def])
QED

(* EVAL ``split_label_list 1 (label_cons (label_integer 1) label_nil)`` *)


Inductive label_typeof:
[~int:] !vars v. label_typeof (vars, label_integer v, tyInt)
[~string:] !vars v. label_typeof (vars, label_string v, tyString)
[~char:] !vars v. label_typeof (vars, label_char v, tyChar)
[~var:] !vars v ty. FLOOKUP vars v = SOME ty ==> label_typeof (vars, label_variable v, ty)
[~indeg:] !vars n. label_typeof (vars, label_indeg n, tyInt)
[~outdeg:] !vars n. label_typeof (vars, label_outdeg n, tyInt)
[~length:] !vars n. FLOOKUP vars n = SOME ty /\ ty IN {tyList; tyAtom; tyString} ==>
    label_typeof (vars, label_length n, tyInt)
[~add:]
  !vars a b.
    label_typeof (vars, a, tyInt) /\ label_typeof (vars, b, tyInt) ==>
    label_typeof (vars, label_add a b, tyInt)
[~sub:]
  !vars a b.
    label_typeof (vars, a, tyInt) /\ label_typeof (vars, b, tyInt) ==>
    label_typeof (vars, label_sub a b, tyInt)
[~mult:]
  !vars a b.
    label_typeof (vars, a, tyInt) /\ label_typeof (vars, b, tyInt) ==>
    label_typeof (vars, label_mult a b, tyInt)
[~div:]
  !vars a b.
    label_typeof (vars, a, tyInt) /\ label_typeof (vars, b, tyInt) ==>
    label_typeof (vars, label_div a b, tyInt)
[~concat:]
  !vars a b.
    (label_typeof (vars, a, tyChar) \/ label_typeof (vars, a, tyString)) /\
    (label_typeof (vars, b, tyChar) \/ label_typeof (vars, b, tyString)) ==>
    label_typeof (vars, label_concat a b, tyString)
[~negate:] !vars v. label_typeof (vars, v, tyInt) ==> label_typeof (vars, label_negate v, tyInt)
[~nil:] !vars. label_typeof (vars, label_nil, tyList)
[~cons:]
  !vars a b tya tyb.
    label_typeof (vars, a, tya) /\ label_typeof (vars, b, tyb) ==>
    label_typeof (vars, label_cons a b, tyList)
End

Theorem label_typeof_rewrites:
  (!vars v ty. label_typeof (vars, label_integer v, ty) <=> ty = tyInt) /\
  (!vars v ty. label_typeof (vars, label_string v, ty) <=> ty = tyString) /\
  (!vars v ty. label_typeof (vars, label_char v, ty) <=> ty = tyChar) /\
  (!vars v ty. label_typeof (vars, label_variable v, ty) <=> FLOOKUP vars v = SOME ty) /\
  (!vars v ty. label_typeof (vars, label_indeg v, ty) <=> ty = tyInt) /\
  (!vars v ty. label_typeof (vars, label_outdeg v, ty) <=> ty = tyInt) /\
  (!vars v ty. label_typeof (vars, label_length v, ty) <=> ty = tyInt /\ (?ty'. FLOOKUP vars v = SOME ty' /\ ty' IN {tyList; tyAtom; tyString})) /\
  (!vars a b ty. label_typeof (vars, label_add a b, ty) <=>
    ty = tyInt /\ label_typeof (vars, a, tyInt) /\ label_typeof (vars, b, tyInt)) /\
  (!vars a b ty. label_typeof (vars, label_sub a b, ty) <=>
    ty = tyInt /\ label_typeof (vars, a, tyInt) /\ label_typeof (vars, b, tyInt)) /\
  (!vars a b ty. label_typeof (vars, label_mult a b, ty) <=>
    ty = tyInt /\ label_typeof (vars, a, tyInt) /\ label_typeof (vars, b, tyInt)) /\
  (!vars a b ty. label_typeof (vars, label_div a b, ty) <=>
    ty = tyInt /\ label_typeof (vars, a, tyInt) /\ label_typeof (vars, b, tyInt)) /\
  (!vars a b ty. label_typeof (vars, label_concat a b, ty) <=>
    ty = tyString /\
    (label_typeof (vars, a, tyString) \/ label_typeof (vars, a, tyChar)) /\
    (label_typeof (vars, b, tyString) \/ label_typeof (vars, b, tyChar))) /\
  (!vars v ty. label_typeof (vars, label_negate v, ty) <=>
    ty = tyInt /\ label_typeof (vars, v, tyInt)) /\
  (!vars ty. label_typeof (vars, label_nil, ty) <=> ty = tyList) /\
  (!vars a b ty. label_typeof (vars, label_cons a b, ty) <=>
    (ty = tyList /\
    (?tya. label_typeof (vars, a, tya)) /\
    (?tyb. label_typeof (vars, b, tyb))))
Proof
  rpt conj_tac
  \\ CONV_TAC (STRIP_QUANT_CONV $ LHS_CONV (ONCE_REWRITE_CONV [label_typeof_cases]))
  \\ simp[]
  \\ metis_tac[]
QED

Definition label_typeof_fun_def:
(label_typeof_fun vars (label_integer v) = SOME tyInt) /\
(label_typeof_fun vars (label_string s) = SOME tyString) /\
(label_typeof_fun vars (label_char c) = SOME tyChar) /\
(label_typeof_fun vars (label_variable v) = FLOOKUP vars v) /\
(label_typeof_fun vars (label_indeg n) = SOME tyInt) /\
(label_typeof_fun vars (label_outdeg n) = SOME tyInt) /\
(label_typeof_fun vars (label_length n) = case FLOOKUP vars n of
  SOME tyList => SOME tyInt |
  SOME tyAtom => SOME tyInt |
  SOME tyString => SOME tyInt |
  _ => NONE) /\
(label_typeof_fun vars (label_add a b) =
  if label_typeof_fun vars a = SOME tyInt /\ label_typeof_fun vars b = SOME tyInt
  then SOME tyInt else NONE) /\
(label_typeof_fun vars (label_sub a b) =
  if label_typeof_fun vars a = SOME tyInt /\ label_typeof_fun vars b = SOME tyInt
  then SOME tyInt else NONE) /\
(label_typeof_fun vars (label_mult a b) =
  if label_typeof_fun vars a = SOME tyInt /\ label_typeof_fun vars b = SOME tyInt
  then SOME tyInt else NONE) /\
(label_typeof_fun vars (label_div a b) =
  if label_typeof_fun vars a = SOME tyInt /\ label_typeof_fun vars b = SOME tyInt
  then SOME tyInt else NONE) /\
(label_typeof_fun vars (label_concat a b) =
  if (label_typeof_fun vars a = SOME tyString \/ label_typeof_fun vars a = SOME tyChar) /\
     (label_typeof_fun vars b = SOME tyString \/ label_typeof_fun vars b = SOME tyChar)
  then SOME tyString else NONE) /\
(label_typeof_fun vars label_nil = SOME tyList) /\
(label_typeof_fun vars (label_cons a b) =
  if IS_SOME (label_typeof_fun vars a) /\ IS_SOME (label_typeof_fun vars b)
  then SOME tyList else NONE) /\
(label_typeof_fun vars (label_negate v) = if label_typeof_fun vars v = SOME tyInt
then SOME tyInt else NONE)
End


Theorem label_typeof_label_typeof_fun:
!vars tm ty. label_typeof (vars, tm, ty) <=> label_typeof_fun vars tm = SOME ty
Proof
  Induct_on ‘tm’
  \\ (
      fs [label_typeof_fun_def, label_typeof_rewrites]
      \\ TRY (metis_tac[])
  )
 >- (
  METIS_TAC [optionTheory.IS_SOME_EXISTS]
)
\\ rpt strip_tac
>- (
  Cases_on ‘FLOOKUP vars v’ \\ fs []
  \\ CASE_TAC \\ fs []
)
QED


Type nodeattr[pp] = ``:label # nodemark option``
Type edgeattr[pp] = ``:label # edgemark option``

Type rulegraph[pp] = ``:(nodeattr, edgeattr) graph``

(*
(*
  Bidirectional Edge 2
  There is at most one bidiretional edge between a pair of nodes.
*)
Definition bidir_edge_uniqueness_def:
  bidir_edge_uniqueness (G:rulegraph) <=>
    CARD (IMAGE (\e. {G.s ' e; G.t ' e}) G.b) = CARD G.b
End *)

Definition get_all_labels_def:
 get_all_labels (G:rulegraph) = IMAGE FST (FRANGE G.l) UNION IMAGE FST (FRANGE G.m)
End

Definition welltyped_rulegraph_def:
  welltyped_rulegraph vars G = !x. x IN get_all_labels G ==> IS_SOME $ label_typeof_fun vars x
End

(* Helper colleting nodeids expressions *)
Definition collect_nodeids_expression_def:
  collect_nodeids_expression (label_integer i) = {} /\
  collect_nodeids_expression (label_string s) = {} /\
  collect_nodeids_expression (label_char c) = {} /\
  collect_nodeids_expression (label_variable v) = {} /\
  collect_nodeids_expression (label_indeg n) = {n} /\
  collect_nodeids_expression (label_outdeg n) = {n} /\
  collect_nodeids_expression (label_length v) = {} /\
  collect_nodeids_expression (label_add a b) = {} /\
  collect_nodeids_expression (label_sub a b) = {} /\
  collect_nodeids_expression (label_mult a b) = {} /\
  collect_nodeids_expression (label_div a b) = {} /\
  collect_nodeids_expression (label_concat a b) =  collect_nodeids_expression a UNION collect_nodeids_expression b /\
  collect_nodeids_expression (label_negate v) = {} /\
  collect_nodeids_expression label_nil = {} /\
  collect_nodeids_expression (label_cons a b) = (collect_nodeids_expression a UNION collect_nodeids_expression b)
End


(* All labels in the graph are in spine form (normalized).
   This is the canonical form produced by the parser.
   Note: This is NOT included in wf_rulegraph because wf_rulegraph
   is used polymorphically on hostgraphs (e.g., deletion result). *)
Definition rulegraph_labels_spine_def:
  rulegraph_labels_spine G <=>
    FEVERY (is_rulelabel_spine o FST o SND) G.l /\
    FEVERY (is_rulelabel_spine o FST o SND) G.m
End

(* wf_rulegraph includes spine form for rule graphs.
   For deletion intermediate results on hostgraphs, use wf_partial_hostgraph. *)
Definition wf_rulegraph_def:
  wf_rulegraph G <=>
    wf_graph G /\
    FDOM G.l SUBSET G.V /\
    FDOM G.m = G.E /\
    rulegraph_labels_spine G
End

(* A totally labelled rulegraph has labels for all nodes.
   This is required for rule graphs L and R in a rule schema,
   per the thesis Definition 3.4.4 (Rule Graph). *)
Definition totally_labelled_rulegraph_def:
  totally_labelled_rulegraph G <=>
    wf_rulegraph G /\
    FDOM G.l = G.V
End

(* All labels in the graph are well-formed.
   Used in proofs only - enforced by parser/translation.
   Note: wf_rulegraph (with spine) does NOT imply wf_rulegraph_labels
   because rule atoms can contain sub-expressions. Both are enforced
   by the parser but tracked separately for proofs. *)
Definition wf_rulegraph_labels_def:
  wf_rulegraph_labels G <=>
    FEVERY (wf_rulelabel o FST o SND) G.l /\
    FEVERY (wf_rulelabel o FST o SND) G.m
End

(* Helper to collect all variable names *)
Definition label_vars_def:
  label_vars (label_integer int) = {} /\
  label_vars (label_string string) = {} /\
  label_vars (label_char char) = {} /\
  label_vars (label_variable v) = {v} /\
  label_vars (label_indeg n) = {} /\
  label_vars (label_outdeg n) = {} /\
  label_vars (label_length v) = {} /\
  label_vars (label_add a b) = label_vars a UNION label_vars b /\
  label_vars (label_sub a b) = label_vars a UNION label_vars b /\
  label_vars (label_mult a b) =  label_vars a UNION label_vars b /\
  label_vars (label_div a b) = label_vars a UNION label_vars b /\
  label_vars (label_concat a b) = label_vars a UNION label_vars b /\
  label_vars (label_negate l) = label_vars l /\
  label_vars label_nil = {} /\
  label_vars (label_cons a b) = label_vars a UNION label_vars b
End

(*
  Brian Thesis: Definition 2.20 (Simple Label)
  It contains no length, degree, or arithmetic operators, except for the unary minus.
*)
Definition is_simple_label1_def:
  is_simple_label1 (label_integer int) = T /\
  is_simple_label1 (label_string string) = T /\
  is_simple_label1 (label_char char) = T /\
  is_simple_label1 (label_variable v) = T /\
  is_simple_label1 (label_indeg n) = F /\
  is_simple_label1 (label_outdeg n) = F /\
  is_simple_label1 (label_length v) = F /\
  is_simple_label1 (label_add a b) = F /\
  is_simple_label1 (label_sub a b) = F /\
  is_simple_label1 (label_mult a b) = F /\
  is_simple_label1 (label_div a b) = F /\
  is_simple_label1 (label_concat a b) = T /\
  is_simple_label1 (label_negate v) = T /\
  is_simple_label1 label_nil = T /\
  is_simple_label1 (label_cons a b) = (is_simple_label1 a /\ is_simple_label1 b)
End

(*
  Brian Thesis: Definition 2.20 (Simple Label)
  It contains at most one list variable.
*)
Definition is_simple_label2_def:
  is_simple_label2 vars l = let
    listvars = {v | v IN label_vars l /\ FLOOKUP vars v = SOME tyList} in
    CARD listvars <= 1
End

(* Helper colleting string expressions *)
Definition collect_string_expression_def:
  collect_string_expression (label_integer i) = {} /\
  collect_string_expression (label_string s) = {} /\
  collect_string_expression (label_char c) = {} /\
  collect_string_expression (label_variable v) = {} /\
  collect_string_expression (label_indeg n) = {} /\
  collect_string_expression (label_outdeg n) = {} /\
  collect_string_expression (label_length v) = {} /\
  collect_string_expression (label_add a b) = {} /\
  collect_string_expression (label_sub a b) = {} /\
  collect_string_expression (label_mult a b) = {} /\
  collect_string_expression (label_div a b) = {} /\
  collect_string_expression (label_concat a b) = {label_concat a b} /\
  collect_string_expression (label_negate v) = {} /\
  collect_string_expression label_nil = {} /\
  collect_string_expression (label_cons a b) = (collect_string_expression a UNION collect_string_expression b)
End


(*
  Brian Thesis: Definition 2.20 (Simple Label)
  Every string expression it contains has at most one string variable.
*)
Definition is_simple_label3_def:
  is_simple_label3 (vars: varname |-> ty) (l:label) = let
    list_expr = collect_string_expression l in
    let expr_vars = BIGUNION (IMAGE label_vars list_expr) in
    let listvars = {v | v IN expr_vars /\ FLOOKUP vars v = SOME tyString} in
    CARD listvars <= 1
End

Definition is_simple_label_def:
  is_simple_label vars l <=>
    is_simple_label1 l /\ is_simple_label2 vars l /\ is_simple_label3 vars l
End

Definition rulegraph_labels_def:
  rulegraph_labels (G:rulegraph) <=> IMAGE FST (FRANGE G.l) UNION IMAGE FST (FRANGE G.m)
End

Definition rulegraph_vars_def:
  rulegraph_vars (G: rulegraph) <=> BIGUNION $ IMAGE label_vars (rulegraph_labels G)
End

val () = export_theory ();
