open HolKernel boolLib bossLib
open finite_mapTheory stringLib integerTheory pred_setTheory listTheory

open graphTheory typingTheory

val () = new_theory "hostgraph";

Datatype: edgemark =
  edgemark_red | edgemark_green | edgemark_blue | edgemark_dashed
End

Datatype: nodemark =
  nodemark_red | nodemark_green | nodemark_blue | nodemark_grey
End

Datatype: label =
  label_integer int | label_string string | label_char char| label_nil | label_cons label label
End

(* Well-formedness for host labels.
   These predicates are used in proofs only - the parser and translation
   functions enforce this structure by construction. *)

(* An atom can appear in head position of label_cons *)
Definition is_host_atom_def:
  is_host_atom (label_integer _) = T /\
  is_host_atom (label_string _) = T /\
  is_host_atom (label_char _) = T /\
  is_host_atom label_nil = F /\
  is_host_atom (label_cons _ _) = F
End

(* A host label is in "spine form" - a proper GP2 list.
   In GP2, labels are sequences of atoms. The spine form is the canonical
   representation that the parser produces and eval_label_fun maintains.
   This is the ONLY valid form for host labels in wf_hostgraph. *)
Definition is_hostlabel_spine_def:
  is_hostlabel_spine label_nil = T /\
  is_hostlabel_spine (label_cons h t) = (is_host_atom h /\ is_hostlabel_spine t) /\
  is_hostlabel_spine _ = F
End

Definition count_labels_def:
  count_labels (label_cons a b) = count_labels a + count_labels b /\
  count_labels label_nil = 0 /\
  count_labels _ = 1n
End

(* Append two label lists. Atoms are treated as singletons.
   This is used by eval_label_fun to splice list-typed variable values
   into cons structures instead of wrapping them. *)
Definition label_append_def:
  label_append label_nil rest = rest /\
  label_append (label_cons h t) rest = label_cons h (label_append t rest) /\
  label_append atom rest = label_cons atom rest
End

Definition split_label_list_def:
  split_label_list 0n l = SOME (label_nil, l) /\
  split_label_list n (label_cons h t) =
    (case split_label_list (n - 1) t of
      SOME (l1, l2) => SOME (label_cons h l1, l2) |
      NONE => NONE) /\
  split_label_list n l = NONE
End


Theorem split_label_list_preserve_count:
  !n l a b. split_label_list n l = SOME (a,b) ==> count_labels l = (count_labels a + count_labels b)
Proof
    Induct_on `n` >> rw[]
    >- (
      Cases_on `split_label_list 0 l`
      \\ gvs[split_label_list_def, count_labels_def]
      )
    >- (

      Cases_on `l`
      \\ fs[split_label_list_def]
      \\ rename1 `label_cons l h`
      \\ fs[split_label_list_def]
      \\ Cases_on `split_label_list n h`
      \\ fs[]
      \\ PairCases_on `x`
      \\ fs []
      \\ first_x_assum drule
      \\ rw[]
      \\ fs [count_labels_def]
    )
QED

Theorem split_label_list_append:
  !n l prefix suffix.
    split_label_list n l = SOME (prefix, suffix) ==>
    label_append prefix suffix = l
Proof
  Induct_on `n`
  >- rw[split_label_list_def, label_append_def]
  >- (rpt strip_tac >> Cases_on `l` >> gvs[split_label_list_def] >>
      qpat_x_assum `_ = SOME _` mp_tac >> simp[AllCaseEqs()] >> strip_tac >>
      gvs[] >> simp[label_append_def])
QED

(* split_label_list preserves spine form *)
Theorem split_label_list_spine:
  !n l prefix suffix.
    is_hostlabel_spine l /\ split_label_list n l = SOME (prefix, suffix) ==>
    is_hostlabel_spine prefix /\ is_hostlabel_spine suffix
Proof
  Induct_on `n` >> rpt strip_tac >> gvs[split_label_list_def, is_hostlabel_spine_def]
  >> Cases_on `l` >> gvs[split_label_list_def, is_hostlabel_spine_def, is_host_atom_def]
  >> qpat_x_assum `_ = SOME _` mp_tac >> simp[AllCaseEqs()] >> strip_tac >> gvs[]
  >> first_x_assum drule >> simp[is_hostlabel_spine_def] >> strip_tac >> simp[]
QED

(* label_append preserves spine form.
   Key theorem: eval_label_fun uses label_append, so results are spine. *)
Theorem label_append_spine:
  !l1 l2. is_hostlabel_spine l1 /\ is_hostlabel_spine l2 ==>
          is_hostlabel_spine (label_append l1 l2)
Proof
  Induct_on `l1` >> rw[label_append_def, is_hostlabel_spine_def] >>
  fs[is_hostlabel_spine_def]
QED

(* Atoms wrapped in cons-nil are spine *)
Theorem is_host_atom_cons_nil_spine:
  !a. is_host_atom a ==> is_hostlabel_spine (label_cons a label_nil)
Proof
  rw[is_hostlabel_spine_def]
QED

(* Rewrite rules for is_hostlabel_spine and is_host_atom combined.
   These simplify the precondition (is_hostlabel_spine hl \/ is_host_atom hl)
   that appears in unify_label_wf_assignment_spine and related theorems. *)
Theorem is_spine_or_atom_rws:
  (is_hostlabel_spine (label_integer i) \/ is_host_atom (label_integer i) <=> T) /\
  (is_hostlabel_spine (label_string s) \/ is_host_atom (label_string s) <=> T) /\
  (is_hostlabel_spine (label_char c) \/ is_host_atom (label_char c) <=> T) /\
  (is_hostlabel_spine label_nil \/ is_host_atom label_nil <=> T) /\
  (is_hostlabel_spine (label_cons h t) \/ is_host_atom (label_cons h t) <=>
   is_host_atom h /\ is_hostlabel_spine t)
Proof
  simp[is_hostlabel_spine_def, is_host_atom_def]
QED

(* Individual rewrites for is_host_atom - useful for case elimination *)
Theorem is_host_atom_rws:
  (is_host_atom (label_integer i) <=> T) /\
  (is_host_atom (label_string s) <=> T) /\
  (is_host_atom (label_char c) <=> T) /\
  (is_host_atom label_nil <=> F) /\
  (is_host_atom (label_cons h t) <=> F)
Proof
  simp[is_host_atom_def]
QED

(* Individual rewrites for is_hostlabel_spine - useful for case elimination *)
Theorem is_hostlabel_spine_rws:
  (is_hostlabel_spine (label_integer i) <=> F) /\
  (is_hostlabel_spine (label_string s) <=> F) /\
  (is_hostlabel_spine (label_char c) <=> F) /\
  (is_hostlabel_spine label_nil <=> T) /\
  (is_hostlabel_spine (label_cons h t) <=> is_host_atom h /\ is_hostlabel_spine t)
Proof
  simp[is_hostlabel_spine_def]
QED

Definition flatten_label_cons_def:
  flatten_label_cons (l:label): label list =
    case l of
      label_cons x xs => flatten_label_cons x ++ flatten_label_cons xs |
      label_nil => [ ] |
      atom => [atom]
End

Definition mk_label_spine_def:
  mk_label_spine (l:label list):label =
    case l of
      [] => label_nil |
      x::xs => label_cons x $ mk_label_spine xs
End

Definition normalize_label_def:
  normalize_label (l:label): label =
    mk_label_spine $ flatten_label_cons l
End

(* flatten_label_cons always produces a list of atoms *)
Theorem flatten_label_cons_all_atoms:
  !l. EVERY is_host_atom (flatten_label_cons l)
Proof
  Induct_on `l` >>
  ONCE_REWRITE_TAC[flatten_label_cons_def] >>
  simp[is_host_atom_def, EVERY_APPEND]
QED

(* mk_label_spine produces spine form when given atoms *)
Theorem mk_label_spine_is_spine:
  !ls. EVERY is_host_atom ls ==> is_hostlabel_spine (mk_label_spine ls)
Proof
  Induct_on `ls`
  >- simp[mk_label_spine_def, is_hostlabel_spine_def]
  >- (rw[] >> ONCE_REWRITE_TAC[mk_label_spine_def] >> simp[is_hostlabel_spine_def])
QED

(* normalize_label always produces spine form *)
Theorem normalize_label_is_spine:
  !l. is_hostlabel_spine (normalize_label l)
Proof
  rw[normalize_label_def] >>
  irule mk_label_spine_is_spine >>
  simp[flatten_label_cons_all_atoms]
QED

(* Helper: flattening an atom gives a singleton list *)
Theorem flatten_label_cons_atom:
  !l. is_host_atom l ==> flatten_label_cons l = [l]
Proof
  Cases_on `l` >> simp[is_host_atom_def, flatten_label_cons_def]
QED

(* For spine-form labels, normalization is identity *)
Theorem normalize_label_spine_id:
  !l. is_hostlabel_spine l ==> normalize_label l = l
Proof
  Induct_on `l` >> rw[is_hostlabel_spine_def] >>
  simp[normalize_label_def] >>
  ONCE_REWRITE_TAC[flatten_label_cons_def] >>
  simp[flatten_label_cons_atom] >>
  ONCE_REWRITE_TAC[mk_label_spine_def] >> simp[] >>
  fs[normalize_label_def]
QED

(* Normalization is idempotent *)
Theorem normalize_label_idempotent:
  !l. normalize_label (normalize_label l) = normalize_label l
Proof
  rw[] >> irule normalize_label_spine_id >> simp[normalize_label_is_spine]
QED

(*
EVAL ``normalize_label $ label_integer 1``
EVAL ``normalize_label $ label_nil``
EVAL ``normalize_label $ label_cons label_nil label_nil``
*)

Definition label_typeof_def:
(label_typeof (label_integer v) = tyInt) /\
(label_typeof (label_string s) = tyString) /\
(label_typeof (label_char c) = tyChar) /\
(label_typeof (label_cons a b) = tyList) /\
(label_typeof label_nil = tyList)
End



Type nodeattr[pp] = ``:label # nodemark option``
Type edgeattr[pp] = ``:label # edgemark option``
Type hostgraph[pp] = ``:(nodeattr, edgeattr) graph``

(* If g SUBMAP f and FEVERY P f, then FEVERY P g.
   Used for preservation of label properties through DRESTRICT. *)
Theorem FEVERY_SUBMAP:
  !P f g. g SUBMAP f /\ FEVERY P f ==> FEVERY P g
Proof
  rpt strip_tac >> fs[FEVERY_DEF, SUBMAP_DEF]
QED

(* All labels in the graph are in spine form (normalized).
   This is the canonical form produced by the parser. *)
Definition hostgraph_labels_spine_def:
  hostgraph_labels_spine G <=>
    FEVERY (is_hostlabel_spine o FST o SND) G.l /\
    FEVERY (is_hostlabel_spine o FST o SND) G.m
End

Definition wf_hostgraph_def:
  wf_hostgraph G <=>
    wf_graph G /\
    FDOM G.l = G.V /\
    FDOM G.m = G.E /\
    hostgraph_labels_spine G
End

(* Partial hostgraph: like wf_hostgraph but allows partial node labeling.
   Used for deletion intermediate results where interface node labels
   are removed (to be replaced by RHS labels in gluing). *)
Definition wf_partial_hostgraph_def:
  wf_partial_hostgraph G <=>
    wf_graph G /\
    FDOM G.l SUBSET G.V /\
    FDOM G.m = G.E /\
    hostgraph_labels_spine G
End

Theorem wf_partial_hostgraph_IMP_wf_graph:
  !G. wf_partial_hostgraph G ==> wf_graph G
Proof
  rw[wf_partial_hostgraph_def]
QED

Theorem wf_partial_hostgraph_IMP_finite_sets:
  wf_partial_hostgraph G ==> FINITE G.V /\ FINITE G.E
Proof
  rw[wf_partial_hostgraph_def, wf_graph_def]
QED

Theorem wf_hostgraph_IMP_wf_partial_hostgraph:
  !G. wf_hostgraph G ==> wf_partial_hostgraph G
Proof
  rw[wf_hostgraph_def, wf_partial_hostgraph_def]
QED

Theorem wf_hostgraph_IMP_wf_graph:
  !G. wf_hostgraph G ==> wf_graph G
Proof
  rw[wf_hostgraph_def]
QED

Theorem wf_hostgraph_IMP_finite_sets:
  wf_hostgraph G ==> FINITE G.V /\ FINITE G.E
Proof
  rw[wf_hostgraph_def, wf_graph_def]
QED

(* wf_hostgraph implies spine form for all labels *)
Theorem wf_hostgraph_IMP_hostgraph_labels_spine:
  !G. wf_hostgraph G ==> hostgraph_labels_spine G
Proof
  rw[wf_hostgraph_def]
QED

Theorem wf_graph_IMP_FDOM_DRESTRICT_m_eq:
  (!G A. wf_hostgraph G ==> A SUBSET G.E ==> FDOM (DRESTRICT G.m A) = A)
Proof
  fs[wf_hostgraph_def,FDOM_DRESTRICT,INTER_SUBSET_EQN]
QED


Definition nodes_unmarked_def:
  nodes_unmarked G <=> FEVERY (IS_NONE o SND o SND) G.l
End

Definition edges_unmarked_def:
  edges_unmarked G <=> FEVERY (IS_NONE o SND o SND) G.m
End

Definition unmarked_hostgraph_def:
  unmarked_hostgraph G <=> nodes_unmarked G /\ edges_unmarked G
End

(* All nodes in the graph are unrooted (p = F for all nodes) *)
Definition unrooted_hostgraph_def:
  unrooted_hostgraph G <=> FDOM G.p = G.V /\ (!n. n IN G.V ==> G.p ' n = F)
End

(* A label is "nonempty spine" if it has the form (label_cons h t, mark)
   where h is a host atom and t is a hostlabel spine.
   This is required by rule_link which matches pattern "x:xs". *)
Definition is_nonempty_spine_label_def:
  is_nonempty_spine_label (l, m) <=>
    ?h t. l = label_cons h t /\ is_host_atom h /\ is_hostlabel_spine t
End

(* All node labels in the graph are non-empty spines.
   Required for rule_link to find morphisms. *)
Definition nonempty_node_labels_def:
  nonempty_node_labels G <=> FEVERY (is_nonempty_spine_label o SND) G.l
End

val () = export_theory ();
