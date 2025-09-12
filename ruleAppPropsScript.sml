open HolKernel boolLib bossLib
open finite_mapTheory pred_setTheory
open hostgraphTheory typingTheory semTheory rulegraphTheory ruleTheory

val () = new_theory "ruleAppProps"

(* Helper lemmas for label unification                                        *)

(* For spine-form labels, split_label_list with count returns (label, nil) *)
Theorem split_label_list_spine_count:
  !sl. is_hostlabel_spine sl ==> split_label_list (count_labels sl) sl = SOME (sl, label_nil)
Proof
  Induct_on `sl` >>
  rw[hostgraphTheory.is_hostlabel_spine_def, hostgraphTheory.count_labels_def,
     hostgraphTheory.split_label_list_def] >>
  `count_labels sl = 1` by (Cases_on `sl` >>
     fs[hostgraphTheory.is_host_atom_def, hostgraphTheory.count_labels_def]) >>
  simp[GSYM arithmeticTheory.ADD1] >>
  ONCE_REWRITE_TAC [hostgraphTheory.split_label_list_def] >> simp[]
QED

(* unify_label succeeds for tyList variable pattern against spine labels *)
Theorem unify_label_tyList_spine:
  !typing v hl.
    FLOOKUP typing v = SOME tyList /\ is_hostlabel_spine hl ==>
    ?a. unify_label typing (label_cons (label_variable v) label_nil) hl = SOME a
Proof
  rpt strip_tac >> Cases_on `hl`
  >- fs[hostgraphTheory.is_hostlabel_spine_def]
  >- fs[hostgraphTheory.is_hostlabel_spine_def]
  >- fs[hostgraphTheory.is_hostlabel_spine_def]
  >- simp[semTheory.unify_label_def, semTheory.extend_assignment_def,
          hostgraphTheory.label_typeof_def, typingTheory.is_subtype_of_def,
          relationTheory.RTC_REFL, semTheory.merge_assignment_def,
          semTheory.agree_on_common_keys_def]
  >- (fs[hostgraphTheory.is_hostlabel_spine_def] >>
      simp[semTheory.unify_label_def, hostgraphTheory.count_labels_def] >>
      `count_labels l = 1` by (Cases_on `l` >>
         fs[hostgraphTheory.is_host_atom_def, hostgraphTheory.count_labels_def]) >>
      `is_hostlabel_spine (label_cons l l0)` by simp[hostgraphTheory.is_hostlabel_spine_def] >>
      drule split_label_list_spine_count >> strip_tac >>
      fs[hostgraphTheory.count_labels_def] >>
      `count_labels label_nil = 0` by EVAL_TAC >> simp[] >>
      `count_labels l0 + 1 = count_labels l + count_labels l0` by simp[] >>
      pop_assum SUBST_ALL_TAC >> simp[] >>
      simp[semTheory.extend_assignment_def, hostgraphTheory.label_typeof_def,
           typingTheory.is_subtype_of_def, relationTheory.RTC_REFL,
           semTheory.merge_assignment_def, semTheory.agree_on_common_keys_def])
QED

(* Generic framework for rules with simple tyList label patterns              *)

(* A rulegraph label pattern is "simple" if it's just a tyList variable: v:nil *)
Definition is_simple_tyList_pattern_def:
  is_simple_tyList_pattern typing lbl <=>
    ?v. lbl = label_cons (label_variable v) label_nil /\
        FLOOKUP typing v = SOME tyList
End

(* A rule has simple labels if all LHS node/edge labels are simple tyList patterns *)
Definition rule_has_simple_labels_def:
  rule_has_simple_labels r <=>
    (* All LHS node labels are simple tyList patterns *)
    (!n. n IN r.lhs.V ==>
         ?lbl. FLOOKUP r.lhs.l n = SOME (lbl, NONE) /\
               is_simple_tyList_pattern r.vars lbl) /\
    (* All LHS edge labels are simple tyList patterns *)
    (!e. e IN r.lhs.E ==>
         ?lbl. FLOOKUP r.lhs.m e = SOME (lbl, NONE) /\
               is_simple_tyList_pattern r.vars lbl)
End

(* Key lemma: unify_nodeattr succeeds for simple patterns on unmarked spine labels *)
Theorem unify_nodeattr_simple_succeeds:
  !typing lbl hl.
    is_simple_tyList_pattern typing lbl /\
    is_hostlabel_spine hl ==>
    ?a. unify_nodeattr typing (lbl, NONE) (hl, NONE) = SOME a
Proof
  rpt strip_tac >>
  Cases_on `lbl` >> fs[is_simple_tyList_pattern_def] >>
  rename1 `label_cons (label_variable v) label_nil` >>
  simp[semTheory.unify_nodeattr_def, semTheory.nodemark_matches_def] >>
  metis_tac[unify_label_tyList_spine]
QED

(* Same for edges *)
Theorem unify_edgeattr_simple_succeeds:
  !typing lbl hl.
    is_simple_tyList_pattern typing lbl /\
    is_hostlabel_spine hl ==>
    ?a. unify_edgeattr typing (lbl, NONE) (hl, NONE) = SOME a
Proof
  rpt strip_tac >>
  Cases_on `lbl` >> fs[is_simple_tyList_pattern_def] >>
  rename1 `label_cons (label_variable v) label_nil` >>
  simp[semTheory.unify_edgeattr_def, semTheory.edgemark_matches_def] >>
  metis_tac[unify_label_tyList_spine]
QED

(* mk_assignment_node/edge succeed for simple patterns                        *)

(* mk_assignment_node succeeds for simple patterns against spine labels *)
Theorem mk_assignment_node_simple_succeeds:
  !r m G nid v.
    nid IN FDOM m.nodemap /\
    m.nodemap ' nid = v /\
    nid IN FDOM r.lhs.l /\
    v IN FDOM G.l /\
    is_simple_tyList_pattern r.vars (FST (r.lhs.l ' nid)) /\
    SND (r.lhs.l ' nid) = NONE /\
    is_hostlabel_spine (FST (G.l ' v)) /\
    SND (G.l ' v) = NONE ==>
    ?a. mk_assignment_node r m G nid = SOME a
Proof
  rpt strip_tac >> simp[semTheory.mk_assignment_node_def, FLOOKUP_DEF] >>
  `r.lhs.l ' nid = (FST (r.lhs.l ' nid), NONE)` by (Cases_on `r.lhs.l ' nid` >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  `G.l ' v = (FST (G.l ' v), NONE)` by (Cases_on `G.l ' v` >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  irule unify_nodeattr_simple_succeeds >> simp[]
QED

(* mk_assignment_edge succeeds for simple patterns against spine labels *)
Theorem mk_assignment_edge_simple_succeeds:
  !r m G eid e.
    eid IN FDOM m.edgemap /\
    m.edgemap ' eid = e /\
    eid IN FDOM r.lhs.m /\
    e IN FDOM G.m /\
    is_simple_tyList_pattern r.vars (FST (r.lhs.m ' eid)) /\
    SND (r.lhs.m ' eid) = NONE /\
    is_hostlabel_spine (FST (G.m ' e)) /\
    SND (G.m ' e) = NONE ==>
    ?a. mk_assignment_edge r m G eid = SOME a
Proof
  rpt strip_tac >> simp[semTheory.mk_assignment_edge_def, FLOOKUP_DEF] >>
  `r.lhs.m ' eid = (FST (r.lhs.m ' eid), NONE)` by (Cases_on `r.lhs.m ' eid` >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  `G.m ' e = (FST (G.m ' e), NONE)` by (Cases_on `G.m ' e` >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  irule unify_edgeattr_simple_succeeds >> simp[]
QED

(* Singleton assignment lemmas for simple patterns                            *)

(* Disjoint domains implies agree_on_common_keys (vacuously) *)
Theorem disjoint_agree:
  !f1 f2. DISJOINT (FDOM f1) (FDOM f2) ==> agree_on_common_keys f1 f2
Proof
  rw[semTheory.agree_on_common_keys_def, DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

(* Disjoint domains implies merge_assignment succeeds *)
Theorem disjoint_merge_succeeds:
  !f1 f2. DISJOINT (FDOM f1) (FDOM f2) ==>
          merge_assignment f1 f2 = SOME (FUNION f1 f2)
Proof
  rw[semTheory.merge_assignment_def] >> metis_tac[disjoint_agree]
QED

(* unify_label for simple tyList pattern returns EXACTLY FEMPTY |+ (v, hl) *)
Theorem unify_label_simple_singleton:
  !typing v hl.
    FLOOKUP typing v = SOME tyList /\ is_hostlabel_spine hl ==>
    unify_label typing (label_cons (label_variable v) label_nil) hl =
    SOME (FEMPTY |+ (v, hl))
Proof
  rpt strip_tac >> Cases_on `hl` >> gvs[hostgraphTheory.is_hostlabel_spine_def]
  (* label_nil case *)
  >- simp[semTheory.unify_label_def, semTheory.extend_assignment_def,
          hostgraphTheory.label_typeof_def, typingTheory.is_subtype_of_def,
          relationTheory.RTC_REFL, semTheory.merge_assignment_def,
          semTheory.agree_on_common_keys_def, FUNION_FEMPTY_1]
  (* label_cons case *)
  >- (`is_hostlabel_spine (label_cons l l0)` by simp[hostgraphTheory.is_hostlabel_spine_def] >>
      `split_label_list (count_labels (label_cons l l0)) (label_cons l l0) =
       SOME (label_cons l l0, label_nil)` by (irule split_label_list_spine_count >> simp[]) >>
      simp[semTheory.unify_label_def] >>
      `count_labels label_nil = 0` by EVAL_TAC >> fs[] >>
      simp[semTheory.extend_assignment_def, hostgraphTheory.label_typeof_def,
           typingTheory.is_subtype_of_def, relationTheory.RTC_REFL,
           semTheory.merge_assignment_def, semTheory.agree_on_common_keys_def,
           FUNION_FEMPTY_2])
QED

(* mk_assignment_node returns EXACTLY FEMPTY |+ (var, hl) for simple patterns *)
Theorem mk_assignment_node_singleton:
  !r m G nid v var.
    FLOOKUP r.lhs.l nid = SOME (label_cons (label_variable var) label_nil, NONE) /\
    FLOOKUP r.vars var = SOME tyList /\
    FLOOKUP m.nodemap nid = SOME v /\
    FLOOKUP G.l v = SOME (hl, NONE) /\
    is_hostlabel_spine hl ==>
    mk_assignment_node r m G nid = SOME (FEMPTY |+ (var, hl))
Proof
  rpt strip_tac >> simp[semTheory.mk_assignment_node_def,
                        semTheory.unify_nodeattr_def,
                        semTheory.nodemark_matches_def] >>
  metis_tac[unify_label_simple_singleton]
QED

(* mk_assignment_edge returns EXACTLY FEMPTY |+ (var, hl) for simple patterns *)
Theorem mk_assignment_edge_singleton:
  !r m G eid e var.
    FLOOKUP r.lhs.m eid = SOME (label_cons (label_variable var) label_nil, NONE) /\
    FLOOKUP r.vars var = SOME tyList /\
    FLOOKUP m.edgemap eid = SOME e /\
    FLOOKUP G.m e = SOME (hl, NONE) /\
    is_hostlabel_spine hl ==>
    mk_assignment_edge r m G eid = SOME (FEMPTY |+ (var, hl))
Proof
  rpt strip_tac >> simp[semTheory.mk_assignment_edge_def,
                        semTheory.unify_edgeattr_def,
                        semTheory.edgemark_matches_def] >>
  metis_tac[unify_label_simple_singleton]
QED

(* FOLDR with singleton assignments succeeds when all operations succeed and keys distinct *)
Theorem foldr_singleton_merge:
  !l f.
    ALL_DISTINCT l /\
    (!x. MEM x l ==> ?k v. f x = SOME (FEMPTY |+ (k, v))) /\
    (!x1 x2 k1 k2 v1 v2. MEM x1 l /\ MEM x2 l /\ x1 <> x2 /\
                          f x1 = SOME (FEMPTY |+ (k1, v1)) /\
                          f x2 = SOME (FEMPTY |+ (k2, v2)) ==> k1 <> k2) ==>
    ?result. FOLDR (\x acc. case f x of NONE => NONE
                           | SOME a => case acc of NONE => NONE
                                       | SOME acc' => merge_assignment acc' a)
                   (SOME FEMPTY) l = SOME result /\
             FDOM result = {k | ?x v. MEM x l /\ f x = SOME (FEMPTY |+ (k, v))}
Proof
  Induct_on `l` >> rw[EXTENSION] >>
  `?k v. f h = SOME (FEMPTY |+ (k, v))` by metis_tac[listTheory.MEM] >>
  gvs[] >>
  first_x_assum (qspec_then `f` mp_tac) >> impl_tac >- metis_tac[] >>
  strip_tac >> gvs[] >>
  `k NOTIN FDOM result` by (gvs[EXTENSION] >> spose_not_then strip_assume_tac >> metis_tac[]) >>
  simp[semTheory.merge_assignment_def] >>
  conj_tac >- (simp[semTheory.agree_on_common_keys_def, FDOM_FUPDATE] >>
               rpt strip_tac >> gvs[EXTENSION] >> metis_tac[]) >>
  rw[] >> EQ_TAC >>
  strip_tac >> gvs[] >>
  TRY (qexists_tac `h` >> simp[] >> metis_tac[]) >>
  TRY (gvs[FEMPTY_FUPDATE_EQ]) >>
  metis_tac[]
QED

(* NAC edge test evaluation                                                   *)

(* Helper: EXISTS over SET_TO_LIST is equivalent to existential over set *)
Theorem EXISTS_SET_TO_LIST:
  !P s. FINITE s ==> (EXISTS P (SET_TO_LIST s) <=> ?x. x IN s /\ P x)
Proof
  rw[listTheory.EXISTS_MEM, listTheory.MEM_SET_TO_LIST]
QED

(* Helper: EVERY over SET_TO_LIST is equivalent to universal over set *)
Theorem EVERY_SET_TO_LIST:
  !P s. FINITE s ==> (EVERY P (SET_TO_LIST s) <=> !x. x IN s ==> P x)
Proof
  rw[listTheory.EVERY_MEM, listTheory.MEM_SET_TO_LIST]
QED

(* The NAC edge test (condEdgeTest src tgt NONE) checks if there's an edge
   from nodemap(src) to nodemap(tgt) in the hostgraph *)
Theorem eval_condEdgeTest_NONE:
  !assign m G src tgt.
    FLOOKUP m.nodemap src = SOME v /\
    FLOOKUP m.nodemap tgt = SOME w /\
    FINITE G.E ==>
    eval_condition_fun assign m G (condEdgeTest src tgt NONE) =
    SOME (EXISTS (\e. FLOOKUP G.s e = SOME v /\ FLOOKUP G.t e = SOME w)
                 (SET_TO_LIST G.E))
Proof
  rw[semTheory.eval_condition_fun_def]
QED

(* Relating EXISTS over edges to has_edge when graph is well-formed *)
Theorem edge_exists_iff_has_edge:
  !G v w.
    wf_graph G ==>
    (EXISTS (\e. FLOOKUP G.s e = SOME v /\ FLOOKUP G.t e = SOME w)
            (SET_TO_LIST G.E) <=>
     has_edge G v w)
Proof
  rw[pathTheory.has_edge_def] >>
  `FINITE G.E` by fs[graphTheory.wf_graph_def] >>
  simp[listTheory.EXISTS_MEM, listTheory.MEM_SET_TO_LIST] >>
  EQ_TAC >> strip_tac >> qexists_tac `e` >> simp[]
  >- (`e IN FDOM G.s /\ e IN FDOM G.t` by fs[graphTheory.wf_graph_def, SUBSET_DEF] >>
      fs[FLOOKUP_DEF])
  >- (`e IN FDOM G.s /\ e IN FDOM G.t` by fs[graphTheory.wf_graph_def, SUBSET_DEF] >>
      fs[FLOOKUP_DEF])
QED

(* Key theorem: NAC negation of edge test evaluates to ~has_edge *)
Theorem eval_condNot_condEdgeTest_iff_no_edge:
  !assign m G src tgt v w.
    wf_graph G /\
    FLOOKUP m.nodemap src = SOME v /\
    FLOOKUP m.nodemap tgt = SOME w ==>
    eval_condition_fun assign m G (condNot (condEdgeTest src tgt NONE)) =
    SOME (~has_edge G v w)
Proof
  rw[semTheory.eval_condition_fun_def] >>
  `FINITE G.E` by fs[graphTheory.wf_graph_def] >>
  ONCE_REWRITE_TAC[listTheory.EVERY_NOT_EXISTS] >>
  simp[combinTheory.o_DEF] >>
  simp[listTheory.EXISTS_MEM, listTheory.MEM_SET_TO_LIST, pathTheory.has_edge_def] >>
  EQ_TAC >> strip_tac
  >- (qexists_tac `x` >> simp[] >>
      `x IN FDOM G.s /\ x IN FDOM G.t` by fs[graphTheory.wf_graph_def, SUBSET_DEF] >>
      fs[FLOOKUP_DEF])
  >- (qexists_tac `e` >> simp[] >>
      `e IN FDOM G.s /\ e IN FDOM G.t` by fs[graphTheory.wf_graph_def, SUBSET_DEF] >>
      fs[FLOOKUP_DEF])
QED

(* eval_label_fun for simple patterns                                         *)

(* label_append with label_nil is identity for spine-form labels *)
Theorem label_append_nil_right_spine:
  !l. is_hostlabel_spine l ==> label_append l label_nil = l
Proof
  Induct_on `l` >>
  simp[hostgraphTheory.label_append_def, hostgraphTheory.is_hostlabel_spine_def]
QED

(* eval_label_fun for simple variable pattern returns the assignment value
   when the value is spine-form *)
Theorem eval_label_fun_simple_pattern:
  !assign m G v hl.
    FLOOKUP assign v = SOME hl /\
    is_hostlabel_spine hl ==>
    eval_label_fun assign m G (label_cons (label_variable v) label_nil) = SOME hl
Proof
  rw[semTheory.eval_label_fun_def] >>
  irule label_append_nil_right_spine >> simp[]
QED

(* instantiate_nodeattr/edgeattr for simple patterns                          *)

(* instantiate_nodeattr succeeds for simple unmarked patterns with spine-form values
   when the node is fresh (not in the host graph via morphism) *)
Theorem instantiate_nodeattr_simple_fresh:
  !r assign m G nid v hl.
    FLOOKUP r.l nid = SOME (label_cons (label_variable v) label_nil, NONE) /\
    FLOOKUP assign v = SOME hl /\
    is_hostlabel_spine hl /\
    FLOOKUP (G.l f_o_f m.nodemap) nid = NONE ==>
    instantiate_nodeattr r assign m G nid = SOME (hl, NONE)
Proof
  rw[semTheory.instantiate_nodeattr_def, eval_label_fun_simple_pattern] >>
  simp[semTheory.rule_to_host_nodemark_def]
QED

(* instantiate_nodeattr succeeds for simple unmarked patterns when the node
   maps to an unmarked host node *)
Theorem instantiate_nodeattr_simple_matched:
  !r assign m G nid v hl hl'.
    FLOOKUP r.l nid = SOME (label_cons (label_variable v) label_nil, NONE) /\
    FLOOKUP assign v = SOME hl /\
    is_hostlabel_spine hl /\
    FLOOKUP (G.l f_o_f m.nodemap) nid = SOME (hl', NONE) ==>
    instantiate_nodeattr r assign m G nid = SOME (hl, NONE)
Proof
  rw[semTheory.instantiate_nodeattr_def, eval_label_fun_simple_pattern] >>
  simp[semTheory.eval_nodemark_def]
QED

(* instantiate_edgeattr succeeds for simple unmarked patterns with spine-form values
   when the edge is fresh (not in the host graph via morphism) *)
Theorem instantiate_edgeattr_simple_fresh:
  !r assign m G eid v hl.
    FLOOKUP r.m eid = SOME (label_cons (label_variable v) label_nil, NONE) /\
    FLOOKUP assign v = SOME hl /\
    is_hostlabel_spine hl /\
    FLOOKUP (G.m f_o_f m.edgemap) eid = NONE ==>
    instantiate_edgeattr r assign m G eid = SOME (hl, NONE)
Proof
  rw[semTheory.instantiate_edgeattr_def, eval_label_fun_simple_pattern] >>
  simp[semTheory.rule_to_host_edgemark_def]
QED

(* instantiate_edgeattr succeeds for simple unmarked patterns when the edge
   maps to an unmarked host edge *)
Theorem instantiate_edgeattr_simple_matched:
  !r assign m G eid v hl hl'.
    FLOOKUP r.m eid = SOME (label_cons (label_variable v) label_nil, NONE) /\
    FLOOKUP assign v = SOME hl /\
    is_hostlabel_spine hl /\
    FLOOKUP (G.m f_o_f m.edgemap) eid = SOME (hl', NONE) ==>
    instantiate_edgeattr r assign m G eid = SOME (hl, NONE)
Proof
  rw[semTheory.instantiate_edgeattr_def, eval_label_fun_simple_pattern] >>
  simp[semTheory.eval_edgemark_def]
QED

(* instantiate_nodeattr works for label_nil patterns when node is fresh *)
Theorem instantiate_nodeattr_nil_fresh:
  !r assign m G nid.
    FLOOKUP r.l nid = SOME (label_nil, NONE) /\
    FLOOKUP (G.l f_o_f m.nodemap) nid = NONE ==>
    instantiate_nodeattr r assign m G nid = SOME (label_nil, NONE)
Proof
  rw[semTheory.instantiate_nodeattr_def, semTheory.eval_label_fun_def,
     semTheory.rule_to_host_nodemark_def]
QED

(* instantiate_nodeattr works for label_nil patterns when matched to unmarked node *)
Theorem instantiate_nodeattr_nil_matched:
  !r assign m G nid hl'.
    FLOOKUP r.l nid = SOME (label_nil, NONE) /\
    FLOOKUP (G.l f_o_f m.nodemap) nid = SOME (hl', NONE) ==>
    instantiate_nodeattr r assign m G nid = SOME (label_nil, NONE)
Proof
  rw[semTheory.instantiate_nodeattr_def, semTheory.eval_label_fun_def,
     semTheory.eval_nodemark_def]
QED

(* instantiate_edgeattr works for label_nil patterns when edge is fresh *)
Theorem instantiate_edgeattr_nil_fresh:
  !r assign m G eid.
    FLOOKUP r.m eid = SOME (label_nil, NONE) /\
    FLOOKUP (G.m f_o_f m.edgemap) eid = NONE ==>
    instantiate_edgeattr r assign m G eid = SOME (label_nil, NONE)
Proof
  rw[semTheory.instantiate_edgeattr_def, semTheory.eval_label_fun_def,
     semTheory.rule_to_host_edgemark_def]
QED

(* instantiate_edgeattr works for label_nil patterns when matched to unmarked edge *)
Theorem instantiate_edgeattr_nil_matched:
  !r assign m G eid hl'.
    FLOOKUP r.m eid = SOME (label_nil, NONE) /\
    FLOOKUP (G.m f_o_f m.edgemap) eid = SOME (hl', NONE) ==>
    instantiate_edgeattr r assign m G eid = SOME (label_nil, NONE)
Proof
  rw[semTheory.instantiate_edgeattr_def, semTheory.eval_label_fun_def,
     semTheory.eval_edgemark_def]
QED

(* wf_assignment_spine for assignments from simple patterns                   *)

(* An assignment is spine-form if all values are spine labels *)
Theorem wf_assignment_spine_singleton:
  !v hl. is_hostlabel_spine hl ==>
         wf_assignment_spine (FEMPTY |+ (v, hl))
Proof
  rw[semTheory.wf_assignment_spine_def] >>
  simp[FEVERY_FUPDATE, FEVERY_FEMPTY]
QED

(* FUNION preserves wf_assignment_spine *)
Theorem wf_assignment_spine_FUNION:
  !a1 a2. wf_assignment_spine a1 /\ wf_assignment_spine a2 ==>
          wf_assignment_spine (FUNION a1 a2)
Proof
  rw[semTheory.wf_assignment_spine_def] >>
  irule fevery_funion >> simp[]
QED

(* mk_assignment_node success for simple patterns                              *)

(* For a single node with simple tyList pattern, mk_assignment_node succeeds
   when the host label is spine-form and unmarked *)
Theorem mk_assignment_node_simple_spine_succeeds:
  !r m G nid v.
    nid IN FDOM m.nodemap /\ m.nodemap ' nid = v /\ v IN FDOM G.l /\
    nid IN FDOM r.lhs.l /\
    is_simple_tyList_pattern r.vars (FST (r.lhs.l ' nid)) /\
    SND (r.lhs.l ' nid) = NONE /\
    is_hostlabel_spine (FST (G.l ' v)) /\
    SND (G.l ' v) = NONE ==>
    ?a. mk_assignment_node r m G nid = SOME a
Proof
  rw[] >> irule mk_assignment_node_simple_succeeds >> simp[] >>
  qexists_tac `v` >> simp[]
QED

(* For a single edge with simple tyList pattern, mk_assignment_edge succeeds *)
Theorem mk_assignment_edge_simple_spine_succeeds:
  !r m G eid edge.
    eid IN FDOM m.edgemap /\ m.edgemap ' eid = edge /\ edge IN FDOM G.m /\
    eid IN FDOM r.lhs.m /\
    is_simple_tyList_pattern r.vars (FST (r.lhs.m ' eid)) /\
    SND (r.lhs.m ' eid) = NONE /\
    is_hostlabel_spine (FST (G.m ' edge)) /\
    SND (G.m ' edge) = NONE ==>
    ?a. mk_assignment_edge r m G eid = SOME a
Proof
  rw[] >> irule mk_assignment_edge_simple_succeeds >> simp[] >>
  qexists_tac `edge` >> simp[]
QED

(* mk_assignment_nodes/edges success theorems                                  *)

(* mk_assignment_nodes succeeds when:
   1. Each node in LHS produces a singleton assignment
   2. All produced keys are distinct *)
Theorem mk_assignment_nodes_simple_succeeds:
  !r m G.
    FINITE r.lhs.V /\
    (!nid. nid IN r.lhs.V ==>
           ?k v. mk_assignment_node r m G nid = SOME (FEMPTY |+ (k, v))) /\
    (!nid1 nid2. nid1 IN r.lhs.V /\ nid2 IN r.lhs.V /\ nid1 <> nid2 ==>
                 !k1 k2 v1 v2. mk_assignment_node r m G nid1 = SOME (FEMPTY |+ (k1, v1)) /\
                               mk_assignment_node r m G nid2 = SOME (FEMPTY |+ (k2, v2)) ==>
                               k1 <> k2) ==>
    ?nassign. mk_assignment_nodes r m G = SOME nassign
Proof
  rw[semTheory.mk_assignment_nodes_def] >>
  qabbrev_tac `nodelist = SET_TO_LIST r.lhs.V` >>
  `ALL_DISTINCT nodelist` by simp[Abbr `nodelist`, listTheory.ALL_DISTINCT_SET_TO_LIST] >>
  `set nodelist = r.lhs.V` by simp[Abbr `nodelist`, listTheory.SET_TO_LIST_INV] >>
  drule_then (qspec_then `mk_assignment_node r m G` mp_tac) foldr_singleton_merge >>
  impl_tac
  >- (rpt conj_tac
      >- (rw[] >> first_x_assum irule >> gvs[listTheory.MEM_SET_TO_LIST])
      >- (rw[] >> SPOSE_NOT_THEN strip_assume_tac >> gvs[listTheory.MEM_SET_TO_LIST] >>
          first_x_assum (qspecl_then [`x1`, `x2`] mp_tac) >> simp[] >>
          qexistsl_tac [`k1`, `v1`, `v2`] >> simp[]))
  >- (strip_tac >> metis_tac[])
QED

(* mk_assignment_edges succeeds when:
   1. Each edge in LHS produces a singleton assignment
   2. All produced keys are distinct *)
Theorem mk_assignment_edges_simple_succeeds:
  !r m G.
    FINITE r.lhs.E /\
    (!eid. eid IN r.lhs.E ==>
           ?k v. mk_assignment_edge r m G eid = SOME (FEMPTY |+ (k, v))) /\
    (!eid1 eid2. eid1 IN r.lhs.E /\ eid2 IN r.lhs.E /\ eid1 <> eid2 ==>
                 !k1 k2 v1 v2. mk_assignment_edge r m G eid1 = SOME (FEMPTY |+ (k1, v1)) /\
                               mk_assignment_edge r m G eid2 = SOME (FEMPTY |+ (k2, v2)) ==>
                               k1 <> k2) ==>
    ?eassign. mk_assignment_edges r m G = SOME eassign
Proof
  rw[semTheory.mk_assignment_edges_def] >>
  qabbrev_tac `edgelist = SET_TO_LIST r.lhs.E` >>
  `ALL_DISTINCT edgelist` by simp[Abbr `edgelist`, listTheory.ALL_DISTINCT_SET_TO_LIST] >>
  `set edgelist = r.lhs.E` by simp[Abbr `edgelist`, listTheory.SET_TO_LIST_INV] >>
  drule_then (qspec_then `mk_assignment_edge r m G` mp_tac) foldr_singleton_merge >>
  impl_tac
  >- (rpt conj_tac
      >- (rw[] >> first_x_assum irule >> gvs[listTheory.MEM_SET_TO_LIST])
      >- (rw[] >> SPOSE_NOT_THEN strip_assume_tac >> gvs[listTheory.MEM_SET_TO_LIST] >>
          first_x_assum (qspecl_then [`x1`, `x2`] mp_tac) >> simp[] >>
          qexistsl_tac [`k1`, `v1`, `v2`] >> simp[]))
  >- (strip_tac >> metis_tac[])
QED

val () = export_theory ()
