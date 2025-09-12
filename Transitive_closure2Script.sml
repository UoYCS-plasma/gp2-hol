open HolKernel boolLib bossLib
open finite_mapTheory pred_setTheory
open programTheory programSyntax ruleTheory rulegraphTheory hostgraphTheory
open graphTheory typingTheory gp2LogicTheory pathTheory
open morphismTheory trackTheory semTheory stackTheory listTheory dpoTheory
open ruleAppPropsTheory

val () = new_theory "Transitive_closure2"

val match_morphism_rwts = [is_match_def, is_inj_morphism_def, is_morphism_def,
                           is_premorphism_def, morphism_dom_ran_def];
val match_source_rwts = [is_match_def, is_inj_morphism_def, is_morphism_def,
                         is_premorphism_def, preserve_source_def];
val match_target_rwts = [is_match_def, is_inj_morphism_def, is_morphism_def,
                         is_premorphism_def, preserve_target_def];
val match_inj_rwts = [is_match_def, is_inj_morphism_def, is_inj_premorphism_def];
val wf_rwts = [wf_hostgraph_def, wf_graph_def];

(* Rule definitions *)
Definition rule_link_def:
  rule_link =
    <|vars :=
    FEMPTY |++
    [(varname "z",tyList); (varname "y",tyList); (varname "x",tyList);
     (varname "b",tyList); (varname "a",tyList)];
  lhs :=
    <|V := {nodeid "n2"; nodeid "n1"; nodeid "n0"};
      E := {edgeid "e1"; edgeid "e0"};
      s := FEMPTY |++ [(edgeid "e1",nodeid "n1"); (edgeid "e0",nodeid "n0")];
      t := FEMPTY |++ [(edgeid "e1",nodeid "n2"); (edgeid "e0",nodeid "n1")];
      l :=
        FEMPTY |++
        [(nodeid "n2",label_cons (label_variable (varname "z")) label_nil,
          NONE);
         (nodeid "n1",label_cons (label_variable (varname "y")) label_nil,
          NONE);
         (nodeid "n0",label_cons (label_variable (varname "x")) label_nil,
          NONE)];
      m :=
        FEMPTY |++
        [(edgeid "e1",label_cons (label_variable (varname "b")) label_nil,
          NONE);
         (edgeid "e0",label_cons (label_variable (varname "a")) label_nil,
          NONE)];
      p := FEMPTY |++ [(nodeid "n2",F); (nodeid "n1",F); (nodeid "n0",F)]|>;
  rhs :=
    <|V := {nodeid "n2"; nodeid "n1"; nodeid "n0"};
      E := {edgeid "e2"; edgeid "e1"; edgeid "e0"};
      s :=
        FEMPTY |++
        [(edgeid "e2",nodeid "n0"); (edgeid "e1",nodeid "n1");
         (edgeid "e0",nodeid "n0")];
      t :=
        FEMPTY |++
        [(edgeid "e2",nodeid "n2"); (edgeid "e1",nodeid "n2");
         (edgeid "e0",nodeid "n1")];
      l :=
        FEMPTY |++
        [(nodeid "n2",label_cons (label_variable (varname "z")) label_nil,
          NONE);
         (nodeid "n1",label_cons (label_variable (varname "y")) label_nil,
          NONE);
         (nodeid "n0",label_cons (label_variable (varname "x")) label_nil,
          NONE)];
      m :=
        FEMPTY |++
        [(edgeid "e2",label_nil,NONE);
         (edgeid "e1",label_cons (label_variable (varname "b")) label_nil,
          NONE);
         (edgeid "e0",label_cons (label_variable (varname "a")) label_nil,
          NONE)];
      p := FEMPTY |++ [(nodeid "n2",F); (nodeid "n1",F); (nodeid "n0",F)]|>;
  inf := {nodeid "n2"; nodeid "n1"; nodeid "n0"};
  cond := SOME (condNot (condEdgeTest (nodeid "n0") (nodeid "n2") NONE))|>
End


Theorem wf_rule_link:
  wf_rule rule_link
Proof
  EVAL_TAC >> simp[FRANGE_FUPDATE, FRANGE_FEMPTY] >>
  rpt conj_tac >> TRY (simp[FEVERY_FUPDATE, FEVERY_FEMPTY] >> EVAL_TAC) >>
  rpt strip_tac >> fs[] >> rpt (EVAL_TAC >> all_tac)
QED

Theorem rule_link_structure:
  rule_link.rhs.s ' (edgeid "e0") = nodeid "n0" /\
  rule_link.rhs.t ' (edgeid "e0") = nodeid "n1" /\
  rule_link.rhs.s ' (edgeid "e1") = nodeid "n1" /\
  rule_link.rhs.t ' (edgeid "e1") = nodeid "n2" /\
  rule_link.rhs.s ' (edgeid "e2") = nodeid "n0" /\
  rule_link.rhs.t ' (edgeid "e2") = nodeid "n2" /\
  rule_link.lhs.s ' (edgeid "e0") = nodeid "n0" /\
  rule_link.lhs.t ' (edgeid "e0") = nodeid "n1" /\
  rule_link.lhs.s ' (edgeid "e1") = nodeid "n1" /\
  rule_link.lhs.t ' (edgeid "e1") = nodeid "n2"
Proof
  EVAL_TAC
QED

(* Procedure definitions *)
Definition proc_Main_def:
  proc_Main = term_alap (term_rscall {ruleid "link"})
End

(* Program definition *)
Definition program_def:
  program =
    <| proc := FEMPTY |++ [("Main", proc_Main)];
       rule := FEMPTY |++ [(ruleid "link", rule_link)] |>
End

Theorem program_wf:
  wf_program program
Proof
  simp[wf_program_def, program_def, FUPDATE_LIST_THM, condition_break_def,
       no_intermediate_terms_def, proc_call_validity_def, rule_call_validity_def,
       has_main_entry_def, FLOOKUP_UPDATE, proc_Main_def] >>
  simp[FEVERY_FUPDATE, FEVERY_FEMPTY, condition_break_def,
       no_intermediate_terms_def, collect_procids_def, collect_ruleids_def,
       INSERT_SUBSET, wf_rule_link]
QED

Definition generated_edges_def:
  generated_edges (m: morphism) (TC: hostgraph) =
    TC.E DIFF (FRANGE m.edgemap)
End

Definition edge_path_justified_def:
  edge_path_justified (G0: hostgraph) (m: morphism) (TC: hostgraph) <=>
    !e. e IN generated_edges m TC ==>
        ?v0 w0. v0 IN G0.V /\ w0 IN G0.V /\
                m.nodemap ' v0 = TC.s ' e /\
                m.nodemap ' w0 = TC.t ' e /\
                reachable_in G0 v0 w0
End

(* Pure agreement: track_bar extends track *)
Definition extends_morphism_def:
  extends_morphism (track: morphism) (track_bar: morphism) <=>
    track_bar.nodemap = track.nodemap /\
    FDOM track.edgemap SUBSET FDOM track_bar.edgemap /\
    !e. e IN FDOM track.edgemap ==>
        track.edgemap ' e = track_bar.edgemap ' e
End

(* No generated edge is parallel to any other edge in TC *)
Definition parallel_free_extension_def:
  parallel_free_extension (track_bar: morphism) (TC: hostgraph) <=>
    !e. e IN TC.E /\ e NOTIN FRANGE track_bar.edgemap ==>
        ~(?e'. e' IN TC.E /\ e' <> e /\
               TC.s ' e' = TC.s ' e /\ TC.t ' e' = TC.t ' e)
End

(* Paper Definition [Minimal extension] using the morphism hierarchy. *)
Definition minimal_extension_def:
  minimal_extension (G0: hostgraph) (track_bar: morphism) (TC: hostgraph) <=>
    is_inj_morphism G0 track_bar TC /\
    BIJ ($' track_bar.nodemap) G0.V TC.V /\
    edge_path_justified G0 track_bar TC /\
    parallel_free_extension track_bar TC
End

val me_inj_rwts = [minimal_extension_def, is_inj_morphism_def, is_morphism_def,
                   is_premorphism_def, morphism_dom_ran_def];

(* Postcondition: only track_bar *)
Definition is_transitive_closure_tracked_def:
  is_transitive_closure_tracked (G0: hostgraph) (track_bar: morphism) (TC: hostgraph) <=>
    is_transitive TC /\
    minimal_extension G0 track_bar TC
End

(* Loop invariant: track_bar is a minimal extension, graph is unmarked/unrooted *)
Definition tc_loop_invariant_total_def:
  tc_loop_invariant_total G0 G track_bar <=>
    wf_hostgraph G /\
    unmarked_hostgraph G /\
    unrooted_hostgraph G /\
    minimal_extension G0 track_bar G
End


(* Composed morphism for link step: track nodemap + custom edgemap *)
Definition link_new_track_bar_def:
  link_new_track_bar G0 track_bar lhs' m G =
    <| nodemap :=
        (compose_morphism (track lhs' rule_link.inf m G) track_bar).nodemap;
       edgemap := FUN_FMAP
          (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (track_bar.edgemap ' e))
          G0.E |>
End

(* Common hypotheses for link step theorems *)
Definition link_step_context_def:
  link_step_context G0 G track_bar lhs' rhs' m <=>
    wf_hostgraph G0 /\ wf_hostgraph G /\ FINITE G0.E /\
    minimal_extension G0 track_bar G /\
    is_match lhs' rule_link.inf m G /\
    lhs'.V = rule_link.lhs.V /\ lhs'.E = rule_link.lhs.E /\
    rhs'.V = rule_link.rhs.V /\ rhs'.E = rule_link.rhs.E /\
    wf_hostgraph lhs' /\ wf_hostgraph rhs' /\
    wf_hostgraph (dpo lhs' rule_link.inf rhs' m G)
End

(* Step 1: Initial state satisfies the loop invariant *)
Theorem tc_invariant_initial:
  !G0. wf_hostgraph G0 /\ unmarked_hostgraph G0 /\ unrooted_hostgraph G0 ==>
       tc_loop_invariant_total G0 G0 (id_track G0) /\
       extends_morphism (id_track G0) (id_track G0)
Proof
  rw[tc_loop_invariant_total_def, minimal_extension_def,
     extends_morphism_def] >> rpt strip_tac
  >- (irule id_track_is_inj_morphism >> simp[])
  >- (irule id_track_nodemap_BIJ >> metis_tac[wf_hostgraph_IMP_finite_sets])
  >- (simp[edge_path_justified_def, generated_edges_def] >> rpt strip_tac >>
      `FINITE G0.E` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
      `FRANGE (id_track G0).edgemap = G0.E` by simp[FRANGE_id_track_edgemap] >>
      gvs[])
  >- (simp[parallel_free_extension_def] >> rpt strip_tac >>
      `FINITE G0.E` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
      `FRANGE (id_track G0).edgemap = G0.E` by simp[FRANGE_id_track_edgemap] >>
      gvs[])
QED

(* Step 2: The link rule preserves the loop invariant *)

(* Helper: edges in G have reachable preimages in G0 *)
Theorem edge_in_G_has_reachable_preimages:
  !G0 m G e.
    minimal_extension G0 m G /\
    wf_hostgraph G0 /\ wf_hostgraph G /\
    e IN G.E ==>
    ?v0 w0. v0 IN G0.V /\ w0 IN G0.V /\
            m.nodemap ' v0 = G.s ' e /\
            m.nodemap ' w0 = G.t ' e /\
            reachable_in G0 v0 w0
Proof
  rpt strip_tac >> fs[minimal_extension_def] >>
  Cases_on `e IN generated_edges m G`
  >- (fs[edge_path_justified_def] >>
      first_x_assum (qspec_then `e` mp_tac) >> simp[])
  >- (fs[generated_edges_def] >>
      `e IN FRANGE m.edgemap` by gvs[] >>
      fs[FRANGE_DEF] >> rename1 `m.edgemap ' e0 = e` >>
      `e0 IN G0.E` by
        (fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def,
            morphism_dom_ran_def, SUBSET_DEF] >> metis_tac[]) >>
      `G0.s ' e0 IN G0.V /\ G0.t ' e0 IN G0.V` by
        (fs (wf_rwts @ [FRANGE_DEF, SUBSET_DEF]) >> metis_tac[]) >>
      `G.s ' (m.edgemap ' e0) = m.nodemap ' (G0.s ' e0)` by
        (fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def,
            preserve_source_def] >>
         `m.nodemap f_o_f G0.s = G.s f_o_f m.edgemap` by metis_tac[] >>
         `FDOM m.edgemap = G0.E` by fs[morphism_dom_ran_def] >>
         `e0 IN FDOM (G.s f_o_f m.edgemap)` by
           (simp[cj 1 f_o_f_DEF] >> fs wf_rwts) >>
         `e0 IN FDOM (m.nodemap f_o_f G0.s)` by metis_tac[fmap_EQ_THM] >>
         `(G.s f_o_f m.edgemap) ' e0 = G.s ' (m.edgemap ' e0)` by
           (irule (cj 2 f_o_f_DEF |> SPEC_ALL) >> simp[]) >>
         `(m.nodemap f_o_f G0.s) ' e0 = m.nodemap ' (G0.s ' e0)` by
           (irule (cj 2 f_o_f_DEF |> SPEC_ALL) >> simp[] >> fs wf_rwts) >>
         metis_tac[fmap_EQ_THM]) >>
      `G.t ' (m.edgemap ' e0) = m.nodemap ' (G0.t ' e0)` by
        (fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def,
            preserve_target_def] >>
         `m.nodemap f_o_f G0.t = G.t f_o_f m.edgemap` by metis_tac[] >>
         `FDOM m.edgemap = G0.E` by fs[morphism_dom_ran_def] >>
         `e0 IN FDOM (G.t f_o_f m.edgemap)` by
           (simp[cj 1 f_o_f_DEF] >> fs wf_rwts) >>
         `e0 IN FDOM (m.nodemap f_o_f G0.t)` by metis_tac[fmap_EQ_THM] >>
         `(G.t f_o_f m.edgemap) ' e0 = G.t ' (m.edgemap ' e0)` by
           (irule (cj 2 f_o_f_DEF |> SPEC_ALL) >> simp[]) >>
         `(m.nodemap f_o_f G0.t) ' e0 = m.nodemap ' (G0.t ' e0)` by
           (irule (cj 2 f_o_f_DEF |> SPEC_ALL) >> simp[] >> fs wf_rwts) >>
         metis_tac[fmap_EQ_THM]) >>
      qexistsl [`G0.s ' e0`, `G0.t ' e0`] >> simp[] >> gvs[] >>
      irule has_edge_imp_reachable_in >>
      simp[hostgraphTheory.wf_hostgraph_IMP_wf_graph] >>
      simp[pathTheory.has_edge_def] >> qexists_tac `e0` >> fs wf_rwts)
QED

(* Helper: for link rule, dpo.V = IMAGE tag_nodeid_left G.V *)
Theorem link_dpo_V:
  !lhs' rhs' m G.
    lhs'.V = rule_link.lhs.V /\ rhs'.V = rule_link.rhs.V ==>
    (dpo lhs' rule_link.inf rhs' m G).V = IMAGE tag_nodeid_left G.V
Proof
  rpt strip_tac >>
  simp[dpoTheory.dpo_def, dpoTheory.gluing_def,
       dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >>
  `rule_link.rhs.V DIFF rule_link.inf = {}` by EVAL_TAC >>
  `deletion_remaining_nodes lhs' m rule_link.inf G = G.V` by
    (simp[dpoTheory.deletion_remaining_nodes_def,
          dpoTheory.deletion_deleted_nodes_def] >>
     `rule_link.lhs.V DIFF rule_link.inf = {}` by EVAL_TAC >> gvs[]) >>
  simp[dpoTheory.deletion_def]
QED

(* Helper: track.nodemap for link rule is BIJ *)
Theorem link_track_nodemap_BIJ:
  !lhs' m G.
    lhs'.V = rule_link.lhs.V /\ FINITE G.V ==>
    BIJ ($' (track lhs' rule_link.inf m G).nodemap) G.V (IMAGE tag_nodeid_left G.V)
Proof
  rpt strip_tac >>
  simp[trackTheory.track_def] >>
  `lhs'.V DIFF rule_link.inf = {}` by (gvs[] >> EVAL_TAC) >>
  `deletion_deleted_nodes lhs' m rule_link.inf = {}` by
    simp[dpoTheory.deletion_deleted_nodes_def] >>
  `deletion_remaining_nodes lhs' m rule_link.inf G = G.V` by
    simp[dpoTheory.deletion_remaining_nodes_def] >>
  gvs[] >> simp[BIJ_DEF, INJ_DEF, SURJ_DEF] >> rpt conj_tac
  >- (rpt strip_tac >> qexists `x` >> simp[FUN_FMAP_DEF])
  >- (rpt strip_tac >> fs[FUN_FMAP_DEF] >>
      fs[taggingTheory.INJ_tag_nodeid, INJ_DEF] >>
      sg `tag_nodeid_left x = tag_nodeid_left y`
      >- metis_tac[trackTheory.FUN_FMAP_APPLY]
      >- (`INJ tag_nodeid_left UNIV UNIV` by simp[taggingTheory.INJ_tag_nodeid] >>
          fs[INJ_DEF]))
  >- (rpt strip_tac >> qexists `x` >> simp[FUN_FMAP_DEF])
  >- (rpt strip_tac >> qexists `x'` >> simp[FUN_FMAP_DEF])
QED

(* Helper: match morphism preserves source/target structure *)
Theorem match_preserves_st_apply:
  !m L Kv G e n_s n_t.
    is_match L Kv m G /\ wf_hostgraph G /\ e IN L.E /\
    L.s ' e = n_s /\ L.t ' e = n_t ==>
    G.s ' (m.edgemap ' e) = m.nodemap ' n_s /\
    G.t ' (m.edgemap ' e) = m.nodemap ' n_t
Proof
  rpt strip_tac >| [
    `m.nodemap f_o_f L.s = G.s f_o_f m.edgemap` by fs match_source_rwts,
    `m.nodemap f_o_f L.t = G.t f_o_f m.edgemap` by fs match_target_rwts
  ] >>
  `FDOM m.edgemap = L.E` by fs match_morphism_rwts >>
  `FRANGE m.edgemap SUBSET G.E` by fs match_morphism_rwts >>
  `m.edgemap ' e IN G.E` by (fs[FRANGE_DEF, SUBSET_DEF] >> metis_tac[]) >>
  (TRY (`e IN FDOM (G.s f_o_f m.edgemap)` by (simp[cj 1 f_o_f_DEF] >> fs wf_rwts) >>
        `(G.s f_o_f m.edgemap) ' e = G.s ' (m.edgemap ' e)` by
          (irule (cj 2 f_o_f_DEF |> SPEC_ALL) >> simp[]) >>
        `FDOM (m.nodemap f_o_f L.s) = FDOM (G.s f_o_f m.edgemap)` by
          metis_tac[fmap_EQ_THM] >>
        `e IN FDOM (m.nodemap f_o_f L.s)` by metis_tac[] >>
        `(m.nodemap f_o_f L.s) ' e = m.nodemap ' (L.s ' e)` by
          (irule (cj 2 f_o_f_DEF |> SPEC_ALL) >> simp[]) >> metis_tac[]) >>
   TRY (`e IN FDOM (G.t f_o_f m.edgemap)` by (simp[cj 1 f_o_f_DEF] >> fs wf_rwts) >>
        `(G.t f_o_f m.edgemap) ' e = G.t ' (m.edgemap ' e)` by
          (irule (cj 2 f_o_f_DEF |> SPEC_ALL) >> simp[]) >>
        `FDOM (m.nodemap f_o_f L.t) = FDOM (G.t f_o_f m.edgemap)` by
          metis_tac[fmap_EQ_THM] >>
        `e IN FDOM (m.nodemap f_o_f L.t)` by metis_tac[] >>
        `(m.nodemap f_o_f L.t) ' e = m.nodemap ' (L.t ' e)` by
          (irule (cj 2 f_o_f_DEF |> SPEC_ALL) >> simp[]) >> metis_tac[]))
QED

(* Helper: for link rule, every RHS edge has reachable preimages in G0 *)
Theorem link_rhs_edge_has_reachable_preimages:
  !G0 G m m'' lhs' rhs' assign x.
    wf_hostgraph G0 /\ wf_hostgraph G /\
    minimal_extension G0 m G /\
    is_match lhs' rule_link.inf m'' G /\
    instantiate_rulegraph rule_link.lhs assign m'' G = SOME lhs' /\
    instantiate_rulegraph rule_link.rhs assign m'' G = SOME rhs' /\
    x IN rhs'.E ==>
    ?v0 w0. v0 IN G0.V /\ w0 IN G0.V /\
            m.nodemap ' v0 = m''.nodemap ' (rhs'.s ' x) /\
            m.nodemap ' w0 = m''.nodemap ' (rhs'.t ' x) /\
            reachable_in G0 v0 w0
Proof
  rpt strip_tac >>
  `rhs'.E = rule_link.rhs.E /\ rhs'.s = rule_link.rhs.s /\
   rhs'.t = rule_link.rhs.t` by
    metis_tac[semTheory.instantiate_rulegraph_preserves_structure] >>
  `lhs'.E = rule_link.lhs.E /\ lhs'.s = rule_link.lhs.s /\
   lhs'.t = rule_link.lhs.t /\ lhs'.V = rule_link.lhs.V` by
    metis_tac[semTheory.instantiate_rulegraph_preserves_structure] >>
  `rule_link.rhs.E = {edgeid "e2"; edgeid "e1"; edgeid "e0"}` by EVAL_TAC >>
  `x = edgeid "e0" \/ x = edgeid "e1" \/ x = edgeid "e2"` by gvs[] >>
  STRIP_ASSUME_TAC rule_link_structure >>
  `FDOM m''.edgemap = lhs'.E` by fs match_morphism_rwts >>
  `FRANGE m''.edgemap SUBSET G.E` by fs match_morphism_rwts >>
  `edgeid "e0" IN lhs'.E` by (gvs[] >> EVAL_TAC) >>
  `edgeid "e1" IN lhs'.E` by (gvs[] >> EVAL_TAC) >>
  `m''.edgemap ' (edgeid "e0") IN G.E` by
    (gvs[SUBSET_DEF, FRANGE_DEF] >> metis_tac[]) >>
  `m''.edgemap ' (edgeid "e1") IN G.E` by
    (gvs[SUBSET_DEF, FRANGE_DEF] >> metis_tac[]) >>
  `?v0 w0. v0 IN G0.V /\ w0 IN G0.V /\
           m.nodemap ' v0 = G.s ' (m''.edgemap ' (edgeid "e0")) /\
           m.nodemap ' w0 = G.t ' (m''.edgemap ' (edgeid "e0")) /\
           reachable_in G0 v0 w0` by
    (irule edge_in_G_has_reachable_preimages >> simp[]) >>
  `?v1 w1. v1 IN G0.V /\ w1 IN G0.V /\
           m.nodemap ' v1 = G.s ' (m''.edgemap ' (edgeid "e1")) /\
           m.nodemap ' w1 = G.t ' (m''.edgemap ' (edgeid "e1")) /\
           reachable_in G0 v1 w1` by
    (irule edge_in_G_has_reachable_preimages >> simp[]) >>
  `G.s ' (m''.edgemap ' (edgeid "e0")) = m''.nodemap ' (nodeid "n0") /\
   G.t ' (m''.edgemap ' (edgeid "e0")) = m''.nodemap ' (nodeid "n1")` by
    (MATCH_MP_TAC match_preserves_st_apply >>
     qexistsl [`lhs'`, `rule_link.inf`] >> fs[]) >>
  `G.s ' (m''.edgemap ' (edgeid "e1")) = m''.nodemap ' (nodeid "n1") /\
   G.t ' (m''.edgemap ' (edgeid "e1")) = m''.nodemap ' (nodeid "n2")` by
    (MATCH_MP_TAC match_preserves_st_apply >>
     qexistsl [`lhs'`, `rule_link.inf`] >> fs[]) >>
  gvs[]
  >- (qexistsl [`v0`, `w0`] >> gvs[])
  >- (qexistsl [`v1`, `w1`] >> gvs[])
  >- (`BIJ ($' m.nodemap) G0.V G.V` by fs[minimal_extension_def] >>
      `w0 = v1` by (fs[BIJ_DEF, INJ_DEF] >> metis_tac[]) >>
      `reachable_in G0 v0 w1` by
        (irule reachable_in_trans >> qexists_tac `w0` >> gvs[]) >>
      qexistsl [`v0`, `w1`] >> gvs[])
QED

val is_rulelabel_tac = rpt (simp_tac (srw_ss())
  [rulegraphTheory.is_rulelabel_spine_def, rulegraphTheory.is_rule_atom_def])

val totally_labelled_tac =
  simp[rulegraphTheory.totally_labelled_rulegraph_def] >> EVAL_TAC >>
  simp[FEVERY_DEF, FRANGE_FUPDATE, FDOM_FUPDATE, FAPPLY_FUPDATE_THM] >>
  rpt strip_tac >> gvs[] >> is_rulelabel_tac

(* Helper: link rule doesn't delete any nodes (inf = lhs.V) *)
Theorem link_no_node_deletion:
  !lhs' m'' G.
    lhs'.V = rule_link.lhs.V ==>
    deletion_remaining_nodes lhs' m'' rule_link.inf G = G.V
Proof
  rpt strip_tac >>
  simp[dpoTheory.deletion_remaining_nodes_def,
       dpoTheory.deletion_deleted_nodes_def] >>
  `rule_link.lhs.V DIFF rule_link.inf = {}` by EVAL_TAC >> gvs[]
QED

(* Helper: track nodemap domain equals G.V for link rule *)
Theorem link_track_nodemap_FDOM:
  !lhs' m'' G.
    lhs'.V = rule_link.lhs.V /\ FINITE G.V ==>
    FDOM (track lhs' rule_link.inf m'' G).nodemap = G.V
Proof
  rpt strip_tac >>
  `FINITE (deletion_remaining_nodes lhs' m'' rule_link.inf G)` by
    (simp[dpoTheory.deletion_remaining_nodes_def] >> fs[]) >>
  `deletion_remaining_nodes lhs' m'' rule_link.inf G = G.V` by
    (irule link_no_node_deletion >> simp[]) >>
  simp[trackTheory.FDOM_track_nodemap]
QED

(* Helper: wf_hostgraph edge properties *)
Theorem wf_hostgraph_edge_props:
  !G e. wf_hostgraph G /\ e IN G.E ==>
        G.s ' e IN G.V /\ G.t ' e IN G.V /\
        e IN FDOM G.s /\ e IN FDOM G.t
Proof
  rpt strip_tac >> fs wf_rwts >-
  (`G.s ' e IN FRANGE G.s` by (simp[FRANGE_DEF] >> qexists_tac `e` >> fs[]) >>
   fs[SUBSET_DEF]) >-
  (`G.t ' e IN FRANGE G.t` by (simp[FRANGE_DEF] >> qexists_tac `e` >> fs[]) >>
   fs[SUBSET_DEF])
QED


(* Step 6: When loop terminates, graph is transitive *)

(* Helper: link can be applied to H - semantic-level predicate *)
Definition link_can_apply_def:
  link_can_apply H <=>
    ?m h. is_prematch rule_link.lhs rule_link.inf m H /\
          apply_rule rule_link m H = SOME h
End

(* Helper: step with term_rscall succeeds iff link_can_apply *)
Theorem step_rscall_link_iff_link_can_apply:
  !G. wf_hostgraph G ==>
      ((?G' m'. step program
                  (running (term_rscall {ruleid "link"}), [(G, id_track G)])
                  (final, [(G', m')])) <=>
       link_can_apply G)
Proof
  rw[EQ_IMP_THM]
  >- (pop_assum mp_tac >> simp[Once semTheory.step_cases] >>
      simp[stackTheory.pop_stack_def, stackTheory.push_stack_def,
           program_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      simp[finite_mapTheory.FUPDATE_LIST_THM,
           finite_mapTheory.FLOOKUP_UPDATE] >>
      strip_tac >> simp[link_can_apply_def] >>
      qexistsl_tac [`m`, `G'`] >> simp[semTheory.apply_rule_def])
  >- (fs[link_can_apply_def, semTheory.apply_rule_def] >>
      simp[Once semTheory.step_cases] >>
      simp[stackTheory.pop_stack_def, stackTheory.push_stack_def,
           program_def, finite_mapTheory.FLOOKUP_UPDATE,
           finite_mapTheory.FUPDATE_LIST_THM] >>
      qexistsl_tac [`h`, `m`, `instance`, `assign`] >> simp[])
QED

(* Backward direction: 2-path without direct edge implies link_can_apply *)
Theorem two_path_implies_link_can_apply:
  !G. wf_hostgraph G /\ unmarked_hostgraph G /\ unrooted_hostgraph G /\
      (?v u w. v IN G.V /\ u IN G.V /\ w IN G.V /\
               v <> w /\ has_edge G v u /\ has_edge G u w /\ ~has_edge G v w) ==>
      link_can_apply G
Proof
  rpt strip_tac >> fs[pathTheory.has_edge_def] >>
  `v <> u` by (SPOSE_NOT_THEN ASSUME_TAC >> gvs[] >>
               first_x_assum (qspec_then `e'` mp_tac) >> simp[]) >>
  `u <> w` by (SPOSE_NOT_THEN ASSUME_TAC >> gvs[] >>
               first_x_assum (qspec_then `e` mp_tac) >> simp[]) >>
  `e <> e'` by (SPOSE_NOT_THEN ASSUME_TAC >> gvs[]) >>
  simp[link_can_apply_def] >>
  qexists_tac `<| nodemap := FEMPTY |+ (nodeid "n0", v)
                                     |+ (nodeid "n1", u)
                                     |+ (nodeid "n2", w);
                  edgemap := FEMPTY |+ (edgeid "e0", e)
                                     |+ (edgeid "e1", e') |>` >>
  qabbrev_tac `m = <| nodemap := FEMPTY |+ (nodeid "n0", v)
                                         |+ (nodeid "n1", u)
                                         |+ (nodeid "n2", w);
                      edgemap := FEMPTY |+ (edgeid "e0", e)
                                         |+ (edgeid "e1", e') |>` >>
  (* is_prematch *)
  sg `is_prematch rule_link.lhs rule_link.inf m G`
  >- (simp[semTheory.is_prematch_def,
           morphismTheory.is_inj_premorphism_def,
           morphismTheory.is_premorphism_def,
           morphismTheory.morphism_dom_ran_def, Abbr`m`, rule_link_def,
           morphismTheory.preserve_source_def,
           morphismTheory.preserve_target_def,
           morphismTheory.preserve_defined_rootedness_def,
           dpoTheory.satisfy_dangling_condition_def,
           finite_mapTheory.FUPDATE_LIST] >> rpt conj_tac
      >- gvs[finite_mapTheory.FRANGE_FUPDATE_DOMSUB,
             finite_mapTheory.DOMSUB_NOT_IN_DOM]
      >- gvs[finite_mapTheory.FRANGE_FUPDATE_DOMSUB,
             finite_mapTheory.DOMSUB_NOT_IN_DOM]
      >- (`e IN FDOM G.s /\ e' IN FDOM G.s` by
            (fs wf_rwts >> metis_tac[SUBSET_DEF]) >>
          simp[finite_mapTheory.fmap_EXT, finite_mapTheory.f_o_f_DEF,
               EXTENSION, finite_mapTheory.FAPPLY_FUPDATE_THM] >>
          rw[] >> EVAL_TAC >> gvs[] >>
          simp[finite_mapTheory.f_o_f_DEF,
               finite_mapTheory.FAPPLY_FUPDATE_THM] >> EVAL_TAC)
      >- (`e IN FDOM G.t /\ e' IN FDOM G.t` by
            (fs wf_rwts >> metis_tac[SUBSET_DEF]) >>
          simp[finite_mapTheory.fmap_EXT, finite_mapTheory.f_o_f_DEF,
               EXTENSION, finite_mapTheory.FAPPLY_FUPDATE_THM] >>
          rw[] >> EVAL_TAC >> gvs[] >>
          simp[finite_mapTheory.f_o_f_DEF,
               finite_mapTheory.FAPPLY_FUPDATE_THM] >> EVAL_TAC)
      >- (fs[hostgraphTheory.unrooted_hostgraph_def] >>
          simp[finite_mapTheory.SUBMAP_DEF,
               finite_mapTheory.FAPPLY_FUPDATE_THM] >> rw[] >>
          simp[finite_mapTheory.f_o_f_DEF,
               finite_mapTheory.FAPPLY_FUPDATE_THM] >> EVAL_TAC >> gvs[])
      >- (simp[INJ_DEF, finite_mapTheory.FAPPLY_FUPDATE_THM] >>
          rw[] >> gvs[] >> EVAL_TAC)
      >- (simp[INJ_DEF, finite_mapTheory.FAPPLY_FUPDATE_THM] >>
          rw[] >> gvs[] >> EVAL_TAC)) >>
  (* apply_rule setup *)
  simp[] >> simp[semTheory.apply_rule_def,
                 semTheory.apply_ruleinstance_def] >> simp[PULL_EXISTS] >>
  `v IN FDOM G.l /\ u IN FDOM G.l /\ w IN FDOM G.l` by
    fs[hostgraphTheory.wf_hostgraph_def] >>
  `e IN FDOM G.m /\ e' IN FDOM G.m` by
    fs[hostgraphTheory.wf_hostgraph_def] >>
  fs[hostgraphTheory.wf_hostgraph_def,
     hostgraphTheory.hostgraph_labels_spine_def,
     hostgraphTheory.unmarked_hostgraph_def,
     hostgraphTheory.nodes_unmarked_def,
     hostgraphTheory.edges_unmarked_def, finite_mapTheory.FEVERY_DEF] >>
  qabbrev_tac `lv = FST (G.l ' v)` >>
  qabbrev_tac `lu = FST (G.l ' u)` >>
  qabbrev_tac `lw = FST (G.l ' w)` >>
  qabbrev_tac `la = FST (G.m ' e)` >>
  qabbrev_tac `lb = FST (G.m ' e')` >>
  `is_hostlabel_spine lv /\ is_hostlabel_spine lu /\
   is_hostlabel_spine lw /\ is_hostlabel_spine la /\
   is_hostlabel_spine lb` by
    (simp[Abbr `lv`, Abbr `lu`, Abbr `lw`, Abbr `la`, Abbr `lb`] >>
     gvs[]) >>
  `G.l ' v = (lv, NONE)` by
    (simp[Abbr `lv`] >> `SND (G.l ' v) = NONE` by gvs[] >>
     Cases_on `G.l ' v` >> gvs[]) >>
  `G.l ' u = (lu, NONE)` by
    (simp[Abbr `lu`] >> `SND (G.l ' u) = NONE` by gvs[] >>
     Cases_on `G.l ' u` >> gvs[]) >>
  `G.l ' w = (lw, NONE)` by
    (simp[Abbr `lw`] >> `SND (G.l ' w) = NONE` by gvs[] >>
     Cases_on `G.l ' w` >> gvs[]) >>
  `G.m ' e = (la, NONE)` by
    (simp[Abbr `la`] >> `SND (G.m ' e) = NONE` by gvs[] >>
     Cases_on `G.m ' e` >> gvs[]) >>
  `G.m ' e' = (lb, NONE)` by
    (simp[Abbr `lb`] >> `SND (G.m ' e') = NONE` by gvs[] >>
     Cases_on `G.m ' e'` >> gvs[]) >>
  `FLOOKUP G.l v = SOME (lv, NONE) /\ FLOOKUP G.l u = SOME (lu, NONE) /\
   FLOOKUP G.l w = SOME (lw, NONE) /\ FLOOKUP G.m e = SOME (la, NONE) /\
   FLOOKUP G.m e' = SOME (lb, NONE)` by simp[FLOOKUP_DEF] >>
  `FLOOKUP m.nodemap (nodeid "n0") = SOME v /\
   FLOOKUP m.nodemap (nodeid "n1") = SOME u /\
   FLOOKUP m.nodemap (nodeid "n2") = SOME w /\
   FLOOKUP m.edgemap (edgeid "e0") = SOME e /\
   FLOOKUP m.edgemap (edgeid "e1") = SOME e'` by
    simp[Abbr `m`, FLOOKUP_UPDATE] >>
  (* mk_assignment_node/edge *)
  `mk_assignment_node rule_link m G (nodeid "n0") =
     SOME (FEMPTY |+ (varname "x", lv)) /\
   mk_assignment_node rule_link m G (nodeid "n1") =
     SOME (FEMPTY |+ (varname "y", lu)) /\
   mk_assignment_node rule_link m G (nodeid "n2") =
     SOME (FEMPTY |+ (varname "z", lw))` by
    (rpt conj_tac >>
     simp[semTheory.mk_assignment_node_def,
          semTheory.unify_nodeattr_def, semTheory.nodemark_matches_def,
          rule_link_def, FLOOKUP_UPDATE, Abbr`m`] >>
     EVAL_TAC >> gvs[] >>
     simp[semTheory.unify_nodeattr_def, semTheory.nodemark_matches_def] >>
     irule ruleAppPropsTheory.unify_label_simple_singleton >>
     simp[FLOOKUP_UPDATE] >> EVAL_TAC) >>
  `mk_assignment_edge rule_link m G (edgeid "e0") =
     SOME (FEMPTY |+ (varname "a", la)) /\
   mk_assignment_edge rule_link m G (edgeid "e1") =
     SOME (FEMPTY |+ (varname "b", lb))` by
    (rpt conj_tac >>
     simp[semTheory.mk_assignment_edge_def,
          semTheory.unify_edgeattr_def, semTheory.edgemark_matches_def,
          rule_link_def, FLOOKUP_UPDATE, Abbr`m`] >>
     EVAL_TAC >> gvs[] >>
     simp[semTheory.unify_edgeattr_def, semTheory.edgemark_matches_def] >>
     irule ruleAppPropsTheory.unify_label_simple_singleton >>
     simp[FLOOKUP_UPDATE] >> EVAL_TAC) >>
  `rule_link.lhs.V = {nodeid "n0"; nodeid "n1"; nodeid "n2"} /\
   rule_link.lhs.E = {edgeid "e0"; edgeid "e1"} /\
   FINITE rule_link.lhs.V /\ FINITE rule_link.lhs.E` by EVAL_TAC >>
  (* mk_assignment_nodes *)
  sg `?nassign. mk_assignment_nodes rule_link m G = SOME nassign /\
      FDOM nassign = {varname "x"; varname "y"; varname "z"}`
  >- (simp[semTheory.mk_assignment_nodes_def] >>
      qspec_then `SET_TO_LIST {nodeid "n0"; nodeid "n1"; nodeid "n2"}`
        mp_tac ruleAppPropsTheory.foldr_singleton_merge >>
      disch_then (qspec_then `mk_assignment_node rule_link m G` mp_tac) >>
      impl_tac
      >- (rpt conj_tac
          >- simp[ALL_DISTINCT_SET_TO_LIST]
          >- (rw[] >> rpt strip_tac >> gvs[MEM_SET_TO_LIST]
              >- (qexists_tac `varname "x"` >> qexists_tac `lv` >> simp[])
              >- (qexists_tac `varname "y"` >> qexists_tac `lu` >> simp[])
              >- (qexists_tac `varname "z"` >> qexists_tac `lw` >> simp[]))
          >- (rpt strip_tac >> gvs[MEM_SET_TO_LIST] >>
              gvs[FEMPTY_FUPDATE_EQ] >> EVAL_TAC))
      >- (strip_tac >> qexists_tac `result` >> simp[] >>
          simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >> gvs[]
          >- fs[FEMPTY_FUPDATE_EQ]
          >- gvs[FEMPTY_FUPDATE_EQ]
          >- fs[FEMPTY_FUPDATE_EQ]
          >- (qexists_tac `nodeid "n0"` >> qexists_tac `lv` >> simp[])
          >- (qexists_tac `nodeid "n1"` >> qexists_tac `lu` >> simp[])
          >- (qexists_tac `nodeid "n2"` >> qexists_tac `lw` >> simp[]))) >>
  (* mk_assignment_edges *)
  sg `?eassign. mk_assignment_edges rule_link m G = SOME eassign /\
      FDOM eassign = {varname "a"; varname "b"}`
  >- (simp[semTheory.mk_assignment_edges_def] >>
      qspec_then `SET_TO_LIST {edgeid "e0"; edgeid "e1"}`
        mp_tac ruleAppPropsTheory.foldr_singleton_merge >>
      disch_then (qspec_then `mk_assignment_edge rule_link m G` mp_tac) >>
      impl_tac
      >- (rpt conj_tac
          >- simp[ALL_DISTINCT_SET_TO_LIST]
          >- (rw[] >> rpt strip_tac >> gvs[MEM_SET_TO_LIST]
              >- (qexists_tac `varname "a"` >> qexists_tac `la` >> simp[])
              >- (qexists_tac `varname "b"` >> qexists_tac `lb` >> simp[]))
          >- (rpt strip_tac >> gvs[MEM_SET_TO_LIST] >>
              gvs[FEMPTY_FUPDATE_EQ] >> EVAL_TAC))
      >- (strip_tac >> qexists_tac `result` >> simp[] >>
          simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >> gvs[]
          >- fs[FEMPTY_FUPDATE_EQ]
          >- fs[FEMPTY_FUPDATE_EQ]
          >- (qexists_tac `edgeid "e0"` >> qexists_tac `la` >> simp[])
          >- (qexists_tac `edgeid "e1"` >> qexists_tac `lb` >> simp[]))) >>
  (* mk_assignment *)
  `agree_on_common_keys nassign eassign` by
    (irule ruleAppPropsTheory.disjoint_agree >> simp[]) >>
  `mk_assignment rule_link m G = SOME (nassign ⊌ eassign)` by
    simp[semTheory.mk_assignment_def, semTheory.merge_assignment_def] >>
  qabbrev_tac `assign = nassign ⊌ eassign` >>
  simp[PULL_EXISTS] >>
  simp[semTheory.instantiate_rule_def, PULL_EXISTS] >>
  (* NAC: eval_rule_condition *)
  sg `eval_rule_condition rule_link assign m G = SOME T`
  >- (simp[semTheory.eval_rule_condition_def, rule_link_def,
           semTheory.eval_condition_fun_def, FLOOKUP_UPDATE, Abbr`m`] >>
      simp[EVERY_MEM, MEM_SET_TO_LIST] >>
      `FINITE G.E` by fs[graphTheory.wf_graph_def] >>
      `FDOM G.s = G.E /\ FDOM G.t = G.E` by fs[graphTheory.wf_graph_def] >>
      rpt strip_tac >> gvs[MEM_SET_TO_LIST] >>
      fs[FLOOKUP_DEF] >>
      first_x_assum (qspec_then `e''` mp_tac) >> simp[]) >>
  simp[] >>
  (* FLOOKUP nassign/eassign via foldr_merge_SUBMAP *)
  qpat_x_assum `mk_assignment_nodes rule_link m G = SOME nassign` mp_tac >>
  simp[semTheory.mk_assignment_nodes_def] >> DISCH_TAC >>
  sg `FLOOKUP nassign (varname "x") = SOME lv /\
      FLOOKUP nassign (varname "y") = SOME lu /\
      FLOOKUP nassign (varname "z") = SOME lw`
  >- (qspecl_then [`mk_assignment_node rule_link m G`,
                    `SET_TO_LIST rule_link.lhs.V`, `nassign`,
                    `nodeid "n0"`] mp_tac semTheory.foldr_merge_SUBMAP >>
      impl_tac >- simp[MEM_SET_TO_LIST] >> strip_tac >>
      `a_x = FEMPTY |+ (varname "x", lv)` by gvs[] >>
      `FLOOKUP a_x (varname "x") = SOME lv` by simp[FLOOKUP_UPDATE] >>
      sg `FLOOKUP nassign (varname "x") = SOME lv`
      >- metis_tac[SUBMAP_FLOOKUP_EQN] >> simp[] >>
      qspecl_then [`mk_assignment_node rule_link m G`,
                    `SET_TO_LIST rule_link.lhs.V`, `nassign`,
                    `nodeid "n1"`] mp_tac semTheory.foldr_merge_SUBMAP >>
      impl_tac >- simp[MEM_SET_TO_LIST] >> strip_tac >>
      `a_x' = FEMPTY |+ (varname "y", lu)` by gvs[] >>
      `FLOOKUP a_x' (varname "y") = SOME lu` by simp[FLOOKUP_UPDATE] >>
      sg `FLOOKUP nassign (varname "y") = SOME lu`
      >- metis_tac[SUBMAP_FLOOKUP_EQN] >> simp[] >>
      qspecl_then [`mk_assignment_node rule_link m G`,
                    `SET_TO_LIST rule_link.lhs.V`, `nassign`,
                    `nodeid "n2"`] mp_tac semTheory.foldr_merge_SUBMAP >>
      impl_tac >- simp[MEM_SET_TO_LIST] >> strip_tac >>
      `a_x'' = FEMPTY |+ (varname "z", lw)` by gvs[] >>
      `FLOOKUP a_x'' (varname "z") = SOME lw` by simp[FLOOKUP_UPDATE] >>
      metis_tac[SUBMAP_FLOOKUP_EQN]) >>
  qpat_x_assum `mk_assignment_edges rule_link m G = SOME eassign` mp_tac >>
  simp[semTheory.mk_assignment_edges_def] >> DISCH_TAC >>
  sg `FLOOKUP eassign (varname "a") = SOME la /\
      FLOOKUP eassign (varname "b") = SOME lb`
  >- (qspecl_then [`mk_assignment_edge rule_link m G`,
                    `SET_TO_LIST rule_link.lhs.E`, `eassign`,
                    `edgeid "e0"`] mp_tac semTheory.foldr_merge_SUBMAP >>
      impl_tac >- simp[MEM_SET_TO_LIST] >> strip_tac >>
      `a_x = FEMPTY |+ (varname "a", la)` by gvs[] >>
      `FLOOKUP a_x (varname "a") = SOME la` by simp[FLOOKUP_UPDATE] >>
      sg `FLOOKUP eassign (varname "a") = SOME la`
      >- metis_tac[SUBMAP_FLOOKUP_EQN] >> simp[] >>
      qspecl_then [`mk_assignment_edge rule_link m G`,
                    `SET_TO_LIST rule_link.lhs.E`, `eassign`,
                    `edgeid "e1"`] mp_tac semTheory.foldr_merge_SUBMAP >>
      impl_tac >- simp[MEM_SET_TO_LIST] >> strip_tac >>
      `a_x' = FEMPTY |+ (varname "b", lb)` by gvs[] >>
      `FLOOKUP a_x' (varname "b") = SOME lb` by simp[FLOOKUP_UPDATE] >>
      metis_tac[SUBMAP_FLOOKUP_EQN]) >>
  (* FLOOKUP assign *)
  `FLOOKUP assign (varname "x") = SOME lv /\
   FLOOKUP assign (varname "y") = SOME lu /\
   FLOOKUP assign (varname "z") = SOME lw /\
   FLOOKUP assign (varname "a") = SOME la /\
   FLOOKUP assign (varname "b") = SOME lb` by
    (simp[Abbr`assign`, FLOOKUP_FUNION] >> rpt conj_tac >> simp[] >>
     `varname "a" NOTIN FDOM nassign /\
      varname "b" NOTIN FDOM nassign` by simp[] >> simp[FLOOKUP_DEF]) >>
  (* f_o_f FLOOKUP facts *)
  `FLOOKUP (G.l f_o_f m.nodemap) (nodeid "n0") = SOME (lv, NONE) /\
   FLOOKUP (G.l f_o_f m.nodemap) (nodeid "n1") = SOME (lu, NONE) /\
   FLOOKUP (G.l f_o_f m.nodemap) (nodeid "n2") = SOME (lw, NONE)` by
    (simp[FLOOKUP_DEF, f_o_f_DEF, FLOOKUP_UPDATE, Abbr`m`] >>
     simp[FAPPLY_FUPDATE_THM]) >>
  `FLOOKUP (G.m f_o_f m.edgemap) (edgeid "e0") = SOME (la, NONE) /\
   FLOOKUP (G.m f_o_f m.edgemap) (edgeid "e1") = SOME (lb, NONE)` by
    (simp[FLOOKUP_DEF, f_o_f_DEF, FLOOKUP_UPDATE, Abbr`m`] >>
     simp[FAPPLY_FUPDATE_THM]) >>
  (* Rule label FLOOKUPs *)
  `FLOOKUP rule_link.lhs.l (nodeid "n0") =
     SOME (label_cons (label_variable (varname "x")) label_nil, NONE) /\
   FLOOKUP rule_link.lhs.l (nodeid "n1") =
     SOME (label_cons (label_variable (varname "y")) label_nil, NONE) /\
   FLOOKUP rule_link.lhs.l (nodeid "n2") =
     SOME (label_cons (label_variable (varname "z")) label_nil, NONE)` by
    EVAL_TAC >>
  `FLOOKUP rule_link.lhs.m (edgeid "e0") =
     SOME (label_cons (label_variable (varname "a")) label_nil, NONE) /\
   FLOOKUP rule_link.lhs.m (edgeid "e1") =
     SOME (label_cons (label_variable (varname "b")) label_nil, NONE)` by
    EVAL_TAC >>
  (* instantiate_nodeattr/edgeattr for LHS *)
  sg `instantiate_nodeattr rule_link.lhs assign m G (nodeid "n0") =
      SOME (lv, NONE)`
  >- (irule ruleAppPropsTheory.instantiate_nodeattr_simple_matched >>
      simp[] >> qexists_tac `lv` >> qexists_tac `varname "x"` >> simp[]) >>
  sg `instantiate_nodeattr rule_link.lhs assign m G (nodeid "n1") =
      SOME (lu, NONE)`
  >- (irule ruleAppPropsTheory.instantiate_nodeattr_simple_matched >>
      simp[] >> qexists_tac `lu` >> qexists_tac `varname "y"` >> simp[]) >>
  sg `instantiate_nodeattr rule_link.lhs assign m G (nodeid "n2") =
      SOME (lw, NONE)`
  >- (irule ruleAppPropsTheory.instantiate_nodeattr_simple_matched >>
      simp[] >> qexists_tac `lw` >> qexists_tac `varname "z"` >> simp[]) >>
  sg `instantiate_edgeattr rule_link.lhs assign m G (edgeid "e0") =
      SOME (la, NONE)`
  >- (irule ruleAppPropsTheory.instantiate_edgeattr_simple_matched >>
      simp[] >> qexists_tac `la` >> qexists_tac `varname "a"` >> simp[]) >>
  sg `instantiate_edgeattr rule_link.lhs assign m G (edgeid "e1") =
      SOME (lb, NONE)`
  >- (irule ruleAppPropsTheory.instantiate_edgeattr_simple_matched >>
      simp[] >> qexists_tac `lb` >> qexists_tac `varname "b"` >> simp[]) >>
  (* instantiate_rulegraph for LHS *)
  `FDOM rule_link.lhs.l = {nodeid "n0"; nodeid "n1"; nodeid "n2"} /\
   FDOM rule_link.lhs.m = {edgeid "e0"; edgeid "e1"} /\
   FINITE (FDOM rule_link.lhs.l) /\
   FINITE (FDOM rule_link.lhs.m)` by EVAL_TAC >>
  sg `?lhs'. instantiate_rulegraph rule_link.lhs assign m G = SOME lhs'`
  >- (simp[semTheory.instantiate_rulegraph_def, PULL_EXISTS] >>
      sg `?l. fmap_buildM (instantiate_nodeattr rule_link.lhs assign m G)
                {nodeid "n0"; nodeid "n1"; nodeid "n2"} = SOME l`
      >- (irule semTheory.fmap_buildM_succeeds >> simp[] >>
          rpt strip_tac >> gvs[] >> metis_tac[]) >>
      simp[PULL_EXISTS] >>
      irule semTheory.fmap_buildM_succeeds >> simp[] >>
      rpt strip_tac >> gvs[] >> metis_tac[]) >>
  (* RHS labels *)
  `FLOOKUP rule_link.rhs.l (nodeid "n0") =
     SOME (label_cons (label_variable (varname "x")) label_nil, NONE) /\
   FLOOKUP rule_link.rhs.l (nodeid "n1") =
     SOME (label_cons (label_variable (varname "y")) label_nil, NONE) /\
   FLOOKUP rule_link.rhs.l (nodeid "n2") =
     SOME (label_cons (label_variable (varname "z")) label_nil, NONE)` by
    EVAL_TAC >>
  `FLOOKUP rule_link.rhs.m (edgeid "e0") =
     SOME (label_cons (label_variable (varname "a")) label_nil, NONE) /\
   FLOOKUP rule_link.rhs.m (edgeid "e1") =
     SOME (label_cons (label_variable (varname "b")) label_nil, NONE) /\
   FLOOKUP rule_link.rhs.m (edgeid "e2") =
     SOME (label_nil, NONE)` by EVAL_TAC >>
  (* instantiate_nodeattr/edgeattr for RHS *)
  sg `instantiate_nodeattr rule_link.rhs assign m G (nodeid "n0") =
      SOME (lv, NONE)`
  >- (irule ruleAppPropsTheory.instantiate_nodeattr_simple_matched >>
      simp[] >> qexists_tac `lv` >> qexists_tac `varname "x"` >> simp[]) >>
  sg `instantiate_nodeattr rule_link.rhs assign m G (nodeid "n1") =
      SOME (lu, NONE)`
  >- (irule ruleAppPropsTheory.instantiate_nodeattr_simple_matched >>
      simp[] >> qexists_tac `lu` >> qexists_tac `varname "y"` >> simp[]) >>
  sg `instantiate_nodeattr rule_link.rhs assign m G (nodeid "n2") =
      SOME (lw, NONE)`
  >- (irule ruleAppPropsTheory.instantiate_nodeattr_simple_matched >>
      simp[] >> qexists_tac `lw` >> qexists_tac `varname "z"` >> simp[]) >>
  sg `instantiate_edgeattr rule_link.rhs assign m G (edgeid "e0") =
      SOME (la, NONE)`
  >- (irule ruleAppPropsTheory.instantiate_edgeattr_simple_matched >>
      simp[] >> qexists_tac `la` >> qexists_tac `varname "a"` >> simp[]) >>
  sg `instantiate_edgeattr rule_link.rhs assign m G (edgeid "e1") =
      SOME (lb, NONE)`
  >- (irule ruleAppPropsTheory.instantiate_edgeattr_simple_matched >>
      simp[] >> qexists_tac `lb` >> qexists_tac `varname "b"` >> simp[]) >>
  `FLOOKUP (G.m f_o_f m.edgemap) (edgeid "e2") = NONE` by
    (simp[FLOOKUP_DEF, f_o_f_DEF, Abbr`m`]) >>
  sg `instantiate_edgeattr rule_link.rhs assign m G (edgeid "e2") =
      SOME (label_nil, NONE)`
  >- (irule ruleAppPropsTheory.instantiate_edgeattr_nil_fresh >> simp[]) >>
  (* instantiate_rulegraph for RHS *)
  `FDOM rule_link.rhs.l = {nodeid "n0"; nodeid "n1"; nodeid "n2"} /\
   FDOM rule_link.rhs.m = {edgeid "e0"; edgeid "e1"; edgeid "e2"} /\
   FINITE (FDOM rule_link.rhs.l) /\
   FINITE (FDOM rule_link.rhs.m)` by EVAL_TAC >>
  sg `?rhs'. instantiate_rulegraph rule_link.rhs assign m G = SOME rhs'`
  >- (simp[semTheory.instantiate_rulegraph_def, PULL_EXISTS] >>
      sg `?l. fmap_buildM (instantiate_nodeattr rule_link.rhs assign m G)
                {nodeid "n0"; nodeid "n1"; nodeid "n2"} = SOME l`
      >- (irule semTheory.fmap_buildM_succeeds >> simp[] >>
          rpt strip_tac >> gvs[] >> metis_tac[]) >>
      sg `?m'. fmap_buildM (instantiate_edgeattr rule_link.rhs assign m G)
                {edgeid "e0"; edgeid "e1"; edgeid "e2"} = SOME m'`
      >- (irule semTheory.fmap_buildM_succeeds >> simp[] >>
          rpt strip_tac >> gvs[] >> metis_tac[]) >>
      simp[PULL_EXISTS]) >>
  simp[]
QED

Theorem no_link_implies_transitive:
  !G. wf_hostgraph G /\ unmarked_hostgraph G /\ unrooted_hostgraph G /\
      ~(?G' m'. step program
                  (running (term_rscall {ruleid "link"}), [(G, id_track G)])
                  (final, [(G', m')])) ==>
      is_transitive G
Proof
  rpt strip_tac >>
  `~link_can_apply G` by
    (drule step_rscall_link_iff_link_can_apply >> fs[]) >>
  sg `!v' u' w'. v' IN G.V /\ u' IN G.V /\ w' IN G.V /\
                 has_edge G v' u' /\ has_edge G u' w' /\ v' <> w' ==>
                 has_edge G v' w'`
  >- (rpt strip_tac >> SPOSE_NOT_THEN ASSUME_TAC >>
      `link_can_apply G` by
        (irule two_path_implies_link_can_apply >> simp[] >> metis_tac[]))
  >- (simp[pathTheory.is_transitive_def] >>
      rpt strip_tac >> fs[pathTheory.reachable_in_def] >>
      pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >>
      pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >>
      qid_spec_tac `w` >> qid_spec_tac `v` >>
      Induct_on `path_length p`
      >- (rw[] >> fs[pathTheory.path_length_nontrivial])
      >- (rw[] >> Cases_on `p`
          >- fs[pathTheory.path_length_def]
          >- (fs[pathTheory.path_start_def, pathTheory.path_end_def,
                 pathTheory.wf_path_def, pathTheory.path_length_def] >>
              qabbrev_tac `u = path_start p'` >>
              `has_edge G n u` by
                (simp[pathTheory.has_edge_def] >>
                 qexists_tac `e` >> simp[Abbr `u`]) >>
              `u IN G.V` by
                simp[Abbr `u`, pathTheory.wf_path_start_in_V] >>
              Cases_on `u = path_end p'`
              >- gvs[]
              >- (sg `is_nontrivial_path p'`
                  >- (fs[pathTheory.is_nontrivial_path_def, Abbr `u`] >>
                      simp[pathTheory.path_length_nontrivial] >>
                      Cases_on `p'` >>
                      fs[pathTheory.path_length_def,
                         pathTheory.path_start_def,
                         pathTheory.path_end_def])
                  >- (`has_edge G (path_start p') (path_end p')` by
                        (first_x_assum (qspec_then `p'` mp_tac) >>
                         simp[]) >>
                      first_x_assum
                        (qspecl_then [`n`, `path_start p'`,
                                      `path_end p'`] mp_tac) >>
                      simp[])))))
QED

(* Helper: For term_rscall, multi-step to final = single step to final *)
Theorem rscall_steps_to_step:
  !env rset G G' m'.
    steps env (running (term_rscall rset), [(G, id_track G)])
              (final, [(G', m')]) ==>
    step env (running (term_rscall rset), [(G, id_track G)])
             (final, [(G', m')])
Proof
  rpt strip_tac >> fs[semTheory.steps_def] >>
  qpat_x_assum `RTC _ _ _` mp_tac >>
  simp[Once relationTheory.RTC_CASES1] >> strip_tac >>
  `?stk. u = (final, stk) \/ u = (failed, stk)` by
    (qpat_x_assum `step _ (running (term_rscall _), _) u` mp_tac >>
     simp[Once semTheory.step_cases] >> rpt strip_tac >> gvs[])
  >- (gvs[] >>
      qpat_x_assum `RTC _ _ _` mp_tac >>
      simp[Once relationTheory.RTC_CASES1] >> strip_tac
      >- gvs[]
      >- (qpat_x_assum `step _ (final, _) _` mp_tac >>
          simp[Once semTheory.step_cases]))
  >- (gvs[] >>
      qpat_x_assum `RTC _ _ _` mp_tac >>
      simp[Once relationTheory.RTC_CASES1] >> strip_tac >>
      qpat_x_assum `step _ (failed, _) _` mp_tac >>
      simp[Once semTheory.step_cases])
QED

(* Helper: steps execution preserves stack_tracks_morphism *)
Theorem steps_to_stack_tracks:
  !env t G0 H m.
    wf_program env /\ wf_hostgraph G0 /\
    steps env (running (term_alap t), [(G0, id_track G0)]) (final, [(H, m)]) ==>
    stack_tracks_morphism G0 [(H, m)]
Proof
  rpt strip_tac >> fs[semTheory.steps_def] >>
  drule arithmeticTheory.RTC_NRC >> strip_tac >>
  `wf_stack_labels [(G0, id_track G0)]` by
    simp[semTheory.wf_stack_labels_def] >>
  `stack_tracks_morphism G0 [(G0, id_track G0)]` by
    (irule semPropsTheory.initial_stack_tracks_morphism >> simp[]) >>
  drule_all semPropsTheory.NRC_step_preserves_stack_tracks_morphism >>
  simp[]
QED

(* DPO label lemmas *)

Theorem wf_hostgraph_FDOM_m_eq_E:
  !G. wf_hostgraph G ==> FDOM G.m = G.E
Proof
  rpt strip_tac >> fs wf_rwts
QED

(* Right-tagged edges get R's edge label *)
Theorem gluing_m_apply_right_tagged:
  !H R e. e IN R.E /\ wf_graph H /\ wf_graph R /\ FINITE (gluing_edges H R) ==>
    (gluing_m (gluing_edges H R) H R) ' (tag_edgeid_right e) = R.m ' e
Proof
  rpt strip_tac >>
  qabbrev_tac `entries = MAP (\eid. if is_left_tagged_edgeid eid
    then (eid, H.m ' (untag_edgeid eid))
    else (eid, R.m ' (untag_edgeid eid)))
    (SET_TO_LIST (gluing_edges H R))` >>
  `ALL_DISTINCT (MAP FST entries)` by
    (unabbrev_all_tac >> rw[MAP_MAP_o, combinTheory.o_DEF] >>
     simp[COND_RAND, pairTheory.FST] >>
     irule ALL_DISTINCT_SET_TO_LIST >> fs[]) >>
  `~is_left_tagged_edgeid (tag_edgeid_right e)` by
    (rw[taggingTheory.is_left_tagged_edgeid_def,
        taggingTheory.tag_edgeid_right_def, graphTheory.edgeid_absrep] >>
     rw[arithmeticTheory.EVEN_ODD, GSYM arithmeticTheory.ADD1,
        arithmeticTheory.ODD_DOUBLE]) >>
  `MEM (tag_edgeid_right e, R.m ' e) entries` by
    (unabbrev_all_tac >> rw[MEM_MAP] >>
     qexists_tac `tag_edgeid_right e` >>
     rw[taggingTheory.tag_untag_edgeid_inv, MEM_SET_TO_LIST,
        gluing_edges_def, edgeid_coprod_def]) >>
  `FLOOKUP (FEMPTY |++ entries) (tag_edgeid_right e) = SOME (R.m ' e)` by
    (irule alistTheory.mem_to_flookup >> rw[]) >>
  fs[flookup_thm, FDOM_FUPDATE_LIST] >>
  pop_assum mp_tac >> simp[gluing_m_def, LET_DEF]
QED

(* Left-tagged interface nodes get R's label (via inverse mapping) *)
Theorem gluing_l_apply_left_tagged_in_interface:
  !H R m Kv n k.
    k IN Kv /\ m.nodemap ' k = n /\
    INJ ($' m.nodemap) Kv H.V /\
    n IN H.V /\ wf_graph H /\ wf_graph R /\
    FINITE (gluing_nodes H Kv R) ==>
    (gluing_l (gluing_nodes H Kv R) Kv m H R) ' (tag_nodeid_left n) = R.l ' k
Proof
  rpt strip_tac >>
  qabbrev_tac `V = gluing_nodes H Kv R` >>
  qabbrev_tac `entries = MAP (\nid.
    if is_left_tagged_nodeid nid then
      let unid = untag_nodeid nid in
      if ?k. k IN Kv /\ m.nodemap ' k = unid
      then (nid, R.l ' (@k. k IN Kv /\ m.nodemap ' k = unid))
      else (nid, H.l ' unid)
    else (nid, R.l ' (untag_nodeid nid))) (SET_TO_LIST V)` >>
  `ALL_DISTINCT (MAP FST entries)` by
    (unabbrev_all_tac >> rw[MAP_MAP_o, combinTheory.o_DEF] >>
     simp[COND_RAND, pairTheory.FST] >>
     irule ALL_DISTINCT_SET_TO_LIST >> fs[]) >>
  `(@k'. k' IN Kv /\ m.nodemap ' k' = n) = k` by
    (SELECT_ELIM_TAC >> conj_tac
     >- (qexists_tac `k` >> simp[])
     >- (rpt strip_tac >> fs[INJ_DEF] >> metis_tac[])) >>
  `MEM (tag_nodeid_left n, R.l ' k) entries` by
    (unabbrev_all_tac >> rw[MEM_MAP] >>
     qexists_tac `tag_nodeid_left n` >> conj_tac
     >- (rw[taggingTheory.correct_tagging,
            taggingTheory.tag_untag_nodeid_inv] >> metis_tac[])
     >- rw[MEM_SET_TO_LIST, gluing_nodes_def,
            tag_nodeid_coprod_membership]) >>
  `FLOOKUP (FEMPTY |++ entries) (tag_nodeid_left n) = SOME (R.l ' k)` by
    (irule alistTheory.mem_to_flookup >> rw[]) >>
  fs[flookup_thm, FDOM_FUPDATE_LIST] >>
  pop_assum mp_tac >>
  simp[gluing_l_def, LET_DEF, Abbr `V`, Abbr `entries`]
QED

(* Helper: LHS and RHS of link rule share the same edge labels on e0 and e1 *)
Theorem link_lhs_rhs_shared_edgelabels:
  !assign pre G lhs' rhs'.
    instantiate_rulegraph rule_link.lhs assign pre G = SOME lhs' /\
    instantiate_rulegraph rule_link.rhs assign pre G = SOME rhs' ==>
    rhs'.m ' (edgeid "e0") = lhs'.m ' (edgeid "e0") /\
    rhs'.m ' (edgeid "e1") = lhs'.m ' (edgeid "e1")
Proof
  rpt strip_tac >>
  rpt (qpat_x_assum `instantiate_rulegraph _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [semTheory.instantiate_rulegraph_def])) >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `FDOM m = FDOM rule_link.lhs.m` by
    (irule semTheory.fmap_buildM_FDOM >> simp[FDOM_FINITE] >> metis_tac[]) >>
  `FDOM m' = FDOM rule_link.rhs.m` by
    (irule semTheory.fmap_buildM_FDOM >> simp[FDOM_FINITE] >> metis_tac[]) >|
  [(* e0 *)
   `FLOOKUP m (edgeid "e0") =
    instantiate_edgeattr rule_link.lhs assign pre G (edgeid "e0")` by
     (irule semTheory.fmap_buildM_FLOOKUP >>
      qexists_tac `FDOM rule_link.lhs.m` >>
      simp[FDOM_FINITE] >> EVAL_TAC) >>
   `FLOOKUP m' (edgeid "e0") =
    instantiate_edgeattr rule_link.rhs assign pre G (edgeid "e0")` by
     (irule semTheory.fmap_buildM_FLOOKUP >>
      qexists_tac `FDOM rule_link.rhs.m` >>
      simp[FDOM_FINITE] >> EVAL_TAC) >>
   `instantiate_edgeattr rule_link.lhs assign pre G (edgeid "e0") =
    instantiate_edgeattr rule_link.rhs assign pre G (edgeid "e0")` by
     simp[semTheory.instantiate_edgeattr_def, rule_link_def,
          FLOOKUP_UPDATE, FUPDATE_LIST_THM] >>
   `edgeid "e0" IN FDOM m` by (simp[] >> EVAL_TAC) >>
   `edgeid "e0" IN FDOM m'` by (simp[] >> EVAL_TAC) >>
   gvs[FLOOKUP_DEF] >> metis_tac[optionTheory.SOME_11],
   (* e1 *)
   `FLOOKUP m (edgeid "e1") =
    instantiate_edgeattr rule_link.lhs assign pre G (edgeid "e1")` by
     (irule semTheory.fmap_buildM_FLOOKUP >>
      qexists_tac `FDOM rule_link.lhs.m` >>
      simp[FDOM_FINITE] >> EVAL_TAC) >>
   `FLOOKUP m' (edgeid "e1") =
    instantiate_edgeattr rule_link.rhs assign pre G (edgeid "e1")` by
     (irule semTheory.fmap_buildM_FLOOKUP >>
      qexists_tac `FDOM rule_link.rhs.m` >>
      simp[FDOM_FINITE] >> EVAL_TAC) >>
   `instantiate_edgeattr rule_link.lhs assign pre G (edgeid "e1") =
    instantiate_edgeattr rule_link.rhs assign pre G (edgeid "e1")` by
     simp[semTheory.instantiate_edgeattr_def, rule_link_def,
          FLOOKUP_UPDATE, FUPDATE_LIST_THM] >>
   `edgeid "e1" IN FDOM m` by (simp[] >> EVAL_TAC) >>
   `edgeid "e1" IN FDOM m'` by (simp[] >> EVAL_TAC) >>
   gvs[FLOOKUP_DEF] >> metis_tac[optionTheory.SOME_11]]
QED

(* Helper: LHS and RHS of link rule share the same node labels on interface nodes *)
Theorem link_lhs_rhs_shared_nodelabels:
  !assign pre G lhs' rhs' k.
    instantiate_rulegraph rule_link.lhs assign pre G = SOME lhs' /\
    instantiate_rulegraph rule_link.rhs assign pre G = SOME rhs' /\
    k IN rule_link.inf ==>
    rhs'.l ' k = lhs'.l ' k
Proof
  rpt strip_tac >>
  rpt (qpat_x_assum `instantiate_rulegraph _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [semTheory.instantiate_rulegraph_def])) >>
  simp[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `FDOM l = FDOM rule_link.lhs.l` by
    (irule semTheory.fmap_buildM_FDOM >> simp[FDOM_FINITE] >> metis_tac[]) >>
  `FDOM l' = FDOM rule_link.rhs.l` by
    (irule semTheory.fmap_buildM_FDOM >> simp[FDOM_FINITE] >> metis_tac[]) >>
  `k IN FDOM rule_link.lhs.l /\ k IN FDOM rule_link.rhs.l` by
    (fs[rule_link_def] >> fs[IN_INSERT] >> EVAL_TAC) >>
  `FLOOKUP l k = instantiate_nodeattr rule_link.lhs assign pre G k` by
    (irule semTheory.fmap_buildM_FLOOKUP >>
     qexists_tac `FDOM rule_link.lhs.l` >> simp[FDOM_FINITE]) >>
  `FLOOKUP l' k = instantiate_nodeattr rule_link.rhs assign pre G k` by
    (irule semTheory.fmap_buildM_FLOOKUP >>
     qexists_tac `FDOM rule_link.rhs.l` >> simp[FDOM_FINITE]) >>
  `instantiate_nodeattr rule_link.lhs assign pre G k =
   instantiate_nodeattr rule_link.rhs assign pre G k` by
    (simp[semTheory.instantiate_nodeattr_def, rule_link_def,
          FLOOKUP_UPDATE, FUPDATE_LIST_THM] >>
     fs[rule_link_def] >> fs[IN_INSERT] >>
     gvs[FLOOKUP_UPDATE, FUPDATE_LIST_THM]) >>
  `k IN FDOM l` by simp[] >>
  `k IN FDOM l'` by simp[] >>
  gvs[FLOOKUP_DEF] >> metis_tac[optionTheory.SOME_11]
QED

Theorem deletion_m_surviving:
  !lhs' Kv m G e.
    wf_hostgraph G /\ e IN deletion_remaining_edges lhs' m G ==>
    (deletion lhs' Kv m G).m ' e = G.m ' e
Proof
  rw[dpoTheory.deletion_def, LET_THM] >>
  simp[DRESTRICT_DEF] >>
  `e IN FDOM G.m` by
    (fs[dpoTheory.deletion_remaining_edges_def,
        wf_hostgraph_def, wf_graph_def]) >>
  simp[]
QED

Theorem deletion_l_surviving:
  !lhs' Kv m G v.
    wf_hostgraph G /\ v IN deletion_relabling_nodes lhs' m Kv G ==>
    (deletion lhs' Kv m G).l ' v = G.l ' v
Proof
  rw[dpoTheory.deletion_def, LET_THM] >>
  simp[DRESTRICT_DEF] >>
  `v IN FDOM G.l` by
    (fs[dpoTheory.deletion_relabling_nodes_def,
        dpoTheory.deletion_remaining_nodes_def,
        wf_hostgraph_def, wf_graph_def]) >>
  simp[]
QED

(* Label preservation through a link step *)
Theorem link_step_preserves_labels:
  !G0 G track_bar lhs' rhs' m.
    link_step_context G0 G track_bar lhs' rhs' m /\
    preserve_edgelabels lhs' m G /\
    preserve_nodelabels lhs' m G /\
    rhs'.m ' (edgeid "e0") = lhs'.m ' (edgeid "e0") /\
    rhs'.m ' (edgeid "e1") = lhs'.m ' (edgeid "e1") /\
    (!k. k IN rule_link.inf ==> rhs'.l ' k = lhs'.l ' k) ==>
    preserve_edgelabels G0 (link_new_track_bar G0 track_bar lhs' m G)
      (dpo lhs' rule_link.inf rhs' m G) /\
    preserve_nodelabels G0 (link_new_track_bar G0 track_bar lhs' m G)
      (dpo lhs' rule_link.inf rhs' m G)
Proof
  rpt strip_tac
  (* ---- preserve_edgelabels ---- *)
  >- (
    simp[preserve_edgelabels_def, link_new_track_bar_def] >>
    fs[link_step_context_def] >>
    `G0.m = G.m f_o_f track_bar.edgemap` by
      fs[preserve_edgelabels_def, minimal_extension_def,
         is_inj_morphism_def, is_morphism_def, is_premorphism_def] >>
    `FDOM track_bar.edgemap = G0.E` by fs me_inj_rwts >>
    `INJ ($' track_bar.edgemap) G0.E G.E` by
      fs[minimal_extension_def, is_inj_morphism_def,
         is_inj_premorphism_def] >>
    `FRANGE track_bar.edgemap SUBSET G.E` by
      (fs me_inj_rwts >> metis_tac[]) >>
    `FDOM m.edgemap = lhs'.E` by fs match_morphism_rwts >>
    `INJ ($' m.edgemap) lhs'.E G.E` by fs match_inj_rwts >>
    `lhs'.E = {edgeid "e1"; edgeid "e0"}` by (gvs[] >> EVAL_TAC) >>
    `m.edgemap ' (edgeid "e0") <> m.edgemap ' (edgeid "e1")` by
      (strip_tac >> `edgeid "e0" IN lhs'.E` by simp[] >>
       `edgeid "e1" IN lhs'.E` by simp[] >>
       `edgeid "e0" = edgeid "e1"` by metis_tac[INJ_DEF] >> fs[]) >>
    `deletion_deleted_edges lhs' m =
     {m.edgemap ' (edgeid "e0"); m.edgemap ' (edgeid "e1")}` by
      (simp[dpoTheory.deletion_deleted_edges_def] >>
       simp[EXTENSION] >> metis_tac[]) >>
    qabbrev_tac `G'0 = dpo lhs' rule_link.inf rhs' m G` >>
    qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
    `FINITE G.E` by fs wf_rwts >>
    `FINITE rhs'.E` by fs wf_rwts >>
    `FINITE D.E` by
      (simp[Abbr `D`, dpoTheory.deletion_def,
            dpoTheory.deletion_remaining_edges_def] >>
       metis_tac[IMAGE_FINITE, FINITE_DIFF]) >>
    `FINITE (gluing_edges D rhs')` by
      (simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
       metis_tac[IMAGE_FINITE, FINITE_UNION]) >>
    `wf_graph D` by
      (simp[Abbr `D`] >> irule wf_partial_hostgraph_IMP_wf_graph >>
       irule dpoTheory.deletion_preserves_wf_graph >>
       rpt conj_tac >> simp[] >> EVAL_TAC) >>
    `FDOM G.m = G.E` by fs wf_rwts >>
    `FDOM G'0.m = G'0.E` by metis_tac[wf_hostgraph_FDOM_m_eq_E] >>
    simp[Once $ GSYM fmap_EQ_THM] >> conj_tac
    (* Domain equality *)
    >- (`FDOM (G.m f_o_f track_bar.edgemap) = G0.E` by
          (simp[f_o_f_DEF, EXTENSION] >> gen_tac >> EQ_TAC >>
           strip_tac >> simp[] >>
           `track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
             (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
           metis_tac[SUBSET_DEF]) >>
        pop_assum SUBST1_TAC >>
        `G'0.E = IMAGE tag_edgeid_left D.E UNION
                 IMAGE tag_edgeid_right rhs'.E` by
          (simp[Abbr `G'0`, Abbr `D`, dpoTheory.dpo_def,
                dpoTheory.gluing_def, dpoTheory.gluing_edges_def,
                dpoTheory.edgeid_coprod_def]) >>
        simp[cj 1 f_o_f_DEF, FUN_FMAP_DEF, EXTENSION] >>
        gen_tac >> EQ_TAC >> strip_tac >> simp[FUN_FMAP_DEF] >>
        Cases_on `track_bar.edgemap ' x IN deletion_deleted_edges lhs' m`
        >- (`track_bar.edgemap ' x = m.edgemap ' (edgeid "e0") \/
             track_bar.edgemap ' x = m.edgemap ' (edgeid "e1")` by
              (gvs[IN_INSERT]) >> simp[]
            >- (DISJ2_TAC >> qexists_tac `edgeid "e0"` >>
                simp[] >> EVAL_TAC)
            >- (DISJ2_TAC >> qexists_tac `edgeid "e1"` >>
                simp[] >> EVAL_TAC))
        >- (fs[IN_INSERT] >> IF_CASES_TAC
            >- gvs[IN_INSERT]
            >- (DISJ1_TAC >> qexists_tac `track_bar.edgemap ' x` >>
                simp[] >>
                simp[Abbr `D`, dpoTheory.deletion_def,
                     dpoTheory.deletion_remaining_edges_def] >>
                `track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
                  (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
                metis_tac[SUBSET_DEF])))
    (* Pointwise equality *)
    >> (rpt strip_tac >>
        `x IN G0.E /\ track_bar.edgemap ' x IN G.E` by
          (qpat_x_assum `x IN FDOM _` mp_tac >> simp[f_o_f_DEF]) >>
        `(G.m f_o_f track_bar.edgemap) ' x =
         G.m ' (track_bar.edgemap ' x)` by
          (irule (cj 2 f_o_f_DEF) >> simp[f_o_f_DEF]) >>
        Cases_on `track_bar.edgemap ' x = m.edgemap ' (edgeid "e0") \/
                  track_bar.edgemap ' x = m.edgemap ' (edgeid "e1")`
        (* --- Deleted edge --- *)
        >- (simp[FUN_FMAP_DEF] >>
            Cases_on `m.edgemap ' (edgeid "e0") = track_bar.edgemap ' x`
            (* e0 case *)
            >- (`tag_edgeid_right (edgeid "e0") IN G'0.E` by
                  (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
                        dpoTheory.gluing_edges_def,
                        dpoTheory.edgeid_coprod_def] >>
                   DISJ2_TAC >> qexists_tac `edgeid "e0"` >>
                   simp[] >> EVAL_TAC) >>
                `x IN FDOM (G'0.m f_o_f FUN_FMAP
                  (\e. if track_bar.edgemap ' e = m.edgemap ' (edgeid "e0") \/
                          track_bar.edgemap ' e = m.edgemap ' (edgeid "e1")
                       then tag_edgeid_right
                         (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                          then edgeid "e0" else edgeid "e1")
                       else tag_edgeid_left (track_bar.edgemap ' e))
                  G0.E)` by (simp[f_o_f_DEF, FUN_FMAP_DEF]) >>
                first_x_assum (mp_tac o MATCH_MP (cj 2 f_o_f_DEF)) >>
                strip_tac >> pop_assum (fn th => REWRITE_TAC[th]) >>
                simp[FUN_FMAP_DEF] >>
                `G'0.m ' (tag_edgeid_right (edgeid "e0")) =
                 rhs'.m ' (edgeid "e0")` by
                  (ntac 2 (qpat_x_assum `rhs'.m ' _ = lhs'.m ' _`
                     (K ALL_TAC)) >>
                   simp[Abbr `G'0`, dpoTheory.dpo_def,
                        dpoTheory.gluing_def] >>
                   irule gluing_m_apply_right_tagged >>
                   simp[] >> fs[wf_hostgraph_def] >> EVAL_TAC) >>
                `lhs'.m ' (edgeid "e0") =
                 (G.m f_o_f m.edgemap) ' (edgeid "e0")` by
                  fs[preserve_edgelabels_def] >>
                `edgeid "e0" IN FDOM m.edgemap` by simp[] >>
                `(G.m f_o_f m.edgemap) ' (edgeid "e0") =
                 G.m ' (m.edgemap ' (edgeid "e0"))` by
                  (irule (cj 2 f_o_f_DEF) >>
                   simp[f_o_f_DEF] >> EVAL_TAC) >>
                simp[])
            (* e1 case *)
            >- (`m.edgemap ' (edgeid "e1") = track_bar.edgemap ' x` by
                  (fs[IN_INSERT] >> metis_tac[]) >>
                `tag_edgeid_right (edgeid "e1") IN G'0.E` by
                  (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
                        dpoTheory.gluing_edges_def,
                        dpoTheory.edgeid_coprod_def] >>
                   DISJ2_TAC >> qexists_tac `edgeid "e1"` >>
                   simp[] >> EVAL_TAC) >>
                `x IN FDOM (G'0.m f_o_f FUN_FMAP
                  (\e. if track_bar.edgemap ' e = m.edgemap ' (edgeid "e0") \/
                          track_bar.edgemap ' e = m.edgemap ' (edgeid "e1")
                       then tag_edgeid_right
                         (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                          then edgeid "e0" else edgeid "e1")
                       else tag_edgeid_left (track_bar.edgemap ' e))
                  G0.E)` by (simp[f_o_f_DEF, FUN_FMAP_DEF]) >>
                first_x_assum (mp_tac o MATCH_MP (cj 2 f_o_f_DEF)) >>
                strip_tac >> pop_assum (fn th => REWRITE_TAC[th]) >>
                simp[FUN_FMAP_DEF] >>
                `G'0.m ' (tag_edgeid_right (edgeid "e1")) =
                 rhs'.m ' (edgeid "e1")` by
                  (ntac 2 (qpat_x_assum `rhs'.m ' _ = lhs'.m ' _`
                     (K ALL_TAC)) >>
                   simp[Abbr `G'0`, dpoTheory.dpo_def,
                        dpoTheory.gluing_def] >>
                   irule gluing_m_apply_right_tagged >>
                   simp[] >> fs[wf_hostgraph_def] >> EVAL_TAC) >>
                `lhs'.m ' (edgeid "e1") =
                 (G.m f_o_f m.edgemap) ' (edgeid "e1")` by
                  fs[preserve_edgelabels_def] >>
                `edgeid "e1" IN FDOM m.edgemap` by simp[] >>
                `(G.m f_o_f m.edgemap) ' (edgeid "e1") =
                 G.m ' (m.edgemap ' (edgeid "e1"))` by
                  (irule (cj 2 f_o_f_DEF) >>
                   simp[f_o_f_DEF] >> EVAL_TAC) >>
                simp[]))
        (* --- Surviving edge --- *)
        >- (`~(track_bar.edgemap ' x = m.edgemap ' (edgeid "e0") \/
               track_bar.edgemap ' x = m.edgemap ' (edgeid "e1"))` by
              (CCONTR_TAC >> gvs[IN_INSERT]) >>
            `FUN_FMAP
              (\e. if track_bar.edgemap ' e = m.edgemap ' (edgeid "e0") \/
                      track_bar.edgemap ' e = m.edgemap ' (edgeid "e1")
                   then tag_edgeid_right
                     (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                      then edgeid "e0" else edgeid "e1")
                   else tag_edgeid_left (track_bar.edgemap ' e))
              G0.E ' x =
             tag_edgeid_left (track_bar.edgemap ' x)` by
              simp[FUN_FMAP_DEF] >>
            `tag_edgeid_left (track_bar.edgemap ' x) IN G'0.E` by
              (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
                    dpoTheory.gluing_edges_def,
                    dpoTheory.edgeid_coprod_def] >>
               DISJ1_TAC >>
               simp[Abbr `D`, dpoTheory.deletion_def,
                    dpoTheory.deletion_remaining_edges_def] >>
               qexists_tac `track_bar.edgemap ' x` >> simp[] >> fs[] >>
               `track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
                 (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
               metis_tac[SUBSET_DEF]) >>
            `x IN FDOM (G'0.m f_o_f FUN_FMAP
              (\e. if track_bar.edgemap ' e = m.edgemap ' (edgeid "e0") \/
                      track_bar.edgemap ' e = m.edgemap ' (edgeid "e1")
                   then tag_edgeid_right
                     (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                      then edgeid "e0" else edgeid "e1")
                   else tag_edgeid_left (track_bar.edgemap ' e))
              G0.E)` by (simp[f_o_f_DEF, FUN_FMAP_DEF]) >>
            first_x_assum (mp_tac o MATCH_MP (cj 2 f_o_f_DEF)) >>
            strip_tac >> pop_assum (fn th => REWRITE_TAC[th]) >>
            simp[FUN_FMAP_DEF] >>
            `track_bar.edgemap ' x IN deletion_remaining_edges lhs' m G` by
              (simp[dpoTheory.deletion_remaining_edges_def]) >>
            `track_bar.edgemap ' x IN D.E` by
              simp[Abbr `D`, dpoTheory.deletion_def] >>
            simp[Abbr `D`, Abbr `G'0`, dpoTheory.dpo_def,
                 dpoTheory.gluing_def] >>
            `(gluing_m (gluing_edges (deletion lhs' rule_link.inf m G) rhs')
                (deletion lhs' rule_link.inf m G) rhs') '
              (tag_edgeid_left (track_bar.edgemap ' x)) =
              (deletion lhs' rule_link.inf m G).m '
              (track_bar.edgemap ' x)` by
               (irule dpoTheory.gluing_m_apply_left_tagged >>
                simp[] >> fs[wf_hostgraph_def]) >>
            `(deletion lhs' rule_link.inf m G).m '
             (track_bar.edgemap ' x) =
             G.m ' (track_bar.edgemap ' x)` by
               metis_tac[deletion_m_surviving] >>
            simp[])))
  (* ---- preserve_nodelabels ---- *)
  >- (
    simp[preserve_nodelabels_def, link_new_track_bar_def,
         compose_morphism_def] >>
    fs[link_step_context_def] >>
    `G0.l = G.l f_o_f track_bar.nodemap` by
      fs[preserve_nodelabels_def, minimal_extension_def,
         is_inj_morphism_def, is_morphism_def, is_premorphism_def] >>
    `G.l = (dpo lhs' rule_link.inf rhs' m G).l f_o_f
           (track lhs' rule_link.inf m G).nodemap` suffices_by
      (strip_tac >> metis_tac[morphismTheory.f_o_f_ASSOC]) >>
    `deletion_remaining_nodes lhs' m rule_link.inf G = G.V` by
      (irule link_no_node_deletion >> gvs[]) >>
    `FINITE G.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
    `FDOM (track lhs' rule_link.inf m G).nodemap = G.V` by
      (irule link_track_nodemap_FDOM >> simp[]) >>
    qabbrev_tac `G'0 = dpo lhs' rule_link.inf rhs' m G` >>
    qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
    `D.V = G.V` by
      (simp[Abbr `D`, dpoTheory.deletion_def,
            dpoTheory.deletion_remaining_nodes_def,
            dpoTheory.deletion_deleted_nodes_def] >>
       gvs[] >> simp[DIFF_EQ_EMPTY, SUBSET_REFL]) >>
    `FDOM G.l = G.V` by fs wf_rwts >>
    `FDOM G'0.l = G'0.V` by fs wf_rwts >>
    `G'0.V = IMAGE tag_nodeid_left G.V` by
      (simp[Abbr `G'0`] >> irule link_dpo_V >> simp[]) >>
    `FDOM m.nodemap = lhs'.V` by fs match_morphism_rwts >>
    `INJ ($' m.nodemap) lhs'.V G.V` by fs match_inj_rwts >>
    simp[Once $ GSYM fmap_EQ_THM] >> conj_tac
    (* Domain *)
    >- (simp[cj 1 f_o_f_DEF, EXTENSION] >>
        gen_tac >> EQ_TAC >> strip_tac >> simp[] >>
        irule_at Any trackTheory.track_nodemap_apply >> simp[])
    (* Per-element *)
    >> (rpt strip_tac >>
        `(track lhs' rule_link.inf m G).nodemap ' x =
         tag_nodeid_left x` by
          (irule trackTheory.track_nodemap_apply >> simp[]) >>
        `x IN FDOM (G'0.l f_o_f
           (track lhs' rule_link.inf m G).nodemap)` by
          (simp[cj 1 f_o_f_DEF] >> qexists_tac `x` >> simp[]) >>
        `(G'0.l f_o_f (track lhs' rule_link.inf m G).nodemap) ' x =
         G'0.l ' ((track lhs' rule_link.inf m G).nodemap ' x)` by
          (irule (cj 2 f_o_f_DEF) >> simp[]) >>
        pop_assum SUBST1_TAC >> simp[] >>
        Cases_on `x IN IMAGE ($' m.nodemap) rule_link.inf`
        (* Interface node *)
        >- (fs[IN_IMAGE] >>
            `rule_link.inf SUBSET lhs'.V` by (gvs[] >> EVAL_TAC) >>
            `INJ ($' m.nodemap) rule_link.inf D.V` by
              metis_tac[INJ_SUBSET, SUBSET_REFL, SUBSET_TRANS] >>
            `wf_graph D` by
              (simp[Abbr `D`] >>
               irule wf_partial_hostgraph_IMP_wf_graph >>
               irule dpoTheory.deletion_preserves_wf_graph >>
               rpt conj_tac >> simp[] >> EVAL_TAC) >>
            `G'0.l ' (tag_nodeid_left (m.nodemap ' x')) =
             rhs'.l ' x'` by
              (qpat_x_assum `!k. _ ==> rhs'.l ' k = _` (K ALL_TAC) >>
               simp[Abbr `G'0`, dpoTheory.dpo_def,
                    dpoTheory.gluing_def] >>
               irule gluing_l_apply_left_tagged_in_interface >>
               simp[] >> fs[wf_hostgraph_def] >>
               simp[dpoTheory.gluing_nodes_def,
                    dpoTheory.nodeid_coprod_def] >>
               `FINITE D.V` by simp[] >>
               `FINITE rhs'.V` by
                 fs[wf_hostgraph_def, wf_graph_def] >>
               metis_tac[IMAGE_FINITE, FINITE_DIFF, FINITE_UNION]) >>
            `rhs'.l ' x' = lhs'.l ' x'` by
              (first_x_assum (mp_tac o Q.SPEC `x'`) >> simp[]) >>
            `lhs'.l ' x' = (G.l f_o_f m.nodemap) ' x'` by
              fs[preserve_nodelabels_def] >>
            `x' IN FDOM m.nodemap` by metis_tac[SUBSET_DEF] >>
            `(G.l f_o_f m.nodemap) ' x' = G.l ' (m.nodemap ' x')` by
              (irule (cj 2 f_o_f_DEF) >> simp[cj 1 f_o_f_DEF] >>
               fs wf_rwts >> fs match_morphism_rwts >>
               metis_tac[SUBSET_DEF, IN_FRANGE]) >>
            simp[])
        (* Non-interface node *)
        >- (`~(?k. k IN rule_link.inf /\ m.nodemap ' k = x)` by
              (strip_tac >> fs[] >> metis_tac[IN_IMAGE]) >>
            `wf_graph D` by
              (simp[Abbr `D`] >>
               irule wf_partial_hostgraph_IMP_wf_graph >>
               irule dpoTheory.deletion_preserves_wf_graph >>
               rpt conj_tac >> simp[] >> EVAL_TAC) >>
            `G'0.l ' (tag_nodeid_left x) = D.l ' x` by
              (simp[Abbr `G'0`, dpoTheory.dpo_def,
                    dpoTheory.gluing_def] >>
               irule dpoTheory.gluing_l_apply_left_tagged >>
               simp[] >> rpt conj_tac
               >- (simp[dpoTheory.gluing_nodes_def,
                         dpoTheory.nodeid_coprod_def] >>
                   `FINITE D.V` by simp[] >>
                   `FINITE rhs'.V` by
                     fs[wf_hostgraph_def, wf_graph_def] >>
                   metis_tac[IMAGE_FINITE, FINITE_DIFF, FINITE_UNION])
               >- fs[wf_hostgraph_def]
               >- metis_tac[]) >>
            `x IN deletion_relabling_nodes lhs' m rule_link.inf G` by
              (simp[dpoTheory.deletion_relabling_nodes_def] >>
               DISJ2_TAC >> qexists_tac `x` >> simp[] >>
               fs[IN_IMAGE] >> metis_tac[]) >>
            `D.l ' x = G.l ' x` by
              (simp[Abbr `D`] >> irule deletion_l_surviving >>
               simp[]) >>
            simp[])))
QED

(* Source/target preservation through a link step *)
Theorem link_step_preserve_st:
  !G0 G track_bar lhs' rhs' m.
    link_step_context G0 G track_bar lhs' rhs' m /\
    lhs'.s = rule_link.lhs.s /\ lhs'.t = rule_link.lhs.t /\
    rhs'.s = rule_link.rhs.s /\ rhs'.t = rule_link.rhs.t ==>
    preserve_source G0 (link_new_track_bar G0 track_bar lhs' m G)
      (dpo lhs' rule_link.inf rhs' m G) /\
    preserve_target G0 (link_new_track_bar G0 track_bar lhs' m G)
      (dpo lhs' rule_link.inf rhs' m G)
Proof
  rpt strip_tac >> fs[link_step_context_def] >>
  qabbrev_tac `G'0 = dpo lhs' rule_link.inf rhs' m G` >>
  qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
  `FDOM track_bar.edgemap = G0.E` by fs me_inj_rwts >>
  `FDOM track_bar.nodemap = G0.V` by fs me_inj_rwts >>
  `INJ ($' track_bar.edgemap) G0.E G.E` by
    fs[minimal_extension_def, is_inj_morphism_def, is_inj_premorphism_def] >>
  `FRANGE track_bar.edgemap SUBSET G.E` by (fs me_inj_rwts >> metis_tac[]) >>
  `FRANGE track_bar.nodemap SUBSET G.V` by (fs me_inj_rwts >> metis_tac[]) >>
  `BIJ ($' track_bar.nodemap) G0.V G.V` by fs[minimal_extension_def] >>
  `FDOM m.edgemap = lhs'.E` by fs match_morphism_rwts >>
  `INJ ($' m.edgemap) lhs'.E G.E` by fs match_inj_rwts >>
  `lhs'.E = {edgeid "e1"; edgeid "e0"}` by (gvs[] >> EVAL_TAC) >>
  `m.edgemap ' (edgeid "e0") <> m.edgemap ' (edgeid "e1")` by
    (strip_tac >> `edgeid "e0" IN lhs'.E` by simp[] >>
     `edgeid "e1" IN lhs'.E` by simp[] >>
     `edgeid "e0" = edgeid "e1"` by metis_tac[INJ_DEF] >> fs[]) >>
  `deletion_deleted_edges lhs' m =
   {m.edgemap ' (edgeid "e0"); m.edgemap ' (edgeid "e1")}` by
    (simp[dpoTheory.deletion_deleted_edges_def] >>
     simp[EXTENSION] >> metis_tac[]) >>
  `FINITE G.E` by fs wf_rwts >>
  `FINITE G.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  `FINITE rhs'.E` by fs wf_rwts >>
  `FINITE D.E` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def] >>
     metis_tac[IMAGE_FINITE, FINITE_DIFF]) >>
  `wf_graph D` by
    (simp[Abbr `D`] >> irule wf_partial_hostgraph_IMP_wf_graph >>
     irule dpoTheory.deletion_preserves_wf_graph >>
     rpt conj_tac >> simp[] >> EVAL_TAC) >>
  `deletion_remaining_nodes lhs' m rule_link.inf G = G.V` by
    (irule link_no_node_deletion >> gvs[]) >>
  `FDOM (track lhs' rule_link.inf m G).nodemap = G.V` by
    (irule link_track_nodemap_FDOM >> simp[]) >>
  qabbrev_tac `nm = (link_new_track_bar G0 track_bar lhs' m G).nodemap` >>
  qabbrev_tac `em = (link_new_track_bar G0 track_bar lhs' m G).edgemap` >>
  `FDOM nm = G0.V` by
    (simp[Abbr `nm`, link_new_track_bar_def, compose_morphism_def,
          cj 1 f_o_f_DEF, EXTENSION] >>
     gen_tac >> EQ_TAC >> strip_tac >> simp[] >>
     metis_tac[BIJ_DEF, INJ_DEF]) >>
  `!v. v IN G0.V ==> nm ' v = tag_nodeid_left (track_bar.nodemap ' v)` by
    (rpt strip_tac >>
     simp[Abbr `nm`, link_new_track_bar_def, compose_morphism_def] >>
     `track_bar.nodemap ' v IN G.V` by metis_tac[BIJ_DEF, INJ_DEF] >>
     simp[f_o_f_DEF] >> irule trackTheory.track_nodemap_apply >> simp[]) >>
  `FDOM m.nodemap = lhs'.V` by fs match_morphism_rwts >>
  (* Pointwise source/target preservation for track_bar *)
  `!e. e IN G0.E ==>
       G.s ' (track_bar.edgemap ' e) = track_bar.nodemap ' (G0.s ' e) /\
       G.t ' (track_bar.edgemap ' e) = track_bar.nodemap ' (G0.t ' e)` by
    (rpt strip_tac >> (
     `preserve_source G0 track_bar G /\ preserve_target G0 track_bar G` by
       fs me_inj_rwts >>
     fs[preserve_source_def, preserve_target_def] >>
     `e IN FDOM (track_bar.nodemap f_o_f G0.s)` by
       (simp[cj 1 f_o_f_DEF] >> fs wf_rwts >>
        `G0.s ' e IN G0.V` by
          (fs[FRANGE_DEF, SUBSET_DEF] >> metis_tac[]) >> metis_tac[]) >>
     `e IN FDOM (track_bar.nodemap f_o_f G0.t)` by
       (simp[cj 1 f_o_f_DEF] >> fs wf_rwts >>
        `G0.t ' e IN G0.V` by
          (fs[FRANGE_DEF, SUBSET_DEF] >> metis_tac[]) >> metis_tac[]) >>
     `e IN FDOM (G.s f_o_f track_bar.edgemap)` by
       (simp[cj 1 f_o_f_DEF] >> `track_bar.edgemap ' e IN G.E` by
          metis_tac[INJ_DEF] >> fs wf_rwts) >>
     `e IN FDOM (G.t f_o_f track_bar.edgemap)` by
       (simp[cj 1 f_o_f_DEF] >> `track_bar.edgemap ' e IN G.E` by
          metis_tac[INJ_DEF] >> fs wf_rwts) >>
     imp_res_tac (cj 2 f_o_f_DEF) >> gvs[])) >>
  `preserve_source lhs' m G` by fs match_source_rwts >>
  `preserve_target lhs' m G` by fs match_target_rwts >>
  `G'0.E = IMAGE tag_edgeid_left D.E UNION IMAGE tag_edgeid_right rhs'.E` by
    (simp[Abbr `G'0`, Abbr `D`, dpoTheory.dpo_def, dpoTheory.gluing_def,
          dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def]) >>
  (* rhs' interface membership and edge membership *)
  `rhs'.s ' (edgeid "e0") IN rule_link.inf /\
   rhs'.t ' (edgeid "e0") IN rule_link.inf /\
   rhs'.s ' (edgeid "e1") IN rule_link.inf /\
   rhs'.t ' (edgeid "e1") IN rule_link.inf` by (gvs[] >> EVAL_TAC) >>
  `edgeid "e0" IN rhs'.E /\ edgeid "e1" IN rhs'.E` by (gvs[] >> EVAL_TAC) >>
  (* Gluing source/target for right-tagged edges - BEFORE concrete EVAL_TAC *)
  `G'0.s ' (tag_edgeid_right (edgeid "e0")) =
   tag_nodeid_left (m.nodemap ' (rhs'.s ' (edgeid "e0"))) /\
   G'0.t ' (tag_edgeid_right (edgeid "e0")) =
   tag_nodeid_left (m.nodemap ' (rhs'.t ' (edgeid "e0"))) /\
   G'0.s ' (tag_edgeid_right (edgeid "e1")) =
   tag_nodeid_left (m.nodemap ' (rhs'.s ' (edgeid "e1"))) /\
   G'0.t ' (tag_edgeid_right (edgeid "e1")) =
   tag_nodeid_left (m.nodemap ' (rhs'.t ' (edgeid "e1")))` by
    (rpt conj_tac >> (
     simp[Abbr `G'0`, Abbr `D`, dpoTheory.dpo_def, dpoTheory.gluing_def,
          LET_THM] >>
     qpat_x_assum `rhs'.s = rule_link.rhs.s`
        (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
     qpat_x_assum `rhs'.t = rule_link.rhs.t`
        (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
     (irule dpoTheory.gluing_s_apply_right_tagged_in_interface ORELSE
      irule dpoTheory.gluing_t_apply_right_tagged_in_interface) >>
     simp[] >> fs[wf_hostgraph_def] >>
     TRY (simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def,
               IMAGE_FINITE]) >>
     EVAL_TAC)) >>
  (* FINITE (gluing_edges D rhs') needed for gluing_t *)
  `FINITE (gluing_edges D rhs')` by
    (simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
     metis_tac[IMAGE_FINITE, FINITE_UNION]) >>
  (* Gluing source for left-tagged (surviving) edges *)
  `!e. e IN D.E ==>
       G'0.s ' (tag_edgeid_left e) = tag_nodeid_left (D.s ' e)` by
    (rpt strip_tac >>
     simp[Abbr `G'0`, Abbr `D`, dpoTheory.dpo_def, dpoTheory.gluing_def,
          LET_THM] >>
     irule dpoTheory.gluing_s_apply_left_tagged >>
     simp[] >> fs[wf_hostgraph_def]) >>
  (* Gluing target for left-tagged (surviving) edges *)
  `!e. e IN D.E ==>
       G'0.t ' (tag_edgeid_left e) = tag_nodeid_left (D.t ' e)` by
    (rpt strip_tac >>
     simp[Abbr `G'0`, Abbr `D`, dpoTheory.dpo_def, dpoTheory.gluing_def,
          LET_THM] >>
     irule dpoTheory.gluing_t_apply_left_tagged >>
     simp[] >> fs[wf_hostgraph_def]) >>
  (* Deletion edges are a subset of graph edges *)
  `D.E SUBSET G.E` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def]) >>
  (* Deletion preserves source/target for surviving edges *)
  `!e. e IN D.E ==>
       D.s ' e = G.s ' e /\ D.t ' e = G.t ' e` by
    (rpt strip_tac >>
     `e IN G.E` by metis_tac[SUBSET_DEF] >>
     fs[Abbr `D`, dpoTheory.deletion_def, LET_THM, DRESTRICT_DEF] >>
     fs wf_rwts) >>
  (* Concrete source/target node values for rule_link *)
  `rule_link.lhs.s ' (edgeid "e0") = nodeid "n0" /\
   rule_link.lhs.t ' (edgeid "e0") = nodeid "n1" /\
   rule_link.lhs.s ' (edgeid "e1") = nodeid "n1" /\
   rule_link.lhs.t ' (edgeid "e1") = nodeid "n2"` by EVAL_TAC >>
  `rule_link.rhs.s ' (edgeid "e0") = nodeid "n0" /\
   rule_link.rhs.t ' (edgeid "e0") = nodeid "n1" /\
   rule_link.rhs.s ' (edgeid "e1") = nodeid "n1" /\
   rule_link.rhs.t ' (edgeid "e1") = nodeid "n2"` by EVAL_TAC >>
  (* Extract match pointwise facts for e0 using imp_res_tac *)
  `m.nodemap ' (nodeid "n0") = G.s ' (m.edgemap ' (edgeid "e0")) /\
   m.nodemap ' (nodeid "n1") = G.t ' (m.edgemap ' (edgeid "e0"))` by
    (qpat_x_assum `preserve_source lhs' m G`
       (fn th => ASSUME_TAC (REWRITE_RULE[preserve_source_def] th)) >>
     qpat_x_assum `preserve_target lhs' m G`
       (fn th => ASSUME_TAC (REWRITE_RULE[preserve_target_def] th)) >>
     `edgeid "e0" IN FDOM (m.nodemap f_o_f lhs'.s)` by
       (simp[cj 1 f_o_f_DEF] >> fs wf_rwts >> gvs[] >> EVAL_TAC) >>
     `edgeid "e0" IN FDOM (m.nodemap f_o_f lhs'.t)` by
       (simp[cj 1 f_o_f_DEF] >> fs wf_rwts >> gvs[] >> EVAL_TAC) >>
     `edgeid "e0" IN FDOM (G.s f_o_f m.edgemap)` by
       (simp[cj 1 f_o_f_DEF] >>
        `m.edgemap ' (edgeid "e0") IN G.E` by
          metis_tac[INJ_DEF, IN_INSERT] >> fs wf_rwts) >>
     `edgeid "e0" IN FDOM (G.t f_o_f m.edgemap)` by
       (simp[cj 1 f_o_f_DEF] >>
        `m.edgemap ' (edgeid "e0") IN G.E` by
          metis_tac[INJ_DEF, IN_INSERT] >> fs wf_rwts) >>
     imp_res_tac (cj 2 f_o_f_DEF) >> gvs[]) >>
  (* Extract match pointwise facts for e1 *)
  `m.nodemap ' (nodeid "n1") = G.s ' (m.edgemap ' (edgeid "e1")) /\
   m.nodemap ' (nodeid "n2") = G.t ' (m.edgemap ' (edgeid "e1"))` by
    (qpat_x_assum `preserve_source lhs' m G`
       (fn th => ASSUME_TAC (REWRITE_RULE[preserve_source_def] th)) >>
     qpat_x_assum `preserve_target lhs' m G`
       (fn th => ASSUME_TAC (REWRITE_RULE[preserve_target_def] th)) >>
     `edgeid "e1" IN FDOM (m.nodemap f_o_f lhs'.s)` by
       (simp[cj 1 f_o_f_DEF] >> fs wf_rwts >> gvs[] >> EVAL_TAC) >>
     `edgeid "e1" IN FDOM (m.nodemap f_o_f lhs'.t)` by
       (simp[cj 1 f_o_f_DEF] >> fs wf_rwts >> gvs[] >> EVAL_TAC) >>
     `edgeid "e1" IN FDOM (G.s f_o_f m.edgemap)` by
       (simp[cj 1 f_o_f_DEF] >>
        `m.edgemap ' (edgeid "e1") IN G.E` by
          metis_tac[INJ_DEF, IN_INSERT] >> fs wf_rwts) >>
     `edgeid "e1" IN FDOM (G.t f_o_f m.edgemap)` by
       (simp[cj 1 f_o_f_DEF] >>
        `m.edgemap ' (edgeid "e1") IN G.E` by
          metis_tac[INJ_DEF, IN_INSERT] >> fs wf_rwts) >>
     imp_res_tac (cj 2 f_o_f_DEF) >> gvs[]) >>
  (* Now prove both preserve_source and preserve_target *)
  rpt conj_tac >> simp[preserve_source_def, preserve_target_def] >>
  simp[Once $ GSYM fmap_EQ_THM] >> conj_tac
  (* ---- Domain equality (same structure for source and target) ---- *)
  >- (`FDOM (nm f_o_f G0.s) = G0.E` by
        (simp[cj 1 f_o_f_DEF, EXTENSION] >> gen_tac >> EQ_TAC >>
         strip_tac >> simp[] >> `FDOM G0.s = G0.E` by fs wf_rwts >> fs[] >>
         `G0.s ' x IN G0.V` by
           (fs (wf_rwts @ [FRANGE_DEF, SUBSET_DEF]) >> metis_tac[]) >>
         metis_tac[]) >>
      pop_assum SUBST1_TAC >>
      `FDOM G'0.s = G'0.E` by fs wf_rwts >>
      simp[cj 1 f_o_f_DEF, Abbr `em`, link_new_track_bar_def,
           FUN_FMAP_DEF, EXTENSION] >>
      gen_tac >> EQ_TAC >> strip_tac >> simp[FUN_FMAP_DEF] >>
      Cases_on `track_bar.edgemap ' x IN deletion_deleted_edges lhs' m`
      >- (`track_bar.edgemap ' x = m.edgemap ' (edgeid "e0") \/
           track_bar.edgemap ' x = m.edgemap ' (edgeid "e1")` by
            (gvs[IN_INSERT]) >> simp[]
          >- (DISJ2_TAC >> qexists_tac `edgeid "e0"` >> simp[] >> EVAL_TAC)
          >- (DISJ2_TAC >> qexists_tac `edgeid "e1"` >> simp[] >> EVAL_TAC))
      >- (fs[IN_INSERT] >> IF_CASES_TAC
          >- gvs[IN_INSERT]
          >- (DISJ1_TAC >> qexists_tac `track_bar.edgemap ' x` >> simp[] >>
              simp[Abbr `D`, dpoTheory.deletion_def,
                   dpoTheory.deletion_remaining_edges_def] >>
              `track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
                (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
              metis_tac[SUBSET_DEF])))
  (* ---- Pointwise equality (source) ---- *)
  >- (rpt strip_tac >>
      `x IN G0.E` by
        (fs[cj 1 f_o_f_DEF] >> `FDOM G0.s = G0.E` by fs wf_rwts >> fs[]) >>
      `G0.s ' x IN G0.V` by
        (fs (wf_rwts @ [FRANGE_DEF, SUBSET_DEF]) >> metis_tac[]) >>
      `track_bar.edgemap ' x IN G.E` by metis_tac[INJ_DEF] >>
      `(nm f_o_f G0.s) ' x = nm ' (G0.s ' x)` by
        (irule (cj 2 f_o_f_DEF) >> simp[cj 1 f_o_f_DEF] >> fs wf_rwts) >>
      `nm ' (G0.s ' x) = tag_nodeid_left (track_bar.nodemap ' (G0.s ' x))`
        by metis_tac[] >>
      Cases_on `track_bar.edgemap ' x IN deletion_deleted_edges lhs' m`
      (* --- Deleted edge --- *)
      >- (gvs[IN_INSERT] >> (
          `(G'0.s f_o_f em) ' x = G'0.s ' (em ' x)` by
            (irule (cj 2 f_o_f_DEF) >> simp[cj 1 f_o_f_DEF, Abbr `em`,
                 link_new_track_bar_def, FUN_FMAP_DEF] >> fs wf_rwts) >>
          simp[Abbr `em`, link_new_track_bar_def, FUN_FMAP_DEF] >>
          metis_tac[]))
      (* --- Surviving edge --- *)
      >- (`~(track_bar.edgemap ' x = m.edgemap ' (edgeid "e0") \/
             track_bar.edgemap ' x = m.edgemap ' (edgeid "e1"))` by
            (CCONTR_TAC >> gvs[IN_INSERT]) >>
          `em ' x = tag_edgeid_left (track_bar.edgemap ' x)` by
            simp[Abbr `em`, link_new_track_bar_def, FUN_FMAP_DEF] >>
          `track_bar.edgemap ' x IN D.E` by
            (simp[Abbr `D`, dpoTheory.deletion_def,
                  dpoTheory.deletion_remaining_edges_def] >>
             `track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
               (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
             metis_tac[SUBSET_DEF]) >>
          gvs[] >>
          `G.s ' (track_bar.edgemap ' x) =
           track_bar.nodemap ' (G0.s ' x)` by metis_tac[] >> gvs[] >>
          `x IN FDOM (G'0.s f_o_f em)` by
            (simp[cj 1 f_o_f_DEF, Abbr `em`, link_new_track_bar_def,
                  FUN_FMAP_DEF] >> fs wf_rwts) >>
          imp_res_tac (cj 2 f_o_f_DEF) >> gvs[]))
  (* preserve_target: same structure with t replacing s *)
  >- (`FDOM (nm f_o_f G0.t) = G0.E` by
        (simp[cj 1 f_o_f_DEF, EXTENSION] >> gen_tac >> EQ_TAC >>
         strip_tac >> simp[] >> `FDOM G0.t = G0.E` by fs wf_rwts >> fs[] >>
         `G0.t ' x IN G0.V` by
           (fs (wf_rwts @ [FRANGE_DEF, SUBSET_DEF]) >> metis_tac[]) >>
         metis_tac[]) >>
      pop_assum SUBST1_TAC >>
      `FDOM G'0.t = G'0.E` by fs wf_rwts >>
      simp[cj 1 f_o_f_DEF, Abbr `em`, link_new_track_bar_def,
           FUN_FMAP_DEF, EXTENSION] >>
      gen_tac >> EQ_TAC >> strip_tac >> simp[FUN_FMAP_DEF] >>
      Cases_on `track_bar.edgemap ' x IN deletion_deleted_edges lhs' m`
      >- (`track_bar.edgemap ' x = m.edgemap ' (edgeid "e0") \/
           track_bar.edgemap ' x = m.edgemap ' (edgeid "e1")` by
            (gvs[IN_INSERT]) >> simp[]
          >- (DISJ2_TAC >> qexists_tac `edgeid "e0"` >> simp[] >> EVAL_TAC)
          >- (DISJ2_TAC >> qexists_tac `edgeid "e1"` >> simp[] >> EVAL_TAC))
      >- (fs[IN_INSERT] >> IF_CASES_TAC
          >- gvs[IN_INSERT]
          >- (DISJ1_TAC >> qexists_tac `track_bar.edgemap ' x` >> simp[] >>
              simp[Abbr `D`, dpoTheory.deletion_def,
                   dpoTheory.deletion_remaining_edges_def] >>
              `track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
                (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
              metis_tac[SUBSET_DEF])))
  (* ---- Pointwise equality (target) ---- *)
  >- (rpt strip_tac >>
      `x IN G0.E` by
        (fs[cj 1 f_o_f_DEF] >> `FDOM G0.t = G0.E` by fs wf_rwts >> fs[]) >>
      `G0.t ' x IN G0.V` by
        (fs (wf_rwts @ [FRANGE_DEF, SUBSET_DEF]) >> metis_tac[]) >>
      `track_bar.edgemap ' x IN G.E` by metis_tac[INJ_DEF] >>
      `(nm f_o_f G0.t) ' x = nm ' (G0.t ' x)` by
        (irule (cj 2 f_o_f_DEF) >> simp[cj 1 f_o_f_DEF] >> fs wf_rwts) >>
      `nm ' (G0.t ' x) = tag_nodeid_left (track_bar.nodemap ' (G0.t ' x))`
        by metis_tac[] >>
      Cases_on `track_bar.edgemap ' x IN deletion_deleted_edges lhs' m`
      (* --- Deleted edge --- *)
      >- (gvs[IN_INSERT] >> (
          `(G'0.t f_o_f em) ' x = G'0.t ' (em ' x)` by
            (irule (cj 2 f_o_f_DEF) >> simp[cj 1 f_o_f_DEF, Abbr `em`,
                 link_new_track_bar_def, FUN_FMAP_DEF] >> fs wf_rwts) >>
          simp[Abbr `em`, link_new_track_bar_def, FUN_FMAP_DEF] >>
          metis_tac[]))
      (* --- Surviving edge --- *)
      >- (`~(track_bar.edgemap ' x = m.edgemap ' (edgeid "e0") \/
             track_bar.edgemap ' x = m.edgemap ' (edgeid "e1"))` by
            (CCONTR_TAC >> gvs[IN_INSERT]) >>
          `em ' x = tag_edgeid_left (track_bar.edgemap ' x)` by
            simp[Abbr `em`, link_new_track_bar_def, FUN_FMAP_DEF] >>
          `track_bar.edgemap ' x IN D.E` by
            (simp[Abbr `D`, dpoTheory.deletion_def,
                  dpoTheory.deletion_remaining_edges_def] >>
             `track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
               (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
             metis_tac[SUBSET_DEF]) >>
          gvs[] >>
          `G.t ' (track_bar.edgemap ' x) =
           track_bar.nodemap ' (G0.t ' x)` by metis_tac[] >> gvs[] >>
          `x IN FDOM (G'0.t f_o_f em)` by
            (simp[cj 1 f_o_f_DEF, Abbr `em`, link_new_track_bar_def,
                  FUN_FMAP_DEF] >> fs wf_rwts) >>
          imp_res_tac (cj 2 f_o_f_DEF) >> gvs[]))
QED

Theorem link_step_preserve_rootedness:
  !G0 G track_bar lhs' rhs' m.
    link_step_context G0 G track_bar lhs' rhs' m /\
    unrooted_hostgraph G /\
    unrooted_hostgraph (dpo lhs' rule_link.inf rhs' m G) ==>
    preserve_defined_rootedness G0
      (link_new_track_bar G0 track_bar lhs' m G)
      (dpo lhs' rule_link.inf rhs' m G)
Proof
  rpt strip_tac >>
  fs[link_step_context_def, preserve_defined_rootedness_def, SUBMAP_DEF] >>
  rpt strip_tac >>
  `x IN G0.V` by
    (fs[wf_hostgraph_def, wf_graph_def] >> metis_tac[SUBSET_DEF]) >>
  `FDOM track_bar.nodemap = G0.V` by
    (fs[minimal_extension_def, is_inj_morphism_def, is_morphism_def,
        is_premorphism_def, morphism_dom_ran_def]) >>
  `FINITE G.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  `FDOM (track lhs' rule_link.inf m G).nodemap = G.V` by
    (irule link_track_nodemap_FDOM >> simp[]) >>
  `FRANGE track_bar.nodemap SUBSET G.V` by
    (fs[minimal_extension_def, is_inj_morphism_def, is_morphism_def,
        is_premorphism_def, morphism_dom_ran_def]) >>
  `track_bar.nodemap ' x IN G.V` by
    (`track_bar.nodemap ' x IN FRANGE track_bar.nodemap` by
       (simp[FRANGE_DEF] >> metis_tac[]) >>
     metis_tac[SUBSET_DEF])
  (* FDOM membership *)
  >- (simp[cj 1 f_o_f_DEF, link_new_track_bar_def, compose_morphism_def] >>
      simp[] >>
      `FDOM (dpo lhs' rule_link.inf rhs' m G).p =
       (dpo lhs' rule_link.inf rhs' m G).V` by fs[unrooted_hostgraph_def] >>
      `(dpo lhs' rule_link.inf rhs' m G).V = IMAGE tag_nodeid_left G.V` by
        (irule link_dpo_V >> simp[]) >>
      `BIJ ($' (track lhs' rule_link.inf m G).nodemap) G.V
           (IMAGE tag_nodeid_left G.V)` by
        (irule link_track_nodemap_BIJ >> simp[]) >>
      `x IN FDOM ((track lhs' rule_link.inf m G).nodemap f_o_f
                   track_bar.nodemap)` by
        simp[cj 1 f_o_f_DEF] >>
      `((track lhs' rule_link.inf m G).nodemap f_o_f
        track_bar.nodemap) ' x =
       (track lhs' rule_link.inf m G).nodemap ' (track_bar.nodemap ' x)` by
        (irule (cj 2 f_o_f_DEF) >> simp[]) >>
      ASM_REWRITE_TAC[] >> fs[BIJ_DEF, INJ_DEF] >> res_tac)
  (* Value equality: both sides are F *)
  >- (`~(G0.p ' x)` by
        (`preserve_defined_rootedness G0 track_bar G` by
           fs[minimal_extension_def, is_inj_morphism_def, is_morphism_def,
              is_premorphism_def] >>
         fs[preserve_defined_rootedness_def, SUBMAP_DEF] >>
         first_x_assum drule >> strip_tac >>
         `x IN FDOM (G.p f_o_f track_bar.nodemap)` by
           (simp[cj 1 f_o_f_DEF] >> fs[unrooted_hostgraph_def]) >>
         `(G.p f_o_f track_bar.nodemap) ' x =
          G.p ' (track_bar.nodemap ' x)` by
           (irule (cj 2 f_o_f_DEF) >> simp[]) >>
         `~(G.p ' (track_bar.nodemap ' x))` by fs[unrooted_hostgraph_def] >>
         gvs[]) >>
      simp[] >> simp[link_new_track_bar_def, compose_morphism_def] >>
      qabbrev_tac `nmap = (track lhs' rule_link.inf m G).nodemap f_o_f
                           track_bar.nodemap` >>
      `x IN FDOM nmap` by (simp[Abbr`nmap`, cj 1 f_o_f_DEF]) >>
      `nmap ' x IN (dpo lhs' rule_link.inf rhs' m G).V` by
        (`(dpo lhs' rule_link.inf rhs' m G).V =
          IMAGE tag_nodeid_left G.V` by (irule link_dpo_V >> simp[]) >>
         `nmap ' x = (track lhs' rule_link.inf m G).nodemap '
                     (track_bar.nodemap ' x)` by
           (simp[Abbr`nmap`] >> irule (cj 2 f_o_f_DEF) >>
            simp[cj 1 f_o_f_DEF]) >>
         `BIJ ($' (track lhs' rule_link.inf m G).nodemap) G.V
              (IMAGE tag_nodeid_left G.V)` by
           (irule link_track_nodemap_BIJ >> simp[]) >>
         ASM_REWRITE_TAC[] >> fs[BIJ_DEF, INJ_DEF] >> res_tac) >>
      `x IN FDOM ((dpo lhs' rule_link.inf rhs' m G).p f_o_f nmap)` by
        (simp[cj 1 f_o_f_DEF] >> fs[unrooted_hostgraph_def]) >>
      `((dpo lhs' rule_link.inf rhs' m G).p f_o_f nmap) ' x =
       (dpo lhs' rule_link.inf rhs' m G).p ' (nmap ' x)` by
        (irule (cj 2 f_o_f_DEF) >> simp[]) >>
      simp[] >> fs[unrooted_hostgraph_def])
QED

Theorem link_step_morphism_dom_ran:
  !G0 G track_bar lhs' rhs' m.
    link_step_context G0 G track_bar lhs' rhs' m ==>
    morphism_dom_ran G0
      (link_new_track_bar G0 track_bar lhs' m G)
      (dpo lhs' rule_link.inf rhs' m G)
Proof
  rpt strip_tac >> fs[link_step_context_def] >>
  simp[morphism_dom_ran_def, link_new_track_bar_def] >>
  `FDOM track_bar.nodemap = G0.V` by fs me_inj_rwts >>
  `FDOM track_bar.edgemap = G0.E` by fs me_inj_rwts >>
  `FINITE G.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  `FDOM (track lhs' rule_link.inf m G).nodemap = G.V` by
    (irule link_track_nodemap_FDOM >> simp[]) >>
  `FRANGE track_bar.nodemap SUBSET G.V` by (fs me_inj_rwts >> metis_tac[]) >>
  rpt conj_tac
  (* FDOM nodemap = G0.V *)
  >- (simp[compose_morphism_def, cj 1 f_o_f_DEF] >> simp[EXTENSION] >>
      rpt strip_tac >> eq_tac >> rpt strip_tac >> gvs[] >>
      `x IN G0.V` by simp[] >>
      `track_bar.nodemap ' x IN FRANGE track_bar.nodemap` by
        (simp[FRANGE_DEF] >> metis_tac[]) >>
      `track_bar.nodemap ' x IN G.V` by metis_tac[SUBSET_DEF] >> simp[])
  (* FRANGE nodemap ⊆ DPO.V *)
  >- (`(dpo lhs' rule_link.inf rhs' m G).V = IMAGE tag_nodeid_left G.V` by
        (irule link_dpo_V >> simp[]) >>
      `BIJ ($' (track lhs' rule_link.inf m G).nodemap) G.V
           (IMAGE tag_nodeid_left G.V)` by
        (irule link_track_nodemap_BIJ >> simp[]) >>
      `BIJ ($' track_bar.nodemap) G0.V G.V` by fs[minimal_extension_def] >>
      ASM_REWRITE_TAC[] >>
      simp[SUBSET_DEF, compose_morphism_def, FRANGE_DEF] >> rpt strip_tac >>
      `x' IN G0.V /\ track_bar.nodemap ' x' IN G.V` by
        (qpat_x_assum `x' IN FDOM _` mp_tac >> simp[cj 1 f_o_f_DEF]) >>
      `((track lhs' rule_link.inf m G).nodemap f_o_f track_bar.nodemap) ' x' =
       (track lhs' rule_link.inf m G).nodemap ' (track_bar.nodemap ' x')` by
        (irule (cj 2 f_o_f_DEF) >> fs[cj 1 f_o_f_DEF]) >>
      gvs[] >> fs[BIJ_DEF, INJ_DEF] >> res_tac >> fs[IN_IMAGE] >> metis_tac[])
  (* IMAGE edgemap ⊆ DPO.E *)
  >- (simp[SUBSET_DEF, IN_IMAGE] >> rpt strip_tac >>
      Cases_on `track_bar.edgemap ' e IN deletion_deleted_edges lhs' m` >> gvs[]
      >- (simp[dpoTheory.dpo_def, dpoTheory.gluing_def,
               dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
          disj2_tac >>
          Cases_on `m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e` >>
          simp[] >>
          `edgeid "e0" IN rhs'.E /\ edgeid "e1" IN rhs'.E` by
            (gvs[] >> EVAL_TAC) >>
          metis_tac[])
      >- (simp[dpoTheory.dpo_def, dpoTheory.gluing_def,
               dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
          disj1_tac >>
          simp[dpoTheory.deletion_def, dpoTheory.deletion_remaining_edges_def] >>
          `FRANGE track_bar.edgemap SUBSET G.E` by fs me_inj_rwts >>
          `track_bar.edgemap ' e IN FRANGE track_bar.edgemap` by
            (simp[FRANGE_DEF] >> metis_tac[]) >>
          `track_bar.edgemap ' e IN G.E` by metis_tac[SUBSET_DEF] >> simp[] >>
          qexists_tac `track_bar.edgemap ' e` >> simp[]))
QED

(* BIJ of composed nodemap through link step *)
Theorem link_step_nodemap_BIJ:
  !G0 G track_bar lhs' rhs' m.
    link_step_context G0 G track_bar lhs' rhs' m ==>
    BIJ ($' (link_new_track_bar G0 track_bar lhs' m G).nodemap)
      G0.V (dpo lhs' rule_link.inf rhs' m G).V
Proof
  rpt strip_tac >> fs[link_step_context_def] >>
  simp[link_new_track_bar_def, compose_morphism_def] >>
  `(dpo lhs' rule_link.inf rhs' m G).V = IMAGE tag_nodeid_left G.V` by
    (irule link_dpo_V >> simp[]) >>
  `FINITE G.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  `BIJ ($' (track lhs' rule_link.inf m G).nodemap) G.V
       (IMAGE tag_nodeid_left G.V)` by
    (irule link_track_nodemap_BIJ >> simp[]) >>
  `FDOM (track lhs' rule_link.inf m G).nodemap = G.V` by
    (irule link_track_nodemap_FDOM >> simp[]) >>
  `BIJ ($' track_bar.nodemap) G0.V G.V` by fs[minimal_extension_def] >>
  ASM_REWRITE_TAC[] >>
  irule (iffRL BIJ_CONG) >>
  qexists_tac `($' (track lhs' rule_link.inf m G).nodemap) o
               ($' track_bar.nodemap)` >>
  conj_tac
  >- (rw[] >> rpt strip_tac >>
      `track_bar.nodemap ' x IN G.V` by
        (fs[BIJ_DEF, INJ_DEF] >>
         `FDOM track_bar.nodemap = G0.V` by fs me_inj_rwts >> res_tac) >>
      irule (cj 2 f_o_f_DEF) >> simp[] >>
      simp[cj 1 f_o_f_DEF] >>
      `FDOM track_bar.nodemap = G0.V` by fs me_inj_rwts >> simp[])
  >- (irule BIJ_COMPOSE >> qexists_tac `G.V` >> simp[])
QED

(* INJ of edgemap under link step *)
Theorem link_step_edgemap_INJ:
  !G0 G track_bar lhs' rhs' m.
    link_step_context G0 G track_bar lhs' rhs' m ==>
    INJ ($' (link_new_track_bar G0 track_bar lhs' m G).edgemap)
      G0.E (dpo lhs' rule_link.inf rhs' m G).E
Proof
  rpt strip_tac >> fs[link_step_context_def] >>
  simp[INJ_DEF, link_new_track_bar_def, FUN_FMAP_DEF] >>
  `FDOM track_bar.edgemap = G0.E` by
    (fs[minimal_extension_def, is_inj_morphism_def, is_morphism_def,
        is_premorphism_def, morphism_dom_ran_def]) >>
  `INJ ($' track_bar.edgemap) G0.E G.E` by
    (fs[minimal_extension_def, is_inj_morphism_def, is_inj_premorphism_def]) >>
  `FDOM m.edgemap = lhs'.E` by
    fs[is_match_def, is_inj_morphism_def, is_morphism_def,
       is_premorphism_def, morphism_dom_ran_def] >>
  `lhs'.E = {edgeid "e1"; edgeid "e0"}` by (gvs[] >> EVAL_TAC) >>
  `deletion_deleted_edges lhs' m =
   {m.edgemap ' (edgeid "e0"); m.edgemap ' (edgeid "e1")}` by
    (simp[dpoTheory.deletion_deleted_edges_def] >> simp[EXTENSION] >>
     rpt strip_tac >> eq_tac >> rpt strip_tac >> gvs[IN_INSERT] >>
     metis_tac[]) >>
  conj_tac
  (* Range *)
  >- (rpt strip_tac >>
      Cases_on `track_bar.edgemap ' x IN deletion_deleted_edges lhs' m` >>
      simp[]
      >- (simp[dpoTheory.dpo_def, dpoTheory.gluing_def,
               dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
          disj2_tac >>
          Cases_on `m.edgemap ' (edgeid "e0") = track_bar.edgemap ' x` >>
          simp[] >>
          `edgeid "e0" IN rhs'.E /\ edgeid "e1" IN rhs'.E` by
            (gvs[] >> EVAL_TAC) >>
          metis_tac[])
      >- (simp[dpoTheory.dpo_def, dpoTheory.gluing_def,
               dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
          disj1_tac >>
          simp[dpoTheory.deletion_def, dpoTheory.deletion_remaining_edges_def] >>
          `track_bar.edgemap ' x IN G.E` by
            (`track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
               (simp[FRANGE_DEF] >> metis_tac[]) >>
             fs[minimal_extension_def, is_inj_morphism_def, is_morphism_def,
                is_premorphism_def, morphism_dom_ran_def] >>
             metis_tac[SUBSET_DEF]) >>
          simp[] >> qexists_tac `track_bar.edgemap ' x` >> simp[] >>
          gvs[IN_INSERT]))
  (* Injectivity *)
  >- (rpt strip_tac >>
      Cases_on `track_bar.edgemap ' x IN deletion_deleted_edges lhs' m` >>
      Cases_on `track_bar.edgemap ' y IN deletion_deleted_edges lhs' m` >>
      gvs[]
      (* both map to m'e0 *)
      >- (fs[INJ_DEF] >> gvs[])
      (* x=m'e0, y=m'e1: m must be injective *)
      >- (`m.edgemap ' (edgeid "e0") <> m.edgemap ' (edgeid "e1")` by
            (`INJ ($' m.edgemap) lhs'.E G.E` by
               fs[is_match_def, is_inj_morphism_def, is_inj_premorphism_def] >>
             `edgeid "e0" IN lhs'.E /\ edgeid "e1" IN lhs'.E /\
              edgeid "e0" <> edgeid "e1"` by (gvs[] >> EVAL_TAC) >>
             fs[INJ_DEF] >> strip_tac >> res_tac >> fs[]) >>
          Cases_on `m.edgemap ' (edgeid "e0") = m.edgemap ' (edgeid "e1")` >>
          gvs[taggingTheory.tag_edgeid_right_def, graphTheory.edgeid_absrep])
      (* x=m'e1, y=m'e0: symmetric *)
      >- (`m.edgemap ' (edgeid "e0") <> m.edgemap ' (edgeid "e1")` by
            (`INJ ($' m.edgemap) lhs'.E G.E` by
               fs[is_match_def, is_inj_morphism_def, is_inj_premorphism_def] >>
             `edgeid "e0" IN lhs'.E /\ edgeid "e1" IN lhs'.E /\
              edgeid "e0" <> edgeid "e1"` by (gvs[] >> EVAL_TAC) >>
             fs[INJ_DEF] >> strip_tac >> res_tac >> fs[]) >>
          Cases_on `m.edgemap ' (edgeid "e0") = m.edgemap ' (edgeid "e1")` >>
          gvs[taggingTheory.tag_edgeid_right_def, graphTheory.edgeid_absrep])
      (* both map to m'e1 *)
      >- (fs[INJ_DEF] >> gvs[])
      (* cross-tag contradictions *)
      >- metis_tac[taggingTheory.tag_disjoint]
      >- metis_tac[taggingTheory.tag_disjoint]
      >- metis_tac[taggingTheory.tag_disjoint]
      >- metis_tac[taggingTheory.tag_disjoint]
      (* both surviving: tag_left injectivity *)
      >- (`track_bar.edgemap ' x = track_bar.edgemap ' y` by
            (`INJ tag_edgeid_left UNIV UNIV` by
               simp[taggingTheory.INJ_tag_edgeid] >>
             fs[INJ_DEF]) >>
          fs[INJ_DEF] >> res_tac))
QED

(* Reachability of generated edges under link step *)
Theorem link_step_reachability:
  !G0 G track_bar lhs' rhs' m.
    link_step_context G0 G track_bar lhs' rhs' m /\
    lhs'.s = rule_link.lhs.s /\ lhs'.t = rule_link.lhs.t /\
    rhs'.s = rule_link.rhs.s /\ rhs'.t = rule_link.rhs.t ==>
    edge_path_justified G0 (link_new_track_bar G0 track_bar lhs' m G)
      (dpo lhs' rule_link.inf rhs' m G)
Proof
  rpt strip_tac >>
  simp[edge_path_justified_def, generated_edges_def] >> rpt strip_tac >>
  fs[link_step_context_def] >>
  `parallel_free_extension track_bar G` by fs[minimal_extension_def] >>
  `FDOM track_bar.edgemap = G0.E` by fs me_inj_rwts >>
  `FRANGE track_bar.edgemap SUBSET G.E` by
    (fs me_inj_rwts >> metis_tac[]) >>
  `INJ ($' track_bar.edgemap) G0.E G.E` by
    fs[minimal_extension_def, is_inj_morphism_def, is_inj_premorphism_def] >>
  `BIJ ($' track_bar.nodemap) G0.V G.V` by fs[minimal_extension_def] >>
  `FDOM track_bar.nodemap = G0.V` by fs me_inj_rwts >>
  `FRANGE track_bar.nodemap SUBSET G.V` by
    (fs me_inj_rwts >> metis_tac[]) >>
  `FDOM m.edgemap = lhs'.E` by fs match_morphism_rwts >>
  `FRANGE m.edgemap SUBSET G.E` by fs match_morphism_rwts >>
  `INJ ($' m.edgemap) lhs'.E G.E` by fs match_inj_rwts >>
  `FDOM m.nodemap = lhs'.V` by fs match_morphism_rwts >>
  `FRANGE m.nodemap SUBSET G.V` by fs match_morphism_rwts >>
  STRIP_ASSUME_TAC rule_link_structure >>
  `lhs'.E = {edgeid "e1"; edgeid "e0"}` by (gvs[] >> EVAL_TAC) >>
  `rhs'.E = {edgeid "e2"; edgeid "e1"; edgeid "e0"}` by
    (gvs[] >> EVAL_TAC) >>
  `m.edgemap ' (edgeid "e0") <> m.edgemap ' (edgeid "e1")` by
    (strip_tac >>
     `edgeid "e0" IN lhs'.E /\ edgeid "e1" IN lhs'.E` by
       (gvs[] >> EVAL_TAC) >>
     `edgeid "e0" = edgeid "e1"` by metis_tac[INJ_DEF] >> fs[]) >>
  `deletion_deleted_edges lhs' m =
   {m.edgemap ' (edgeid "e0"); m.edgemap ' (edgeid "e1")}` by
    (simp[dpoTheory.deletion_deleted_edges_def] >>
     simp[EXTENSION] >> metis_tac[]) >>
  qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
  qabbrev_tac `G'0 = dpo lhs' rule_link.inf rhs' m G` >>
  `wf_graph D` by
    (simp[Abbr `D`] >>
     irule hostgraphTheory.wf_partial_hostgraph_IMP_wf_graph >>
     irule dpoTheory.deletion_preserves_wf_graph >> simp[] >> EVAL_TAC) >>
  `FINITE D.E` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def] >>
     fs[wf_hostgraph_def, wf_graph_def]) >>
  `FINITE rhs'.E` by simp[] >>
  `FINITE G.V` by fs wf_rwts >>
  `D.E SUBSET G.E` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def] >>
     simp[SUBSET_DEF] >> metis_tac[]) >>
  `G'0.E = IMAGE tag_edgeid_left D.E UNION IMAGE tag_edgeid_right rhs'.E` by
    (simp[Abbr `G'0`, Abbr `D`, dpoTheory.dpo_def, dpoTheory.gluing_def,
          dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def]) >>
  `FDOM (track lhs' rule_link.inf m G).nodemap = G.V` by
    (irule link_track_nodemap_FDOM >> simp[]) >>
  `deletion_remaining_nodes lhs' m rule_link.inf G = G.V` by
    (irule link_no_node_deletion >> gvs[]) >>
  (* Helper for composed morphism (shared by both cases) *)
  `!u. u IN G0.V /\ track_bar.nodemap ' u IN G.V ==>
   (link_new_track_bar G0 track_bar lhs' m G).nodemap ' u =
   tag_nodeid_left (track_bar.nodemap ' u)` by
    (rpt strip_tac >>
     simp[link_new_track_bar_def, compose_morphism_def] >>
     `u IN FDOM ((track lhs' rule_link.inf m G).nodemap f_o_f
                  track_bar.nodemap)` by
       (simp[cj 1 f_o_f_DEF] >> fs[BIJ_DEF, SURJ_DEF]) >>
     `((track lhs' rule_link.inf m G).nodemap f_o_f
       track_bar.nodemap) ' u =
      (track lhs' rule_link.inf m G).nodemap ' (track_bar.nodemap ' u)` by
       (irule (cj 2 f_o_f_DEF |> SPEC_ALL) >> simp[]) >>
     gvs[] >> irule trackTheory.track_nodemap_apply >>
     metis_tac[dpoTheory.wf_hostgraph_IMP_finite_remaining_elements,
               link_no_node_deletion]) >>
  (* case split on left/right-tagged *)
  `e IN IMAGE tag_edgeid_left D.E \/ e IN IMAGE tag_edgeid_right rhs'.E` by
    gvs[]
  (* ===== Case 1: Left-tagged edge (surviving from D) ===== *)
  >- (
    pop_assum (STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) >>
    rpt BasicProvers.VAR_EQ_TAC >>
    `x IN G.E` by metis_tac[SUBSET_DEF] >>
    sg `x NOTIN FRANGE track_bar.edgemap`
    >- (CCONTR_TAC >> fs[FRANGE_DEF] >>
        `x NOTIN deletion_deleted_edges lhs' m` by
          (fs[Abbr `D`, dpoTheory.deletion_def,
              dpoTheory.deletion_remaining_edges_def] >> gvs[]) >>
        `x' IN G0.E` by gvs[] >>
        `(link_new_track_bar G0 track_bar lhs' m G).edgemap ' x' =
         tag_edgeid_left x` by
          (simp[link_new_track_bar_def, FUN_FMAP_DEF] >> gvs[]) >>
        first_x_assum (qspec_then `x'` mp_tac) >>
        simp[link_new_track_bar_def, FUN_FMAP_DEF]) >>
    `edge_path_justified G0 track_bar G` by fs[minimal_extension_def] >>
    `?v w. v IN G0.V /\ w IN G0.V /\ track_bar.nodemap ' v = G.s ' x /\
           track_bar.nodemap ' w = G.t ' x /\ reachable_in G0 v w` by
      (fs[edge_path_justified_def, generated_edges_def] >>
       first_x_assum (qspec_then `x` mp_tac) >> simp[]) >>
    qexistsl [`v`, `w`] >> simp[] >>
    `D.s ' x = G.s ' x` by
      (fs[Abbr `D`, dpoTheory.deletion_def, LET_THM,
          finite_mapTheory.DRESTRICT_DEF] >>
       `x IN FDOM G.s` by fs wf_rwts >> gvs[]) >>
    `D.t ' x = G.t ' x` by
      (fs[Abbr `D`, dpoTheory.deletion_def, LET_THM,
          finite_mapTheory.DRESTRICT_DEF] >>
       `x IN FDOM G.t` by fs wf_rwts >> gvs[]) >>
    `gluing_s rule_link.inf m D rhs' ' (tag_edgeid_left x) =
     tag_nodeid_left (D.s ' x)` by
      (irule dpoTheory.gluing_s_apply_left_tagged >> simp[] >>
       fs[wf_hostgraph_def]) >>
    `gluing_t (gluing_edges D rhs') rule_link.inf m D rhs' '
     (tag_edgeid_left x) = tag_nodeid_left (D.t ' x)` by
      (irule dpoTheory.gluing_t_apply_left_tagged >>
       simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
       fs[wf_hostgraph_def]) >>
    `G'0.s ' (tag_edgeid_left x) = tag_nodeid_left (G.s ' x)` by
      (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def, LET_THM] >>
       gvs[Abbr `D`]) >>
    `G'0.t ' (tag_edgeid_left x) = tag_nodeid_left (G.t ' x)` by
      (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def, LET_THM] >>
       gvs[]) >>
    gvs[] >>
    `G.s ' x IN G.V` by
      (`FRANGE G.s SUBSET G.V` by fs wf_rwts >>
       `x IN FDOM G.s` by fs wf_rwts >>
       `G.s ' x IN FRANGE G.s` by (simp[FRANGE_DEF] >> metis_tac[]) >>
       fs[SUBSET_DEF]) >>
    `G.t ' x IN G.V` by
      (`FRANGE G.t SUBSET G.V` by fs wf_rwts >>
       `x IN FDOM G.t` by fs wf_rwts >>
       `G.t ' x IN FRANGE G.t` by (simp[FRANGE_DEF] >> metis_tac[]) >>
       fs[SUBSET_DEF]) >>
    conj_tac
    >- (first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
        disch_then irule >> fs[BIJ_DEF, INJ_DEF] >> metis_tac[])
    >- (first_x_assum (qspec_then `w` mp_tac) >> simp[] >>
        disch_then irule >> fs[BIJ_DEF, INJ_DEF] >> metis_tac[]))
  (* ===== Case 2: Right-tagged edge (from rhs) ===== *)
  >- (
    pop_assum (STRIP_ASSUME_TAC o REWRITE_RULE[IN_IMAGE]) >>
    rpt BasicProvers.VAR_EQ_TAC >>
    rename1 `tag_edgeid_right x` >>
    SUBGOAL_THEN
      ``x = edgeid "e0" \/ x = edgeid "e1" \/ x = edgeid "e2"``
      ASSUME_TAC
    >- (qpat_x_assum `rhs'.E = _` SUBST_ALL_TAC >> fs[IN_INSERT]) >>
    `edgeid "e0" IN lhs'.E` by (gvs[] >> EVAL_TAC) >>
    `edgeid "e1" IN lhs'.E` by (gvs[] >> EVAL_TAC) >>
    `m.edgemap ' (edgeid "e0") IN G.E` by
      (gvs[SUBSET_DEF, FRANGE_DEF] >> metis_tac[]) >>
    `m.edgemap ' (edgeid "e1") IN G.E` by
      (gvs[SUBSET_DEF, FRANGE_DEF] >> metis_tac[]) >>
    `edge_path_justified G0 track_bar G` by fs[minimal_extension_def] >>
    `?v0 w0. v0 IN G0.V /\ w0 IN G0.V /\
             track_bar.nodemap ' v0 = G.s ' (m.edgemap ' (edgeid "e0")) /\
             track_bar.nodemap ' w0 = G.t ' (m.edgemap ' (edgeid "e0")) /\
             reachable_in G0 v0 w0` by
      (fs[edge_path_justified_def, generated_edges_def] >>
       irule edge_in_G_has_reachable_preimages >> simp[]) >>
    `?v1 w1. v1 IN G0.V /\ w1 IN G0.V /\
             track_bar.nodemap ' v1 = G.s ' (m.edgemap ' (edgeid "e1")) /\
             track_bar.nodemap ' w1 = G.t ' (m.edgemap ' (edgeid "e1")) /\
             reachable_in G0 v1 w1` by
      (fs[edge_path_justified_def, generated_edges_def] >>
       irule edge_in_G_has_reachable_preimages >> simp[]) >>
    `G.s ' (m.edgemap ' (edgeid "e0")) = m.nodemap ' (nodeid "n0") /\
     G.t ' (m.edgemap ' (edgeid "e0")) = m.nodemap ' (nodeid "n1")` by
      (MATCH_MP_TAC match_preserves_st_apply >>
       qexistsl [`lhs'`, `rule_link.inf`] >> fs[]) >>
    `G.s ' (m.edgemap ' (edgeid "e1")) = m.nodemap ' (nodeid "n1") /\
     G.t ' (m.edgemap ' (edgeid "e1")) = m.nodemap ' (nodeid "n2")` by
      (MATCH_MP_TAC match_preserves_st_apply >>
       qexistsl [`lhs'`, `rule_link.inf`] >> fs[]) >>
    `rhs'.V = rule_link.inf` by (gvs[] >> EVAL_TAC) >>
    `!n. n IN rule_link.lhs.V ==>
         n IN FDOM m.nodemap /\ m.nodemap ' n IN G.V` by
      (rpt strip_tac >> gvs[] >>
       `m.nodemap ' n IN FRANGE m.nodemap` by
         (simp[FRANGE_DEF] >> metis_tac[]) >>
       fs[SUBSET_DEF]) >>
    `nodeid "n0" IN rule_link.lhs.V` by EVAL_TAC >>
    `nodeid "n1" IN rule_link.lhs.V` by EVAL_TAC >>
    `nodeid "n2" IN rule_link.lhs.V` by EVAL_TAC >>
    `!z. z IN rhs'.E ==> rhs'.s ' z IN rule_link.inf /\
                          rhs'.t ' z IN rule_link.inf` by
      (simp[] >> rpt strip_tac >> gvs[] >> EVAL_TAC) >>
    (* DPO source/target of right-tagged edges *)
    `!eid nid. eid IN rhs'.E /\ rhs'.s ' eid = nid /\ nid IN rule_link.inf ==>
     G'0.s ' (tag_edgeid_right eid) = tag_nodeid_left (m.nodemap ' nid)` by
      (rpt strip_tac >>
       simp[Abbr `G'0`, dpoTheory.dpo_def,
            dpoTheory.gluing_def, LET_THM] >>
       qpat_assum `rhs'.s ' eid = nid` (fn th =>
         ONCE_REWRITE_TAC[GSYM th]) >>
       irule dpoTheory.gluing_s_apply_right_tagged_in_interface >>
       simp[] >> gvs[] >> fs[wf_hostgraph_def] >>
       TRY (simp[dpoTheory.gluing_edges_def,
                 dpoTheory.edgeid_coprod_def, IMAGE_FINITE]) >>
       metis_tac[]) >>
    `!eid nid. eid IN rhs'.E /\ rhs'.t ' eid = nid /\ nid IN rule_link.inf ==>
     G'0.t ' (tag_edgeid_right eid) = tag_nodeid_left (m.nodemap ' nid)` by
      (rpt strip_tac >>
       simp[Abbr `G'0`, dpoTheory.dpo_def,
            dpoTheory.gluing_def, LET_THM] >>
       qpat_assum `rhs'.t ' eid = nid` (fn th =>
         ONCE_REWRITE_TAC[GSYM th]) >>
       irule dpoTheory.gluing_t_apply_right_tagged_in_interface >>
       simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
       gvs[] >> fs[wf_hostgraph_def] >> metis_tac[]) >>
    `m.nodemap ' (nodeid "n0") IN G.V` by metis_tac[] >>
    `m.nodemap ' (nodeid "n1") IN G.V` by metis_tac[] >>
    `m.nodemap ' (nodeid "n2") IN G.V` by metis_tac[] >>
    `rule_link.rhs.s ' (edgeid "e0") IN rule_link.inf` by EVAL_TAC >>
    `rule_link.rhs.t ' (edgeid "e0") IN rule_link.inf` by EVAL_TAC >>
    `rule_link.rhs.s ' (edgeid "e1") IN rule_link.inf` by EVAL_TAC >>
    `rule_link.rhs.t ' (edgeid "e1") IN rule_link.inf` by EVAL_TAC >>
    `rule_link.rhs.s ' (edgeid "e2") IN rule_link.inf` by EVAL_TAC >>
    `rule_link.rhs.t ' (edgeid "e2") IN rule_link.inf` by EVAL_TAC >>
    gvs[]
    >- (qexistsl [`v0`, `w0`] >> gvs[] >>
        conj_tac >> first_x_assum irule >> simp[] >>
        fs[BIJ_DEF, INJ_DEF] >> metis_tac[])
    >- (qexistsl [`v1`, `w1`] >> gvs[] >>
        conj_tac >> first_x_assum irule >> simp[] >>
        fs[BIJ_DEF, INJ_DEF] >> metis_tac[])
    >- (`track_bar.nodemap ' w0 = track_bar.nodemap ' v1` by gvs[] >>
        `w0 = v1` by
          (fs[BIJ_DEF, INJ_DEF] >> metis_tac[]) >>
        `reachable_in G0 v0 w1` by
          (irule reachable_in_trans >> qexists_tac `w0` >> gvs[]) >>
        qexistsl [`v0`, `w1`] >> gvs[] >>
        conj_tac >> first_x_assum irule >> simp[] >>
        fs[BIJ_DEF, INJ_DEF] >> metis_tac[])
    (* Duplicate goals from gvs[] splitting IMAGE UNION + disjunction *)
    >- (gvs[] >> qexistsl [`v0`, `w0`] >> gvs[] >>
        conj_tac >> first_x_assum irule >> simp[] >>
        fs[BIJ_DEF, INJ_DEF] >> metis_tac[])
    >- (gvs[] >> qexistsl [`v1`, `w1`] >> gvs[] >>
        conj_tac >> first_x_assum irule >> simp[] >>
        fs[BIJ_DEF, INJ_DEF] >> metis_tac[])
    >- (gvs[] >>
        `track_bar.nodemap ' w0 = track_bar.nodemap ' v1` by gvs[] >>
        `w0 = v1` by
          (fs[BIJ_DEF, INJ_DEF] >> metis_tac[]) >>
        `reachable_in G0 v0 w1` by
          (irule reachable_in_trans >> qexists_tac `w0` >> gvs[]) >>
        qexistsl [`v0`, `w1`] >> gvs[] >>
        conj_tac >> first_x_assum irule >> simp[] >>
        fs[BIJ_DEF, INJ_DEF] >> metis_tac[]))
QED

(* tag_nodeid_left is injective *)
Theorem tag_nodeid_left_11:
  tag_nodeid_left a = tag_nodeid_left b <=> (a = b)
Proof
  eq_tac >-
  (mp_tac taggingTheory.INJ_tag_nodeid >> simp[INJ_DEF]) >-
  simp[]
QED

(* Link step preserves parallel_free_extension.
   Key: the NAC ~has_edge(n0,n2) prevents creating parallel edges. *)
Theorem link_step_parallel_free:
  !G0 G track_bar lhs' rhs' m.
    link_step_context G0 G track_bar lhs' rhs' m /\
    lhs'.s = rule_link.lhs.s /\ lhs'.t = rule_link.lhs.t /\
    rhs'.s = rule_link.rhs.s /\ rhs'.t = rule_link.rhs.t /\
    ~has_edge G (m.nodemap ' (nodeid "n0")) (m.nodemap ' (nodeid "n2")) ==>
    parallel_free_extension
      (link_new_track_bar G0 track_bar lhs' m G)
      (dpo lhs' rule_link.inf rhs' m G)
Proof
  rpt strip_tac >>
  simp[parallel_free_extension_def, link_new_track_bar_def] >>
  fs[link_step_context_def] >>
  (* ---- Extract from minimal_extension ---- *)
  `parallel_free_extension track_bar G` by fs[minimal_extension_def] >>
  `FDOM track_bar.edgemap = G0.E` by fs me_inj_rwts >>
  `FRANGE track_bar.edgemap SUBSET G.E` by
    (fs me_inj_rwts >> metis_tac[]) >>
  `INJ ($' track_bar.edgemap) G0.E G.E` by
    fs[minimal_extension_def, is_inj_morphism_def,
       is_inj_premorphism_def] >>
  (* ---- Extract from is_match ---- *)
  `FDOM m.edgemap = lhs'.E` by fs match_morphism_rwts >>
  `FRANGE m.edgemap SUBSET G.E` by
    (fs match_morphism_rwts >> metis_tac[]) >>
  `INJ ($' m.edgemap) lhs'.E G.E` by fs match_inj_rwts >>
  `INJ ($' m.nodemap) lhs'.V G.V` by fs match_inj_rwts >>
  (* ---- Rule structure ---- *)
  `lhs'.E = {edgeid "e1"; edgeid "e0"}` by (gvs[] >> EVAL_TAC) >>
  `rhs'.E = {edgeid "e2"; edgeid "e1"; edgeid "e0"}` by
    (gvs[] >> EVAL_TAC) >>
  `lhs'.V = {nodeid "n2"; nodeid "n1"; nodeid "n0"}` by
    (gvs[] >> EVAL_TAC) >>
  STRIP_ASSUME_TAC rule_link_structure >>
  `m.edgemap ' (edgeid "e0") <> m.edgemap ' (edgeid "e1")` by
    (strip_tac >>
     `edgeid "e0" IN lhs'.E /\ edgeid "e1" IN lhs'.E` by
       (gvs[] >> EVAL_TAC) >>
     `edgeid "e0" = edgeid "e1"` by metis_tac[INJ_DEF] >> fs[]) >>
  `deletion_deleted_edges lhs' m =
   {m.edgemap ' (edgeid "e0"); m.edgemap ' (edgeid "e1")}` by
    (simp[dpoTheory.deletion_deleted_edges_def] >>
     simp[EXTENSION] >> metis_tac[]) >>
  (* ---- DPO structural setup ---- *)
  qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
  qabbrev_tac `G'0 = dpo lhs' rule_link.inf rhs' m G` >>
  `wf_graph D` by
    (simp[Abbr `D`] >>
     irule wf_partial_hostgraph_IMP_wf_graph >>
     irule dpoTheory.deletion_preserves_wf_graph >>
     rpt conj_tac >> simp[] >> EVAL_TAC) >>
  `wf_graph rhs'` by fs[wf_hostgraph_def] >>
  `FINITE D.E` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def] >>
     fs[wf_hostgraph_def, wf_graph_def]) >>
  `FINITE rhs'.E` by simp[] >>
  `G'0.E = IMAGE tag_edgeid_left D.E UNION
           IMAGE tag_edgeid_right rhs'.E` by
    (simp[Abbr `G'0`, Abbr `D`, dpoTheory.dpo_def, dpoTheory.gluing_def,
          dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def]) >>
  `D.E SUBSET G.E` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def] >>
     simp[SUBSET_DEF] >> metis_tac[]) >>
  `FINITE (gluing_edges D rhs')` by
    simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
  (* ---- Matched edge source/target in G ---- *)
  `FDOM G.s = G.E /\ FDOM G.t = G.E` by fs wf_rwts >>
  `preserve_source lhs' m G` by fs match_source_rwts >>
  `preserve_target lhs' m G` by fs match_target_rwts >>
  `FDOM m.nodemap = lhs'.V` by fs match_morphism_rwts >>
  `m.edgemap ' (edgeid "e0") IN G.E /\
   m.edgemap ' (edgeid "e1") IN G.E` by
    (`edgeid "e0" IN FDOM m.edgemap /\
      edgeid "e1" IN FDOM m.edgemap` by simp[] >>
     metis_tac[FRANGE_FLOOKUP, FLOOKUP_DEF, SUBSET_DEF]) >>
  `G.s ' (m.edgemap ' (edgeid "e0")) = m.nodemap ' (nodeid "n0") /\
   G.t ' (m.edgemap ' (edgeid "e0")) = m.nodemap ' (nodeid "n1")` by
    (qpat_x_assum `preserve_source lhs' m G`
       (fn th => ASSUME_TAC (REWRITE_RULE[preserve_source_def] th)) >>
     qpat_x_assum `preserve_target lhs' m G`
       (fn th => ASSUME_TAC (REWRITE_RULE[preserve_target_def] th)) >>
     `(edgeid "e0") IN FDOM (m.nodemap f_o_f lhs'.s)` by
       (simp[cj 1 f_o_f_DEF] >> fs wf_rwts >> gvs[] >> EVAL_TAC) >>
     `(edgeid "e0") IN FDOM (m.nodemap f_o_f lhs'.t)` by
       (simp[cj 1 f_o_f_DEF] >> fs wf_rwts >> gvs[] >> EVAL_TAC) >>
     `(edgeid "e0") IN FDOM (G.s f_o_f m.edgemap)` by
       (simp[cj 1 f_o_f_DEF] >>
        `m.edgemap ' (edgeid "e0") IN G.E` by
          metis_tac[INJ_DEF, IN_INSERT] >> fs wf_rwts) >>
     `(edgeid "e0") IN FDOM (G.t f_o_f m.edgemap)` by
       (simp[cj 1 f_o_f_DEF] >>
        `m.edgemap ' (edgeid "e0") IN G.E` by
          metis_tac[INJ_DEF, IN_INSERT] >> fs wf_rwts) >>
     imp_res_tac (cj 2 f_o_f_DEF) >> gvs[]) >>
  `G.s ' (m.edgemap ' (edgeid "e1")) = m.nodemap ' (nodeid "n1") /\
   G.t ' (m.edgemap ' (edgeid "e1")) = m.nodemap ' (nodeid "n2")` by
    (qpat_x_assum `preserve_source lhs' m G`
       (fn th => ASSUME_TAC (REWRITE_RULE[preserve_source_def] th)) >>
     qpat_x_assum `preserve_target lhs' m G`
       (fn th => ASSUME_TAC (REWRITE_RULE[preserve_target_def] th)) >>
     `(edgeid "e1") IN FDOM (m.nodemap f_o_f lhs'.s)` by
       (simp[cj 1 f_o_f_DEF] >> fs wf_rwts >> gvs[] >> EVAL_TAC) >>
     `(edgeid "e1") IN FDOM (m.nodemap f_o_f lhs'.t)` by
       (simp[cj 1 f_o_f_DEF] >> fs wf_rwts >> gvs[] >> EVAL_TAC) >>
     `(edgeid "e1") IN FDOM (G.s f_o_f m.edgemap)` by
       (simp[cj 1 f_o_f_DEF] >>
        `m.edgemap ' (edgeid "e1") IN G.E` by
          metis_tac[INJ_DEF, IN_INSERT] >> fs wf_rwts) >>
     `(edgeid "e1") IN FDOM (G.t f_o_f m.edgemap)` by
       (simp[cj 1 f_o_f_DEF] >>
        `m.edgemap ' (edgeid "e1") IN G.E` by
          metis_tac[INJ_DEF, IN_INSERT] >> fs wf_rwts) >>
     imp_res_tac (cj 2 f_o_f_DEF) >> gvs[]) >>
  (* ---- Deleted edges not in D.E ---- *)
  `m.edgemap ' (edgeid "e0") NOTIN D.E /\
   m.edgemap ' (edgeid "e1") NOTIN D.E` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def] >> simp[]) >>
  (* ---- D.s/D.t preserves G.s/G.t for surviving edges ---- *)
  `!x. x IN D.E ==> D.s ' x = G.s ' x /\ D.t ' x = G.t ' x` by
    (rpt strip_tac >>
     `D.s = DRESTRICT G.s D.E /\ D.t = DRESTRICT G.t D.E` by
       simp[Abbr `D`, dpoTheory.deletion_def, LET_THM] >>
     gvs[DRESTRICT_DEF] >> metis_tac[SUBSET_DEF]) >>
  (* ---- DPO source/target for left-tagged edges ---- *)
  `!x. x IN D.E ==>
       G'0.s ' (tag_edgeid_left x) = tag_nodeid_left (G.s ' x) /\
       G'0.t ' (tag_edgeid_left x) = tag_nodeid_left (G.t ' x)` by
    (rpt strip_tac >>
     `D.s ' x = G.s ' x /\ D.t ' x = G.t ' x` by metis_tac[]
     >- (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
              LET_THM] >>
         `gluing_s rule_link.inf m D rhs' ' (tag_edgeid_left x) =
          tag_nodeid_left (D.s ' x)` by
           (irule dpoTheory.gluing_s_apply_left_tagged >>
            simp[]) >> gvs[])
     >- (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
              LET_THM] >>
         `FINITE (gluing_edges D rhs')` by
           simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
         `gluing_t (gluing_edges D rhs') rule_link.inf m D rhs' '
          (tag_edgeid_left x) = tag_nodeid_left (D.t ' x)` by
           (irule dpoTheory.gluing_t_apply_left_tagged >>
            simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
            simp[]) >> gvs[])) >>
  (* ---- Interface membership for rhs edges ---- *)
  `!z. z IN rhs'.E ==>
       rhs'.s ' z IN rule_link.inf /\ rhs'.t ' z IN rule_link.inf` by
    (simp[] >> rpt strip_tac >> gvs[] >> EVAL_TAC) >>
  (* ---- DPO source/target for right-tagged edges ---- *)
  `!z. z IN rhs'.E ==>
       G'0.s ' (tag_edgeid_right z) =
         tag_nodeid_left (m.nodemap ' (rhs'.s ' z)) /\
       G'0.t ' (tag_edgeid_right z) =
         tag_nodeid_left (m.nodemap ' (rhs'.t ' z))` by
    (rpt strip_tac >>
     simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def, LET_THM]
     >- (qpat_x_assum `rhs'.s = rule_link.rhs.s` (fn th =>
           PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
         irule dpoTheory.gluing_s_apply_right_tagged_in_interface >>
         simp[] >> fs[wf_hostgraph_def] >>
         TRY (simp[dpoTheory.gluing_edges_def,
                   dpoTheory.edgeid_coprod_def, IMAGE_FINITE]) >>
         metis_tac[])
     >- (qpat_x_assum `rhs'.t = rule_link.rhs.t` (fn th =>
           PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
         irule dpoTheory.gluing_t_apply_right_tagged_in_interface >>
         simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
         fs[wf_hostgraph_def] >> metis_tac[])) >>
  (* ==== Main proof: contradiction on parallel edges ==== *)
  rpt strip_tac >>
  SPOSE_NOT_THEN strip_assume_tac >>
  `e' IN G'0.E` by fs[] >>
  (* Decompose e, e' via coprod *)
  `e IN IMAGE tag_edgeid_left D.E \/
   e IN IMAGE tag_edgeid_right rhs'.E` by gvs[] >>
  `e' IN IMAGE tag_edgeid_left D.E \/
   e' IN IMAGE tag_edgeid_right rhs'.E` by gvs[] >>
  fs[IN_IMAGE] >> rpt BasicProvers.VAR_EQ_TAC
  (* ---- Case 1: (left, left) ---- *)
  >- (`x <> x'` by (strip_tac >> gvs[]) >>
      `G.s ' x = G.s ' x' /\ G.t ' x = G.t ' x'` by
        (res_tac >> gvs[tag_nodeid_left_11]) >>
      `x NOTIN FRANGE track_bar.edgemap` by
        (simp[FRANGE_DEF] >> Q.X_GEN_TAC `y` >> rpt strip_tac >>
         first_x_assum (qspec_then `y` mp_tac) >>
         `y IN G0.E` by metis_tac[] >>
         `track_bar.edgemap ' y NOTIN deletion_deleted_edges lhs' m` by
           (strip_tac >>
            `x IN deletion_deleted_edges lhs' m` by metis_tac[] >>
            gvs[Abbr `D`, dpoTheory.deletion_def,
                dpoTheory.deletion_remaining_edges_def]) >> simp[]) >>
      `x IN G.E /\ x' IN G.E` by metis_tac[SUBSET_DEF] >>
      fs[parallel_free_extension_def] >> metis_tac[])
  (* ---- Case 2: (left, right) ---- *)
  >- (`x IN G.E` by metis_tac[SUBSET_DEF] >>
      `x NOTIN FRANGE track_bar.edgemap` by
        (simp[FRANGE_DEF] >> Q.X_GEN_TAC `y` >> rpt strip_tac >>
         first_x_assum (qspec_then `y` mp_tac) >>
         `y IN G0.E` by metis_tac[] >>
         `track_bar.edgemap ' y NOTIN deletion_deleted_edges lhs' m` by
           (strip_tac >>
            `x IN deletion_deleted_edges lhs' m` by metis_tac[] >>
            gvs[Abbr `D`, dpoTheory.deletion_def,
                dpoTheory.deletion_remaining_edges_def]) >> simp[]) >>
      `G'0.s ' (tag_edgeid_left x) = tag_nodeid_left (G.s ' x) /\
       G'0.t ' (tag_edgeid_left x) = tag_nodeid_left (G.t ' x)` by
        (res_tac >> gvs[]) >>
      `G'0.s ' (tag_edgeid_right x') =
         tag_nodeid_left (m.nodemap ' (rhs'.s ' x')) /\
       G'0.t ' (tag_edgeid_right x') =
         tag_nodeid_left (m.nodemap ' (rhs'.t ' x'))` by
        (res_tac >> gvs[]) >>
      `G.s ' x = m.nodemap ' (rhs'.s ' x') /\
       G.t ' x = m.nodemap ' (rhs'.t ' x')` by
        gvs[tag_nodeid_left_11] >>
      `x' = edgeid "e0" \/ x' = edgeid "e1" \/ x' = edgeid "e2"` by
        (qpat_x_assum `rhs'.E = _` SUBST_ALL_TAC >> fs[IN_INSERT]) >>
      gvs[] >>
      ((fs[parallel_free_extension_def] >> metis_tac[]) ORELSE
       (fs[pathTheory.has_edge_def] >> metis_tac[])))
  (* ---- Case 3: (right, left) ---- *)
  >- (`x' IN G.E` by metis_tac[SUBSET_DEF] >>
      `G'0.s ' (tag_edgeid_right x) =
         tag_nodeid_left (m.nodemap ' (rhs'.s ' x)) /\
       G'0.t ' (tag_edgeid_right x) =
         tag_nodeid_left (m.nodemap ' (rhs'.t ' x))` by
        (res_tac >> gvs[]) >>
      `G'0.s ' (tag_edgeid_left x') = tag_nodeid_left (G.s ' x') /\
       G'0.t ' (tag_edgeid_left x') = tag_nodeid_left (G.t ' x')` by
        (res_tac >> gvs[]) >>
      `G.s ' x' = m.nodemap ' (rhs'.s ' x) /\
       G.t ' x' = m.nodemap ' (rhs'.t ' x)` by
        gvs[tag_nodeid_left_11] >>
      `x = edgeid "e0" \/ x = edgeid "e1" \/ x = edgeid "e2"` by
        (qpat_x_assum `rhs'.E = _` SUBST_ALL_TAC >> fs[IN_INSERT]) >>
      gvs[] >>
      ((`m.edgemap ' (edgeid "e0") NOTIN FRANGE track_bar.edgemap` by
          (simp[FRANGE_DEF] >> Q.X_GEN_TAC `y` >> rpt strip_tac >>
           first_x_assum (qspec_then `y` mp_tac) >>
           `y IN G0.E` by metis_tac[] >>
           `track_bar.edgemap ' y IN deletion_deleted_edges lhs' m` by
             metis_tac[] >> simp[]) >>
        fs[parallel_free_extension_def] >> metis_tac[]) ORELSE
       (`m.edgemap ' (edgeid "e1") NOTIN FRANGE track_bar.edgemap` by
          (simp[FRANGE_DEF] >> Q.X_GEN_TAC `y` >> rpt strip_tac >>
           first_x_assum (qspec_then `y` mp_tac) >>
           `y IN G0.E` by metis_tac[] >>
           `track_bar.edgemap ' y IN deletion_deleted_edges lhs' m` by
             metis_tac[] >> simp[]) >>
        fs[parallel_free_extension_def] >> metis_tac[]) ORELSE
       (fs[pathTheory.has_edge_def] >> metis_tac[])))
  (* ---- Case 4: (right, right) ---- *)
  >- (`x <> x'` by
        (strip_tac >> gvs[] >>
         metis_tac[taggingTheory.INJ_tag_edgeid, INJ_DEF]) >>
      `G'0.s ' (tag_edgeid_right x) =
         tag_nodeid_left (m.nodemap ' (rhs'.s ' x)) /\
       G'0.t ' (tag_edgeid_right x) =
         tag_nodeid_left (m.nodemap ' (rhs'.t ' x))` by
        (res_tac >> gvs[]) >>
      `G'0.s ' (tag_edgeid_right x') =
         tag_nodeid_left (m.nodemap ' (rhs'.s ' x')) /\
       G'0.t ' (tag_edgeid_right x') =
         tag_nodeid_left (m.nodemap ' (rhs'.t ' x'))` by
        (res_tac >> gvs[]) >>
      `m.nodemap ' (rhs'.s ' x) = m.nodemap ' (rhs'.s ' x') /\
       m.nodemap ' (rhs'.t ' x) = m.nodemap ' (rhs'.t ' x')` by
        gvs[tag_nodeid_left_11] >>
      `x = edgeid "e0" \/ x = edgeid "e1" \/ x = edgeid "e2"` by
        (qpat_x_assum `rhs'.E = _` SUBST_ALL_TAC >> fs[IN_INSERT]) >>
      `x' = edgeid "e0" \/ x' = edgeid "e1" \/ x' = edgeid "e2"` by
        (qpat_x_assum `rhs'.E = _` SUBST_ALL_TAC >> fs[IN_INSERT]) >>
      gvs[] >>
      TRY (
        qpat_assum `INJ ($' m.nodemap) _ _` (fn th =>
          mp_tac (Q.SPECL [`nodeid "n0"`, `nodeid "n1"`]
            (CONJUNCT2 (REWRITE_RULE [INJ_DEF] th)))) >>
        impl_tac >- metis_tac[IN_INSERT, NOT_IN_EMPTY] >>
        simp[]) >>
      TRY (
        qpat_assum `INJ ($' m.nodemap) _ _` (fn th =>
          mp_tac (Q.SPECL [`nodeid "n1"`, `nodeid "n2"`]
            (CONJUNCT2 (REWRITE_RULE [INJ_DEF] th)))) >>
        impl_tac >- metis_tac[IN_INSERT, NOT_IN_EMPTY] >>
        simp[]))
QED

(* Helper: instantiate_rule success implies NAC: no edge n0->n2 *)
Theorem link_rule_NAC_no_edge:
  !assign m G inst.
    wf_hostgraph G /\
    FDOM m.nodemap = rule_link.lhs.V /\
    instantiate_rule rule_link assign m G = SOME inst ==>
    ~has_edge G (m.nodemap ' (nodeid "n0")) (m.nodemap ' (nodeid "n2"))
Proof
  rpt strip_tac >> fs[pathTheory.has_edge_def] >>
  `eval_rule_condition rule_link assign m G = SOME T` by
    (fs[semTheory.instantiate_rule_def] >> gvs[AllCaseEqs()]) >>
  qpat_x_assum `eval_rule_condition _ _ _ _ = _` mp_tac >>
  `rule_link.cond =
     SOME (condNot (condEdgeTest (nodeid "n0") (nodeid "n2") NONE))` by
    EVAL_TAC >>
  simp[semTheory.eval_rule_condition_def,
       semTheory.eval_condition_fun_def] >>
  `FINITE G.E` by fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
  simp[listTheory.EXISTS_MEM, listTheory.MEM_SET_TO_LIST] >>
  qexists_tac `e` >> simp[] >>
  `FDOM G.s = G.E /\ FDOM G.t = G.E` by
    fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
  `nodeid "n0" IN FDOM m.nodemap /\ nodeid "n2" IN FDOM m.nodemap` by
    (gvs[] >> EVAL_TAC) >>
  gvs[FLOOKUP_DEF]
QED

(* Step 2: link preserves the invariant *)
Theorem link_preserves_invariant:
  !G0 G track_bar m0 G' m'.
    wf_hostgraph G0 /\
    tc_loop_invariant_total G0 G track_bar /\
    extends_morphism m0 track_bar /\
    step program (running (term_rscall {ruleid "link"}), [(G, id_track G)])
                 (final, [(G', m')]) ==>
    ?track_bar'. tc_loop_invariant_total G0 G' track_bar' /\
                 extends_morphism (compose_morphism m' m0) track_bar'
Proof
  rpt strip_tac >> fs[tc_loop_invariant_total_def] >>
  (* Destructure the step *)
  qpat_x_assum `step _ _ _` mp_tac >>
  simp[Once semTheory.step_cases] >> strip_tac >>
  gvs[stackTheory.push_stack_def, stackTheory.pop_stack_def,
      trackTheory.id_track_def] >>
  `r = rule_link` by
    gvs[program_def, finite_mapTheory.FUPDATE_LIST_THM,
        finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[semTheory.apply_ruleinstance_def, semTheory.instantiate_rule_def] >>
  (* Structural facts from instantiate_rulegraph *)
  `lhs'.V = rule_link.lhs.V` by
    metis_tac[semTheory.instantiate_rulegraph_preserves_V] >>
  `rhs'.V = rule_link.rhs.V` by
    metis_tac[semTheory.instantiate_rulegraph_preserves_V] >>
  `lhs'.E = rule_link.lhs.E /\ lhs'.s = rule_link.lhs.s /\
   lhs'.t = rule_link.lhs.t` by
    metis_tac[semTheory.instantiate_rulegraph_preserves_structure] >>
  `rhs'.E = rule_link.rhs.E /\ rhs'.s = rule_link.rhs.s /\
   rhs'.t = rule_link.rhs.t` by
    metis_tac[semTheory.instantiate_rulegraph_preserves_structure] >>
  `hostgraph_labels_spine G` by
    metis_tac[hostgraphTheory.wf_hostgraph_IMP_hostgraph_labels_spine] >>
  `wf_assignment_spine assign` by
    (irule semTheory.mk_assignment_wf_assignment_spine >> metis_tac[]) >>
  `wf_hostgraph lhs'` by
    (irule semTheory.instantiate_rulegraph_wf >>
     qexistsl [`G`, `assign`, `m`, `rule_link.lhs`] >> simp[] >>
     totally_labelled_tac) >>
  `wf_hostgraph rhs'` by
    (irule semTheory.instantiate_rulegraph_wf >>
     qexistsl [`G`, `assign`, `m`, `rule_link.rhs`] >> simp[] >>
     totally_labelled_tac) >>
  `instantiate_rule rule_link assign m G =
     SOME <|lhs := lhs'; inf := rule_link.inf; rhs := rhs'|>` by
    simp[semTheory.instantiate_rule_def] >>
  sg `is_match lhs' rule_link.inf m G`
  >- (`wf_rule rule_link` by simp[wf_rule_link] >>
      `wf_rulegraph_labels rule_link.lhs` by fs[ruleTheory.wf_rule_def] >>
      drule_all semTheory.prematch_instantiation_is_match >> simp[])
  >- (
  `wf_hostgraph (dpo lhs' rule_link.inf rhs' m G)` by
    (irule dpoTheory.wf_dpo >> simp[] >> gvs[] >> EVAL_TAC) >>
  `FINITE G0.E` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  `link_step_context G0 G track_bar lhs' rhs' m` by
    (simp[link_step_context_def] >> gvs[]) >>
  (* Establish unrooted_hostgraph for DPO result (needed by preserve_rootedness) *)
  sg `unrooted_hostgraph (dpo lhs' rule_link.inf rhs' m G)`
  >- (simp[hostgraphTheory.unrooted_hostgraph_def, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
      qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
      qabbrev_tac `Vg = gluing_nodes D rule_link.inf rhs'` >>
      sg `FINITE Vg`
      >- (simp[Abbr `Vg`, dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >>
          `FINITE rule_link.rhs.V` by EVAL_TAC >>
          `FINITE D.V` by (simp[Abbr `D`, dpoTheory.deletion_def, dpoTheory.deletion_remaining_nodes_def] >>
                           fs wf_rwts) >> simp[])
      >- (`FDOM (gluing_p Vg rule_link.inf m D rhs') = Vg` by simp[trackTheory.FDOM_gluing_p] >> simp[] >>
          sg `FEVERY (\(nid,b). b <=> F) (gluing_p Vg rule_link.inf m D rhs')`
          >- (irule dpoTheory.gluing_p_unrooted >> rpt conj_tac
              >- (rpt strip_tac >> `rhs'.V DIFF rule_link.inf = {}` by (gvs[] >> EVAL_TAC) >>
                  `Vg = IMAGE tag_nodeid_left D.V`
                    by simp[Abbr `Vg`, dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >>
                  `is_left_tagged_nodeid n` by (gvs[IN_IMAGE] >> metis_tac[taggingTheory.correct_tagging]))
              >- (sg `unrooted_hostgraph rhs'`
                  >- (`FDOM rule_link.rhs.p = rule_link.rhs.V` by EVAL_TAC >>
                      sg `!n. n IN rule_link.rhs.V ==> (rule_link.rhs.p ' n <=> F)`
                      >- (rpt strip_tac >> `rule_link.rhs.V = {nodeid "n0"; nodeid "n1"; nodeid "n2"}`
                            by EVAL_TAC >> gvs[] >> EVAL_TAC)
                      >- (drule_all semTheory.instantiate_rulegraph_unrooted >> simp[]))
                  >- (rpt strip_tac >> `rule_link.inf = rhs'.V` by (gvs[] >> EVAL_TAC) >>
                      `FDOM rhs'.p = rhs'.V` by fs[unrooted_hostgraph_def] >> gvs[] >>
                      SELECT_ELIM_TAC >> rpt conj_tac >- metis_tac[] >- simp[]))
              >- (rpt strip_tac >> simp[Abbr `D`, dpoTheory.deletion_def, FDOM_DRESTRICT] >>
                  `rule_link.lhs.V DIFF rule_link.inf = {}` by (gvs[] >> EVAL_TAC) >>
                  simp[dpoTheory.deletion_remaining_nodes_def, dpoTheory.deletion_deleted_nodes_def] >>
                  rpt conj_tac
                  >- (`FDOM G.p = G.V` by fs[unrooted_hostgraph_def] >> gvs[] >>
                      `rhs'.V DIFF rule_link.inf = {}` by (gvs[] >> EVAL_TAC) >>
                      `Vg = IMAGE tag_nodeid_left (deletion lhs' rule_link.inf m G).V`
                        by (simp[Abbr `Vg`, dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >> gvs[]) >>
                      `(deletion lhs' rule_link.inf m G).V = G.V`
                        by simp[dpoTheory.deletion_def, dpoTheory.deletion_remaining_nodes_def,
                                dpoTheory.deletion_deleted_nodes_def] >>
                      gvs[IN_IMAGE] >> metis_tac[taggingTheory.tag_untag_nodeid_inv])
                  >- (simp[dpoTheory.deletion_relabling_nodes_def, dpoTheory.deletion_remaining_nodes_def,
                           dpoTheory.deletion_deleted_nodes_def] >>
                      `rule_link.lhs.V = rule_link.inf` by (gvs[] >> EVAL_TAC) >> rpt conj_tac
                      >- (`rhs'.V DIFF rule_link.inf = {}` by (gvs[] >> EVAL_TAC) >>
                          `Vg = IMAGE tag_nodeid_left (deletion lhs' rule_link.inf m G).V`
                            by simp[Abbr `Vg`, dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >>
                          `(deletion lhs' rule_link.inf m G).V = G.V`
                            by simp[dpoTheory.deletion_def, dpoTheory.deletion_remaining_nodes_def,
                                    dpoTheory.deletion_deleted_nodes_def] >>
                          gvs[IN_IMAGE] >> metis_tac[taggingTheory.tag_untag_nodeid_inv])
                      >- (rpt strip_tac >> CCONTR_TAC >> fs[] >> first_x_assum (qspec_then `x` mp_tac) >> simp[])))
              >- (rpt strip_tac >> simp[Abbr `D`, dpoTheory.deletion_def, DRESTRICT_DEF] >>
                  `FDOM G.p = G.V` by fs[unrooted_hostgraph_def] >>
                  `!n. n IN G.V ==> (G.p ' n <=> F)` by fs[unrooted_hostgraph_def] >>
                  gvs[FDOM_DRESTRICT] >> DISJ1_TAC >>
                  `n IN FDOM (deletion lhs' rule_link.inf m G).p` by gvs[] >>
                  fs[dpoTheory.deletion_def, FDOM_DRESTRICT])
              >- (`FDOM rule_link.rhs.p = rule_link.rhs.V` by EVAL_TAC >>
                  `!n. n IN rule_link.rhs.V ==> (rule_link.rhs.p ' n <=> F)`
                    by (rpt strip_tac >> `rule_link.rhs.V = {nodeid "n0"; nodeid "n1"; nodeid "n2"}`
                          by EVAL_TAC >> gvs[] >> EVAL_TAC) >>
                  `unrooted_hostgraph rhs'` by (drule_all semTheory.instantiate_rulegraph_unrooted >> simp[]) >>
                  fs[unrooted_hostgraph_def])
              >- (simp[Abbr `Vg`, dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >>
                  simp[Abbr `D`, dpoTheory.deletion_def, dpoTheory.deletion_remaining_nodes_def] >>
                  `FINITE G.V` by fs wf_rwts >>
                  `FINITE rule_link.rhs.V` by EVAL_TAC >> simp[]))
          >- (rpt strip_tac >> fs[FEVERY_DEF] >> first_x_assum (qspec_then `n` mp_tac) >> simp[])))
  >- (
  (* Witness the new track_bar *)
  qexists_tac `link_new_track_bar G0 track_bar lhs' m G` >>
  conj_tac
  >- (
    simp[] >> rpt conj_tac
    (* === unmarked_hostgraph === *)
    >- (simp[hostgraphTheory.unmarked_hostgraph_def] >> rpt conj_tac
        (* nodes_unmarked *)
        >- (simp[hostgraphTheory.nodes_unmarked_def, dpoTheory.dpo_def,
                 dpoTheory.gluing_def] >>
            qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
            irule dpoTheory.gluing_l_unmarked >> rpt conj_tac
            >- (rpt strip_tac >> `rhs'.V DIFF rule_link.inf = {}` by (gvs[] >> EVAL_TAC) >>
                `gluing_nodes D rule_link.inf rhs' = IMAGE tag_nodeid_left D.V`
                  by simp[dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >>
                `is_left_tagged_nodeid n` by (gvs[IN_IMAGE] >> metis_tac[taggingTheory.correct_tagging]))
            >- (rpt strip_tac >> `rule_link.inf = rhs'.V` by (gvs[] >> EVAL_TAC) >>
                `FDOM rhs'.l = rhs'.V` by fs wf_rwts >> gvs[] >>
                SELECT_ELIM_TAC >> rpt conj_tac >- metis_tac[] >- simp[])
            >- (rpt strip_tac >> `rhs'.V DIFF rule_link.inf = {}` by (gvs[] >> EVAL_TAC) >>
                `gluing_nodes D rule_link.inf rhs' = IMAGE tag_nodeid_left D.V`
                  by simp[dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >>
                `untag_nodeid n IN D.V` by (gvs[IN_IMAGE] >> metis_tac[taggingTheory.tag_untag_nodeid_inv]) >>
                simp[Abbr `D`, dpoTheory.deletion_def, FDOM_DRESTRICT] >> rpt conj_tac
                >- (sg `(deletion lhs' rule_link.inf m G).V = G.V`
                    >- (simp[dpoTheory.deletion_def, dpoTheory.deletion_remaining_nodes_def,
                             dpoTheory.deletion_deleted_nodes_def] >>
                        `rule_link.lhs.V DIFF rule_link.inf = {}` by (gvs[] >> EVAL_TAC) >> simp[])
                    >- (`FDOM G.l = G.V` by fs wf_rwts >> gvs[]))
                >- (simp[dpoTheory.deletion_relabling_nodes_def, dpoTheory.deletion_remaining_nodes_def,
                         dpoTheory.deletion_deleted_nodes_def] >>
                    `rule_link.lhs.V = rule_link.inf` by (gvs[] >> EVAL_TAC) >> rpt conj_tac
                    >- (gvs[] >> `(deletion lhs' rule_link.inf m G).V SUBSET G.V`
                          by simp[dpoTheory.deletion_def, dpoTheory.deletion_remaining_nodes_def] >>
                        fs[SUBSET_DEF])
                    >- gvs[]
                    >- (rpt strip_tac >> CCONTR_TAC >> gvs[] >> metis_tac[])))
            >- (simp[Abbr `D`, dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def,
                     dpoTheory.deletion_def, dpoTheory.deletion_remaining_nodes_def] >>
                `FINITE G.V` by fs wf_rwts >> simp[] >>
                `FINITE rule_link.rhs.V` by EVAL_TAC >> simp[])
            >- (simp[Abbr `D`, dpoTheory.deletion_def, FEVERY_DEF, FDOM_DRESTRICT, DRESTRICT_DEF] >>
                rpt strip_tac >> fs[unmarked_hostgraph_def, hostgraphTheory.nodes_unmarked_def, FEVERY_DEF] >>
                metis_tac[])
            >- (simp[FEVERY_DEF, FRANGE_FUPDATE, FDOM_FUPDATE, FAPPLY_FUPDATE_THM] >> EVAL_TAC >> simp[] >>
                sg `FEVERY (IS_NONE o SND o SND) rhs'.l`
                >- (`FEVERY (\(x,l,mk). mk = NONE) rule_link.rhs.l`
                      by (simp[FEVERY_DEF, FDOM_FUPDATE, FAPPLY_FUPDATE_THM] >> EVAL_TAC >> rpt strip_tac >> gvs[]) >>
                    `FEVERY (\(x,l,mk). mk = NONE) rule_link.rhs.m`
                      by (simp[FEVERY_DEF, FDOM_FUPDATE, FAPPLY_FUPDATE_THM] >> EVAL_TAC >> rpt strip_tac >> gvs[]) >>
                    `FEVERY (IS_NONE o SND o SND) rhs'.l /\ FEVERY (IS_NONE o SND o SND) rhs'.m`
                      by (drule_all semTheory.instantiate_rulegraph_unmarked >> simp[]))
                >- fs[FEVERY_DEF]))
        (* edges_unmarked *)
        >- (simp[hostgraphTheory.edges_unmarked_def, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
            irule dpoTheory.gluing_m_unmarked >> rpt conj_tac
            >- (rpt strip_tac >> gvs[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def]
                >- (simp[dpoTheory.deletion_def, FDOM_DRESTRICT] >> fs[dpoTheory.deletion_def] >>
                    `FDOM G.m = G.E` by fs wf_rwts >>
                    `deletion_remaining_edges lhs' m G SUBSET G.E`
                      by simp[dpoTheory.deletion_remaining_edges_def] >> gvs[SUBSET_DEF])
                >- (`~is_left_tagged_edgeid (tag_edgeid_right x)`
                      by metis_tac[taggingTheory.correct_tagging, taggingTheory.is_left_tagged_edgeid_def,
                                   taggingTheory.is_right_tagged_edgeid_def, arithmeticTheory.ODD_EVEN]))
            >- (rpt strip_tac >> gvs[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def]
                >- (`is_left_tagged_edgeid (tag_edgeid_left x)` by metis_tac[taggingTheory.correct_tagging])
                >- (`FDOM rhs'.m = rhs'.E` by fs wf_rwts >> gvs[]))
            >- (simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def, dpoTheory.deletion_def,
                     dpoTheory.deletion_remaining_edges_def] >>
                `FINITE G.E` by fs wf_rwts >>
                `FINITE rhs'.E` by fs wf_rwts >>
                `FINITE rule_link.rhs.E` by EVAL_TAC >> simp[])
            >- (simp[dpoTheory.deletion_def, FEVERY_DEF, FDOM_DRESTRICT, DRESTRICT_DEF] >>
                rpt strip_tac >> fs[unmarked_hostgraph_def, hostgraphTheory.edges_unmarked_def, FEVERY_DEF])
            >- (`FEVERY (\(x,l,mk). mk = NONE) rule_link.rhs.l`
                  by (simp[FEVERY_DEF, FDOM_FUPDATE, FAPPLY_FUPDATE_THM] >> EVAL_TAC >> rpt strip_tac >> gvs[]) >>
                `FEVERY (\(x,l,mk). mk = NONE) rule_link.rhs.m`
                  by (simp[FEVERY_DEF, FDOM_FUPDATE, FAPPLY_FUPDATE_THM] >> EVAL_TAC >> rpt strip_tac >> gvs[]) >>
                drule_all semTheory.instantiate_rulegraph_unmarked >> simp[])))
    (* === minimal_extension === *)
    >- (simp[minimal_extension_def] >> rpt conj_tac
        (* is_inj_morphism: establish all sub-facts then close *)
        >- (`morphism_dom_ran G0 (link_new_track_bar G0 track_bar lhs' m G)
               (dpo lhs' rule_link.inf rhs' m G)` by
              (irule link_step_morphism_dom_ran >> simp[]) >>
            `preserve_source G0 (link_new_track_bar G0 track_bar lhs' m G)
               (dpo lhs' rule_link.inf rhs' m G) /\
             preserve_target G0 (link_new_track_bar G0 track_bar lhs' m G)
               (dpo lhs' rule_link.inf rhs' m G)` by
              (drule_all link_step_preserve_st >> simp[]) >>
            `preserve_defined_rootedness G0 (link_new_track_bar G0 track_bar lhs' m G)
               (dpo lhs' rule_link.inf rhs' m G)` by
              (irule link_step_preserve_rootedness >> simp[]) >>
            `preserve_edgelabels lhs' m G` by
              (`wf_rule rule_link` by simp[wf_rule_link] >>
               `wf_rulegraph_labels rule_link.lhs` by fs[ruleTheory.wf_rule_def] >>
               drule_all semTheory.mk_assignment_preserves_edgelabels >> simp[]) >>
            `rhs'.m ' (edgeid "e0") = lhs'.m ' (edgeid "e0") /\
             rhs'.m ' (edgeid "e1") = lhs'.m ' (edgeid "e1")` by
              (irule link_lhs_rhs_shared_edgelabels >> metis_tac[]) >>
            `preserve_nodelabels lhs' m G` by
              (`wf_rule rule_link` by simp[wf_rule_link] >>
               `wf_rulegraph_labels rule_link.lhs` by fs[ruleTheory.wf_rule_def] >>
               drule_all semTheory.mk_assignment_preserves_nodelabels >> simp[]) >>
            `!k. k IN rule_link.inf ==> rhs'.l ' k = lhs'.l ' k` by
              (rpt strip_tac >> irule link_lhs_rhs_shared_nodelabels >> metis_tac[]) >>
            `preserve_edgelabels G0 (link_new_track_bar G0 track_bar lhs' m G)
               (dpo lhs' rule_link.inf rhs' m G) /\
             preserve_nodelabels G0 (link_new_track_bar G0 track_bar lhs' m G)
               (dpo lhs' rule_link.inf rhs' m G)` by
              (drule_all link_step_preserves_labels >> simp[]) >>
            `BIJ ($' (link_new_track_bar G0 track_bar lhs' m G).nodemap) G0.V
               (dpo lhs' rule_link.inf rhs' m G).V` by
              (irule link_step_nodemap_BIJ >> simp[]) >>
            `INJ ($' (link_new_track_bar G0 track_bar lhs' m G).edgemap) G0.E
               (dpo lhs' rule_link.inf rhs' m G).E` by
              (irule link_step_edgemap_INJ >> simp[]) >>
            fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def] >>
            metis_tac[BIJ_DEF])
        (* BIJ *)
        >- (irule link_step_nodemap_BIJ >> simp[])
        (* edge_path_justified *)
        >- (irule link_step_reachability >> simp[])
        (* parallel_free_extension *)
        >- (irule link_step_parallel_free >> simp[] >>
            irule link_rule_NAC_no_edge >> simp[] >>
            `FDOM m.nodemap = lhs'.V` by fs match_morphism_rwts >> gvs[] >>
            qexists_tac `assign` >> simp[])))
  (* === extends_morphism === *)
  >- (
    simp[extends_morphism_def, link_new_track_bar_def] >>
    `<|nodemap := FUN_FMAP I G.V; edgemap := FUN_FMAP I G.E|> = id_track G`
      by simp[trackTheory.id_track_def] >> gvs[] >>
    `FINITE (deletion_remaining_nodes lhs' m rule_link.inf G) /\
     FINITE (deletion_remaining_edges lhs' m G)` by
      metis_tac[dpoTheory.wf_hostgraph_IMP_finite_remaining_elements] >>
    `compose_morphism (track lhs' rule_link.inf m G) (id_track G) =
     track lhs' rule_link.inf m G` by
      (irule trackTheory.compose_morphism_id_track_right >> simp[] >>
       simp[trackTheory.FDOM_track_nodemap, trackTheory.FDOM_track_edgemap] >>
       metis_tac[dpoTheory.deletion_remaining_elements_SUBSET_base]) >>
    gvs[] >>
    rpt conj_tac
    (* nodemap agreement *)
    >- (fs[extends_morphism_def, morphismTheory.compose_morphism_def])
    (* FDOM subset *)
    >- (simp[morphismTheory.compose_morphism_def, f_o_f_DEF] >>
        simp[SUBSET_DEF] >> rpt strip_tac >>
        `FDOM m0.edgemap SUBSET FDOM track_bar.edgemap` by fs[extends_morphism_def] >>
        `FDOM track_bar.edgemap = G0.E` by fs me_inj_rwts >>
        metis_tac[SUBSET_DEF])
    (* pointwise agreement *)
    >- (rpt strip_tac >>
        simp[morphismTheory.compose_morphism_def] >>
        `FDOM m0.edgemap SUBSET FDOM track_bar.edgemap` by fs[extends_morphism_def] >>
        `!e'. e' IN FDOM m0.edgemap ==> m0.edgemap ' e' = track_bar.edgemap ' e'`
          by fs[extends_morphism_def] >>
        `FDOM track_bar.edgemap = G0.E` by fs me_inj_rwts >>
        `e IN FDOM m0.edgemap` by
          (qpat_x_assum `e IN FDOM (compose_morphism _ _).edgemap` mp_tac >>
           simp[morphismTheory.compose_morphism_def, f_o_f_DEF]) >>
        `e IN G0.E` by metis_tac[SUBSET_DEF] >>
        `m0.edgemap ' e = track_bar.edgemap ' e` by metis_tac[] >>
        `FINITE G0.E` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
        simp[FUN_FMAP_DEF] >>
        `FINITE (deletion_remaining_edges lhs' m G)` by
          metis_tac[dpoTheory.wf_hostgraph_IMP_finite_remaining_elements] >>
        `FDOM (track lhs' rule_link.inf m G).edgemap =
         deletion_remaining_edges lhs' m G` by
          simp[trackTheory.FDOM_track_edgemap] >>
        `m0.edgemap ' e IN deletion_remaining_edges lhs' m G` by
          (qpat_x_assum `e IN FDOM (compose_morphism _ _).edgemap` mp_tac >>
           simp[morphismTheory.compose_morphism_def, f_o_f_DEF]) >>
        `track_bar.edgemap ' e IN deletion_remaining_edges lhs' m G` by gvs[] >>
        `track_bar.edgemap ' e NOTIN deletion_deleted_edges lhs' m` by
          fs[dpoTheory.deletion_remaining_edges_def] >>
        simp[] >>
        `((track lhs' rule_link.inf m G).edgemap f_o_f m0.edgemap) ' e =
         (track lhs' rule_link.inf m G).edgemap ' (m0.edgemap ' e)` by
          (irule (cj 2 f_o_f_DEF) >>
           simp[morphismTheory.compose_morphism_def, f_o_f_DEF] >>
           qpat_x_assum `e IN FDOM (compose_morphism _ _).edgemap` mp_tac >>
           simp[morphismTheory.compose_morphism_def, f_o_f_DEF]) >>
        gvs[] >>
        simp[trackTheory.track_def, LET_THM] >>
        simp[FUNION_DEF, FDOM_DRESTRICT, dpoTheory.deletion_def] >>
        simp[DRESTRICT_DEF] >>
        simp[FUN_FMAP_DEF]))))
QED

(* Step 3: Body either succeeds with invariant preserved, or fails *)
Theorem link_body_succeeds_or_fails:
  !G0 G track_bar m0 c.
    wf_hostgraph G0 /\
    tc_loop_invariant_total G0 G track_bar /\
    extends_morphism m0 track_bar /\
    steps program (running (term_rscall {ruleid "link"}), [(G, id_track G)]) c /\
    ~can_step c ==>
    (?H mH. c = (final, [(H, mH)]) /\
            ?track_bar'. tc_loop_invariant_total G0 H track_bar' /\
                         extends_morphism (compose_morphism mH m0) track_bar') \/
    (c = (failed, [(G, id_track G)]))
Proof
  rpt strip_tac >>
  `FEVERY (no_intermediate_terms o SND) program.proc` by
    simp[program_wf |> SIMP_RULE std_ss [programTheory.wf_program_def]] >>
  `no_intermediate_terms (term_rscall {ruleid "link"})` by EVAL_TAC >>
  `!x. (\(_,t). no_intermediate_terms t) x = (no_intermediate_terms o SND) x` by
    (Cases >> simp[]) >>
  `FEVERY (\(_,t). no_intermediate_terms t) program.proc` by
    (fs[finite_mapTheory.FEVERY_DEF] >> rw[] >> res_tac) >>
  drule_all_then strip_assume_tac semPropsTheory.steps_SINGLETON_STACK_FINAL
  (* Case 1: final - rule applied successfully *)
  >- (DISJ1_TAC >> gvs[] >> Cases_on `G'` >> qexistsl [`q`, `r`] >> simp[] >>
      `evaluate program G (term_rscall {ruleid "link"}) (q, r)` by
        (simp[semTheory.evaluate_def] >> qexists `[(q,r)]` >> simp[]) >>
      gvs[semPropsTheory.evaluate_rscall] >>
      sg `step program (running (term_rscall {ruleid "link"}), [(G, id_track G)])
               (final, [(q, compose_morphism (track ri.lhs ri.inf m G) (id_track G))])`
      >- (simp[Once semTheory.step_cases] >>
          qexistsl [`G`, `id_track G`, `[]`, `r'`, `m`, `q`, `ri`, `assign`] >>
          simp[stackTheory.push_stack_def, stackTheory.pop_stack_def])
      >- (irule_at Any link_preserves_invariant >>
          simp[] >> qexistsl [`G`, `track_bar`] >> simp[]))
  (* Case 2: failed - rule didn't apply *)
  >- (DISJ2_TAC >> gvs[] >>
      fs[semTheory.steps_def] >>
      `?n. NRC (step program) n
           (running (term_rscall {ruleid "link"}), [(G, id_track G)])
           (failed, [G'])` by metis_tac[arithmeticTheory.RTC_NRC] >>
      Cases_on `n` >> gvs[semTheory.can_step_def] >>
      gvs[arithmeticTheory.NRC] >>
      `?stk. z = (final, stk) \/ z = (failed, stk)` by
        (qpat_x_assum `step _ (running (term_rscall _), _) z` mp_tac >>
         simp[Once semTheory.step_cases] >> rpt strip_tac >> gvs[])
      >- (gvs[] >> Cases_on `n'` >> gvs[arithmeticTheory.NRC] >>
          qpat_x_assum `step _ (final, _) _` mp_tac >>
          simp[Once semTheory.step_cases])
      >- (gvs[] >>
          qpat_x_assum `step _ (running (term_rscall _), _) (failed, _)` mp_tac >>
          simp[Once semTheory.step_cases, stackTheory.pop_stack_def] >>
          strip_tac >> gvs[] >>
          Cases_on `n'` >> gvs[arithmeticTheory.NRC] >>
          qpat_x_assum `step _ (failed, _) _` mp_tac >>
          simp[Once semTheory.step_cases]))
  (* Case 3: running term_break - impossible for term_rscall *)
  >- (gvs[] >>
      `!c. step program (running (term_rscall {ruleid "link"}), [(G, id_track G)]) c
           ==> ?stk. c = (final, stk) \/ c = (failed, stk)` by
        (simp[Once semTheory.step_cases] >> rpt strip_tac >> gvs[]) >>
      fs[semTheory.steps_def, Once relationTheory.RTC_CASES1] >>
      first_x_assum drule >> strip_tac >> gvs[]
      >- (fs[Once relationTheory.RTC_CASES1] >>
          qpat_x_assum `step _ (final, _) _` mp_tac >>
          simp[Once semTheory.step_cases])
      >- (fs[Once relationTheory.RTC_CASES1] >>
          qpat_x_assum `step _ (failed, _) _` mp_tac >>
          simp[Once semTheory.step_cases]))
QED
(* Main correctness theorem *)
Theorem transitive_closure_correct:
  !G0. WSPEC program
    (\G. G = G0 /\ wf_hostgraph G0 /\ unmarked_hostgraph G0 /\ unrooted_hostgraph G0)
    (term_proc "Main")
    (\TC track. ?track_bar.
       is_transitive_closure_tracked G0 track_bar TC /\
       extends_morphism track track_bar)
Proof
  strip_tac >>
  irule gp2LogicTheory.WSPEC_proc >>
  qexists_tac `proc_Main` >> simp[program_def, FLOOKUP_UPDATE, FUPDATE_LIST] >>
  simp[proc_Main_def] >>
  simp[gp2LogicTheory.WSPEC_def] >>
  simp[SYM program_def, SYM proc_Main_def] >>
  conj_tac
  >- (simp[FUPDATE_LIST] >>
      `<|proc := FEMPTY |+ ("Main",proc_Main);
         rule := FEMPTY |+ (ruleid "link",rule_link)|> = program` by
        simp[program_def, FUPDATE_LIST] >>
      gvs[program_wf])
  >- (
    conj_tac >- simp[proc_Main_def, programTheory.no_intermediate_terms_def] >>
    `<|proc := FEMPTY |+ ("Main",proc_Main);
       rule := FEMPTY |+ (ruleid "link",rule_link)|> = program` by
      simp[program_def, FUPDATE_LIST] >>
    fs[] >> rpt strip_tac >> gvs[proc_Main_def] >>
    mp_tac (ISPECL [``program``,
                    ``term_rscall {ruleid "link"}``,
                    ``\G:hostgraph m:morphism.
                        ?track_bar. tc_loop_invariant_total G0 G track_bar /\
                                    extends_morphism m track_bar``,
                    ``\G:hostgraph m:morphism. is_transitive G``]
            gp2LogicTheory.WSPEC_alap_allowing_failure) >>
    simp[] >> impl_tac
    >- (rpt conj_tac
        >- simp[program_wf]
        >- EVAL_TAC
        >- (rpt strip_tac >> irule link_body_succeeds_or_fails >> simp[] >>
            metis_tac[])
        >- (rpt strip_tac >> irule no_link_implies_transitive >> simp[] >>
            fs[tc_loop_invariant_total_def] >>
            SPOSE_NOT_THEN strip_assume_tac >> fs[semTheory.steps_def] >>
            `?n. NRC (step program) n
                 (running (term_rscall {ruleid "link"}), [(G, id_track G)])
                 (failed, [(G, id_track G)])` by
              metis_tac[arithmeticTheory.RTC_NRC] >>
            Cases_on `n` >> gvs[arithmeticTheory.NRC] >> simp[] >>
            `?stk. z = (final, stk) \/ z = (failed, stk)` by
              (qpat_x_assum `step _ (running (term_rscall _), _) z` mp_tac >>
               simp[Once semTheory.step_cases] >> rpt strip_tac >> gvs[])
            >- (gvs[] >> Cases_on `n'` >> gvs[arithmeticTheory.NRC] >>
                qpat_x_assum `step _ (final, _) _` mp_tac >>
                simp[Once semTheory.step_cases])
            >- (gvs[] >>
                qpat_x_assum `step _ _ (failed, _)` mp_tac >>
                simp[Once semTheory.step_cases, stackTheory.pop_stack_def] >>
                rpt strip_tac >> gvs[] >>
                qpat_x_assum `step _ _ (final, _)` mp_tac >>
                simp[Once semTheory.step_cases, stackTheory.push_stack_def,
                     stackTheory.pop_stack_def] >>
                rpt strip_tac >> gvs[semTheory.apply_rule_def] >>
                metis_tac[]))
        >- (rpt strip_tac >>
            fs[tc_loop_invariant_total_def, extends_morphism_def,
               minimal_extension_def, is_inj_morphism_def, is_morphism_def,
               is_premorphism_def, morphism_dom_ran_def] >>
            irule SUBSET_TRANS >> qexists_tac `FRANGE track_bar.edgemap` >>
            simp[] >> simp[FRANGE_DEF, SUBSET_DEF] >> rpt strip_tac >>
            `x' IN FDOM track_bar.edgemap` by metis_tac[SUBSET_DEF] >>
            qexists_tac `x'` >> simp[] >> metis_tac[]))
    >- (
      `tc_loop_invariant_total G0 G0 (id_track G0)` by
        (irule (cj 1 tc_invariant_initial) >> simp[]) >>
      disch_tac >> first_x_assum (qspec_then `id_track G0` mp_tac) >>
      simp[gp2LogicTheory.WSPEC_def] >>
      strip_tac >> first_x_assum (qspecl_then [`G0`, `c`] mp_tac) >>
      impl_tac
      >- (simp[] >> qexists_tac `id_track G0` >> simp[] >>
          simp[extends_morphism_def])
      >- (strip_tac >> qexistsl [`H`, `m`] >> simp[] >>
          qexists_tac `track_bar` >>
          simp[is_transitive_closure_tracked_def,
               tc_loop_invariant_total_def] >>
          sg `compose_morphism m (id_track G0) = m`
          >- (irule trackTheory.compose_morphism_id_track_right >> simp[] >>
              mp_tac steps_to_stack_tracks >> disch_tac >>
              first_x_assum (qspecl_then [`program`,
                `term_rscall {ruleid "link"}`, `G0`, `H`, `m`] mp_tac) >>
              impl_tac >- (simp[program_wf] >> gvs[]) >>
              simp[semPropsTheory.stack_tracks_morphism_def,
                   trackTheory.is_track_morphism_def,
                   morphismTheory.partial_dom_ran_def])
          >- (gvs[] >> fs[tc_loop_invariant_total_def]))))
QED

val () = export_theory ()
