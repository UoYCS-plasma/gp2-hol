open HolKernel boolLib bossLib
open finite_mapTheory pred_setTheory
open programTheory programSyntax ruleTheory rulegraphTheory hostgraphTheory
open graphTheory typingTheory gp2LogicTheory pathTheory
open morphismTheory trackTheory semTheory stackTheory listTheory dpoTheory
open ruleAppPropsTheory

val () = new_theory "Transitive_closure"

val match_morphism_ss = [is_match_def, is_inj_morphism_def, is_morphism_def,
                         is_premorphism_def, morphism_dom_ran_def];
val match_source_ss = [is_match_def, is_inj_morphism_def, is_morphism_def,
                       is_premorphism_def, preserve_source_def];
val match_target_ss = [is_match_def, is_inj_morphism_def, is_morphism_def,
                       is_premorphism_def, preserve_target_def];
val match_inj_ss = [is_match_def, is_inj_morphism_def, is_inj_premorphism_def];
val wf_ss = [wf_hostgraph_def, wf_graph_def];

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
       has_main_entry_def, FLOOKUP_UPDATE, proc_Main_def]
  \\ simp[FEVERY_FUPDATE, FEVERY_FEMPTY, condition_break_def,
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

Definition minimally_extends_def:
  minimally_extends (G0: hostgraph) (m: morphism) (TC: hostgraph) <=>
    is_track_morphism G0 m TC /\
    FDOM m.nodemap = G0.V /\
    BIJ ($' m.nodemap) G0.V TC.V /\
    edge_path_justified G0 m TC
End

(* Pure agreement: track_bar extends track *)
Definition extends_morphism_def:
  extends_morphism (track: morphism) (track_bar: morphism) <=>
    track_bar.nodemap = track.nodemap /\
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

(* Paper Definition [Minimal extension] using the morphism hierarchy.
   is_inj_morphism provides: FDOM, FRANGE, INJ, source/target preservation,
   rootedness, label preservation.
   Additional conjuncts: BIJ on nodes, reachability for non-image edges,
   and no new parallel edges (from the NAC of link). *)
Definition minimal_extension_def:
  minimal_extension (G0: hostgraph) (track_bar: morphism) (TC: hostgraph) <=>
    is_inj_morphism G0 track_bar TC /\
    BIJ ($' track_bar.nodemap) G0.V TC.V /\
    edge_path_justified G0 track_bar TC /\
    parallel_free_extension track_bar TC
End

val me_inj_ss = [minimal_extension_def, is_inj_morphism_def, is_morphism_def,
                 is_premorphism_def, morphism_dom_ran_def];

(* Postcondition: only track_bar *)
Definition is_transitive_closure_tracked_def:
  is_transitive_closure_tracked (G0: hostgraph) (track_bar: morphism)
                                (TC: hostgraph) <=>
    is_transitive TC /\
    minimal_extension G0 track_bar TC
End

Definition tc_loop_invariant_def:
  tc_loop_invariant (G0: hostgraph) (H: hostgraph) (m: morphism) <=>
    wf_hostgraph H /\
    minimally_extends G0 m H /\
    unmarked_hostgraph H /\
    unrooted_hostgraph H
End

(* Loop invariant for track_bar: only track_bar *)
Definition tc_loop_invariant_total_def:
  tc_loop_invariant_total G0 G track_bar <=>
    wf_hostgraph G /\
    unmarked_hostgraph G /\
    unrooted_hostgraph G /\
    minimal_extension G0 track_bar G
End

(* Bridge theorem: extract pointwise facts from minimal_extension *)
Theorem minimal_extension_pointwise:
  !G0 track_bar TC.
    wf_hostgraph G0 /\ wf_hostgraph TC /\
    minimal_extension G0 track_bar TC ==>
    FDOM track_bar.nodemap = G0.V /\
    FDOM track_bar.edgemap = G0.E /\
    BIJ ($' track_bar.nodemap) G0.V TC.V /\
    INJ ($' track_bar.edgemap) G0.E TC.E /\
    FRANGE track_bar.nodemap SUBSET TC.V /\
    FRANGE track_bar.edgemap SUBSET TC.E /\
    (!e. e IN G0.E ==>
         track_bar.edgemap ' e IN FDOM TC.s /\
         track_bar.edgemap ' e IN FDOM TC.t /\
         TC.s ' (track_bar.edgemap ' e) = track_bar.nodemap ' (G0.s ' e) /\
         TC.t ' (track_bar.edgemap ' e) = track_bar.nodemap ' (G0.t ' e)) /\
    (!v. v IN FDOM G0.p ==>
         track_bar.nodemap ' v IN FDOM TC.p /\
         (TC.p ' (track_bar.nodemap ' v) <=> G0.p ' v)) /\
    preserve_edgelabels G0 track_bar TC /\
    preserve_nodelabels G0 track_bar TC
Proof
  rpt strip_tac >> fs[wf_hostgraph_def, wf_graph_def] >> fs me_inj_ss
  (* edgemap ' e IN TC.E (x2: for FDOM TC.s and FDOM TC.t) *)
  >- metis_tac[INJ_DEF]
  >- metis_tac[INJ_DEF]
  (* source preservation: pointwise from f_o_f *)
  >- (`G0.s ' e IN G0.V` by (fs[FRANGE_DEF, SUBSET_DEF] >> metis_tac[]) >>
      `e IN FDOM (track_bar.nodemap f_o_f G0.s)`
        by (rw[f_o_f_DEF] >> gvs[]) >>
      `(track_bar.nodemap f_o_f G0.s) ' e = track_bar.nodemap ' (G0.s ' e)`
        by metis_tac[cj 2 f_o_f_DEF] >>
      `e IN FDOM (TC'.s f_o_f track_bar.edgemap)`
        by (rw[f_o_f_DEF] >> gvs[INJ_DEF]) >>
      `(TC'.s f_o_f track_bar.edgemap) ' e =
       TC'.s ' (track_bar.edgemap ' e)`
        by metis_tac[cj 2 f_o_f_DEF] >>
      metis_tac[preserve_source_def])
  (* target preservation: pointwise from f_o_f *)
  >- (`G0.t ' e IN G0.V` by (fs[FRANGE_DEF, SUBSET_DEF] >> metis_tac[]) >>
      `e IN FDOM (track_bar.nodemap f_o_f G0.t)`
        by (rw[f_o_f_DEF] >> gvs[]) >>
      `(track_bar.nodemap f_o_f G0.t) ' e = track_bar.nodemap ' (G0.t ' e)`
        by metis_tac[cj 2 f_o_f_DEF] >>
      `e IN FDOM (TC'.t f_o_f track_bar.edgemap)`
        by (rw[f_o_f_DEF] >> gvs[INJ_DEF]) >>
      `(TC'.t f_o_f track_bar.edgemap) ' e =
       TC'.t ' (track_bar.edgemap ' e)`
        by metis_tac[cj 2 f_o_f_DEF] >>
      metis_tac[preserve_target_def])
  (* rootedness FDOM: from SUBMAP + f_o_f *)
  >- (fs[preserve_defined_rootedness_def, SUBMAP_DEF] >>
      `v IN FDOM (TC'.p f_o_f track_bar.nodemap)` by metis_tac[] >>
      gvs[f_o_f_DEF])
  (* rootedness value: from SUBMAP + f_o_f *)
  >- (fs[preserve_defined_rootedness_def, SUBMAP_DEF] >>
      `v IN FDOM (TC'.p f_o_f track_bar.nodemap)` by metis_tac[] >>
      `G0.p ' v = (TC'.p f_o_f track_bar.nodemap) ' v` by metis_tac[] >>
      `(TC'.p f_o_f track_bar.nodemap) ' v =
       TC'.p ' (track_bar.nodemap ' v)`
        by metis_tac[cj 2 f_o_f_DEF] >>
      gvs[])
QED

(* Proof Structure for Transitive Closure Correctness                        *)

(* -------------------------------------------------------------------------- *)
(* Auxiliary lemmas (many already proven in trackTheory)                      *)
(*                                                                            *)
(* From trackTheory:                                                          *)
(*   - id_track_is_track_morphism                                             *)
(*   - FDOM_id_track_nodemap, FDOM_id_track_edgemap                           *)
(*   - FRANGE_id_track_nodemap, FRANGE_id_track_edgemap                       *)
(*   - id_track_nodemap_BIJ, id_track_edgemap_BIJ                             *)
(*   - id_track_nodemap_apply, id_track_edgemap_apply                         *)
(*   - compose_is_track_morphism                                              *)
(* -------------------------------------------------------------------------- *)

(* No generated edges initially (all edges are in FRANGE of id_track) *)
Theorem id_track_no_generated_edges:
  !G. FINITE G.E ==> generated_edges (id_track G) G = {}
Proof
  rw[generated_edges_def, FRANGE_id_track_edgemap, DIFF_EQ_EMPTY]
QED

(* Trivially edge_path_justified when no generated edges *)
Theorem empty_generated_edges_justified:
  !G0 m G. generated_edges m G = {} ==> edge_path_justified G0 m G
Proof
  rw[edge_path_justified_def, NOT_IN_EMPTY]
QED

(* Trivially parallel_free when no generated edges *)
Theorem no_generated_parallel_free:
  !m TC. generated_edges m TC = {} ==> parallel_free_extension m TC
Proof
  simp[parallel_free_extension_def, generated_edges_def, EXTENSION,
       NOT_IN_EMPTY] >> metis_tac[]
QED

(* -------------------------------------------------------------------------- *)
(* Step 1: Initial state satisfies the loop invariant with identity morphism *)
(* -------------------------------------------------------------------------- *)

Theorem tc_invariant_initial:
  !G0. wf_hostgraph G0 /\ unmarked_hostgraph G0 /\ unrooted_hostgraph G0 ==>
       tc_loop_invariant G0 G0 (id_track G0)
Proof
  rw[tc_loop_invariant_def, minimally_extends_def] >>
  `FINITE G0.V /\ FINITE G0.E` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  rpt conj_tac
  (* is_track_morphism G0 (id_track G0) G0 *)
  >- (irule id_track_is_track_morphism >> fs[wf_hostgraph_def])
  (* FDOM (id_track G0).nodemap = G0.V *)
  >- simp[FDOM_id_track_nodemap]
  (* BIJ ($' (id_track G0).nodemap) G0.V G0.V *)
  >- simp[id_track_nodemap_BIJ]
  (* edge_path_justified G0 (id_track G0) G0 *)
  >- (irule empty_generated_edges_justified >> simp[id_track_no_generated_edges])
QED

(* -------------------------------------------------------------------------- *)
(* Step 2: The link rule preserves the loop invariant                         *)
(*         When link applies, it adds an edge for a path of length 2          *)
(*                                                                            *)
(* Key insight: m' is the track morphism COMPUTED by the step semantics,      *)
(* not an arbitrary morphism. It tracks exactly how the DPO rewrite           *)
(* transformed G into G'.                                                     *)
(* -------------------------------------------------------------------------- *)

(* Helper: edges in G have reachable preimages in G0 *)
Theorem edge_in_G_has_reachable_preimages:
  !G0 m G e.
    minimally_extends G0 m G /\ wf_hostgraph G0 /\ wf_hostgraph G /\
    e IN G.E ==>
    ?v0 w0. v0 IN G0.V /\ w0 IN G0.V /\
            m.nodemap ' v0 = G.s ' e /\
            m.nodemap ' w0 = G.t ' e /\
            reachable_in G0 v0 w0
Proof
  rpt strip_tac >>
  fs[minimally_extends_def] >>
  Cases_on `e IN generated_edges m G`
  (* Case 1: e is a generated edge - use edge_path_justified *)
  >- (fs[edge_path_justified_def] >>
      first_x_assum (qspec_then `e` mp_tac) >> simp[])
  (* Case 2: e is in FRANGE m.edgemap - use track morphism properties *)
  >- (fs[generated_edges_def] >>
      `e IN FRANGE m.edgemap` by gvs[] >>
      fs[FRANGE_DEF] >>
      rename1 `m.edgemap ' e0 = e` >>
      `e0 IN G0.E` by
        (fs[trackTheory.is_track_morphism_def, morphismTheory.partial_dom_ran_def,
            SUBSET_DEF] >> metis_tac[]) >>
      `G0.s ' e0 IN G0.V /\ G0.t ' e0 IN G0.V` by
        (fs (wf_ss @ [FRANGE_DEF, SUBSET_DEF]) >> metis_tac[]) >>
      `G.s f_o_f m.edgemap SUBMAP m.nodemap f_o_f G0.s` by
        fs[trackTheory.is_track_morphism_def, morphismTheory.partial_preserve_source_def] >>
      `G.t f_o_f m.edgemap SUBMAP m.nodemap f_o_f G0.t` by
        fs[trackTheory.is_track_morphism_def, morphismTheory.partial_preserve_target_def] >>
      sg `G.s ' e = m.nodemap ' (G0.s ' e0)` >-
        (fs[SUBMAP_DEF] >>
         `e0 IN FDOM (G.s f_o_f m.edgemap)` by
           (simp[f_o_f_DEF] >> fs wf_ss >>
            `m.edgemap ' e0 IN G.E` by
              (fs[trackTheory.is_track_morphism_def, morphismTheory.partial_dom_ran_def,
                  FRANGE_DEF, SUBSET_DEF] >> metis_tac[]) >>
            metis_tac[SUBSET_DEF]) >>
         first_x_assum drule >> strip_tac >> gvs[f_o_f_DEF]) >>
      sg `G.t ' e = m.nodemap ' (G0.t ' e0)` >-
        (fs[SUBMAP_DEF] >>
         `e0 IN FDOM (G.t f_o_f m.edgemap)` by
           (simp[f_o_f_DEF] >> fs wf_ss >>
            `m.edgemap ' e0 IN G.E` by
              (fs[trackTheory.is_track_morphism_def, morphismTheory.partial_dom_ran_def,
                  FRANGE_DEF, SUBSET_DEF] >> metis_tac[]) >>
            metis_tac[SUBSET_DEF]) >>
         first_x_assum drule >> strip_tac >> gvs[f_o_f_DEF]) >>
      qexistsl [`G0.s ' e0`, `G0.t ' e0`] >> simp[] >>
      (* Adjacent nodes are reachable *)
      irule has_edge_imp_reachable_in >>
      conj_tac >- fs[wf_hostgraph_IMP_wf_graph] >>
      simp[has_edge_def] >> qexists_tac `e0` >> simp[] >>
      fs wf_ss)
QED

(* Helper: for link rule, dpo.V = IMAGE tag_nodeid_left G.V *)
Theorem link_dpo_V:
  !lhs' rhs' m G.
    lhs'.V = rule_link.lhs.V /\ rhs'.V = rule_link.rhs.V ==>
    (dpo lhs' rule_link.inf rhs' m G).V = IMAGE tag_nodeid_left G.V
Proof
  rpt strip_tac >>
  simp[dpoTheory.dpo_def, dpoTheory.gluing_def, dpoTheory.gluing_nodes_def,
       dpoTheory.nodeid_coprod_def] >>
  `rule_link.rhs.V DIFF rule_link.inf = {}` by EVAL_TAC >>
  `deletion_remaining_nodes lhs' m rule_link.inf G = G.V` by
    (simp[dpoTheory.deletion_remaining_nodes_def, dpoTheory.deletion_deleted_nodes_def] >>
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
  gvs[] >>
  simp[BIJ_DEF, INJ_DEF, SURJ_DEF] >>
  rpt conj_tac
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
Theorem match_preserves_source_apply:
  !m L Kv G e n.
    is_match L Kv m G /\ wf_hostgraph G /\ e IN L.E /\ L.s ' e = n ==>
    G.s ' (m.edgemap ' e) = m.nodemap ' n
Proof
  rpt strip_tac >>
  `m.nodemap f_o_f L.s = G.s f_o_f m.edgemap` by fs match_source_ss >>
  `FDOM m.edgemap = L.E` by fs match_morphism_ss >>
  `FRANGE m.edgemap SUBSET G.E` by fs match_morphism_ss >>
  `m.edgemap ' e IN G.E` by (fs[FRANGE_DEF, SUBSET_DEF] >> metis_tac[]) >>
  `e IN FDOM (G.s f_o_f m.edgemap)` by (simp[cj 1 f_o_f_DEF] >> fs wf_ss) >>
  `(G.s f_o_f m.edgemap) ' e = G.s ' (m.edgemap ' e)` by
    (irule (cj 2 f_o_f_DEF |> SPEC_ALL) >> simp[]) >>
  `FDOM (m.nodemap f_o_f L.s) = FDOM (G.s f_o_f m.edgemap)` by
    metis_tac[fmap_EQ_THM] >>
  `e IN FDOM (m.nodemap f_o_f L.s)` by metis_tac[] >>
  `(m.nodemap f_o_f L.s) ' e = m.nodemap ' (L.s ' e)` by
    (irule (cj 2 f_o_f_DEF |> SPEC_ALL) >> simp[]) >>
  metis_tac[]
QED

Theorem match_preserves_target_apply:
  !m L Kv G e n.
    is_match L Kv m G /\ wf_hostgraph G /\ e IN L.E /\ L.t ' e = n ==>
    G.t ' (m.edgemap ' e) = m.nodemap ' n
Proof
  rpt strip_tac >>
  `m.nodemap f_o_f L.t = G.t f_o_f m.edgemap` by fs match_target_ss >>
  `FDOM m.edgemap = L.E` by fs match_morphism_ss >>
  `FRANGE m.edgemap SUBSET G.E` by fs match_morphism_ss >>
  `m.edgemap ' e IN G.E` by (fs[FRANGE_DEF, SUBSET_DEF] >> metis_tac[]) >>
  `e IN FDOM (G.t f_o_f m.edgemap)` by (simp[cj 1 f_o_f_DEF] >> fs wf_ss) >>
  `(G.t f_o_f m.edgemap) ' e = G.t ' (m.edgemap ' e)` by
    (irule (cj 2 f_o_f_DEF |> SPEC_ALL) >> simp[]) >>
  `FDOM (m.nodemap f_o_f L.t) = FDOM (G.t f_o_f m.edgemap)` by
    metis_tac[fmap_EQ_THM] >>
  `e IN FDOM (m.nodemap f_o_f L.t)` by metis_tac[] >>
  `(m.nodemap f_o_f L.t) ' e = m.nodemap ' (L.t ' e)` by
    (irule (cj 2 f_o_f_DEF |> SPEC_ALL) >> simp[]) >>
  metis_tac[]
QED

(* Helper: for link rule, every RHS edge has reachable preimages in G0 *)
Theorem link_rhs_edge_has_reachable_preimages:
  !G0 G m G' m'' lhs' rhs' assign x.
    wf_hostgraph G0 /\ wf_hostgraph G /\ minimally_extends G0 m G /\
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
  `rhs'.E = rule_link.rhs.E /\ rhs'.s = rule_link.rhs.s /\ rhs'.t = rule_link.rhs.t`
    by metis_tac[semTheory.instantiate_rulegraph_preserves_structure] >>
  `lhs'.E = rule_link.lhs.E /\ lhs'.s = rule_link.lhs.s /\ lhs'.t = rule_link.lhs.t /\
   lhs'.V = rule_link.lhs.V`
    by metis_tac[semTheory.instantiate_rulegraph_preserves_structure] >>
  `rule_link.rhs.E = {edgeid "e2"; edgeid "e1"; edgeid "e0"}` by EVAL_TAC >>
  `x = edgeid "e0" \/ x = edgeid "e1" \/ x = edgeid "e2"` by gvs[]
  (* Case: e0 - edge from n0 to n1 *)
  >- (gvs[] >>
      `FDOM m''.edgemap = lhs'.E` by
        fs match_morphism_ss >>
      `FRANGE m''.edgemap SUBSET G.E` by
        fs match_morphism_ss >>
      `edgeid "e0" IN lhs'.E` by (gvs[] >> EVAL_TAC) >>
      `m''.edgemap ' (edgeid "e0") IN G.E` by (gvs[SUBSET_DEF, FRANGE_DEF] >> metis_tac[]) >>
      `?v0 w0. v0 IN G0.V /\ w0 IN G0.V /\
               m.nodemap ' v0 = G.s ' (m''.edgemap ' (edgeid "e0")) /\
               m.nodemap ' w0 = G.t ' (m''.edgemap ' (edgeid "e0")) /\
               reachable_in G0 v0 w0` by (irule edge_in_G_has_reachable_preimages >> simp[]) >>
      `m''.nodemap f_o_f lhs'.s = G.s f_o_f m''.edgemap` by
        fs match_source_ss >>
      `m''.nodemap f_o_f lhs'.t = G.t f_o_f m''.edgemap` by
        fs match_target_ss >>
      `FDOM m''.nodemap = lhs'.V` by
        fs match_morphism_ss >>
      qexistsl [`v0`, `w0`] >> simp[] >>
      STRIP_ASSUME_TAC rule_link_structure >>
      (* Source equality *)
      `G.s ' (m''.edgemap ' (edgeid "e0")) = m''.nodemap ' (nodeid "n0")` by
        (irule match_preserves_source_apply >> simp[] >>
         qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
      (* Target equality *)
      `G.t ' (m''.edgemap ' (edgeid "e0")) = m''.nodemap ' (nodeid "n1")` by
        (irule match_preserves_target_apply >> simp[] >>
         qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
      gvs[])
  (* Case: e1 - edge from n1 to n2 *)
  >- (gvs[] >>
      `FDOM m''.edgemap = lhs'.E` by
        fs match_morphism_ss >>
      `FRANGE m''.edgemap SUBSET G.E` by
        fs match_morphism_ss >>
      `edgeid "e1" IN lhs'.E` by (gvs[] >> EVAL_TAC) >>
      `m''.edgemap ' (edgeid "e1") IN G.E` by (gvs[SUBSET_DEF, FRANGE_DEF] >> metis_tac[]) >>
      `?v0 w0. v0 IN G0.V /\ w0 IN G0.V /\
               m.nodemap ' v0 = G.s ' (m''.edgemap ' (edgeid "e1")) /\
               m.nodemap ' w0 = G.t ' (m''.edgemap ' (edgeid "e1")) /\
               reachable_in G0 v0 w0` by (irule edge_in_G_has_reachable_preimages >> simp[]) >>
      `m''.nodemap f_o_f lhs'.s = G.s f_o_f m''.edgemap` by
        fs match_source_ss >>
      `m''.nodemap f_o_f lhs'.t = G.t f_o_f m''.edgemap` by
        fs match_target_ss >>
      `FDOM m''.nodemap = lhs'.V` by
        fs match_morphism_ss >>
      qexistsl [`v0`, `w0`] >> simp[] >>
      STRIP_ASSUME_TAC rule_link_structure >>
      (* Source equality *)
      `G.s ' (m''.edgemap ' (edgeid "e1")) = m''.nodemap ' (nodeid "n1")` by
        (irule match_preserves_source_apply >> simp[] >>
         qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
      (* Target equality *)
      `G.t ' (m''.edgemap ' (edgeid "e1")) = m''.nodemap ' (nodeid "n2")` by
        (irule match_preserves_target_apply >> simp[] >>
         qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
      gvs[])
  (* Case: e2 - shortcut edge from n0 to n2, uses transitivity *)
  >- (gvs[] >>
      `FDOM m''.edgemap = lhs'.E` by
        fs match_morphism_ss >>
      `FRANGE m''.edgemap SUBSET G.E` by
        fs match_morphism_ss >>
      `edgeid "e0" IN lhs'.E` by (gvs[] >> EVAL_TAC) >>
      `edgeid "e1" IN lhs'.E` by (gvs[] >> EVAL_TAC) >>
      `m''.edgemap ' (edgeid "e0") IN G.E` by (gvs[SUBSET_DEF, FRANGE_DEF] >> metis_tac[]) >>
      `m''.edgemap ' (edgeid "e1") IN G.E` by (gvs[SUBSET_DEF, FRANGE_DEF] >> metis_tac[]) >>
      (* Get reachable preimages for e0 and e1 *)
      `?v0 w0. v0 IN G0.V /\ w0 IN G0.V /\
               m.nodemap ' v0 = G.s ' (m''.edgemap ' (edgeid "e0")) /\
               m.nodemap ' w0 = G.t ' (m''.edgemap ' (edgeid "e0")) /\
               reachable_in G0 v0 w0` by (irule edge_in_G_has_reachable_preimages >> simp[]) >>
      `?v1 w1. v1 IN G0.V /\ w1 IN G0.V /\
               m.nodemap ' v1 = G.s ' (m''.edgemap ' (edgeid "e1")) /\
               m.nodemap ' w1 = G.t ' (m''.edgemap ' (edgeid "e1")) /\
               reachable_in G0 v1 w1` by (irule edge_in_G_has_reachable_preimages >> simp[]) >>
      `m''.nodemap f_o_f lhs'.s = G.s f_o_f m''.edgemap` by
        fs match_source_ss >>
      `m''.nodemap f_o_f lhs'.t = G.t f_o_f m''.edgemap` by
        fs match_target_ss >>
      `FDOM m''.nodemap = lhs'.V` by
        fs match_morphism_ss >>
      STRIP_ASSUME_TAC rule_link_structure >>
      (* Key equalities via match_preserves_source/target_apply *)
      `G.s ' (m''.edgemap ' (edgeid "e0")) = m''.nodemap ' (nodeid "n0")` by
        (irule match_preserves_source_apply >> simp[] >>
         qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
      `G.t ' (m''.edgemap ' (edgeid "e0")) = m''.nodemap ' (nodeid "n1")` by
        (irule match_preserves_target_apply >> simp[] >>
         qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
      `G.s ' (m''.edgemap ' (edgeid "e1")) = m''.nodemap ' (nodeid "n1")` by
        (irule match_preserves_source_apply >> simp[] >>
         qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
      `G.t ' (m''.edgemap ' (edgeid "e1")) = m''.nodemap ' (nodeid "n2")` by
        (irule match_preserves_target_apply >> simp[] >>
         qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
      (* Connect w0 and v1 via bijectivity - both map to n1 in G *)
      `m.nodemap ' w0 = m''.nodemap ' (nodeid "n1")` by gvs[] >>
      `m.nodemap ' v1 = m''.nodemap ' (nodeid "n1")` by gvs[] >>
      `BIJ ($' m.nodemap) G0.V G.V` by fs[minimally_extends_def] >>
      `w0 = v1` by (fs[BIJ_DEF, INJ_DEF] >> metis_tac[]) >>
      (* Transitivity of reachability *)
      `reachable_in G0 v0 w1` by (irule reachable_in_trans >> qexists_tac `w0` >> gvs[]) >>
      `m.nodemap ' v0 = m''.nodemap ' (nodeid "n0")` by gvs[] >>
      `m.nodemap ' w1 = m''.nodemap ' (nodeid "n2")` by gvs[] >>
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
  simp[dpoTheory.deletion_remaining_nodes_def, dpoTheory.deletion_deleted_nodes_def] >>
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
  `deletion_remaining_nodes lhs' m'' rule_link.inf G = G.V`
    by (irule link_no_node_deletion >> simp[]) >>
  simp[trackTheory.FDOM_track_nodemap]
QED

(* Helper: f_o_f application when inner value is in outer FDOM *)
Theorem f_o_f_apply:
  !f g x. x IN FDOM g /\ g ' x IN FDOM f ==>
          (f f_o_f g) ' x = f ' (g ' x)
Proof
  rpt strip_tac >>
  `x IN FDOM (f f_o_f g)` by simp[finite_mapTheory.f_o_f_DEF] >>
  irule (GEN_ALL (CONJUNCT2 (SPEC_ALL finite_mapTheory.f_o_f_DEF))) >> simp[]
QED

(* Helper: node in FRANGE of source/target map is in G.V *)
Theorem wf_graph_st_in_V:
  !G e. wf_hostgraph G /\ e IN G.E ==>
        G.s ' e IN G.V /\ G.t ' e IN G.V
Proof
  rpt strip_tac >> fs wf_ss >>
  (`FRANGE G.s SUBSET G.V` by fs[] >> `FRANGE G.t SUBSET G.V` by fs[]) >>
  (`G.s ' e IN FRANGE G.s` by (simp[FRANGE_DEF] >> qexists_tac `e` >> fs[]) >>
   `G.t ' e IN FRANGE G.t` by (simp[FRANGE_DEF] >> qexists_tac `e` >> fs[])) >>
  fs[SUBSET_DEF]
QED

Theorem wf_hostgraph_FDOM_st:
  !G e. wf_hostgraph G /\ e IN G.E ==>
        e IN FDOM G.s /\ e IN FDOM G.t
Proof
  rw wf_ss
QED

Theorem link_preserves_invariant:
  !G0 G m G' m'.
    wf_hostgraph G0 /\
    tc_loop_invariant G0 G m /\
    step program (running (term_rscall {ruleid "link"}), [(G, id_track G)])
                 (final, [(G', m')]) ==>
    tc_loop_invariant G0 G' (compose_morphism m' m)
Proof
  rpt strip_tac >> fs[tc_loop_invariant_def] >>
  qpat_x_assum `step _ _ _` mp_tac >>
  simp[Once semTheory.step_cases] >> strip_tac >>
  gvs[push_stack_def, pop_stack_def, id_track_def] >>
  `r = rule_link` by
    gvs[program_def, finite_mapTheory.FUPDATE_LIST_THM,
        finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[semTheory.apply_ruleinstance_def, semTheory.instantiate_rule_def] >>
  (* Establish key facts *)
  `lhs'.V = rule_link.lhs.V` by
    metis_tac[semTheory.instantiate_rulegraph_preserves_V] >>
  `rhs'.V = rule_link.rhs.V` by
    metis_tac[semTheory.instantiate_rulegraph_preserves_V] >>
  `wf_assignment_spine assign` by
    (irule semTheory.mk_assignment_wf_assignment_spine >>
     qexistsl [`G`, `m''`, `rule_link`] >> simp[] >>
     drule hostgraphTheory.wf_hostgraph_IMP_hostgraph_labels_spine >> simp[]) >>
  `wf_hostgraph lhs'` by
    (irule semTheory.instantiate_rulegraph_wf >>
     qexistsl [`G`, `assign`, `m''`, `rule_link.lhs`] >> simp[] >>
     totally_labelled_tac) >>
  `wf_hostgraph rhs'` by
    (irule semTheory.instantiate_rulegraph_wf >>
     qexistsl [`G`, `assign`, `m''`, `rule_link.rhs`] >> simp[] >>
     totally_labelled_tac) >>
  `instantiate_rule rule_link assign m'' G =
     SOME <|lhs := lhs'; inf := rule_link.inf; rhs := rhs'|>` by
    simp[semTheory.instantiate_rule_def] >>
  (* Establish is_match *)
  sg `is_match lhs' rule_link.inf m'' G`
  >- (qabbrev_tac `ri = <|lhs := lhs'; inf := rule_link.inf; rhs := rhs'|>` >>
      `lhs' = ri.lhs` by simp[Abbr `ri`] >>
      `rule_link.inf = ri.inf` by simp[Abbr `ri`] >> gvs[] >>
      `wf_rule rule_link` by metis_tac[wf_rule_link] >>
      `wf_rulegraph_labels rule_link.lhs` by
        metis_tac[wf_rule_link, ruleTheory.wf_rule_def] >>
      drule_all semTheory.prematch_instantiation_is_match >> simp[])
  >- (rpt conj_tac
      (* 1. wf_hostgraph G' *)
      >- (irule dpoTheory.wf_dpo >> simp[] >> gvs[] >> EVAL_TAC)
      (* 2. minimally_extends - contains BIJ and edge_path_justified *)
      >- (simp[minimally_extends_def] >>
          (* Simplify composition with id_track *)
          `<|nodemap := FUN_FMAP I G.V; edgemap := FUN_FMAP I G.E|> = id_track G`
            by simp[id_track_def] >>
          `compose_morphism (track lhs' rule_link.inf m'' G) (id_track G) =
           track lhs' rule_link.inf m'' G` by
            (irule trackTheory.compose_morphism_id_track_right >> simp[] >>
             `FINITE (deletion_remaining_nodes lhs' m'' rule_link.inf G) /\
              FINITE (deletion_remaining_edges lhs' m'' G)` by
               (irule dpoTheory.wf_hostgraph_IMP_finite_remaining_elements >> simp[]) >>
             simp[trackTheory.FDOM_track_nodemap, trackTheory.FDOM_track_edgemap] >>
             metis_tac[dpoTheory.deletion_remaining_elements_SUBSET_base]) >>
          gvs[] >> rpt conj_tac
          (* is_track_morphism - use composition *)
          >- (sg `is_track_morphism G (track lhs' rule_link.inf m'' G)
                   (dpo lhs' rule_link.inf rhs' m'' G)`
              >- (irule trackTheory.track_is_track_morphism >> simp[] >>
                  conj_tac >- EVAL_TAC >- EVAL_TAC)
              >- (fs[minimally_extends_def] >>
                  drule_all trackTheory.compose_is_track_morphism >> simp[]))
          (* FDOM nodemap = G0.V *)
          >- (simp[morphismTheory.compose_morphism_def] >>
              `FINITE G.V` by fs wf_ss >>
              `FDOM (track lhs' rule_link.inf m'' G).nodemap = G.V`
                by (irule link_track_nodemap_FDOM >> simp[]) >>
              fs[minimally_extends_def] >>
              `FRANGE m.nodemap SUBSET G.V` by
                (fs[BIJ_DEF, SURJ_DEF, FRANGE_DEF] >> rw[SUBSET_DEF] >> metis_tac[]) >>
              `FRANGE m.nodemap SUBSET FDOM (track lhs' rule_link.inf m'' G).nodemap` by gvs[] >>
              metis_tac[FRANGE_SUBSET_FDOM_COMP_FDOM_EQUALITY])
          (* BIJ for composed nodemap - composition of bijections *)
          >- (`(dpo lhs' rule_link.inf rhs' m'' G).V = IMAGE tag_nodeid_left G.V`
                by (irule link_dpo_V >> simp[]) >>
              `FINITE G.V` by fs wf_ss >>
              `BIJ ($' (track lhs' rule_link.inf m'' G).nodemap) G.V
                   (IMAGE tag_nodeid_left G.V)` by (irule link_track_nodemap_BIJ >> simp[]) >>
              fs[minimally_extends_def] >>
              simp[morphismTheory.compose_morphism_def] >>
              `FDOM (track lhs' rule_link.inf m'' G).nodemap = G.V`
                by (irule link_track_nodemap_FDOM >> simp[]) >>
              `FDOM ((track lhs' rule_link.inf m'' G).nodemap f_o_f m.nodemap) = G0.V` by
                (simp[f_o_f_DEF] >> fs[EXTENSION] >> rw[] >>
                 EQ_TAC >> rw[] >> fs[BIJ_DEF, SURJ_DEF] >> metis_tac[]) >>
              simp[BIJ_DEF, INJ_DEF, SURJ_DEF] >> rpt conj_tac
              (* range in IMAGE *)
              >- (rw[] >> `x IN FDOM m.nodemap` by gvs[] >>
                  `m.nodemap ' x IN G.V` by fs[BIJ_DEF, SURJ_DEF] >>
                  `(track lhs' rule_link.inf m'' G).nodemap ' (m.nodemap ' x) IN
                   IMAGE tag_nodeid_left G.V` by fs[BIJ_DEF, SURJ_DEF] >>
                  `((track lhs' rule_link.inf m'' G).nodemap f_o_f m.nodemap) ' x =
                   (track lhs' rule_link.inf m'' G).nodemap ' (m.nodemap ' x)` by
                    (irule f_o_f_apply >> simp[]) >>
                  gvs[IN_IMAGE] >> metis_tac[])
              (* injectivity *)
              >- (rw[] >>
                  `((track lhs' rule_link.inf m'' G).nodemap f_o_f m.nodemap) ' x =
                   (track lhs' rule_link.inf m'' G).nodemap ' (m.nodemap ' x)` by
                    (irule f_o_f_apply >> simp[] >> fs[BIJ_DEF, SURJ_DEF]) >>
                  `((track lhs' rule_link.inf m'' G).nodemap f_o_f m.nodemap) ' y =
                   (track lhs' rule_link.inf m'' G).nodemap ' (m.nodemap ' y)` by
                    (irule f_o_f_apply >> simp[] >> fs[BIJ_DEF, SURJ_DEF]) >>
                  `(track lhs' rule_link.inf m'' G).nodemap ' (m.nodemap ' x) =
                   (track lhs' rule_link.inf m'' G).nodemap ' (m.nodemap ' y)` by gvs[] >>
                  `m.nodemap ' x IN G.V` by fs[BIJ_DEF, SURJ_DEF] >>
                  `m.nodemap ' y IN G.V` by fs[BIJ_DEF, SURJ_DEF] >>
                  `m.nodemap ' x = m.nodemap ' y` by fs[BIJ_DEF, INJ_DEF] >>
                  fs[BIJ_DEF, INJ_DEF])
              (* range again *)
              >- (rw[] >> `x IN FDOM m.nodemap` by gvs[] >>
                  `m.nodemap ' x IN G.V` by fs[BIJ_DEF, SURJ_DEF] >>
                  `(track lhs' rule_link.inf m'' G).nodemap ' (m.nodemap ' x) IN
                   IMAGE tag_nodeid_left G.V` by fs[BIJ_DEF, SURJ_DEF] >>
                  `((track lhs' rule_link.inf m'' G).nodemap f_o_f m.nodemap) ' x =
                   (track lhs' rule_link.inf m'' G).nodemap ' (m.nodemap ' x)` by
                    (irule f_o_f_apply >> simp[]) >>
                  gvs[IN_IMAGE] >> metis_tac[])
              (* surjectivity *)
              >- (rw[] >> `x' IN G.V` by gvs[] >>
                  `tag_nodeid_left x' IN IMAGE tag_nodeid_left G.V` by (simp[IN_IMAGE] >> metis_tac[]) >>
                  `?v. v IN G.V /\ (track lhs' rule_link.inf m'' G).nodemap ' v =
                       tag_nodeid_left x'` by (fs[BIJ_DEF, SURJ_DEF] >> metis_tac[]) >>
                  `?u. u IN G0.V /\ m.nodemap ' u = v` by
                    (fs[BIJ_DEF, SURJ_DEF] >> metis_tac[]) >>
                  qexists `u` >> conj_tac >- gvs[] >>
                  `((track lhs' rule_link.inf m'' G).nodemap f_o_f m.nodemap) ' u =
                   (track lhs' rule_link.inf m'' G).nodemap ' (m.nodemap ' u)` by
                    (irule f_o_f_apply >> gvs[BIJ_DEF, SURJ_DEF]) >>
                  gvs[]))
          (* edge_path_justified *)
          >- (simp[edge_path_justified_def] >> rpt strip_tac >>
              simp[dpoTheory.dpo_def, dpoTheory.gluing_def] >>
              qabbrev_tac `D = deletion lhs' rule_link.inf m'' G` >>
              Cases_on `is_left_tagged_edgeid e`
              (* Case 1: Left-tagged edge from deletion D *)
              >- (gvs[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
                  sg `e IN IMAGE tag_edgeid_left D.E UNION IMAGE tag_edgeid_right rhs'.E`
                  >- (fs[generated_edges_def, dpoTheory.dpo_def, dpoTheory.gluing_def,
                         dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def]
                      >- (DISJ1_TAC >> qexists `x` >> gvs[])
                      >- (DISJ2_TAC >> qexists `x` >> gvs[])) >>
                  sg `e IN IMAGE tag_edgeid_left D.E`
                  >- (gvs[IN_UNION, IN_IMAGE]
                      >- (qexists `x` >> gvs[])
                      >- (`~is_left_tagged_edgeid (tag_edgeid_right x)` by
                            metis_tac[taggingTheory.correct_tagging,
                                      taggingTheory.is_left_tagged_edgeid_def,
                                      taggingTheory.is_right_tagged_edgeid_def,
                                      arithmeticTheory.ODD_EVEN])) >>
                  gvs[IN_IMAGE] >>
                  sg `gluing_s rule_link.inf m'' D rhs' ' (tag_edgeid_left x) = tag_nodeid_left (D.s ' x)`
                  >- (sg `wf_graph D`
                      >- (simp[Abbr `D`] >>
                          irule hostgraphTheory.wf_partial_hostgraph_IMP_wf_graph >>
                          irule dpoTheory.deletion_preserves_wf_graph >> simp[] >> EVAL_TAC)
                      >- (irule dpoTheory.gluing_s_apply_left_tagged >> simp[] >> fs[wf_hostgraph_def])) >>
                  gvs[] >>
                  sg `gluing_t (IMAGE tag_edgeid_left D.E UNION IMAGE tag_edgeid_right rhs'.E)
                               rule_link.inf m'' D rhs' ' (tag_edgeid_left x) = tag_nodeid_left (D.t ' x)`
                  >- (`IMAGE tag_edgeid_left D.E UNION IMAGE tag_edgeid_right rhs'.E = gluing_edges D rhs'`
                        by simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
                      `wf_graph D` by (simp[Abbr `D`] >>
                          irule hostgraphTheory.wf_partial_hostgraph_IMP_wf_graph >>
                          irule dpoTheory.deletion_preserves_wf_graph >> simp[] >> EVAL_TAC) >>
                      `FINITE D.E` by fs[Abbr `D`, dpoTheory.deletion_def,
                                         dpoTheory.deletion_remaining_edges_def, wf_hostgraph_def, wf_graph_def] >>
                      `FINITE rhs'.E` by fs wf_ss >>
                      `FINITE (IMAGE tag_edgeid_left D.E UNION IMAGE tag_edgeid_right rhs'.E)` by simp[] >>
                      gvs[] >> irule dpoTheory.gluing_t_apply_left_tagged >> simp[] >> conj_tac
                      >- (simp[Once dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
                          fs[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def])
                      >- fs[wf_hostgraph_def]) >>
                  sg `x IN G.E` >- fs[Abbr `D`, dpoTheory.deletion_def, dpoTheory.deletion_remaining_edges_def] >>
                  sg `D.s ' x = G.s ' x`
                  >- (fs[Abbr `D`, dpoTheory.deletion_def, LET_THM] >>
                      simp[finite_mapTheory.DRESTRICT_DEF] >>
                      `x IN FDOM G.s` by fs wf_ss >> gvs[])
                  >- (sg `D.t ' x = G.t ' x`
                      >- (fs[Abbr `D`, dpoTheory.deletion_def, LET_THM, finite_mapTheory.DRESTRICT_DEF] >>
                          `x IN FDOM G.t` by fs wf_ss >> gvs[])
                      >- (gvs[] >> drule_all edge_in_G_has_reachable_preimages >> strip_tac >>
                          qexistsl [`v0`, `w0`] >> rpt conj_tac >> gvs[]
                          >- (simp[morphismTheory.compose_morphism_def] >>
                              `FINITE G.V` by fs wf_ss >>
                              `FDOM (track lhs' rule_link.inf m'' G).nodemap = G.V`
                                by (irule link_track_nodemap_FDOM >> simp[]) >>
                              `G.s ' x IN G.V` by (drule_all wf_graph_st_in_V >> simp[]) >>
                              `((track lhs' rule_link.inf m'' G).nodemap f_o_f m.nodemap) ' v0 =
                               (track lhs' rule_link.inf m'' G).nodemap ' (m.nodemap ' v0)` by
                                (irule f_o_f_apply >> simp[] >> fs[minimally_extends_def, BIJ_DEF, SURJ_DEF]) >>
                              gvs[] >> irule trackTheory.track_nodemap_apply >>
                              metis_tac[dpoTheory.wf_hostgraph_IMP_finite_remaining_elements,
                                        link_no_node_deletion])
                          >- (simp[morphismTheory.compose_morphism_def] >>
                              `FINITE G.V` by fs wf_ss >>
                              `FDOM (track lhs' rule_link.inf m'' G).nodemap = G.V`
                                by (irule link_track_nodemap_FDOM >> simp[]) >>
                              `G.t ' x IN G.V` by (drule_all wf_graph_st_in_V >> simp[]) >>
                              `((track lhs' rule_link.inf m'' G).nodemap f_o_f m.nodemap) ' w0 =
                               (track lhs' rule_link.inf m'' G).nodemap ' (m.nodemap ' w0)` by
                                (irule f_o_f_apply >> simp[] >> fs[minimally_extends_def, BIJ_DEF, SURJ_DEF]) >>
                              gvs[] >> irule trackTheory.track_nodemap_apply >>
                              metis_tac[dpoTheory.wf_hostgraph_IMP_finite_remaining_elements,
                                        link_no_node_deletion]))))
              (* Case 2: Right-tagged edge from rhs' *)
              >- (gvs[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
                  sg `e IN IMAGE tag_edgeid_right rhs'.E`
                  >- (fs[generated_edges_def, dpoTheory.dpo_def, dpoTheory.gluing_def,
                         dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def]
                      >- (`is_left_tagged_edgeid (tag_edgeid_left x)`
                            by metis_tac[taggingTheory.correct_tagging,
                                         taggingTheory.is_left_tagged_edgeid_def,
                                         arithmeticTheory.EVEN_DOUBLE] >> gvs[])
                      >- (qexists `x` >> gvs[]))
                  >- (gvs[IN_IMAGE] >>
                      sg `gluing_s rule_link.inf m'' D rhs' ' (tag_edgeid_right x) =
                          tag_nodeid_left (m''.nodemap ' (rhs'.s ' x))`
                      >- (irule dpoTheory.gluing_s_apply_right_tagged_in_interface >> rpt conj_tac
                          >- (simp[Abbr `D`] >> irule hostgraphTheory.wf_partial_hostgraph_IMP_wf_graph >>
                              irule dpoTheory.deletion_preserves_wf_graph >> simp[] >> EVAL_TAC)
                          >- fs[wf_hostgraph_def]
                          >- gvs[]
                          >- (sg `rhs'.s ' x IN rhs'.V`
                              >- (`FRANGE rhs'.s SUBSET rhs'.V` by fs wf_ss >>
                                  `rhs'.s ' x IN FRANGE rhs'.s`
                                    by (simp[finite_mapTheory.FRANGE_DEF] >> qexists `x` >>
                                        fs wf_ss) >>
                                  fs[pred_setTheory.SUBSET_DEF])
                              >- (`rhs'.V = rule_link.rhs.V` by gvs[] >>
                                  `rule_link.rhs.V = rule_link.inf` by EVAL_TAC >> gvs[])))
                      >- (gvs[] >>
                          sg `gluing_t (IMAGE tag_edgeid_left D.E UNION IMAGE tag_edgeid_right rhs'.E)
                                       rule_link.inf m'' D rhs' ' (tag_edgeid_right x) =
                              tag_nodeid_left (m''.nodemap ' (rhs'.t ' x))`
                          >- (`IMAGE tag_edgeid_left D.E UNION IMAGE tag_edgeid_right rhs'.E = gluing_edges D rhs'`
                                by simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >> gvs[] >>
                              irule dpoTheory.gluing_t_apply_right_tagged_in_interface >> rpt conj_tac
                              >- (`FINITE D.E` by fs[Abbr `D`, dpoTheory.deletion_def,
                                                    dpoTheory.deletion_remaining_edges_def,
                                                    wf_hostgraph_def, wf_graph_def] >>
                                  `FINITE rhs'.E` by fs wf_ss >>
                                  fs[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def])
                              >- (simp[Abbr `D`] >> irule hostgraphTheory.wf_partial_hostgraph_IMP_wf_graph >>
                                  irule dpoTheory.deletion_preserves_wf_graph >> simp[] >> EVAL_TAC)
                              >- fs[wf_hostgraph_def]
                              >- gvs[]
                              >- (`rhs'.t ' x IN rhs'.V`
                                    by (`FRANGE rhs'.t SUBSET rhs'.V` by fs wf_ss >>
                                        `rhs'.t ' x IN FRANGE rhs'.t`
                                          by (simp[finite_mapTheory.FRANGE_DEF] >> qexists `x` >>
                                              fs wf_ss) >>
                                        fs[pred_setTheory.SUBSET_DEF]) >>
                                  `rhs'.V = rule_link.rhs.V` by gvs[] >>
                                  `rule_link.rhs.V = rule_link.inf` by EVAL_TAC >> gvs[]))
                          >- (gvs[] >> drule_all link_rhs_edge_has_reachable_preimages >> strip_tac >> fs[] >>
                              qexistsl [`v0`, `w0`] >> rpt conj_tac >> gvs[]
                              (* v0 case - source *)
                              >- (simp[morphismTheory.compose_morphism_def] >>
                                  `FINITE G.V` by fs wf_ss >>
                                  `FDOM (track lhs' rule_link.inf m'' G).nodemap = G.V`
                                    by (irule link_track_nodemap_FDOM >> simp[]) >>
                                  `rhs'.s ' x IN rule_link.inf`
                                    by (drule_all wf_graph_st_in_V >> strip_tac >>
                                        `rhs'.V = rule_link.inf` by (gvs[] >> EVAL_TAC) >> gvs[]) >>
                                  `m''.nodemap ' (rhs'.s ' x) IN G.V` by
                                    (`FRANGE m''.nodemap SUBSET G.V`
                                       by fs[dpoTheory.is_match_def, morphismTheory.is_inj_morphism_def,
                                             morphismTheory.is_morphism_def, morphismTheory.is_premorphism_def,
                                             morphismTheory.morphism_dom_ran_def] >>
                                     `rhs'.s ' x IN FDOM m''.nodemap`
                                       by (`FDOM m''.nodemap = lhs'.V`
                                             by fs[dpoTheory.is_match_def, morphismTheory.is_inj_morphism_def,
                                                   morphismTheory.is_morphism_def, morphismTheory.is_premorphism_def,
                                                   morphismTheory.morphism_dom_ran_def] >>
                                           `lhs'.V = rule_link.inf` by (gvs[] >> EVAL_TAC) >> gvs[]) >>
                                     `m''.nodemap ' (rhs'.s ' x) IN FRANGE m''.nodemap`
                                       by (simp[FRANGE_DEF] >> qexists_tac `rhs'.s ' x` >> gvs[]) >>
                                     fs[SUBSET_DEF]) >>
                                  `((track lhs' rule_link.inf m'' G).nodemap f_o_f m.nodemap) ' v0 =
                                   (track lhs' rule_link.inf m'' G).nodemap ' (m.nodemap ' v0)` by
                                    (irule f_o_f_apply >> simp[] >> fs[minimally_extends_def, BIJ_DEF, SURJ_DEF]) >>
                                  gvs[] >> irule trackTheory.track_nodemap_apply >>
                                  metis_tac[dpoTheory.wf_hostgraph_IMP_finite_remaining_elements, link_no_node_deletion])
                              (* w0 case - target *)
                              >- (simp[morphismTheory.compose_morphism_def] >>
                                  `FINITE G.V` by fs wf_ss >>
                                  `FDOM (track lhs' rule_link.inf m'' G).nodemap = G.V`
                                    by (irule link_track_nodemap_FDOM >> simp[]) >>
                                  `rhs'.t ' x IN rule_link.inf`
                                    by (drule_all wf_graph_st_in_V >> strip_tac >>
                                        `rhs'.V = rule_link.inf` by (gvs[] >> EVAL_TAC) >> gvs[]) >>
                                  `m''.nodemap ' (rhs'.t ' x) IN G.V` by
                                    (`FRANGE m''.nodemap SUBSET G.V`
                                       by fs[dpoTheory.is_match_def, morphismTheory.is_inj_morphism_def,
                                             morphismTheory.is_morphism_def, morphismTheory.is_premorphism_def,
                                             morphismTheory.morphism_dom_ran_def] >>
                                     `rhs'.t ' x IN FDOM m''.nodemap`
                                       by (`FDOM m''.nodemap = lhs'.V`
                                             by fs[dpoTheory.is_match_def, morphismTheory.is_inj_morphism_def,
                                                   morphismTheory.is_morphism_def, morphismTheory.is_premorphism_def,
                                                   morphismTheory.morphism_dom_ran_def] >>
                                           `lhs'.V = rule_link.inf` by (gvs[] >> EVAL_TAC) >> gvs[]) >>
                                     `m''.nodemap ' (rhs'.t ' x) IN FRANGE m''.nodemap`
                                       by (simp[FRANGE_DEF] >> qexists_tac `rhs'.t ' x` >> gvs[]) >>
                                     fs[SUBSET_DEF]) >>
                                  `((track lhs' rule_link.inf m'' G).nodemap f_o_f m.nodemap) ' w0 =
                                   (track lhs' rule_link.inf m'' G).nodemap ' (m.nodemap ' w0)` by
                                    (irule f_o_f_apply >> simp[] >> fs[minimally_extends_def, BIJ_DEF, SURJ_DEF]) >>
                                  gvs[] >> irule trackTheory.track_nodemap_apply >>
                                  metis_tac[dpoTheory.wf_hostgraph_IMP_finite_remaining_elements, link_no_node_deletion])))))))
      (* 3. unmarked_hostgraph G' - DPO preserves unmarked *)
      >- (simp[hostgraphTheory.unmarked_hostgraph_def] >> rpt conj_tac
          (* nodes_unmarked *)
          >- (simp[hostgraphTheory.nodes_unmarked_def, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
              qabbrev_tac `D = deletion lhs' rule_link.inf m'' G` >>
              irule dpoTheory.gluing_l_unmarked >> rpt conj_tac
              (* not-left-tagged: contradiction since Vg = IMAGE tag_nodeid_left D.V *)
              >- (rpt strip_tac >> `rhs'.V DIFF rule_link.inf = {}` by (gvs[] >> EVAL_TAC) >>
                  `gluing_nodes D rule_link.inf rhs' = IMAGE tag_nodeid_left D.V`
                    by simp[dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >>
                  `is_left_tagged_nodeid n` by (gvs[IN_IMAGE] >> metis_tac[taggingTheory.correct_tagging]))
              (* left-tagged in interface: use rhs'.l *)
              >- (rpt strip_tac >> `rule_link.inf = rhs'.V` by (gvs[] >> EVAL_TAC) >>
                  `FDOM rhs'.l = rhs'.V` by fs wf_ss >> gvs[] >>
                  SELECT_ELIM_TAC >> rpt conj_tac >- metis_tac[] >- simp[])
              (* left-tagged not in interface: use D.l *)
              >- (rpt strip_tac >> `rhs'.V DIFF rule_link.inf = {}` by (gvs[] >> EVAL_TAC) >>
                  `gluing_nodes D rule_link.inf rhs' = IMAGE tag_nodeid_left D.V`
                    by simp[dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >>
                  `untag_nodeid n IN D.V` by (gvs[IN_IMAGE] >> metis_tac[taggingTheory.tag_untag_nodeid_inv]) >>
                  simp[Abbr `D`, dpoTheory.deletion_def, FDOM_DRESTRICT] >> rpt conj_tac
                  >- (sg `(deletion lhs' rule_link.inf m'' G).V = G.V`
                      >- (simp[dpoTheory.deletion_def, dpoTheory.deletion_remaining_nodes_def,
                               dpoTheory.deletion_deleted_nodes_def] >>
                          `rule_link.lhs.V DIFF rule_link.inf = {}` by (gvs[] >> EVAL_TAC) >> simp[])
                      >- (`FDOM G.l = G.V` by fs wf_ss >> gvs[]))
                  >- (simp[dpoTheory.deletion_relabling_nodes_def, dpoTheory.deletion_remaining_nodes_def,
                           dpoTheory.deletion_deleted_nodes_def] >>
                      `rule_link.lhs.V = rule_link.inf` by (gvs[] >> EVAL_TAC) >> rpt conj_tac
                      >- (gvs[] >> `(deletion lhs' rule_link.inf m'' G).V SUBSET G.V`
                            by simp[dpoTheory.deletion_def, dpoTheory.deletion_remaining_nodes_def] >>
                          fs[SUBSET_DEF])
                      >- gvs[]
                      >- (rpt strip_tac >> CCONTR_TAC >> gvs[] >> metis_tac[])))
              (* FINITE gluing_nodes *)
              >- (simp[Abbr `D`, dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def,
                       dpoTheory.deletion_def, dpoTheory.deletion_remaining_nodes_def] >>
                  `FINITE G.V` by fs wf_ss >> simp[] >>
                  `FINITE rule_link.rhs.V` by EVAL_TAC >> simp[])
              (* FEVERY D.l *)
              >- (simp[Abbr `D`, dpoTheory.deletion_def, FEVERY_DEF, FDOM_DRESTRICT, DRESTRICT_DEF] >>
                  rpt strip_tac >> fs[unmarked_hostgraph_def, hostgraphTheory.nodes_unmarked_def, FEVERY_DEF] >>
                  metis_tac[])
              (* FEVERY rhs'.l *)
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
              (* left-tagged edges in deletion *)
              >- (rpt strip_tac >> gvs[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def]
                  >- (simp[dpoTheory.deletion_def, FDOM_DRESTRICT] >> fs[dpoTheory.deletion_def] >>
                      `FDOM G.m = G.E` by fs wf_ss >>
                      `deletion_remaining_edges lhs' m'' G SUBSET G.E`
                        by simp[dpoTheory.deletion_remaining_edges_def] >> gvs[SUBSET_DEF])
                  >- (`~is_left_tagged_edgeid (tag_edgeid_right x)`
                        by metis_tac[taggingTheory.correct_tagging, taggingTheory.is_left_tagged_edgeid_def,
                                     taggingTheory.is_right_tagged_edgeid_def, arithmeticTheory.ODD_EVEN]))
              (* not-left-tagged edges in rhs' *)
              >- (rpt strip_tac >> gvs[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def]
                  >- (`is_left_tagged_edgeid (tag_edgeid_left x)` by metis_tac[taggingTheory.correct_tagging])
                  >- (`FDOM rhs'.m = rhs'.E` by fs wf_ss >> gvs[]))
              (* FINITE gluing_edges *)
              >- (simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def, dpoTheory.deletion_def,
                       dpoTheory.deletion_remaining_edges_def] >>
                  `FINITE G.E` by fs wf_ss >>
                  `FINITE rhs'.E` by fs wf_ss >> simp[])
              (* FEVERY deletion.m *)
              >- (simp[dpoTheory.deletion_def, FEVERY_DEF, FDOM_DRESTRICT, DRESTRICT_DEF] >>
                  rpt strip_tac >> fs[unmarked_hostgraph_def, hostgraphTheory.edges_unmarked_def, FEVERY_DEF])
              (* FEVERY rhs'.m *)
              >- (`FEVERY (\(x,l,mk). mk = NONE) rule_link.rhs.l`
                    by (simp[FEVERY_DEF, FDOM_FUPDATE, FAPPLY_FUPDATE_THM] >> EVAL_TAC >> rpt strip_tac >> gvs[]) >>
                  `FEVERY (\(x,l,mk). mk = NONE) rule_link.rhs.m`
                    by (simp[FEVERY_DEF, FDOM_FUPDATE, FAPPLY_FUPDATE_THM] >> EVAL_TAC >> rpt strip_tac >> gvs[]) >>
                  drule_all semTheory.instantiate_rulegraph_unmarked >> simp[])))
      (* 4. unrooted_hostgraph G' - DPO preserves unrooted *)
      >- (simp[hostgraphTheory.unrooted_hostgraph_def, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
          qabbrev_tac `D = deletion lhs' rule_link.inf m'' G` >>
          qabbrev_tac `Vg = gluing_nodes D rule_link.inf rhs'` >>
          sg `FINITE Vg`
          >- (simp[Abbr `Vg`, dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >>
              `FINITE rule_link.rhs.V` by EVAL_TAC >>
              `FINITE D.V` by (simp[Abbr `D`, dpoTheory.deletion_def, dpoTheory.deletion_remaining_nodes_def] >>
                               fs wf_ss) >> simp[])
          >- (`FDOM (gluing_p Vg rule_link.inf m'' D rhs') = Vg` by simp[trackTheory.FDOM_gluing_p] >> simp[] >>
              sg `FEVERY (\(nid,b). b <=> F) (gluing_p Vg rule_link.inf m'' D rhs')`
              >- (irule dpoTheory.gluing_p_unrooted >> rpt conj_tac
                  (* not-left-tagged: contradiction *)
                  >- (rpt strip_tac >> `rhs'.V DIFF rule_link.inf = {}` by (gvs[] >> EVAL_TAC) >>
                      `Vg = IMAGE tag_nodeid_left D.V`
                        by simp[Abbr `Vg`, dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >>
                      `is_left_tagged_nodeid n` by (gvs[IN_IMAGE] >> metis_tac[taggingTheory.correct_tagging]))
                  (* left-tagged in interface: use rhs'.p *)
                  >- (sg `unrooted_hostgraph rhs'`
                      >- (`FDOM rule_link.rhs.p = rule_link.rhs.V` by EVAL_TAC >>
                          sg `!n. n IN rule_link.rhs.V ==> (rule_link.rhs.p ' n <=> F)`
                          >- (rpt strip_tac >> `rule_link.rhs.V = {nodeid "n0"; nodeid "n1"; nodeid "n2"}`
                                by EVAL_TAC >> gvs[] >> EVAL_TAC)
                          >- (drule_all semTheory.instantiate_rulegraph_unrooted >> simp[]))
                      >- (rpt strip_tac >> `rule_link.inf = rhs'.V` by (gvs[] >> EVAL_TAC) >>
                          `FDOM rhs'.p = rhs'.V` by fs[unrooted_hostgraph_def] >> gvs[] >>
                          SELECT_ELIM_TAC >> rpt conj_tac >- metis_tac[] >- simp[]))
                  (* left-tagged not in interface: use D.p *)
                  >- (rpt strip_tac >> simp[Abbr `D`, dpoTheory.deletion_def, FDOM_DRESTRICT] >>
                      `rule_link.lhs.V DIFF rule_link.inf = {}` by (gvs[] >> EVAL_TAC) >>
                      simp[dpoTheory.deletion_remaining_nodes_def, dpoTheory.deletion_deleted_nodes_def] >>
                      rpt conj_tac
                      >- (`FDOM G.p = G.V` by fs[unrooted_hostgraph_def] >> gvs[] >>
                          `rhs'.V DIFF rule_link.inf = {}` by (gvs[] >> EVAL_TAC) >>
                          `Vg = IMAGE tag_nodeid_left (deletion lhs' rule_link.inf m'' G).V`
                            by (simp[Abbr `Vg`, dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >> gvs[]) >>
                          `(deletion lhs' rule_link.inf m'' G).V = G.V`
                            by simp[dpoTheory.deletion_def, dpoTheory.deletion_remaining_nodes_def,
                                    dpoTheory.deletion_deleted_nodes_def] >>
                          gvs[IN_IMAGE] >> metis_tac[taggingTheory.tag_untag_nodeid_inv])
                      >- (simp[dpoTheory.deletion_relabling_nodes_def, dpoTheory.deletion_remaining_nodes_def,
                               dpoTheory.deletion_deleted_nodes_def] >>
                          `rule_link.lhs.V = rule_link.inf` by (gvs[] >> EVAL_TAC) >> rpt conj_tac
                          >- (`rhs'.V DIFF rule_link.inf = {}` by (gvs[] >> EVAL_TAC) >>
                              `Vg = IMAGE tag_nodeid_left (deletion lhs' rule_link.inf m'' G).V`
                                by simp[Abbr `Vg`, dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >>
                              `(deletion lhs' rule_link.inf m'' G).V = G.V`
                                by simp[dpoTheory.deletion_def, dpoTheory.deletion_remaining_nodes_def,
                                        dpoTheory.deletion_deleted_nodes_def] >>
                              gvs[IN_IMAGE] >> metis_tac[taggingTheory.tag_untag_nodeid_inv])
                          >- (rpt strip_tac >> CCONTR_TAC >> fs[] >> first_x_assum (qspec_then `x` mp_tac) >> simp[])))
                  (* D.p values are F *)
                  >- (rpt strip_tac >> simp[Abbr `D`, dpoTheory.deletion_def, DRESTRICT_DEF] >>
                      `FDOM G.p = G.V` by fs[unrooted_hostgraph_def] >>
                      `!n. n IN G.V ==> (G.p ' n <=> F)` by fs[unrooted_hostgraph_def] >>
                      gvs[FDOM_DRESTRICT] >> DISJ1_TAC >>
                      `n IN FDOM (deletion lhs' rule_link.inf m'' G).p` by gvs[] >>
                      fs[dpoTheory.deletion_def, FDOM_DRESTRICT])
                  (* rhs'.p values are F *)
                  >- (`FDOM rule_link.rhs.p = rule_link.rhs.V` by EVAL_TAC >>
                      `!n. n IN rule_link.rhs.V ==> (rule_link.rhs.p ' n <=> F)`
                        by (rpt strip_tac >> `rule_link.rhs.V = {nodeid "n0"; nodeid "n1"; nodeid "n2"}`
                              by EVAL_TAC >> gvs[] >> EVAL_TAC) >>
                      `unrooted_hostgraph rhs'` by (drule_all semTheory.instantiate_rulegraph_unrooted >> simp[]) >>
                      fs[unrooted_hostgraph_def])
                  (* FINITE Vg *)
                  >- (simp[Abbr `Vg`, dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >>
                      simp[Abbr `D`, dpoTheory.deletion_def, dpoTheory.deletion_remaining_nodes_def] >>
                      `FINITE G.V` by fs wf_ss >>
                      `FINITE rule_link.rhs.V` by EVAL_TAC >> simp[]))
              >- (rpt strip_tac >> fs[FEVERY_DEF] >> first_x_assum (qspec_then `n` mp_tac) >> simp[]))))
QED

(* -------------------------------------------------------------------------- *)
(* Step 3: Body either succeeds with invariant preserved, or fails            *)
(*         This is weaker than WSPEC - allows the body to fail                *)
(* -------------------------------------------------------------------------- *)

Theorem link_body_succeeds_or_fails:
  !G0 G m c.
    wf_hostgraph G0 /\ wf_hostgraph G /\ tc_loop_invariant G0 G m /\
    steps program (running (term_rscall {ruleid "link"}), [(G, id_track G)]) c /\
    ~can_step c ==>
    (?H mH. c = (final, [(H, mH)]) /\ tc_loop_invariant G0 H (compose_morphism mH m)) \/
    (c = (failed, [(G, id_track G)]))
Proof
  rpt strip_tac >>
  (* Establish FEVERY for steps_SINGLETON_STACK_FINAL *)
  `FEVERY (no_intermediate_terms o SND) program.proc` by
    simp[program_wf |> SIMP_RULE std_ss [programTheory.wf_program_def]] >>
  `no_intermediate_terms (term_rscall {ruleid "link"})` by EVAL_TAC >>
  `!x. (\(_,t). no_intermediate_terms t) x = (no_intermediate_terms o SND) x` by
    (Cases >> simp[]) >>
  `FEVERY (\(_,t). no_intermediate_terms t) program.proc` by
    (fs[finite_mapTheory.FEVERY_DEF] >> rw[] >> res_tac) >>
  (* Determine the form of the final configuration *)
  drule_all_then strip_assume_tac semPropsTheory.steps_SINGLETON_STACK_FINAL
  (* Case 1: c = (final, [G']) - rule applied successfully *)
  >- (DISJ1_TAC >> gvs[] >> Cases_on `G'` >> qexistsl [`q`, `r`] >> simp[] >>
      (* Use evaluate characterization *)
      `evaluate program G (term_rscall {ruleid "link"}) (q, r)` by
        (simp[semTheory.evaluate_def] >> qexists `[(q,r)]` >> simp[]) >>
      gvs[semPropsTheory.evaluate_rscall] >>
      (* Simplify compose with id_track *)
      `compose_morphism (track ri.lhs ri.inf m' G) (id_track G) =
       track ri.lhs ri.inf m' G` by
        (irule trackTheory.compose_morphism_id_track_right >> simp[] >>
         `FINITE (deletion_remaining_nodes ri.lhs m' ri.inf G) /\
          FINITE (deletion_remaining_edges ri.lhs m' G)` by
           (irule dpoTheory.wf_hostgraph_IMP_finite_remaining_elements >> simp[]) >>
         simp[trackTheory.FDOM_track_nodemap, trackTheory.FDOM_track_edgemap] >>
         metis_tac[dpoTheory.deletion_remaining_elements_SUBSET_base]) >>
      gvs[] >>
      (* Establish the step for link_preserves_invariant *)
      sg `step program (running (term_rscall {ruleid "link"}), [(G, id_track G)])
               (final, [(q, track ri.lhs ri.inf m' G)])`
      >- (simp[Once semTheory.step_cases] >>
          qexistsl [`G`, `id_track G`, `[]`, `r'`, `m'`, `q`, `ri`, `assign`] >>
          simp[stackTheory.push_stack_def, stackTheory.pop_stack_def])
      (* Use link_preserves_invariant *)
      >- (irule link_preserves_invariant >> simp[] >> qexists `G` >> simp[]))
  (* Case 2: c = (failed, [G']) - rule failed, show G' = (G, id_track G) *)
  >- (DISJ2_TAC >> gvs[] >>
      fs[semTheory.steps_def] >>
      `?n. NRC (step program) n (running (term_rscall {ruleid "link"}), [(G, id_track G)])
                                 (failed, [G'])` by metis_tac[arithmeticTheory.RTC_NRC] >>
      Cases_on `n` >> gvs[semTheory.can_step_def] >>
      gvs[arithmeticTheory.NRC] >>
      `?stk. z = (final, stk) \/ z = (failed, stk)` by
        (qpat_x_assum `step _ (running (term_rscall _), _) z` mp_tac >>
         simp[Once semTheory.step_cases] >> rpt strip_tac >> gvs[])
      (* z = (final, stk): can't reach failed from final *)
      >- (gvs[] >> Cases_on `n'` >> gvs[arithmeticTheory.NRC] >>
          qpat_x_assum `step _ (final, _) _` mp_tac >> simp[Once semTheory.step_cases])
      (* z = (failed, stk): term_rscall failure preserves stack *)
      >- (gvs[] >>
          qpat_x_assum `step _ (running (term_rscall _), _) (failed, _)` mp_tac >>
          simp[Once semTheory.step_cases, stackTheory.pop_stack_def] >>
          strip_tac >> gvs[] >>
          Cases_on `n'` >> gvs[arithmeticTheory.NRC] >>
          qpat_x_assum `step _ (failed, _) _` mp_tac >> simp[Once semTheory.step_cases]))
  (* Case 3: c = (running term_break, [G']) - impossible for term_rscall *)
  >- (gvs[] >>
      (* term_rscall can only step to final or failed *)
      `!c. step program (running (term_rscall {ruleid "link"}), [(G, id_track G)]) c
           ==> ?stk. c = (final, stk) \/ c = (failed, stk)` by
        (simp[Once semTheory.step_cases] >> rpt strip_tac >> gvs[]) >>
      fs[semTheory.steps_def, Once relationTheory.RTC_CASES1] >>
      first_x_assum drule >> strip_tac >> gvs[]
      (* u = (final, stk): can't step further *)
      >- (fs[Once relationTheory.RTC_CASES1] >>
          qpat_x_assum `step _ (final, _) _` mp_tac >> simp[Once semTheory.step_cases])
      (* u = (failed, stk): can't step further *)
      >- (fs[Once relationTheory.RTC_CASES1] >>
          qpat_x_assum `step _ (failed, _) _` mp_tac >> simp[Once semTheory.step_cases]))
QED

(* -------------------------------------------------------------------------- *)
(* Step 5: Morphism well-formedness follows from invariant                    *)
(* -------------------------------------------------------------------------- *)

Theorem tc_invariant_implies_morphism_wf:
  !G0 G m. tc_loop_invariant G0 G m ==>
           FRANGE m.nodemap SUBSET G.V /\ FRANGE m.edgemap SUBSET G.E
Proof
  rw[tc_loop_invariant_def, minimally_extends_def] >>
  fs[is_track_morphism_def, partial_dom_ran_def]
QED

(* -------------------------------------------------------------------------- *)
(* Step 6: When loop terminates, graph is transitive                          *)
(*         No applicable link rule means no missing transitive edges          *)
(*                                                                            *)
(* The link rule pattern: n0 -> n1 -> n2 with condition "no edge n0 -> n2"   *)
(* If link cannot apply, then for every path v -> u -> w, edge v -> w exists *)
(* -------------------------------------------------------------------------- *)

(* Helper: link can be applied to H - semantic-level predicate *)
Definition link_can_apply_def:
  link_can_apply H <=>
    ?m h. is_prematch rule_link.lhs rule_link.inf m H /\
          apply_rule rule_link m H = SOME h
End

(* Helper: step with term_rscall succeeds iff link_can_apply.
   This connects the operational semantics to the semantic predicate. *)
Theorem step_rscall_link_iff_link_can_apply:
  !G. wf_hostgraph G ==>
      ((?G' m'. step program
                  (running (term_rscall {ruleid "link"}), [(G, id_track G)])
                  (final, [(G', m')])) <=>
       link_can_apply G)
Proof
  rw[EQ_IMP_THM]
  (* Forward: step succeeds ==> link_can_apply *)
  >- (
    pop_assum mp_tac >> simp[Once step_cases] >>
    simp[pop_stack_def, push_stack_def, program_def, FLOOKUP_UPDATE] >>
    simp[FUPDATE_LIST_THM, FLOOKUP_UPDATE] >>
    strip_tac >> simp[link_can_apply_def] >>
    qexistsl_tac [`m`, `G'`] >> simp[apply_rule_def]
  )
  (* Backward: link_can_apply ==> step succeeds *)
  >- (
    fs[link_can_apply_def, apply_rule_def] >>
    simp[Once step_cases] >>
    simp[pop_stack_def, push_stack_def, program_def, FLOOKUP_UPDATE, FUPDATE_LIST_THM] >>
    qexistsl_tac [`h`, `m`, `instance`, `assign`] >> simp[]
  )
QED

(* Backward direction: 2-path without direct edge implies link_can_apply.

   This is a structural fact: if the graph has the right shape (2-path without
   direct edge), then the link rule can apply. The proof requires:
   1. Constructing morphism m: n0->v, n1->u, n2->w, e0->edge(v,u), e1->edge(u,w)
   2. Proving is_inj_premorphism (mechanical: source/target preservation, injectivity)
   3. Proving satisfy_dangling_condition (trivial: rule_link.inf = rule_link.lhs.V)
   4. Proving apply_rule succeeds:
      - mk_assignment succeeds (rule_link has simple labels)
      - eval_rule_condition = SOME T (NAC ~edge(v,w) satisfied by assumption)
      - instantiate_rulegraph succeeds (labels are spine-form)

   Note: requires v <> w for morphism injectivity. *)
Theorem two_path_implies_link_can_apply:
  !G. wf_hostgraph G /\ unmarked_hostgraph G /\ unrooted_hostgraph G /\
      (?v u w. v IN G.V /\ u IN G.V /\ w IN G.V /\
               v <> w /\ has_edge G v u /\ has_edge G u w /\ ~has_edge G v w) ==>
      link_can_apply G
Proof
  rpt strip_tac >> fs[has_edge_def] >>
  `v <> u` by (SPOSE_NOT_THEN ASSUME_TAC >> gvs[] >>
               first_x_assum (qspec_then `e'` mp_tac) >> simp[]) >>
  `u <> w` by (SPOSE_NOT_THEN ASSUME_TAC >> gvs[] >>
               first_x_assum (qspec_then `e` mp_tac) >> simp[]) >>
  `e <> e'` by (SPOSE_NOT_THEN ASSUME_TAC >> gvs[]) >>
  simp[link_can_apply_def] >>
  qexists_tac `<| nodemap := FEMPTY |+ (nodeid "n0", v) |+ (nodeid "n1", u) |+ (nodeid "n2", w);
                  edgemap := FEMPTY |+ (edgeid "e0", e) |+ (edgeid "e1", e') |>` >>
  qabbrev_tac `m = <| nodemap := FEMPTY |+ (nodeid "n0", v) |+ (nodeid "n1", u) |+ (nodeid "n2", w);
                      edgemap := FEMPTY |+ (edgeid "e0", e) |+ (edgeid "e1", e') |>` >>
  (* Prove is_prematch *)
  sg `is_prematch rule_link.lhs rule_link.inf m G` >- (
    simp[is_prematch_def, is_inj_premorphism_def, is_premorphism_def,
         morphism_dom_ran_def, Abbr`m`, rule_link_def, preserve_source_def,
         preserve_target_def, preserve_defined_rootedness_def,
         satisfy_dangling_condition_def, FUPDATE_LIST] >> rpt conj_tac >-
    gvs[FRANGE_FUPDATE_DOMSUB, DOMSUB_NOT_IN_DOM] >-
    gvs[FRANGE_FUPDATE_DOMSUB, DOMSUB_NOT_IN_DOM] >-
    (`e IN FDOM G.s /\ e' IN FDOM G.s` by
       (fs wf_ss >> metis_tac[SUBSET_DEF]) >>
     simp[fmap_EXT, f_o_f_DEF, EXTENSION, FAPPLY_FUPDATE_THM] >> rw[] >>
     EVAL_TAC >> gvs[] >> simp[f_o_f_DEF, FAPPLY_FUPDATE_THM] >> EVAL_TAC) >-
    (`e IN FDOM G.t /\ e' IN FDOM G.t` by
       (fs wf_ss >> metis_tac[SUBSET_DEF]) >>
     simp[fmap_EXT, f_o_f_DEF, EXTENSION, FAPPLY_FUPDATE_THM] >> rw[] >>
     EVAL_TAC >> gvs[] >> simp[f_o_f_DEF, FAPPLY_FUPDATE_THM] >> EVAL_TAC) >-
    (fs[unrooted_hostgraph_def] >> simp[SUBMAP_DEF, FAPPLY_FUPDATE_THM] >> rw[] >>
     simp[f_o_f_DEF, FAPPLY_FUPDATE_THM] >> EVAL_TAC >> gvs[]) >-
    (simp[INJ_DEF, FAPPLY_FUPDATE_THM] >> rw[] >> gvs[] >> EVAL_TAC) >-
    (simp[INJ_DEF, FAPPLY_FUPDATE_THM] >> rw[] >> gvs[] >> EVAL_TAC)) >>
  simp[] >> simp[apply_rule_def, apply_ruleinstance_def] >>
  simp[PULL_EXISTS] >>
  (* Establish label properties *)
  `v IN FDOM G.l /\ u IN FDOM G.l /\ w IN FDOM G.l` by fs[wf_hostgraph_def] >>
  `e IN FDOM G.m /\ e' IN FDOM G.m` by fs[wf_hostgraph_def] >>
  fs[wf_hostgraph_def, hostgraph_labels_spine_def, unmarked_hostgraph_def,
     nodes_unmarked_def, edges_unmarked_def, FEVERY_DEF] >>
  qabbrev_tac `lv = FST (G.l ' v)` >> qabbrev_tac `lu = FST (G.l ' u)` >>
  qabbrev_tac `lw = FST (G.l ' w)` >> qabbrev_tac `la = FST (G.m ' e)` >>
  qabbrev_tac `lb = FST (G.m ' e')` >>
  `is_hostlabel_spine lv /\ is_hostlabel_spine lu /\ is_hostlabel_spine lw /\
   is_hostlabel_spine la /\ is_hostlabel_spine lb` by
    (simp[Abbr `lv`, Abbr `lu`, Abbr `lw`, Abbr `la`, Abbr `lb`] >> gvs[]) >>
  `G.l ' v = (lv, NONE)` by (simp[Abbr `lv`] >> `SND (G.l ' v) = NONE` by gvs[] >>
                              Cases_on `G.l ' v` >> gvs[]) >>
  `G.l ' u = (lu, NONE)` by (simp[Abbr `lu`] >> `SND (G.l ' u) = NONE` by gvs[] >>
                              Cases_on `G.l ' u` >> gvs[]) >>
  `G.l ' w = (lw, NONE)` by (simp[Abbr `lw`] >> `SND (G.l ' w) = NONE` by gvs[] >>
                              Cases_on `G.l ' w` >> gvs[]) >>
  `G.m ' e = (la, NONE)` by (simp[Abbr `la`] >> `SND (G.m ' e) = NONE` by gvs[] >>
                              Cases_on `G.m ' e` >> gvs[]) >>
  `G.m ' e' = (lb, NONE)` by (simp[Abbr `lb`] >> `SND (G.m ' e') = NONE` by gvs[] >>
                               Cases_on `G.m ' e'` >> gvs[]) >>
  `FLOOKUP G.l v = SOME (lv, NONE) /\ FLOOKUP G.l u = SOME (lu, NONE) /\
   FLOOKUP G.l w = SOME (lw, NONE) /\ FLOOKUP G.m e = SOME (la, NONE) /\
   FLOOKUP G.m e' = SOME (lb, NONE)` by simp[FLOOKUP_DEF] >>
  `FLOOKUP m.nodemap (nodeid "n0") = SOME v /\ FLOOKUP m.nodemap (nodeid "n1") = SOME u /\
   FLOOKUP m.nodemap (nodeid "n2") = SOME w /\ FLOOKUP m.edgemap (edgeid "e0") = SOME e /\
   FLOOKUP m.edgemap (edgeid "e1") = SOME e'` by simp[Abbr `m`, FLOOKUP_UPDATE] >>
  (* Prove mk_assignment_node results *)
  `mk_assignment_node rule_link m G (nodeid "n0") = SOME (FEMPTY |+ (varname "x", lv)) /\
   mk_assignment_node rule_link m G (nodeid "n1") = SOME (FEMPTY |+ (varname "y", lu)) /\
   mk_assignment_node rule_link m G (nodeid "n2") = SOME (FEMPTY |+ (varname "z", lw))` by
    (rpt conj_tac >> simp[mk_assignment_node_def, semTheory.unify_nodeattr_def,
                          semTheory.nodemark_matches_def, rule_link_def, FLOOKUP_UPDATE, Abbr`m`] >>
     EVAL_TAC >> gvs[] >> simp[semTheory.unify_nodeattr_def, semTheory.nodemark_matches_def] >>
     irule ruleAppPropsTheory.unify_label_simple_singleton >> simp[FLOOKUP_UPDATE] >> EVAL_TAC) >>
  (* Prove mk_assignment_edge results *)
  `mk_assignment_edge rule_link m G (edgeid "e0") = SOME (FEMPTY |+ (varname "a", la)) /\
   mk_assignment_edge rule_link m G (edgeid "e1") = SOME (FEMPTY |+ (varname "b", lb))` by
    (rpt conj_tac >> simp[mk_assignment_edge_def, semTheory.unify_edgeattr_def,
                          semTheory.edgemark_matches_def, rule_link_def, FLOOKUP_UPDATE, Abbr`m`] >>
     EVAL_TAC >> gvs[] >> simp[semTheory.unify_edgeattr_def, semTheory.edgemark_matches_def] >>
     irule ruleAppPropsTheory.unify_label_simple_singleton >> simp[FLOOKUP_UPDATE] >> EVAL_TAC) >>
  `rule_link.lhs.V = {nodeid "n0"; nodeid "n1"; nodeid "n2"} /\
   rule_link.lhs.E = {edgeid "e0"; edgeid "e1"} /\
   FINITE rule_link.lhs.V /\ FINITE rule_link.lhs.E` by EVAL_TAC >>
  (* Prove mk_assignment_nodes succeeds with FDOM characterization *)
  sg `?nassign. mk_assignment_nodes rule_link m G = SOME nassign /\
      FDOM nassign = {varname "x"; varname "y"; varname "z"}` >- (
    simp[mk_assignment_nodes_def] >>
    qspec_then `SET_TO_LIST {nodeid "n0"; nodeid "n1"; nodeid "n2"}`
      mp_tac ruleAppPropsTheory.foldr_singleton_merge >>
    disch_then (qspec_then `mk_assignment_node rule_link m G` mp_tac) >>
    impl_tac >- (
      rpt conj_tac >-
      simp[ALL_DISTINCT_SET_TO_LIST] >-
      (rw[] >> rpt strip_tac >> gvs[MEM_SET_TO_LIST] >-
       (qexists_tac `varname "x"` >> qexists_tac `lv` >> simp[]) >-
       (qexists_tac `varname "y"` >> qexists_tac `lu` >> simp[]) >-
       (qexists_tac `varname "z"` >> qexists_tac `lw` >> simp[])) >-
      (rpt strip_tac >> gvs[MEM_SET_TO_LIST] >-
       (simp[] >> gvs[FEMPTY_FUPDATE_EQ]) >-
       fs[FEMPTY_FUPDATE_EQ] >-
       (gvs[FEMPTY_FUPDATE_EQ] >> EVAL_TAC) >-
       (`varname "z" = k1` by (qpat_x_assum `FEMPTY |+ (varname "z",lw) = _` mp_tac >>
                               simp[FEMPTY_FUPDATE_EQ]) >>
        `varname "y" = k1` by (qpat_x_assum `FEMPTY |+ (varname "y",lu) = _` mp_tac >>
                               simp[FEMPTY_FUPDATE_EQ]) >> gvs[]) >-
       (fs[FEMPTY_FUPDATE_EQ] >> gvs[] >> EVAL_TAC) >-
       fs[FEMPTY_FUPDATE_EQ, rulegraphTheory.varname_11])) >-
    (strip_tac >> qexists_tac `result` >> simp[] >>
     simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >> gvs[] >-
     fs[FEMPTY_FUPDATE_EQ] >-
     gvs[FEMPTY_FUPDATE_EQ] >-
     fs[FEMPTY_FUPDATE_EQ] >-
     (qexists_tac `nodeid "n0"` >> qexists_tac `lv` >> simp[]) >-
     (qexists_tac `nodeid "n1"` >> qexists_tac `lu` >> simp[]) >-
     (qexists_tac `nodeid "n2"` >> qexists_tac `lw` >> simp[]))) >>
  (* Prove mk_assignment_edges succeeds with FDOM characterization *)
  sg `?eassign. mk_assignment_edges rule_link m G = SOME eassign /\
      FDOM eassign = {varname "a"; varname "b"}` >- (
    simp[mk_assignment_edges_def] >>
    qspec_then `SET_TO_LIST {edgeid "e0"; edgeid "e1"}`
      mp_tac ruleAppPropsTheory.foldr_singleton_merge >>
    disch_then (qspec_then `mk_assignment_edge rule_link m G` mp_tac) >>
    impl_tac >- (
      rpt conj_tac >-
      simp[ALL_DISTINCT_SET_TO_LIST] >-
      (rw[] >> rpt strip_tac >> gvs[MEM_SET_TO_LIST] >-
       (qexists_tac `varname "a"` >> qexists_tac `la` >> simp[]) >-
       (qexists_tac `varname "b"` >> qexists_tac `lb` >> simp[])) >-
      (rpt strip_tac >> gvs[MEM_SET_TO_LIST] >-
       fs[FEMPTY_FUPDATE_EQ, rulegraphTheory.varname_11] >-
       (qpat_x_assum `FEMPTY |+ (varname "a",_) = _` mp_tac >>
        qpat_x_assum `FEMPTY |+ (varname "b",_) = _` mp_tac >>
        simp[FEMPTY_FUPDATE_EQ]))) >-
    (strip_tac >> qexists_tac `result` >> simp[] >>
     simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >> gvs[] >-
     fs[FEMPTY_FUPDATE_EQ] >-
     fs[FEMPTY_FUPDATE_EQ] >-
     (qexists_tac `edgeid "e0"` >> qexists_tac `la` >> simp[]) >-
     (qexists_tac `edgeid "e1"` >> qexists_tac `lb` >> simp[]))) >>
  (* Prove agree_on_common_keys *)
  `agree_on_common_keys nassign eassign` by
    (irule ruleAppPropsTheory.disjoint_agree >> simp[]) >>
  (* Prove mk_assignment succeeds *)
  `mk_assignment rule_link m G = SOME (nassign ⊌ eassign)` by
    simp[mk_assignment_def, merge_assignment_def] >>
  qabbrev_tac `assign = nassign ⊌ eassign` >>
  simp[PULL_EXISTS] >>
  simp[instantiate_rule_def, PULL_EXISTS] >>
  (* Prove eval_rule_condition = SOME T (NAC satisfied) *)
  sg `eval_rule_condition rule_link assign m G = SOME T` >- (
    simp[eval_rule_condition_def, rule_link_def, eval_condition_fun_def,
         FLOOKUP_UPDATE, Abbr`m`] >>
    simp[EVERY_MEM, MEM_SET_TO_LIST] >>
    rpt strip_tac >> gvs[MEM_SET_TO_LIST] >>
    `FINITE G.E` by fs[wf_graph_def] >>
    `e'' IN G.E` by fs[MEM_SET_TO_LIST] >>
    `G.s ' e'' = G.s ' e` by (fs[FLOOKUP_DEF, wf_graph_def] >> metis_tac[SUBSET_DEF]) >>
    `G.t ' e'' = G.t ' e'` by (fs[FLOOKUP_DEF, wf_graph_def] >> metis_tac[SUBSET_DEF]) >>
    metis_tac[]) >>
  simp[] >>
  (* Establish FLOOKUP facts for assign via foldr_merge_SUBMAP *)
  qpat_x_assum `mk_assignment_nodes rule_link m G = SOME nassign` mp_tac >>
  simp[mk_assignment_nodes_def] >> DISCH_TAC >>
  sg `FLOOKUP nassign (varname "x") = SOME lv /\ FLOOKUP nassign (varname "y") = SOME lu /\
      FLOOKUP nassign (varname "z") = SOME lw` >- (
    (* For varname "x" via nodeid "n0" *)
    qspecl_then [`mk_assignment_node rule_link m G`, `SET_TO_LIST rule_link.lhs.V`,
                 `nassign`, `nodeid "n0"`] mp_tac semTheory.foldr_merge_SUBMAP >>
    impl_tac >- simp[MEM_SET_TO_LIST] >> strip_tac >>
    `a_x = FEMPTY |+ (varname "x", lv)` by gvs[] >>
    `FLOOKUP a_x (varname "x") = SOME lv` by simp[FLOOKUP_UPDATE] >>
    sg `FLOOKUP nassign (varname "x") = SOME lv` >- metis_tac[SUBMAP_FLOOKUP_EQN] >>
    simp[] >>
    (* For varname "y" via nodeid "n1" *)
    qspecl_then [`mk_assignment_node rule_link m G`, `SET_TO_LIST rule_link.lhs.V`,
                 `nassign`, `nodeid "n1"`] mp_tac semTheory.foldr_merge_SUBMAP >>
    impl_tac >- simp[MEM_SET_TO_LIST] >> strip_tac >>
    `a_x' = FEMPTY |+ (varname "y", lu)` by gvs[] >>
    `FLOOKUP a_x' (varname "y") = SOME lu` by simp[FLOOKUP_UPDATE] >>
    sg `FLOOKUP nassign (varname "y") = SOME lu` >- metis_tac[SUBMAP_FLOOKUP_EQN] >>
    simp[] >>
    (* For varname "z" via nodeid "n2" *)
    qspecl_then [`mk_assignment_node rule_link m G`, `SET_TO_LIST rule_link.lhs.V`,
                 `nassign`, `nodeid "n2"`] mp_tac semTheory.foldr_merge_SUBMAP >>
    impl_tac >- simp[MEM_SET_TO_LIST] >> strip_tac >>
    `a_x'' = FEMPTY |+ (varname "z", lw)` by gvs[] >>
    `FLOOKUP a_x'' (varname "z") = SOME lw` by simp[FLOOKUP_UPDATE] >>
    metis_tac[SUBMAP_FLOOKUP_EQN]) >>
  qpat_x_assum `mk_assignment_edges rule_link m G = SOME eassign` mp_tac >>
  simp[mk_assignment_edges_def] >> DISCH_TAC >>
  sg `FLOOKUP eassign (varname "a") = SOME la /\ FLOOKUP eassign (varname "b") = SOME lb` >- (
    (* For varname "a" via edgeid "e0" *)
    qspecl_then [`mk_assignment_edge rule_link m G`, `SET_TO_LIST rule_link.lhs.E`,
                 `eassign`, `edgeid "e0"`] mp_tac semTheory.foldr_merge_SUBMAP >>
    impl_tac >- simp[MEM_SET_TO_LIST] >> strip_tac >>
    `a_x = FEMPTY |+ (varname "a", la)` by gvs[] >>
    `FLOOKUP a_x (varname "a") = SOME la` by simp[FLOOKUP_UPDATE] >>
    sg `FLOOKUP eassign (varname "a") = SOME la` >- metis_tac[SUBMAP_FLOOKUP_EQN] >>
    simp[] >>
    (* For varname "b" via edgeid "e1" *)
    qspecl_then [`mk_assignment_edge rule_link m G`, `SET_TO_LIST rule_link.lhs.E`,
                 `eassign`, `edgeid "e1"`] mp_tac semTheory.foldr_merge_SUBMAP >>
    impl_tac >- simp[MEM_SET_TO_LIST] >> strip_tac >>
    `a_x' = FEMPTY |+ (varname "b", lb)` by gvs[] >>
    `FLOOKUP a_x' (varname "b") = SOME lb` by simp[FLOOKUP_UPDATE] >>
    metis_tac[SUBMAP_FLOOKUP_EQN]) >>
  (* FLOOKUP facts for assign = nassign ⊌ eassign *)
  `FLOOKUP assign (varname "x") = SOME lv /\ FLOOKUP assign (varname "y") = SOME lu /\
   FLOOKUP assign (varname "z") = SOME lw /\ FLOOKUP assign (varname "a") = SOME la /\
   FLOOKUP assign (varname "b") = SOME lb` by
    (simp[Abbr`assign`, FLOOKUP_FUNION] >> rpt conj_tac >> simp[] >>
     `varname "a" NOTIN FDOM nassign /\ varname "b" NOTIN FDOM nassign` by simp[] >>
     simp[FLOOKUP_DEF]) >>
  (* Establish f_o_f FLOOKUP facts *)
  `FLOOKUP (G.l f_o_f m.nodemap) (nodeid "n0") = SOME (lv, NONE) /\
   FLOOKUP (G.l f_o_f m.nodemap) (nodeid "n1") = SOME (lu, NONE) /\
   FLOOKUP (G.l f_o_f m.nodemap) (nodeid "n2") = SOME (lw, NONE)` by
    (simp[FLOOKUP_DEF, f_o_f_DEF, FLOOKUP_UPDATE, Abbr`m`] >> simp[FAPPLY_FUPDATE_THM]) >>
  `FLOOKUP (G.m f_o_f m.edgemap) (edgeid "e0") = SOME (la, NONE) /\
   FLOOKUP (G.m f_o_f m.edgemap) (edgeid "e1") = SOME (lb, NONE)` by
    (simp[FLOOKUP_DEF, f_o_f_DEF, FLOOKUP_UPDATE, Abbr`m`] >> simp[FAPPLY_FUPDATE_THM]) >>
  (* Rule label FLOOKUP facts *)
  `FLOOKUP rule_link.lhs.l (nodeid "n0") = SOME (label_cons (label_variable (varname "x")) label_nil, NONE) /\
   FLOOKUP rule_link.lhs.l (nodeid "n1") = SOME (label_cons (label_variable (varname "y")) label_nil, NONE) /\
   FLOOKUP rule_link.lhs.l (nodeid "n2") = SOME (label_cons (label_variable (varname "z")) label_nil, NONE)` by EVAL_TAC >>
  `FLOOKUP rule_link.lhs.m (edgeid "e0") = SOME (label_cons (label_variable (varname "a")) label_nil, NONE) /\
   FLOOKUP rule_link.lhs.m (edgeid "e1") = SOME (label_cons (label_variable (varname "b")) label_nil, NONE)` by EVAL_TAC >>
  (* instantiate_nodeattr facts for LHS nodes *)
  sg `instantiate_nodeattr rule_link.lhs assign m G (nodeid "n0") = SOME (lv, NONE)` >-
    (irule ruleAppPropsTheory.instantiate_nodeattr_simple_matched >> simp[] >>
     qexists_tac `lv` >> qexists_tac `varname "x"` >> simp[]) >>
  sg `instantiate_nodeattr rule_link.lhs assign m G (nodeid "n1") = SOME (lu, NONE)` >-
    (irule ruleAppPropsTheory.instantiate_nodeattr_simple_matched >> simp[] >>
     qexists_tac `lu` >> qexists_tac `varname "y"` >> simp[]) >>
  sg `instantiate_nodeattr rule_link.lhs assign m G (nodeid "n2") = SOME (lw, NONE)` >-
    (irule ruleAppPropsTheory.instantiate_nodeattr_simple_matched >> simp[] >>
     qexists_tac `lw` >> qexists_tac `varname "z"` >> simp[]) >>
  (* instantiate_edgeattr facts for LHS edges *)
  sg `instantiate_edgeattr rule_link.lhs assign m G (edgeid "e0") = SOME (la, NONE)` >-
    (irule ruleAppPropsTheory.instantiate_edgeattr_simple_matched >> simp[] >>
     qexists_tac `la` >> qexists_tac `varname "a"` >> simp[]) >>
  sg `instantiate_edgeattr rule_link.lhs assign m G (edgeid "e1") = SOME (lb, NONE)` >-
    (irule ruleAppPropsTheory.instantiate_edgeattr_simple_matched >> simp[] >>
     qexists_tac `lb` >> qexists_tac `varname "b"` >> simp[]) >>
  (* FDOM facts for rule_link.lhs *)
  `FDOM rule_link.lhs.l = {nodeid "n0"; nodeid "n1"; nodeid "n2"} /\
   FDOM rule_link.lhs.m = {edgeid "e0"; edgeid "e1"} /\
   FINITE (FDOM rule_link.lhs.l) /\ FINITE (FDOM rule_link.lhs.m)` by EVAL_TAC >>
  (* Prove instantiate_rulegraph rule_link.lhs succeeds *)
  sg `?lhs'. instantiate_rulegraph rule_link.lhs assign m G = SOME lhs'` >- (
    simp[semTheory.instantiate_rulegraph_def, PULL_EXISTS] >>
    sg `?l. fmap_buildM (instantiate_nodeattr rule_link.lhs assign m G)
              {nodeid "n0"; nodeid "n1"; nodeid "n2"} = SOME l` >-
      (irule semTheory.fmap_buildM_succeeds >> simp[] >> rpt strip_tac >>
       gvs[] >> metis_tac[]) >>
    simp[PULL_EXISTS] >>
    irule semTheory.fmap_buildM_succeeds >> simp[] >> rpt strip_tac >>
    gvs[] >> metis_tac[]) >>
  (* Now for RHS - same nodes, edges e0,e1 plus fresh edge e2 *)
  `FLOOKUP rule_link.rhs.l (nodeid "n0") = SOME (label_cons (label_variable (varname "x")) label_nil, NONE) /\
   FLOOKUP rule_link.rhs.l (nodeid "n1") = SOME (label_cons (label_variable (varname "y")) label_nil, NONE) /\
   FLOOKUP rule_link.rhs.l (nodeid "n2") = SOME (label_cons (label_variable (varname "z")) label_nil, NONE)` by EVAL_TAC >>
  `FLOOKUP rule_link.rhs.m (edgeid "e0") = SOME (label_cons (label_variable (varname "a")) label_nil, NONE) /\
   FLOOKUP rule_link.rhs.m (edgeid "e1") = SOME (label_cons (label_variable (varname "b")) label_nil, NONE) /\
   FLOOKUP rule_link.rhs.m (edgeid "e2") = SOME (label_nil, NONE)` by EVAL_TAC >>
  (* instantiate_nodeattr facts for RHS nodes (same as LHS) *)
  sg `instantiate_nodeattr rule_link.rhs assign m G (nodeid "n0") = SOME (lv, NONE)` >-
    (irule ruleAppPropsTheory.instantiate_nodeattr_simple_matched >> simp[] >>
     qexists_tac `lv` >> qexists_tac `varname "x"` >> simp[]) >>
  sg `instantiate_nodeattr rule_link.rhs assign m G (nodeid "n1") = SOME (lu, NONE)` >-
    (irule ruleAppPropsTheory.instantiate_nodeattr_simple_matched >> simp[] >>
     qexists_tac `lu` >> qexists_tac `varname "y"` >> simp[]) >>
  sg `instantiate_nodeattr rule_link.rhs assign m G (nodeid "n2") = SOME (lw, NONE)` >-
    (irule ruleAppPropsTheory.instantiate_nodeattr_simple_matched >> simp[] >>
     qexists_tac `lw` >> qexists_tac `varname "z"` >> simp[]) >>
  (* instantiate_edgeattr facts for RHS edges (e0, e1 matched, e2 fresh) *)
  sg `instantiate_edgeattr rule_link.rhs assign m G (edgeid "e0") = SOME (la, NONE)` >-
    (irule ruleAppPropsTheory.instantiate_edgeattr_simple_matched >> simp[] >>
     qexists_tac `la` >> qexists_tac `varname "a"` >> simp[]) >>
  sg `instantiate_edgeattr rule_link.rhs assign m G (edgeid "e1") = SOME (lb, NONE)` >-
    (irule ruleAppPropsTheory.instantiate_edgeattr_simple_matched >> simp[] >>
     qexists_tac `lb` >> qexists_tac `varname "b"` >> simp[]) >>
  (* e2 is fresh - not in m.edgemap, so FLOOKUP (G.m f_o_f m.edgemap) = NONE *)
  `FLOOKUP (G.m f_o_f m.edgemap) (edgeid "e2") = NONE` by
    (simp[FLOOKUP_DEF, f_o_f_DEF, Abbr`m`]) >>
  sg `instantiate_edgeattr rule_link.rhs assign m G (edgeid "e2") = SOME (label_nil, NONE)` >-
    (irule ruleAppPropsTheory.instantiate_edgeattr_nil_fresh >> simp[]) >>
  (* FDOM facts for rule_link.rhs *)
  `FDOM rule_link.rhs.l = {nodeid "n0"; nodeid "n1"; nodeid "n2"} /\
   FDOM rule_link.rhs.m = {edgeid "e0"; edgeid "e1"; edgeid "e2"} /\
   FINITE (FDOM rule_link.rhs.l) /\ FINITE (FDOM rule_link.rhs.m)` by EVAL_TAC >>
  (* Prove instantiate_rulegraph rule_link.rhs succeeds *)
  sg `?rhs'. instantiate_rulegraph rule_link.rhs assign m G = SOME rhs'` >- (
    simp[semTheory.instantiate_rulegraph_def, PULL_EXISTS] >>
    sg `?l. fmap_buildM (instantiate_nodeattr rule_link.rhs assign m G)
              {nodeid "n0"; nodeid "n1"; nodeid "n2"} = SOME l` >-
      (irule semTheory.fmap_buildM_succeeds >> simp[] >> rpt strip_tac >>
       gvs[] >> metis_tac[]) >>
    sg `?m'. fmap_buildM (instantiate_edgeattr rule_link.rhs assign m G)
               {edgeid "e0"; edgeid "e1"; edgeid "e2"} = SOME m'` >-
      (irule semTheory.fmap_buildM_succeeds >> simp[] >> rpt strip_tac >>
       gvs[] >> metis_tac[]) >>
    simp[PULL_EXISTS]) >>
  simp[]
QED

(* Characterization: link applies iff there's a 2-path without direct edge
 *
 * Proof outline:
 * (=>) If step succeeds via Call1:
 *   - pop_stack gives G'' = G
 *   - FLOOKUP program.rule (ruleid "link") = SOME rule_link
 *   - is_prematch rule_link.lhs rule_link.inf m G implies:
 *     * m is injective morphism from LHS (nodes n0,n1,n2; edges e0,e1) to G
 *     * preserve_source/target: m maps e0:(n0→n1) to edge in G, similarly e1:(n1→n2)
 *     * So has_edge G (m.nodemap ' n0) (m.nodemap ' n1) and
 *           has_edge G (m.nodemap ' n1) (m.nodemap ' n2)
 *   - instantiate_rule success implies eval_rule_condition returns SOME T
 *     * rule_link.cond = SOME (condNot (condEdgeTest n0 n2 NONE))
 *     * eval_condition_fun evaluates to: no edge from m(n0) to m(n2)
 *     * So ~has_edge G (m.nodemap ' n0) (m.nodemap ' n2)
 *   - Witnesses: v = m.nodemap ' n0, u = m.nodemap ' n1, w = m.nodemap ' n2
 *
 * (<=) If 2-path v→u→w exists without v→w:
 *   - Construct morphism m with m.nodemap ' n0 = v, m.nodemap ' n1 = u, m.nodemap ' n2 = w
 *   - The edges v→u and u→w provide m.edgemap mappings
 *   - Show is_prematch holds (injective, dangling condition trivial for this rule)
 *   - Show instantiate_rule succeeds (condition ~has_edge v w holds by assumption)
 *   - Apply step_Call1 rule
 *)
Theorem no_link_implies_transitive:
  !G. wf_hostgraph G /\ unmarked_hostgraph G /\ unrooted_hostgraph G /\
      ~(?G' m'. step program
                  (running (term_rscall {ruleid "link"}), [(G, id_track G)])
                  (final, [(G', m')])) ==>
      is_transitive G
Proof
  (* No link applicable means for all v, u, w with v -> u -> w,
     there exists edge v -> w. Then any reachable path has direct edge. *)
  rpt strip_tac >>
  `~link_can_apply G` by (drule step_rscall_link_iff_link_can_apply >> fs[]) >>
  (* Key step: no link applicable implies two-step closure for v ≠ w *)
  sg `!v' u' w'. v' IN G.V /\ u' IN G.V /\ w' IN G.V /\ has_edge G v' u' /\
                 has_edge G u' w' /\ v' <> w' ==> has_edge G v' w'`
  >- (rpt strip_tac >> SPOSE_NOT_THEN ASSUME_TAC >>
      `link_can_apply G` by
        (irule two_path_implies_link_can_apply >> simp[] >> metis_tac[]))
  >- (
    (* Show path implies direct edge by induction on path length *)
    simp[pathTheory.is_transitive_def] >>
    rpt strip_tac >> fs[pathTheory.reachable_in_def] >>
    pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >>
    pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >>
    qid_spec_tac `w` >> qid_spec_tac `v` >> Induct_on `path_length p`
    >- (rw[] >> fs[pathTheory.path_length_nontrivial])
    >- (
      rw[] >> Cases_on `p`
      >- fs[pathTheory.path_length_def]
      >- (
        fs[pathTheory.path_start_def, pathTheory.path_end_def,
           pathTheory.wf_path_def, pathTheory.path_length_def] >>
        qabbrev_tac `u = path_start p'` >>
        `has_edge G n u` by
          (simp[pathTheory.has_edge_def] >> qexists_tac `e` >> simp[Abbr `u`]) >>
        `u IN G.V` by simp[Abbr `u`, pathTheory.wf_path_start_in_V] >>
        Cases_on `u = path_end p'`
        >- gvs[]
        >- (
          sg `is_nontrivial_path p'`
          >- (fs[pathTheory.is_nontrivial_path_def, Abbr `u`] >>
              simp[pathTheory.path_length_nontrivial] >>
              Cases_on `p'` >>
              fs[pathTheory.path_length_def, pathTheory.path_start_def,
                 pathTheory.path_end_def])
          >- (
            `has_edge G (path_start p') (path_end p')` by
              (first_x_assum (qspec_then `p'` mp_tac) >> simp[]) >>
            first_x_assum (qspecl_then [`n`, `path_start p'`, `path_end p'`] mp_tac) >>
            simp[])))))
QED

(* When link rule fails (steps to failed), the graph is transitive.
   This connects failure semantics to the graph property.
   Key idea: if steps reaches (failed, _), then no step to (final, _) exists,
   so by no_link_implies_transitive, the graph is transitive. *)
Theorem link_failure_implies_transitive:
  !G0 G m.
    wf_hostgraph G /\ tc_loop_invariant G0 G m /\
    steps program (running (term_rscall {ruleid "link"}), [(G, id_track G)])
                  (failed, [(G, id_track G)]) ==>
    is_transitive G
Proof
  rpt strip_tac >> fs[tc_loop_invariant_def] >>
  irule no_link_implies_transitive >> simp[] >>
  (* Show: if we have step to (final, _), derive contradiction *)
  rpt strip_tac >>
  fs[semTheory.steps_def] >>
  fs[Once relationTheory.RTC_CASES1] >>
  (* Decompose: (running...) steps to u, then u steps* to (failed...) *)
  `?stk. u = (final, stk) \/ u = (failed, stk)` by
    (qpat_x_assum `step _ (running (term_rscall _), _) u` mp_tac >>
     simp[Once semTheory.step_cases] >> rpt strip_tac >> gvs[])
  (* Case: u = (final, stk) - can't step from final to reach failed *)
  >- (gvs[] >> fs[Once relationTheory.RTC_CASES1] >>
      qpat_x_assum `step _ (final, _) _` mp_tac >> simp[Once semTheory.step_cases])
  (* Case: u = (failed, stk) - but we also have step to (final, _)
     This contradicts determinism of term_rscall: Call1 and Call2 are mutually exclusive *)
  >- (gvs[] >>
      (* Expand both step assumptions *)
      qpat_x_assum `step _ (running (term_rscall _), _) (final, _)` mp_tac >>
      qpat_x_assum `step _ (running (term_rscall _), _) (failed, _)` mp_tac >>
      simp[Once semTheory.step_cases, SimpL ``$==>``, stackTheory.pop_stack_def] >>
      strip_tac >> gvs[Once semTheory.step_cases, stackTheory.pop_stack_def,
                       stackTheory.push_stack_def] >>
      simp[Once semTheory.step_cases, stackTheory.pop_stack_def,
           stackTheory.push_stack_def] >>
      rpt strip_tac >>
      (* We have: no rule matched (from failed step) AND rule applied (from final step) *)
      `apply_rule r m'' G = SOME G'` by
        (simp[semTheory.apply_rule_def] >> qexistsl [`assign`, `ri`] >> simp[]) >>
      (* But "no rule matched" says apply_rule => ~is_prematch, contradicting assumption *)
      first_x_assum (qspecl_then [`r`, `m''`, `G'`] mp_tac) >> simp[])
QED

(* -------------------------------------------------------------------------- *)
(* Step 7: Loop invariant at termination implies transitive closure           *)
(* -------------------------------------------------------------------------- *)

Theorem tc_invariant_termination:
  !G0 TC track_bar.
    tc_loop_invariant_total G0 TC track_bar /\
    is_transitive TC ==>
    is_transitive_closure_tracked G0 track_bar TC
Proof
  rw[tc_loop_invariant_total_def,
     is_transitive_closure_tracked_def]
QED

(* -------------------------------------------------------------------------- *)
(* Helper: For term_rscall, multi-step to final = single step to final        *)
(* -------------------------------------------------------------------------- *)

Theorem rscall_steps_to_step:
  !env rset G G' m'.
    steps env (running (term_rscall rset), [(G, id_track G)])
              (final, [(G', m')]) ==>
    step env (running (term_rscall rset), [(G, id_track G)])
             (final, [(G', m')])
Proof
  rpt strip_tac >>
  fs[semTheory.steps_def] >>
  qpat_x_assum `RTC _ _ _` mp_tac >>
  simp[Once relationTheory.RTC_CASES1] >> strip_tac >>
  (* Get intermediate u with step ... u and RTC u (final, ...) *)
  `?stk. u = (final, stk) \/ u = (failed, stk)` by
    (qpat_x_assum `step _ (running (term_rscall _), _) u` mp_tac >>
     simp[Once semTheory.step_cases] >> rpt strip_tac >> gvs[])
  (* u = (final, stk): final can't step, so RTC is reflexive *)
  >- (gvs[] >>
      qpat_x_assum `RTC _ _ _` mp_tac >>
      simp[Once relationTheory.RTC_CASES1] >> strip_tac
      >- gvs[]
      >- (qpat_x_assum `step _ (final, _) _` mp_tac >>
          simp[Once semTheory.step_cases]))
  (* u = (failed, stk): failed can't step to reach final *)
  >- (gvs[] >>
      qpat_x_assum `RTC _ _ _` mp_tac >>
      simp[Once relationTheory.RTC_CASES1] >>
      strip_tac >>
      qpat_x_assum `step _ (failed, _) _` mp_tac >>
      simp[Once semTheory.step_cases])
QED

(* -------------------------------------------------------------------------- *)
(* Helper: steps execution preserves stack_tracks_morphism                    *)
(* -------------------------------------------------------------------------- *)

Theorem steps_to_stack_tracks:
  !env t G0 H m.
    wf_program env /\ wf_hostgraph G0 /\
    steps env (running (term_alap t), [(G0, id_track G0)]) (final, [(H, m)]) ==>
    stack_tracks_morphism G0 [(H, m)]
Proof
  rpt strip_tac >>
  fs[semTheory.steps_def] >>
  drule arithmeticTheory.RTC_NRC >> strip_tac >>
  `wf_stack_labels [(G0, id_track G0)]` by simp[semTheory.wf_stack_labels_def] >>
  `stack_tracks_morphism G0 [(G0, id_track G0)]` by
    (irule semPropsTheory.initial_stack_tracks_morphism >> simp[]) >>
  drule_all semPropsTheory.NRC_step_preserves_stack_tracks_morphism >>
  simp[]
QED

(* Minimal Extension: Inductive construction of total track_bar morphism     *)

(* -------------------------------------------------------------------------- *)
(* Base case: identity morphism is a minimal extension                        *)
(* -------------------------------------------------------------------------- *)

Theorem minimal_extension_initial:
  !G0. wf_hostgraph G0 /\ unrooted_hostgraph G0 ==>
       minimal_extension G0 (id_track G0) G0
Proof
  rw[minimal_extension_def] >> rpt strip_tac >>
  `FINITE G0.E` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  `FINITE G0.V` by metis_tac[wf_hostgraph_IMP_finite_sets]
  (* is_inj_morphism *)
  >- (simp[is_inj_morphism_def, is_morphism_def, is_premorphism_def,
           morphism_dom_ran_def] >>
      simp[FDOM_id_track_nodemap, FDOM_id_track_edgemap,
           FRANGE_id_track_nodemap, FRANGE_id_track_edgemap, SUBSET_REFL] >>
      rpt conj_tac
      (* preserve_source *)
      >- (simp[preserve_source_def, id_track_def] >>
          fs[wf_hostgraph_def, wf_graph_def] >>
          metis_tac[FUN_FMAP_I_f_o_f_left, FUN_FMAP_I_f_o_f_right])
      (* preserve_target *)
      >- (simp[preserve_target_def, id_track_def] >>
          fs[wf_hostgraph_def, wf_graph_def] >>
          metis_tac[FUN_FMAP_I_f_o_f_left, FUN_FMAP_I_f_o_f_right])
      (* preserve_defined_rootedness *)
      >- (simp[preserve_defined_rootedness_def, id_track_def, SUBMAP_DEF,
               f_o_f_DEF] >>
          rpt strip_tac >> fs[wf_hostgraph_def, wf_graph_def, SUBSET_DEF] >>
          res_tac >> simp[FUN_FMAP_APPLY] >>
          `x IN FDOM (G0.p f_o_f FUN_FMAP I G0.V)`
            by (simp[f_o_f_DEF, FUN_FMAP_APPLY]) >>
          `(G0.p f_o_f FUN_FMAP I G0.V) ' x =
           G0.p ' ((FUN_FMAP I G0.V) ' x)`
            by metis_tac[cj 2 f_o_f_DEF] >>
          simp[FUN_FMAP_APPLY])
      (* preserve_edgelabels *)
      >- (rw[preserve_edgelabels_def, id_track_def] >>
          `FDOM G0.m = G0.E` by fs[wf_hostgraph_def, wf_graph_def] >>
          irule (GSYM FUN_FMAP_I_f_o_f_right) >> simp[])
      (* preserve_nodelabels *)
      >- (rw[preserve_nodelabels_def, id_track_def] >>
          `FDOM G0.l = G0.V` by fs[wf_hostgraph_def, wf_graph_def] >>
          irule (GSYM FUN_FMAP_I_f_o_f_right) >> simp[])
      (* INJ nodemap *)
      >- simp[INJ_DEF, id_track_nodemap_apply]
      (* INJ edgemap *)
      >- simp[INJ_DEF, id_track_edgemap_apply])
  (* BIJ *)
  >- simp[id_track_nodemap_BIJ]
  (* edge_path_justified — vacuous, no generated edges *)
  >- (irule empty_generated_edges_justified >> simp[id_track_no_generated_edges])
  (* parallel_free_extension — vacuous, no generated edges *)
  >- (irule no_generated_parallel_free >> simp[id_track_no_generated_edges])
QED

(* -------------------------------------------------------------------------- *)
(* DPO label lemmas (local to this theory)                                    *)
(* -------------------------------------------------------------------------- *)

Theorem wf_hostgraph_FDOM_m_eq_E:
  !G. wf_hostgraph G ==> FDOM G.m = G.E
Proof
  rpt strip_tac >> fs wf_ss
QED

(* Right-tagged edges get R's edge label *)
Theorem gluing_m_apply_right_tagged:
  !H R e. e IN R.E /\ wf_graph H /\ wf_graph R /\ FINITE (gluing_edges H R) ==>
    (gluing_m (gluing_edges H R) H R) ' (tag_edgeid_right e) = R.m ' e
Proof
  rpt strip_tac
  \\ qabbrev_tac `entries = MAP (\eid. if is_left_tagged_edgeid eid
                                       then (eid, H.m ' (untag_edgeid eid))
                                       else (eid, R.m ' (untag_edgeid eid)))
                                (SET_TO_LIST (gluing_edges H R))`
  \\ `ALL_DISTINCT (MAP FST entries)` by (
    unabbrev_all_tac
    \\ rw[MAP_MAP_o, combinTheory.o_DEF]
    \\ simp[COND_RAND, pairTheory.FST]
    \\ irule ALL_DISTINCT_SET_TO_LIST
    \\ fs[])
  \\ `~is_left_tagged_edgeid (tag_edgeid_right e)` by (
    rw[taggingTheory.is_left_tagged_edgeid_def, taggingTheory.tag_edgeid_right_def,
       graphTheory.edgeid_absrep]
    \\ rw[arithmeticTheory.EVEN_ODD, GSYM arithmeticTheory.ADD1,
          arithmeticTheory.ODD_DOUBLE])
  \\ `MEM (tag_edgeid_right e, R.m ' e) entries` by (
    unabbrev_all_tac
    \\ rw[MEM_MAP]
    \\ qexists_tac `tag_edgeid_right e`
    \\ rw[taggingTheory.tag_untag_edgeid_inv, MEM_SET_TO_LIST, gluing_edges_def,
          edgeid_coprod_def])
  \\ `FLOOKUP (FEMPTY |++ entries) (tag_edgeid_right e) = SOME (R.m ' e)` by (
    irule alistTheory.mem_to_flookup
    \\ rw[])
  \\ fs[flookup_thm, FDOM_FUPDATE_LIST]
  \\ pop_assum mp_tac
  \\ simp[gluing_m_def, LET_DEF]
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
  rpt strip_tac
  \\ qabbrev_tac `V = gluing_nodes H Kv R`
  \\ qabbrev_tac `entries = MAP (\nid.
       if is_left_tagged_nodeid nid then
         let unid = untag_nodeid nid in
         if ?k. k IN Kv /\ m.nodemap ' k = unid
         then (nid, R.l ' (@k. k IN Kv /\ m.nodemap ' k = unid))
         else (nid, H.l ' unid)
       else (nid, R.l ' (untag_nodeid nid))) (SET_TO_LIST V)`
  \\ `ALL_DISTINCT (MAP FST entries)` by (
    unabbrev_all_tac
    \\ rw[MAP_MAP_o, combinTheory.o_DEF]
    \\ simp[COND_RAND, pairTheory.FST]
    \\ irule ALL_DISTINCT_SET_TO_LIST
    \\ fs[])
  \\ `(@k'. k' IN Kv /\ m.nodemap ' k' = n) = k` by (
    SELECT_ELIM_TAC >> conj_tac
    >- (qexists_tac `k` >> simp[])
    >- (rpt strip_tac >> fs[INJ_DEF] >> metis_tac[]))
  \\ `MEM (tag_nodeid_left n, R.l ' k) entries` by (
    unabbrev_all_tac
    \\ rw[MEM_MAP]
    \\ qexists_tac `tag_nodeid_left n`
    \\ conj_tac
    >- (rw[taggingTheory.correct_tagging, taggingTheory.tag_untag_nodeid_inv] >> metis_tac[])
    >- rw[MEM_SET_TO_LIST, gluing_nodes_def, tag_nodeid_coprod_membership])
  \\ `FLOOKUP (FEMPTY |++ entries) (tag_nodeid_left n) = SOME (R.l ' k)` by (
    irule alistTheory.mem_to_flookup
    \\ rw[])
  \\ fs[flookup_thm, FDOM_FUPDATE_LIST]
  \\ pop_assum mp_tac
  \\ simp[gluing_l_def, LET_DEF, Abbr `V`, Abbr `entries`]
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
    (irule semTheory.fmap_buildM_FDOM >> simp[FDOM_FINITE] >> metis_tac[]) >>
  rpt conj_tac
  (* e0 *)
  >- (`FLOOKUP m (edgeid "e0") =
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
      gvs[FLOOKUP_DEF] >> metis_tac[optionTheory.SOME_11])
  (* e1 *)
  >- (`FLOOKUP m (edgeid "e1") =
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
      gvs[FLOOKUP_DEF] >> metis_tac[optionTheory.SOME_11])
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

(* -------------------------------------------------------------------------- *)
(* Initial case with label preservation                                       *)
(* -------------------------------------------------------------------------- *)

Theorem tc_invariant_total_initial:
  !G0. wf_hostgraph G0 /\ unmarked_hostgraph G0 /\ unrooted_hostgraph G0 ==>
       tc_loop_invariant_total G0 G0 (id_track G0)
Proof
  rw[tc_loop_invariant_total_def] >>
  irule minimal_extension_initial >> simp[]
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

(* -------------------------------------------------------------------------- *)
(* Factored helpers: label preservation through a link step                   *)
(* -------------------------------------------------------------------------- *)

Theorem link_step_preserves_edgelabels:
  !G0 G track_bar lhs' rhs' m.
    wf_hostgraph G0 /\ wf_hostgraph G /\ FINITE G0.E /\
    minimal_extension G0 track_bar G /\
    is_match lhs' rule_link.inf m G /\
    lhs'.V = rule_link.lhs.V /\
    lhs'.E = rule_link.lhs.E /\
    rhs'.E = rule_link.rhs.E /\
    preserve_edgelabels lhs' m G /\
    rhs'.m ' (edgeid "e0") = lhs'.m ' (edgeid "e0") /\
    rhs'.m ' (edgeid "e1") = lhs'.m ' (edgeid "e1") /\
    wf_hostgraph lhs' /\ wf_hostgraph rhs' /\
    wf_hostgraph (dpo lhs' rule_link.inf rhs' m G) ==>
    preserve_edgelabels G0
      <| nodemap :=
        (compose_morphism (track lhs' rule_link.inf m G)
          <| nodemap := track_bar.nodemap;
             edgemap := track_bar.edgemap |>).nodemap;
        edgemap := FUN_FMAP
          (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (track_bar.edgemap ' e))
          G0.E |>
      (dpo lhs' rule_link.inf rhs' m G)
Proof
  rpt strip_tac >>
  simp[preserve_edgelabels_def] >>
  (* Extract IH facts from minimal_extension *)
  `preserve_edgelabels G0 track_bar G` by fs me_inj_ss >>
  `G0.m = G.m f_o_f track_bar.edgemap` by fs[preserve_edgelabels_def] >>
  `FDOM track_bar.edgemap = G0.E` by fs (me_inj_ss @ wf_ss) >>
  `INJ ($' track_bar.edgemap) G0.E G.E` by fs me_inj_ss >>
  (* Match facts *)
  `FDOM m.edgemap = lhs'.E` by fs match_morphism_ss >>
  `INJ ($' m.edgemap) lhs'.E G.E` by fs match_inj_ss >>
  `lhs'.E = {edgeid "e1"; edgeid "e0"}` by (fs[] >> EVAL_TAC) >>
  `m.edgemap ' (edgeid "e0") <> m.edgemap ' (edgeid "e1")` by
    (strip_tac >>
     `edgeid "e0" IN lhs'.E` by simp[] >>
     `edgeid "e1" IN lhs'.E` by simp[] >>
     `edgeid "e0" = edgeid "e1"` by metis_tac[INJ_DEF] >> fs[]) >>
  `deletion_deleted_edges lhs' m =
   {m.edgemap ' (edgeid "e0"); m.edgemap ' (edgeid "e1")}` by
    (simp[dpoTheory.deletion_deleted_edges_def] >> fs[] >>
     simp[EXTENSION] >> metis_tac[]) >>
  (* Abbreviate for readability *)
  qabbrev_tac `G'0 = dpo lhs' rule_link.inf rhs' m G` >>
  qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
  (* FINITE and wf_graph D *)
  `FINITE G.E` by fs wf_ss >>
  `FINITE rhs'.E` by fs wf_ss >>
  `FINITE D.E` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def] >>
     metis_tac[IMAGE_FINITE, FINITE_DIFF]) >>
  `FINITE (gluing_edges D rhs')` by
    (simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
     metis_tac[IMAGE_FINITE, FINITE_UNION]) >>
  `wf_graph D` by
    (simp[Abbr `D`] >>
     irule wf_partial_hostgraph_IMP_wf_graph >>
     irule dpoTheory.deletion_preserves_wf_graph >>
     rpt conj_tac >> simp[] >> EVAL_TAC) >>
  `FDOM G.m = G.E` by fs wf_ss >>
  `FDOM G'0.m = G'0.E` by metis_tac[wf_hostgraph_FDOM_m_eq_E] >>
  (* fmap_EQ_THM: domain + pointwise *)
  simp[Once $ GSYM fmap_EQ_THM] >>
  conj_tac
  (* ---- Domain equality ---- *)
  >- (`FDOM (G.m f_o_f track_bar.edgemap) = G0.E` by
        (simp[f_o_f_DEF, EXTENSION] >> gen_tac >> EQ_TAC >> strip_tac >> simp[] >>
         `track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
           (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
         `FRANGE track_bar.edgemap SUBSET G.E` by fs me_inj_ss >>
         metis_tac[SUBSET_DEF]) >>
      pop_assum SUBST1_TAC >>
      simp[f_o_f_DEF, FUN_FMAP_DEF] >>
      simp[EXTENSION] >> gen_tac >> EQ_TAC >> strip_tac >> simp[FUN_FMAP_DEF] >>
      `G'0.E = IMAGE tag_edgeid_left D.E UNION IMAGE tag_edgeid_right rhs'.E` by
        (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
              dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def]) >>
      Cases_on `track_bar.edgemap ' x = m.edgemap ' (edgeid "e0") \/
                track_bar.edgemap ' x = m.edgemap ' (edgeid "e1")`
      >- (simp[] >>
          Cases_on `m.edgemap ' (edgeid "e0") = track_bar.edgemap ' x`
          >- (simp[] >> DISJ2_TAC >> qexists_tac `edgeid "e0"` >> simp[] >> EVAL_TAC)
          >- (simp[] >> DISJ2_TAC >> qexists_tac `edgeid "e1"` >> simp[] >> EVAL_TAC))
      >- (simp[] >> DISJ1_TAC >>
          simp[Abbr `D`, dpoTheory.deletion_def,
               dpoTheory.deletion_remaining_edges_def] >>
          qexists_tac `track_bar.edgemap ' x` >> simp[] >>
          `track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
            (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
          `FRANGE track_bar.edgemap SUBSET G.E` by fs me_inj_ss >>
          metis_tac[SUBSET_DEF]))
  (* ---- Pointwise equality ---- *)
  >> (rpt strip_tac >>
      `x IN G0.E /\ track_bar.edgemap ' x IN G.E` by
        (qpat_x_assum `x IN FDOM _` mp_tac >> simp[f_o_f_DEF]) >>
      (* Reduce LHS: (G.m f_o_f track_bar.edgemap) ' x = G.m ' (m_E ' x) *)
      `(G.m f_o_f track_bar.edgemap) ' x = G.m ' (track_bar.edgemap ' x)` by
        (irule (cj 2 f_o_f_DEF) >> simp[f_o_f_DEF]) >>
      Cases_on `track_bar.edgemap ' x = m.edgemap ' (edgeid "e0") \/
                track_bar.edgemap ' x = m.edgemap ' (edgeid "e1")`
      (* --- Deleted edge case --- *)
      >- (
        `FUN_FMAP (\e. if track_bar.edgemap ' e = m.edgemap ' (edgeid "e0") \/
                          track_bar.edgemap ' e = m.edgemap ' (edgeid "e1")
                       then tag_edgeid_right
                              (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                               then edgeid "e0" else edgeid "e1")
                       else tag_edgeid_left (track_bar.edgemap ' e)) G0.E ' x =
         tag_edgeid_right (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' x
                           then edgeid "e0" else edgeid "e1")` by
          simp[FUN_FMAP_DEF] >>
        Cases_on `m.edgemap ' (edgeid "e0") = track_bar.edgemap ' x`
        (* e0 case *)
        >- (`tag_edgeid_right (edgeid "e0") IN G'0.E` by
              (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
                    dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
               DISJ2_TAC >> qexists_tac `edgeid "e0"` >> simp[] >> EVAL_TAC) >>
            `x IN FDOM (G'0.m f_o_f FUN_FMAP (\e. if track_bar.edgemap ' e = m.edgemap ' (edgeid "e0") \/
                track_bar.edgemap ' e = m.edgemap ' (edgeid "e1") then tag_edgeid_right
                (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e then edgeid "e0" else edgeid "e1")
                else tag_edgeid_left (track_bar.edgemap ' e)) G0.E)` by
              (simp[f_o_f_DEF, FUN_FMAP_DEF]) >>
            first_x_assum (mp_tac o MATCH_MP (cj 2 f_o_f_DEF)) >>
            strip_tac >> pop_assum (fn th => REWRITE_TAC[th]) >>
            simp[FUN_FMAP_DEF] >>
            `G'0.m ' (tag_edgeid_right (edgeid "e0")) = rhs'.m ' (edgeid "e0")` by
              (ntac 2 (qpat_x_assum `rhs'.m ' _ = lhs'.m ' _` (K ALL_TAC)) >>
               simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
               irule gluing_m_apply_right_tagged >>
               simp[] >> fs[wf_hostgraph_def] >> EVAL_TAC) >>
            `lhs'.m ' (edgeid "e0") = (G.m f_o_f m.edgemap) ' (edgeid "e0")` by
              fs[preserve_edgelabels_def] >>
            `edgeid "e0" IN FDOM m.edgemap` by simp[] >>
            `(G.m f_o_f m.edgemap) ' (edgeid "e0") = G.m ' (m.edgemap ' (edgeid "e0"))` by
              (irule (cj 2 f_o_f_DEF) >> simp[f_o_f_DEF] >> EVAL_TAC) >>
            simp[])
        (* e1 case *)
        >- (`m.edgemap ' (edgeid "e1") = track_bar.edgemap ' x` by
              (fs[IN_INSERT] >> metis_tac[]) >>
            `tag_edgeid_right (edgeid "e1") IN G'0.E` by
              (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
                    dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
               DISJ2_TAC >> qexists_tac `edgeid "e1"` >> simp[] >> EVAL_TAC) >>
            `x IN FDOM (G'0.m f_o_f FUN_FMAP (\e. if track_bar.edgemap ' e = m.edgemap ' (edgeid "e0") \/
                track_bar.edgemap ' e = m.edgemap ' (edgeid "e1") then tag_edgeid_right
                (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e then edgeid "e0" else edgeid "e1")
                else tag_edgeid_left (track_bar.edgemap ' e)) G0.E)` by
              (simp[f_o_f_DEF, FUN_FMAP_DEF]) >>
            first_x_assum (mp_tac o MATCH_MP (cj 2 f_o_f_DEF)) >>
            strip_tac >> pop_assum (fn th => REWRITE_TAC[th]) >>
            simp[FUN_FMAP_DEF] >>
            `G'0.m ' (tag_edgeid_right (edgeid "e1")) = rhs'.m ' (edgeid "e1")` by
              (ntac 2 (qpat_x_assum `rhs'.m ' _ = lhs'.m ' _` (K ALL_TAC)) >>
               simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
               irule gluing_m_apply_right_tagged >>
               simp[] >> fs[wf_hostgraph_def] >> EVAL_TAC) >>
            `lhs'.m ' (edgeid "e1") = (G.m f_o_f m.edgemap) ' (edgeid "e1")` by
              fs[preserve_edgelabels_def] >>
            `edgeid "e1" IN FDOM m.edgemap` by simp[] >>
            `(G.m f_o_f m.edgemap) ' (edgeid "e1") = G.m ' (m.edgemap ' (edgeid "e1"))` by
              (irule (cj 2 f_o_f_DEF) >> simp[f_o_f_DEF] >> EVAL_TAC) >>
            simp[]))
      (* --- Surviving edge case --- *)
      >- (
        `FUN_FMAP (\e. if track_bar.edgemap ' e = m.edgemap ' (edgeid "e0") \/
                          track_bar.edgemap ' e = m.edgemap ' (edgeid "e1")
                       then tag_edgeid_right
                              (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                               then edgeid "e0" else edgeid "e1")
                       else tag_edgeid_left (track_bar.edgemap ' e)) G0.E ' x =
         tag_edgeid_left (track_bar.edgemap ' x)` by simp[FUN_FMAP_DEF] >>
        `tag_edgeid_left (track_bar.edgemap ' x) IN G'0.E` by
          (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
                dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
           DISJ1_TAC >>
           simp[Abbr `D`, dpoTheory.deletion_def,
                dpoTheory.deletion_remaining_edges_def] >>
           qexists_tac `track_bar.edgemap ' x` >> simp[] >> fs[]) >>
        `x IN FDOM (G'0.m f_o_f FUN_FMAP (\e. if track_bar.edgemap ' e = m.edgemap ' (edgeid "e0") \/
            track_bar.edgemap ' e = m.edgemap ' (edgeid "e1") then tag_edgeid_right
            (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e then edgeid "e0" else edgeid "e1")
            else tag_edgeid_left (track_bar.edgemap ' e)) G0.E)` by
          (simp[f_o_f_DEF, FUN_FMAP_DEF]) >>
        first_x_assum (mp_tac o MATCH_MP (cj 2 f_o_f_DEF)) >>
        strip_tac >> pop_assum (fn th => REWRITE_TAC[th]) >>
        simp[FUN_FMAP_DEF] >>
        `track_bar.edgemap ' x IN deletion_remaining_edges lhs' m G` by
          (simp[dpoTheory.deletion_remaining_edges_def]) >>
        `track_bar.edgemap ' x IN D.E` by simp[Abbr `D`, dpoTheory.deletion_def] >>
        simp[Abbr `D`, Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
        `(gluing_m (gluing_edges (deletion lhs' rule_link.inf m G) rhs')
            (deletion lhs' rule_link.inf m G) rhs') '
          (tag_edgeid_left (track_bar.edgemap ' x)) =
          (deletion lhs' rule_link.inf m G).m ' (track_bar.edgemap ' x)` by
           (irule dpoTheory.gluing_m_apply_left_tagged >> simp[] >>
            fs[wf_hostgraph_def]) >>
        `(deletion lhs' rule_link.inf m G).m ' (track_bar.edgemap ' x) =
          G.m ' (track_bar.edgemap ' x)` by
           metis_tac[deletion_m_surviving] >>
        simp[]))
QED

Theorem link_step_preserves_nodelabels:
  !G0 G track_bar lhs' rhs' m.
    wf_hostgraph G0 /\ wf_hostgraph G /\ FINITE G0.E /\
    minimal_extension G0 track_bar G /\
    is_match lhs' rule_link.inf m G /\
    lhs'.V = rule_link.lhs.V /\
    lhs'.E = rule_link.lhs.E /\
    rhs'.V = rule_link.rhs.V /\
    preserve_nodelabels lhs' m G /\
    (!k. k IN rule_link.inf ==> rhs'.l ' k = lhs'.l ' k) /\
    wf_hostgraph lhs' /\ wf_hostgraph rhs' /\
    wf_hostgraph (dpo lhs' rule_link.inf rhs' m G) ==>
    preserve_nodelabels G0
      <| nodemap :=
        (compose_morphism (track lhs' rule_link.inf m G)
          <| nodemap := track_bar.nodemap;
             edgemap := track_bar.edgemap |>).nodemap;
        edgemap := FUN_FMAP
          (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (track_bar.edgemap ' e))
          G0.E |>
      (dpo lhs' rule_link.inf rhs' m G)
Proof
  rpt strip_tac >>
  simp[preserve_nodelabels_def] >>
  simp[morphismTheory.compose_morphism_def] >>
  (* IH: G0.l = G.l f_o_f track_bar.nodemap *)
  `G0.l = G.l f_o_f track_bar.nodemap` by
    fs (preserve_nodelabels_def :: me_inj_ss) >>
  (* Shared structural facts *)
  `deletion_remaining_nodes lhs' m rule_link.inf G = G.V` by
    (irule link_no_node_deletion >> gvs[]) >>
  `FINITE G.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  `FDOM (track lhs' rule_link.inf m G).nodemap = G.V` by
    simp[trackTheory.FDOM_track_nodemap] >>
  qabbrev_tac `G'0 = dpo lhs' rule_link.inf rhs' m G` >>
  qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
  `D.V = G.V` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_nodes_def,
          dpoTheory.deletion_deleted_nodes_def] >>
     gvs[] >> simp[DIFF_EQ_EMPTY, SUBSET_REFL]) >>
  `FDOM G.l = G.V` by fs wf_ss >>
  `FDOM G'0.l = G'0.V` by fs wf_ss >>
  `G'0.V = IMAGE tag_nodeid_left G.V` by
    (simp[Abbr `G'0`] >> irule link_dpo_V >> simp[]) >>
  `FDOM m.nodemap = lhs'.V` by fs match_morphism_ss >>
  `INJ ($' m.nodemap) lhs'.V G.V` by fs match_inj_ss >>
  (* Use f_o_f_ASSOC: suffices to show G.l = G'0.l f_o_f (track ...).nodemap *)
  `G.l = G'0.l f_o_f (track lhs' rule_link.inf m G).nodemap` suffices_by
    (strip_tac >> metis_tac[morphismTheory.f_o_f_ASSOC]) >>
  simp[Once $ GSYM fmap_EQ_THM] >>
  conj_tac
  (* Domain *)
  >- (simp[cj 1 f_o_f_DEF, EXTENSION] >>
      gen_tac >> EQ_TAC >> strip_tac >> simp[] >>
      irule_at Any trackTheory.track_nodemap_apply >> simp[])
  (* Per-element *)
  >> (rpt strip_tac >>
    `(track lhs' rule_link.inf m G).nodemap ' x = tag_nodeid_left x` by
      (irule trackTheory.track_nodemap_apply >> simp[]) >>
    `x IN FDOM (G'0.l f_o_f (track lhs' rule_link.inf m G).nodemap)` by
      (simp[cj 1 f_o_f_DEF] >> qexists_tac `x` >> simp[]) >>
    `(G'0.l f_o_f (track lhs' rule_link.inf m G).nodemap) ' x =
      G'0.l ' ((track lhs' rule_link.inf m G).nodemap ' x)` by
      (irule (cj 2 f_o_f_DEF) >> simp[]) >>
    pop_assum SUBST1_TAC >> simp[] >>
    (* Goal: G.l ' x = G'0.l ' (tag_nodeid_left x) *)
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
        `G'0.l ' (tag_nodeid_left (m.nodemap ' x')) = rhs'.l ' x'` by
          (qpat_x_assum `!k. _ ==> rhs'.l ' k = _` (K ALL_TAC) >>
           simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
           irule gluing_l_apply_left_tagged_in_interface >>
           simp[] >> fs[wf_hostgraph_def] >>
           simp[dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >>
           `FINITE D.V` by simp[] >>
           `FINITE rhs'.V` by fs[wf_hostgraph_def, wf_graph_def] >>
           metis_tac[IMAGE_FINITE, FINITE_DIFF, FINITE_UNION]) >>
        `rhs'.l ' x' = lhs'.l ' x'` by
          (first_x_assum (mp_tac o Q.SPEC `x'`) >> simp[]) >>
        `lhs'.l ' x' = (G.l f_o_f m.nodemap) ' x'` by
          fs[preserve_nodelabels_def] >>
        `x' IN FDOM m.nodemap` by metis_tac[SUBSET_DEF] >>
        `(G.l f_o_f m.nodemap) ' x' = G.l ' (m.nodemap ' x')` by
          (irule (cj 2 f_o_f_DEF) >> simp[cj 1 f_o_f_DEF] >>
           fs wf_ss >> fs match_morphism_ss >>
           metis_tac[SUBSET_DEF, IN_FRANGE]) >>
        simp[])
    (* Non-interface node *)
    >- (
        `~(?k. k IN rule_link.inf /\ m.nodemap ' k = x)` by
          (strip_tac >> fs[] >> metis_tac[IN_IMAGE]) >>
        `wf_graph D` by
          (simp[Abbr `D`] >>
           irule wf_partial_hostgraph_IMP_wf_graph >>
           irule dpoTheory.deletion_preserves_wf_graph >>
           rpt conj_tac >> simp[] >> EVAL_TAC) >>
        `G'0.l ' (tag_nodeid_left x) = D.l ' x` by
          (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
           irule dpoTheory.gluing_l_apply_left_tagged >> simp[] >>
           rpt conj_tac
           >- (simp[dpoTheory.gluing_nodes_def, dpoTheory.nodeid_coprod_def] >>
               `FINITE D.V` by simp[] >>
               `FINITE rhs'.V` by fs[wf_hostgraph_def, wf_graph_def] >>
               metis_tac[IMAGE_FINITE, FINITE_DIFF, FINITE_UNION])
           >- fs[wf_hostgraph_def]
           >- metis_tac[]) >>
        `x IN deletion_relabling_nodes lhs' m rule_link.inf G` by
          (simp[dpoTheory.deletion_relabling_nodes_def] >>
           DISJ2_TAC >> qexists_tac `x` >> simp[] >>
           fs[IN_IMAGE] >> metis_tac[]) >>
        `D.l ' x = G.l ' x` by
          (simp[Abbr `D`] >> irule deletion_l_surviving >> simp[]) >>
        simp[]))
QED

(* -------------------------------------------------------------------------- *)
(* Factored sub-proofs for the link step's is_inj_morphism assembly          *)
(* -------------------------------------------------------------------------- *)

Theorem link_step_preserve_source:
  !G0 G track_bar lhs' rhs' m.
    wf_hostgraph G0 /\ wf_hostgraph G /\ FINITE G0.E /\
    minimal_extension G0 track_bar G /\
    is_match lhs' rule_link.inf m G /\
    lhs'.V = rule_link.lhs.V /\
    lhs'.E = rule_link.lhs.E /\ lhs'.s = rule_link.lhs.s /\
    rhs'.V = rule_link.rhs.V /\ rhs'.E = rule_link.rhs.E /\
    rhs'.s = rule_link.rhs.s /\
    wf_hostgraph lhs' /\ wf_hostgraph rhs' /\
    wf_hostgraph (dpo lhs' rule_link.inf rhs' m G) ==>
    preserve_source G0
      <| nodemap :=
        (compose_morphism (track lhs' rule_link.inf m G)
          <| nodemap := track_bar.nodemap;
             edgemap := track_bar.edgemap |>).nodemap;
        edgemap := FUN_FMAP
          (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (track_bar.edgemap ' e))
          G0.E |>
      (dpo lhs' rule_link.inf rhs' m G)
Proof
  rpt strip_tac >> simp[preserve_source_def] >>
  drule_all minimal_extension_pointwise >> strip_tac >>
  qabbrev_tac `G'0 = dpo lhs' rule_link.inf rhs' m G` >>
  qabbrev_tac `nm = (compose_morphism (track lhs' rule_link.inf m G)
    <| nodemap := track_bar.nodemap;
       edgemap := track_bar.edgemap |>).nodemap` >>
  qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
  `FDOM m.edgemap = lhs'.E` by fs match_morphism_ss >>
  `INJ ($' m.edgemap) lhs'.E G.E` by fs match_inj_ss >>
  `lhs'.E = {edgeid "e1"; edgeid "e0"}` by (fs[] >> EVAL_TAC) >>
  `m.edgemap ' (edgeid "e0") <> m.edgemap ' (edgeid "e1")` by
    (strip_tac >> `edgeid "e0" IN lhs'.E` by simp[] >>
     `edgeid "e1" IN lhs'.E` by simp[] >>
     `edgeid "e0" = edgeid "e1"` by metis_tac[INJ_DEF] >> fs[]) >>
  `deletion_deleted_edges lhs' m =
   {m.edgemap ' (edgeid "e0"); m.edgemap ' (edgeid "e1")}` by
    (simp[dpoTheory.deletion_deleted_edges_def] >> fs[] >>
     simp[EXTENSION] >> metis_tac[]) >>
  `FINITE G.E` by fs wf_ss >>
  `FINITE G.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  `FINITE rhs'.E` by fs wf_ss >>
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
    simp[trackTheory.FDOM_track_nodemap] >>
  sg `FDOM nm = G0.V`
  >- (simp[Abbr `nm`, morphismTheory.compose_morphism_def,
           cj 1 f_o_f_DEF, EXTENSION] >>
      gen_tac >> EQ_TAC >> strip_tac >> simp[] >>
      metis_tac[BIJ_DEF, INJ_DEF]) >>
  `!v. v IN G0.V ==> nm ' v = tag_nodeid_left (track_bar.nodemap ' v)` by
    (rpt strip_tac >>
     simp[Abbr `nm`, morphismTheory.compose_morphism_def] >>
     `track_bar.nodemap ' v IN G.V` by metis_tac[BIJ_DEF, INJ_DEF] >>
     simp[f_o_f_DEF] >> irule trackTheory.track_nodemap_apply >> simp[]) >>
  `preserve_source lhs' m G` by fs match_source_ss >>
  simp[Once $ GSYM fmap_EQ_THM] >>
  conj_tac
  (* ---- Domain equality ---- *)
  >- (`FDOM (nm f_o_f G0.s) = G0.E` by
        (simp[cj 1 f_o_f_DEF, EXTENSION, GSPECIFICATION] >>
         gen_tac >> EQ_TAC >> strip_tac >> simp[] >>
         `FDOM G0.s = G0.E` by fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
         fs[] >>
         `G0.s ' x IN G0.V` by
           (fs[wf_hostgraph_def, graphTheory.wf_graph_def, FRANGE_DEF,
               SUBSET_DEF] >> metis_tac[]) >>
         metis_tac[]) >>
      pop_assum SUBST1_TAC >>
      `FDOM G'0.s = G'0.E` by fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
      `G'0.E = IMAGE tag_edgeid_left D.E UNION IMAGE tag_edgeid_right rhs'.E` by
        (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
              dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def]) >>
      simp[cj 1 f_o_f_DEF, FUN_FMAP_DEF, EXTENSION] >>
      gen_tac >> EQ_TAC >> strip_tac >> simp[FUN_FMAP_DEF] >>
      Cases_on `track_bar.edgemap ' x = m.edgemap ' (edgeid "e0") \/
                track_bar.edgemap ' x = m.edgemap ' (edgeid "e1")`
      >- (simp[] >>
          Cases_on `m.edgemap ' (edgeid "e0") = track_bar.edgemap ' x`
          >- (simp[] >> DISJ2_TAC >>
              qexists_tac `edgeid "e0"` >> simp[] >> EVAL_TAC)
          >- (simp[] >> DISJ2_TAC >>
              qexists_tac `edgeid "e1"` >> simp[] >> EVAL_TAC))
      >- (simp[] >> DISJ1_TAC >>
          simp[Abbr `D`, dpoTheory.deletion_def,
               dpoTheory.deletion_remaining_edges_def] >>
          qexists_tac `track_bar.edgemap ' x` >> simp[] >>
          `track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
            (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
          `FRANGE track_bar.edgemap SUBSET G.E` by fs me_inj_ss >>
          metis_tac[SUBSET_DEF]))
  (* ---- Pointwise equality ---- *)
  >> (rpt strip_tac >>
      `x IN G0.E` by
        (fs[cj 1 f_o_f_DEF, GSPECIFICATION] >>
         `FDOM G0.s = G0.E` by fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
         fs[]) >>
      `G0.s ' x IN G0.V` by
        (fs[wf_hostgraph_def, graphTheory.wf_graph_def, FRANGE_DEF,
            SUBSET_DEF] >> metis_tac[]) >>
      `track_bar.edgemap ' x IN G.E` by
        (fs me_inj_ss >> metis_tac[INJ_DEF]) >>
      `G.s ' (track_bar.edgemap ' x) = track_bar.nodemap ' (G0.s ' x)` by
        metis_tac[] >>
      `(nm f_o_f G0.s) ' x = nm ' (G0.s ' x)` by
        (irule (cj 2 f_o_f_DEF) >>
         simp[cj 1 f_o_f_DEF, GSPECIFICATION] >>
         fs[wf_hostgraph_def, graphTheory.wf_graph_def]) >>
      `nm ' (G0.s ' x) = tag_nodeid_left (track_bar.nodemap ' (G0.s ' x))` by
        metis_tac[] >>
      Cases_on `track_bar.edgemap ' x = m.edgemap ' (edgeid "e0") \/
                track_bar.edgemap ' x = m.edgemap ' (edgeid "e1")`
      (* --- Deleted edge case --- *)
      >- (
        Cases_on `m.edgemap ' (edgeid "e0") = track_bar.edgemap ' x`
        (* e0 case *)
        >- (`tag_edgeid_right (edgeid "e0") IN G'0.E` by
              (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
                    dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
               DISJ2_TAC >> qexists_tac `edgeid "e0"` >> simp[] >> EVAL_TAC) >>
            `FDOM G'0.s = G'0.E` by
              fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
            `x IN FDOM (G'0.s f_o_f FUN_FMAP (\e.
               if track_bar.edgemap ' e = m.edgemap ' (edgeid "e0") \/
                  track_bar.edgemap ' e = m.edgemap ' (edgeid "e1")
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (track_bar.edgemap ' e)) G0.E)` by
              (simp[f_o_f_DEF, FUN_FMAP_DEF]) >>
            first_x_assum (mp_tac o MATCH_MP (cj 2 f_o_f_DEF)) >>
            strip_tac >> pop_assum (fn th => REWRITE_TAC[th]) >>
            simp[FUN_FMAP_DEF] >>
            `G'0.s ' (tag_edgeid_right (edgeid "e0")) =
             tag_nodeid_left (m.nodemap ' (rhs'.s ' (edgeid "e0")))` by
              (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
               qpat_x_assum `rhs'.s = rule_link.rhs.s`
                 (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
               irule dpoTheory.gluing_s_apply_right_tagged_in_interface >>
               simp[] >> fs[wf_hostgraph_def] >> EVAL_TAC) >>
            simp[] >>
            `edgeid "e0" IN lhs'.E` by simp[] >>
            `(G.s f_o_f m.edgemap) ' (edgeid "e0") =
             G.s ' (m.edgemap ' (edgeid "e0"))` by
              (irule f_o_f_apply >> gvs[] >> EVAL_TAC) >>
            `FDOM m.nodemap = lhs'.V` by fs match_morphism_ss >>
            sg `(m.nodemap f_o_f lhs'.s) ' (edgeid "e0") =
                m.nodemap ' (lhs'.s ' (edgeid "e0"))`
            >- (irule f_o_f_apply >> conj_tac
                >- (simp[] >> EVAL_TAC)
                >- (`FDOM lhs'.s = lhs'.E` by
                      fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
                    simp[]))
            >- (`m.nodemap ' (lhs'.s ' (edgeid "e0")) =
                 G.s ' (m.edgemap ' (edgeid "e0"))` by
                  (fs[preserve_source_def] >> metis_tac[]) >>
                gvs[] >>
                `rule_link.rhs.s ' (edgeid "e0") = lhs'.s ' (edgeid "e0")` by
                  (simp[] >> EVAL_TAC) >>
                gvs[]))
        (* e1 case *)
        >- (`m.edgemap ' (edgeid "e1") = track_bar.edgemap ' x` by
              (fs[IN_INSERT] >> metis_tac[]) >>
            `tag_edgeid_right (edgeid "e1") IN G'0.E` by
              (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
                    dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
               DISJ2_TAC >> qexists_tac `edgeid "e1"` >> simp[] >> EVAL_TAC) >>
            `FDOM G'0.s = G'0.E` by
              fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
            `x IN FDOM (G'0.s f_o_f FUN_FMAP (\e.
               if track_bar.edgemap ' e = m.edgemap ' (edgeid "e0") \/
                  track_bar.edgemap ' e = m.edgemap ' (edgeid "e1")
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (track_bar.edgemap ' e)) G0.E)` by
              (simp[f_o_f_DEF, FUN_FMAP_DEF]) >>
            first_x_assum (mp_tac o MATCH_MP (cj 2 f_o_f_DEF)) >>
            strip_tac >> pop_assum (fn th => REWRITE_TAC[th]) >>
            simp[FUN_FMAP_DEF] >>
            `G'0.s ' (tag_edgeid_right (edgeid "e1")) =
             tag_nodeid_left (m.nodemap ' (rhs'.s ' (edgeid "e1")))` by
              (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
               qpat_x_assum `rhs'.s = rule_link.rhs.s`
                 (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
               irule dpoTheory.gluing_s_apply_right_tagged_in_interface >>
               simp[] >> fs[wf_hostgraph_def] >> EVAL_TAC) >>
            simp[] >>
            `(G.s f_o_f m.edgemap) ' (edgeid "e1") =
             G.s ' (m.edgemap ' (edgeid "e1"))` by
              (irule f_o_f_apply >> gvs[] >> EVAL_TAC) >>
            sg `(m.nodemap f_o_f lhs'.s) ' (edgeid "e1") =
                m.nodemap ' (lhs'.s ' (edgeid "e1"))`
            >- (irule f_o_f_apply >> conj_tac
                >- (simp[] >> EVAL_TAC >> fs[] >> EVAL_TAC >> gvs[] >>
                    EVAL_TAC >>
                    `FDOM m.nodemap = lhs'.V` by fs match_morphism_ss >>
                    `nodeid "n1" IN rule_link.lhs.V` by EVAL_TAC >>
                    metis_tac[])
                >- (`FDOM lhs'.s = lhs'.E` by
                      fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
                    simp[]))
            >- (`m.nodemap ' (lhs'.s ' (edgeid "e1")) =
                 G.s ' (m.edgemap ' (edgeid "e1"))` by
                  (fs[preserve_source_def] >> metis_tac[]) >>
                `rule_link.rhs.s ' (edgeid "e1") = lhs'.s ' (edgeid "e1")` by
                  (simp[] >> EVAL_TAC) >>
                gvs[])))
      (* --- Surviving edge case --- *)
      >- (`FDOM G'0.s = G'0.E` by
            fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
          `tag_edgeid_left (track_bar.edgemap ' x) IN G'0.E` by
            (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
                  dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
             DISJ1_TAC >>
             simp[Abbr `D`, dpoTheory.deletion_def,
                  dpoTheory.deletion_remaining_edges_def] >>
             qexists_tac `track_bar.edgemap ' x` >> simp[] >>
             `track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
               (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
             `FRANGE track_bar.edgemap SUBSET G.E` by fs me_inj_ss >>
             metis_tac[SUBSET_DEF]) >>
          `x IN FDOM (G'0.s f_o_f FUN_FMAP (\e.
             if track_bar.edgemap ' e = m.edgemap ' (edgeid "e0") \/
                track_bar.edgemap ' e = m.edgemap ' (edgeid "e1")
             then tag_edgeid_right
                    (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                     then edgeid "e0" else edgeid "e1")
             else tag_edgeid_left (track_bar.edgemap ' e)) G0.E)` by
            (simp[f_o_f_DEF, FUN_FMAP_DEF]) >>
          first_x_assum (mp_tac o MATCH_MP (cj 2 f_o_f_DEF)) >>
          strip_tac >> pop_assum (fn th => REWRITE_TAC[th]) >>
          simp[FUN_FMAP_DEF] >>
          `track_bar.edgemap ' x IN D.E` by
            (simp[Abbr `D`, dpoTheory.deletion_def,
                  dpoTheory.deletion_remaining_edges_def] >>
             `track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
               (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
             `FRANGE track_bar.edgemap SUBSET G.E` by fs me_inj_ss >>
             metis_tac[SUBSET_DEF]) >>
          `G'0.s ' (tag_edgeid_left (track_bar.edgemap ' x)) =
           tag_nodeid_left (D.s ' (track_bar.edgemap ' x))` by
            (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
             irule dpoTheory.gluing_s_apply_left_tagged >>
             simp[] >> fs[wf_hostgraph_def]) >>
          `D.s ' (track_bar.edgemap ' x) = G.s ' (track_bar.edgemap ' x)` by
            (fs[Abbr `D`, dpoTheory.deletion_def, LET_THM, DRESTRICT_DEF]) >>
          gvs[]))
QED

Theorem link_step_preserve_target:
  !G0 G track_bar lhs' rhs' m.
    wf_hostgraph G0 /\ wf_hostgraph G /\ FINITE G0.E /\
    minimal_extension G0 track_bar G /\
    is_match lhs' rule_link.inf m G /\
    lhs'.V = rule_link.lhs.V /\
    lhs'.E = rule_link.lhs.E /\ lhs'.t = rule_link.lhs.t /\
    rhs'.V = rule_link.rhs.V /\ rhs'.E = rule_link.rhs.E /\
    rhs'.t = rule_link.rhs.t /\
    wf_hostgraph lhs' /\ wf_hostgraph rhs' /\
    wf_hostgraph (dpo lhs' rule_link.inf rhs' m G) ==>
    preserve_target G0
      <| nodemap :=
        (compose_morphism (track lhs' rule_link.inf m G)
          <| nodemap := track_bar.nodemap;
             edgemap := track_bar.edgemap |>).nodemap;
        edgemap := FUN_FMAP
          (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (track_bar.edgemap ' e))
          G0.E |>
      (dpo lhs' rule_link.inf rhs' m G)
Proof
  rpt strip_tac >> simp[preserve_target_def] >>
  drule_all minimal_extension_pointwise >> strip_tac >>
  qabbrev_tac `G'0 = dpo lhs' rule_link.inf rhs' m G` >>
  qabbrev_tac `nm = (compose_morphism (track lhs' rule_link.inf m G)
    <| nodemap := track_bar.nodemap;
       edgemap := track_bar.edgemap |>).nodemap` >>
  qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
  `FDOM m.edgemap = lhs'.E` by fs match_morphism_ss >>
  `INJ ($' m.edgemap) lhs'.E G.E` by fs match_inj_ss >>
  `lhs'.E = {edgeid "e1"; edgeid "e0"}` by (fs[] >> EVAL_TAC) >>
  `m.edgemap ' (edgeid "e0") <> m.edgemap ' (edgeid "e1")` by
    (strip_tac >> `edgeid "e0" IN lhs'.E` by simp[] >>
     `edgeid "e1" IN lhs'.E` by simp[] >>
     `edgeid "e0" = edgeid "e1"` by metis_tac[INJ_DEF] >> fs[]) >>
  `deletion_deleted_edges lhs' m =
   {m.edgemap ' (edgeid "e0"); m.edgemap ' (edgeid "e1")}` by
    (simp[dpoTheory.deletion_deleted_edges_def] >> fs[] >>
     simp[EXTENSION] >> metis_tac[]) >>
  `FINITE G.E` by fs wf_ss >>
  `FINITE G.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  `FINITE rhs'.E` by fs wf_ss >>
  `FINITE D.E` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def] >>
     metis_tac[IMAGE_FINITE, FINITE_DIFF]) >>
  `wf_graph D` by
    (simp[Abbr `D`] >> irule wf_partial_hostgraph_IMP_wf_graph >>
     irule dpoTheory.deletion_preserves_wf_graph >>
     rpt conj_tac >> simp[] >> EVAL_TAC) >>
  `FINITE (gluing_edges D rhs')` by
    (simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
     metis_tac[IMAGE_FINITE, FINITE_UNION]) >>
  `deletion_remaining_nodes lhs' m rule_link.inf G = G.V` by
    (irule link_no_node_deletion >> gvs[]) >>
  `FDOM (track lhs' rule_link.inf m G).nodemap = G.V` by
    simp[trackTheory.FDOM_track_nodemap] >>
  sg `FDOM nm = G0.V`
  >- (simp[Abbr `nm`, morphismTheory.compose_morphism_def,
           cj 1 f_o_f_DEF, EXTENSION] >>
      gen_tac >> EQ_TAC >> strip_tac >> simp[] >>
      metis_tac[BIJ_DEF, INJ_DEF]) >>
  `!v. v IN G0.V ==> nm ' v = tag_nodeid_left (track_bar.nodemap ' v)` by
    (rpt strip_tac >>
     simp[Abbr `nm`, morphismTheory.compose_morphism_def] >>
     `track_bar.nodemap ' v IN G.V` by metis_tac[BIJ_DEF, INJ_DEF] >>
     simp[f_o_f_DEF] >> irule trackTheory.track_nodemap_apply >> simp[]) >>
  `preserve_target lhs' m G` by fs match_target_ss >>
  simp[Once $ GSYM fmap_EQ_THM] >>
  conj_tac
  (* ---- Domain equality ---- *)
  >- (`FDOM (nm f_o_f G0.t) = G0.E` by
        (simp[cj 1 f_o_f_DEF, EXTENSION, GSPECIFICATION] >>
         gen_tac >> EQ_TAC >> strip_tac >> simp[] >>
         `FDOM G0.t = G0.E` by fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
         fs[] >>
         `G0.t ' x IN G0.V` by
           (fs[wf_hostgraph_def, graphTheory.wf_graph_def, FRANGE_DEF,
               SUBSET_DEF] >> metis_tac[]) >>
         metis_tac[]) >>
      pop_assum SUBST1_TAC >>
      `FDOM G'0.t = G'0.E` by fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
      `G'0.E = IMAGE tag_edgeid_left D.E UNION IMAGE tag_edgeid_right rhs'.E` by
        (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
              dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def]) >>
      simp[cj 1 f_o_f_DEF, FUN_FMAP_DEF, EXTENSION] >>
      gen_tac >> EQ_TAC >> strip_tac >> simp[FUN_FMAP_DEF] >>
      Cases_on `track_bar.edgemap ' x = m.edgemap ' (edgeid "e0") \/
                track_bar.edgemap ' x = m.edgemap ' (edgeid "e1")`
      >- (simp[] >>
          Cases_on `m.edgemap ' (edgeid "e0") = track_bar.edgemap ' x`
          >- (simp[] >> DISJ2_TAC >>
              qexists_tac `edgeid "e0"` >> simp[] >> EVAL_TAC)
          >- (simp[] >> DISJ2_TAC >>
              qexists_tac `edgeid "e1"` >> simp[] >> EVAL_TAC))
      >- (simp[] >> DISJ1_TAC >>
          simp[Abbr `D`, dpoTheory.deletion_def,
               dpoTheory.deletion_remaining_edges_def] >>
          qexists_tac `track_bar.edgemap ' x` >> simp[] >>
          `track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
            (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
          `FRANGE track_bar.edgemap SUBSET G.E` by fs me_inj_ss >>
          metis_tac[SUBSET_DEF]))
  (* ---- Pointwise equality ---- *)
  >> (rpt strip_tac >>
      `x IN G0.E` by
        (fs[cj 1 f_o_f_DEF, GSPECIFICATION] >>
         `FDOM G0.t = G0.E` by fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
         fs[]) >>
      `G0.t ' x IN G0.V` by
        (fs[wf_hostgraph_def, graphTheory.wf_graph_def, FRANGE_DEF,
            SUBSET_DEF] >> metis_tac[]) >>
      `track_bar.edgemap ' x IN G.E` by
        (fs me_inj_ss >> metis_tac[INJ_DEF]) >>
      `G.t ' (track_bar.edgemap ' x) = track_bar.nodemap ' (G0.t ' x)` by
        metis_tac[] >>
      `(nm f_o_f G0.t) ' x = nm ' (G0.t ' x)` by
        (irule (cj 2 f_o_f_DEF) >>
         simp[cj 1 f_o_f_DEF, GSPECIFICATION] >>
         fs[wf_hostgraph_def, graphTheory.wf_graph_def]) >>
      `nm ' (G0.t ' x) = tag_nodeid_left (track_bar.nodemap ' (G0.t ' x))` by
        metis_tac[] >>
      Cases_on `track_bar.edgemap ' x = m.edgemap ' (edgeid "e0") \/
                track_bar.edgemap ' x = m.edgemap ' (edgeid "e1")`
      (* --- Deleted edge case --- *)
      >- (
        Cases_on `m.edgemap ' (edgeid "e0") = track_bar.edgemap ' x`
        (* e0 case *)
        >- (`tag_edgeid_right (edgeid "e0") IN G'0.E` by
              (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
                    dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
               DISJ2_TAC >> qexists_tac `edgeid "e0"` >> simp[] >> EVAL_TAC) >>
            `FDOM G'0.t = G'0.E` by
              fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
            `x IN FDOM (G'0.t f_o_f FUN_FMAP (\e.
               if track_bar.edgemap ' e = m.edgemap ' (edgeid "e0") \/
                  track_bar.edgemap ' e = m.edgemap ' (edgeid "e1")
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (track_bar.edgemap ' e)) G0.E)` by
              (simp[f_o_f_DEF, FUN_FMAP_DEF]) >>
            first_x_assum (mp_tac o MATCH_MP (cj 2 f_o_f_DEF)) >>
            strip_tac >> pop_assum (fn th => REWRITE_TAC[th]) >>
            simp[FUN_FMAP_DEF] >>
            `G'0.t ' (tag_edgeid_right (edgeid "e0")) =
             tag_nodeid_left (m.nodemap ' (rhs'.t ' (edgeid "e0")))` by
              (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
               qpat_x_assum `rhs'.t = rule_link.rhs.t`
                 (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
               irule dpoTheory.gluing_t_apply_right_tagged_in_interface >>
               simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
               fs[wf_hostgraph_def] >> EVAL_TAC >>
               simp[IMAGE_FINITE]) >>
            simp[] >>
            `edgeid "e0" IN lhs'.E` by simp[] >>
            `(G.t f_o_f m.edgemap) ' (edgeid "e0") =
             G.t ' (m.edgemap ' (edgeid "e0"))` by
              (irule f_o_f_apply >> gvs[] >> EVAL_TAC) >>
            `FDOM m.nodemap = lhs'.V` by fs match_morphism_ss >>
            sg `(m.nodemap f_o_f lhs'.t) ' (edgeid "e0") =
                m.nodemap ' (lhs'.t ' (edgeid "e0"))`
            >- (irule f_o_f_apply >> conj_tac
                >- (simp[] >> EVAL_TAC)
                >- (`FDOM lhs'.t = lhs'.E` by
                      fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
                    simp[]))
            >- (`m.nodemap ' (lhs'.t ' (edgeid "e0")) =
                 G.t ' (m.edgemap ' (edgeid "e0"))` by
                  (fs[preserve_target_def] >> metis_tac[]) >>
                gvs[] >>
                `rule_link.rhs.t ' (edgeid "e0") = lhs'.t ' (edgeid "e0")` by
                  (simp[] >> EVAL_TAC) >>
                gvs[]))
        (* e1 case *)
        >- (`m.edgemap ' (edgeid "e1") = track_bar.edgemap ' x` by
              (fs[IN_INSERT] >> metis_tac[]) >>
            `tag_edgeid_right (edgeid "e1") IN G'0.E` by
              (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
                    dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
               DISJ2_TAC >> qexists_tac `edgeid "e1"` >> simp[] >> EVAL_TAC) >>
            `FDOM G'0.t = G'0.E` by
              fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
            `x IN FDOM (G'0.t f_o_f FUN_FMAP (\e.
               if track_bar.edgemap ' e = m.edgemap ' (edgeid "e0") \/
                  track_bar.edgemap ' e = m.edgemap ' (edgeid "e1")
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (track_bar.edgemap ' e)) G0.E)` by
              (simp[f_o_f_DEF, FUN_FMAP_DEF]) >>
            first_x_assum (mp_tac o MATCH_MP (cj 2 f_o_f_DEF)) >>
            strip_tac >> pop_assum (fn th => REWRITE_TAC[th]) >>
            simp[FUN_FMAP_DEF] >>
            `G'0.t ' (tag_edgeid_right (edgeid "e1")) =
             tag_nodeid_left (m.nodemap ' (rhs'.t ' (edgeid "e1")))` by
              (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
               qpat_x_assum `rhs'.t = rule_link.rhs.t`
                 (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
               irule dpoTheory.gluing_t_apply_right_tagged_in_interface >>
               simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
               fs[wf_hostgraph_def] >> EVAL_TAC >>
               simp[IMAGE_FINITE]) >>
            simp[] >>
            `(G.t f_o_f m.edgemap) ' (edgeid "e1") =
             G.t ' (m.edgemap ' (edgeid "e1"))` by
              (irule f_o_f_apply >> gvs[] >> EVAL_TAC) >>
            sg `(m.nodemap f_o_f lhs'.t) ' (edgeid "e1") =
                m.nodemap ' (lhs'.t ' (edgeid "e1"))`
            >- (irule f_o_f_apply >> conj_tac
                >- (simp[] >> EVAL_TAC >> fs[] >> EVAL_TAC >> gvs[] >>
                    EVAL_TAC >>
                    `FDOM m.nodemap = lhs'.V` by fs match_morphism_ss >>
                    `nodeid "n2" IN rule_link.lhs.V` by EVAL_TAC >>
                    metis_tac[])
                >- (`FDOM lhs'.t = lhs'.E` by
                      fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
                    simp[]))
            >- (`m.nodemap ' (lhs'.t ' (edgeid "e1")) =
                 G.t ' (m.edgemap ' (edgeid "e1"))` by
                  (fs[preserve_target_def] >> metis_tac[]) >>
                `rule_link.rhs.t ' (edgeid "e1") = lhs'.t ' (edgeid "e1")` by
                  (simp[] >> EVAL_TAC) >>
                gvs[])))
      (* --- Surviving edge case --- *)
      >- (`FDOM G'0.t = G'0.E` by
            fs[wf_hostgraph_def, graphTheory.wf_graph_def] >>
          `tag_edgeid_left (track_bar.edgemap ' x) IN G'0.E` by
            (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
                  dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
             DISJ1_TAC >>
             simp[Abbr `D`, dpoTheory.deletion_def,
                  dpoTheory.deletion_remaining_edges_def] >>
             qexists_tac `track_bar.edgemap ' x` >> simp[] >>
             `track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
               (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
             `FRANGE track_bar.edgemap SUBSET G.E` by fs me_inj_ss >>
             metis_tac[SUBSET_DEF]) >>
          `x IN FDOM (G'0.t f_o_f FUN_FMAP (\e.
             if track_bar.edgemap ' e = m.edgemap ' (edgeid "e0") \/
                track_bar.edgemap ' e = m.edgemap ' (edgeid "e1")
             then tag_edgeid_right
                    (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                     then edgeid "e0" else edgeid "e1")
             else tag_edgeid_left (track_bar.edgemap ' e)) G0.E)` by
            (simp[f_o_f_DEF, FUN_FMAP_DEF]) >>
          first_x_assum (mp_tac o MATCH_MP (cj 2 f_o_f_DEF)) >>
          strip_tac >> pop_assum (fn th => REWRITE_TAC[th]) >>
          simp[FUN_FMAP_DEF] >>
          `track_bar.edgemap ' x IN D.E` by
            (simp[Abbr `D`, dpoTheory.deletion_def,
                  dpoTheory.deletion_remaining_edges_def] >>
             `track_bar.edgemap ' x IN FRANGE track_bar.edgemap` by
               (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
             `FRANGE track_bar.edgemap SUBSET G.E` by fs me_inj_ss >>
             metis_tac[SUBSET_DEF]) >>
          `G'0.t ' (tag_edgeid_left (track_bar.edgemap ' x)) =
           tag_nodeid_left (D.t ' (track_bar.edgemap ' x))` by
            (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
             irule dpoTheory.gluing_t_apply_left_tagged >>
             simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
             fs[wf_hostgraph_def] >> simp[IMAGE_FINITE]) >>
          `D.t ' (track_bar.edgemap ' x) = G.t ' (track_bar.edgemap ' x)` by
            (fs[Abbr `D`, dpoTheory.deletion_def, LET_THM, DRESTRICT_DEF]) >>
          gvs[]))
QED

Theorem link_step_preserve_rootedness:
  !G0 G track_bar lhs' rhs' m.
    wf_hostgraph G0 /\ wf_hostgraph G /\ FINITE G0.E /\
    minimal_extension G0 track_bar G /\
    unrooted_hostgraph G /\
    is_match lhs' rule_link.inf m G /\
    lhs'.E = rule_link.lhs.E /\ lhs'.V = rule_link.lhs.V /\
    rhs'.V = rule_link.rhs.V /\ rhs'.E = rule_link.rhs.E /\
    wf_hostgraph lhs' /\ wf_hostgraph rhs' /\
    wf_hostgraph (dpo lhs' rule_link.inf rhs' m G) /\
    unrooted_hostgraph (dpo lhs' rule_link.inf rhs' m G) ==>
    preserve_defined_rootedness G0
      <| nodemap :=
        (compose_morphism (track lhs' rule_link.inf m G)
          <| nodemap := track_bar.nodemap;
             edgemap := track_bar.edgemap |>).nodemap;
        edgemap := FUN_FMAP
          (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (track_bar.edgemap ' e))
          G0.E |>
      (dpo lhs' rule_link.inf rhs' m G)
Proof
  rpt strip_tac >> simp[preserve_defined_rootedness_def, SUBMAP_DEF] >>
  qabbrev_tac `G'0 = dpo lhs' rule_link.inf rhs' m G` >>
  qabbrev_tac `nm = (compose_morphism (track lhs' rule_link.inf m G)
    <| nodemap := track_bar.nodemap;
       edgemap := track_bar.edgemap |>).nodemap` >>
  drule_all minimal_extension_pointwise >> strip_tac >>
  `FINITE G.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  `deletion_remaining_nodes lhs' m rule_link.inf G = G.V` by
    (irule link_no_node_deletion >> gvs[]) >>
  `FDOM (track lhs' rule_link.inf m G).nodemap = G.V` by
    simp[trackTheory.FDOM_track_nodemap] >>
  `G'0.V = IMAGE tag_nodeid_left G.V` by
    (simp[Abbr `G'0`] >> irule link_dpo_V >> simp[]) >>
  sg `FDOM nm = G0.V`
  >- (simp[Abbr `nm`, morphismTheory.compose_morphism_def,
           cj 1 f_o_f_DEF, EXTENSION] >>
      gen_tac >> EQ_TAC >> strip_tac >> simp[] >>
      metis_tac[BIJ_DEF, INJ_DEF])
  >- (
  `!v. v IN G0.V ==> nm ' v = tag_nodeid_left (track_bar.nodemap ' v)` by
    (rpt strip_tac >>
     simp[Abbr `nm`, morphismTheory.compose_morphism_def] >>
     `track_bar.nodemap ' v IN G.V` by metis_tac[BIJ_DEF, INJ_DEF] >>
     simp[f_o_f_DEF] >> irule trackTheory.track_nodemap_apply >> simp[]) >>
  `FDOM G'0.p = G'0.V` by fs[unrooted_hostgraph_def] >>
  rpt strip_tac
  >- (`x IN G0.V` by
        (qpat_x_assum `wf_hostgraph G0` mp_tac >>
         simp[wf_hostgraph_def, graphTheory.wf_graph_def] >>
         metis_tac[SUBSET_DEF]) >>
      simp[cj 1 f_o_f_DEF, EXTENSION] >>
      metis_tac[BIJ_DEF, INJ_DEF])
  >- (`x IN G0.V` by
        (qpat_x_assum `wf_hostgraph G0` mp_tac >>
         simp[wf_hostgraph_def, graphTheory.wf_graph_def] >>
         metis_tac[SUBSET_DEF]) >>
      `~(G0.p ' x)` by
        (qpat_x_assum `!v. v IN FDOM G0.p ==> _` (qspec_then `x` mp_tac) >>
         simp[] >> fs[unrooted_hostgraph_def] >>
         metis_tac[BIJ_DEF, INJ_DEF]) >>
      `nm ' x = tag_nodeid_left (track_bar.nodemap ' x)` by metis_tac[] >>
      `nm ' x IN FDOM G'0.p` by
        (simp[] >>
         `track_bar.nodemap ' x IN G.V` by metis_tac[BIJ_DEF, INJ_DEF] >>
         simp[IN_IMAGE] >> metis_tac[]) >>
      `x IN FDOM nm` by metis_tac[] >>
      `~((G'0.p f_o_f nm) ' x)` suffices_by simp[] >>
      `(G'0.p f_o_f nm) ' x = G'0.p ' (nm ' x)` suffices_by
        (simp[] >> fs[unrooted_hostgraph_def] >>
         metis_tac[IN_IMAGE, BIJ_DEF, INJ_DEF]) >>
      irule (cj 2 f_o_f_DEF) >>
      simp[cj 1 f_o_f_DEF] >> metis_tac[BIJ_DEF, INJ_DEF]))
QED

Theorem link_step_morphism_dom_ran:
  !G0 G track_bar lhs' rhs' m.
    wf_hostgraph G0 /\ wf_hostgraph G /\ FINITE G0.E /\
    minimal_extension G0 track_bar G /\
    is_match lhs' rule_link.inf m G /\
    lhs'.E = rule_link.lhs.E /\ lhs'.V = rule_link.lhs.V /\
    rhs'.V = rule_link.rhs.V /\ rhs'.E = rule_link.rhs.E /\
    wf_hostgraph lhs' /\ wf_hostgraph rhs' /\
    wf_hostgraph (dpo lhs' rule_link.inf rhs' m G) ==>
    morphism_dom_ran G0
      <| nodemap :=
        (compose_morphism (track lhs' rule_link.inf m G)
          <| nodemap := track_bar.nodemap;
             edgemap := track_bar.edgemap |>).nodemap;
        edgemap := FUN_FMAP
          (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (track_bar.edgemap ' e))
          G0.E |>
      (dpo lhs' rule_link.inf rhs' m G)
Proof
  rpt strip_tac >>
  `FINITE G.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  `FINITE G0.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  drule_all minimal_extension_pointwise >> strip_tac >>
  `(dpo lhs' rule_link.inf rhs' m G).V = IMAGE tag_nodeid_left G.V`
    by (irule link_dpo_V >> simp[]) >>
  `FDOM (track lhs' rule_link.inf m G).nodemap = G.V`
    by (irule link_track_nodemap_FDOM >> simp[]) >>
  simp[morphism_dom_ran_def, compose_morphism_def] >>
  conj_tac
  >- (simp[cj 1 f_o_f_DEF, EXTENSION] >> rw[] >> eq_tac >>
      rw[] >> fs[BIJ_DEF, INJ_DEF])
  >> conj_tac
  >- (simp[FRANGE_DEF, SUBSET_DEF, PULL_EXISTS, cj 1 f_o_f_DEF] >>
      `BIJ ($' (track lhs' rule_link.inf m G).nodemap) G.V
           (IMAGE tag_nodeid_left G.V)`
        by (irule link_track_nodemap_BIJ >> simp[]) >>
      rw[] >>
      `((track lhs' rule_link.inf m G).nodemap f_o_f
        track_bar.nodemap) ' x' =
       (track lhs' rule_link.inf m G).nodemap ' (track_bar.nodemap ' x')`
        by (irule (cj 2 f_o_f_DEF) >> simp[cj 1 f_o_f_DEF]) >> simp[] >>
      `(track lhs' rule_link.inf m G).nodemap ' (track_bar.nodemap ' x')
       IN IMAGE tag_nodeid_left G.V`
        by (fs[BIJ_DEF, SURJ_DEF] >> first_x_assum irule >> simp[]) >>
      fs[IN_IMAGE] >> metis_tac[])
  >- (`(dpo lhs' rule_link.inf rhs' m G).E =
       edgeid_coprod (G.E DIFF deletion_deleted_edges lhs' m) rule_link.rhs.E`
        by simp[dpo_def, gluing_def, gluing_edges_def, deletion_def,
                deletion_remaining_edges_def] >>
      ASM_REWRITE_TAC[] >> simp[SUBSET_DEF, PULL_EXISTS] >> rw[] >>
      Cases_on `track_bar.edgemap ' e IN deletion_deleted_edges lhs' m` >>
      simp[tag_edgeid_coprod_membership]
      >- EVAL_TAC
      >- EVAL_TAC
      >- EVAL_TAC
      >- metis_tac[]
      >- metis_tac[]
      >- (`track_bar.edgemap ' e IN FRANGE track_bar.edgemap`
            by (simp[FRANGE_DEF] >> qexists_tac `e` >> simp[]) >>
          metis_tac[SUBSET_DEF]))
QED

(* -------------------------------------------------------------------------- *)
(* Factored helper: BIJ of composed nodemap through link step                 *)
(* -------------------------------------------------------------------------- *)

Theorem link_step_nodemap_BIJ:
  !G0 G track_bar lhs' rhs' m.
    wf_hostgraph G /\
    BIJ ($' track_bar.nodemap) G0.V G.V /\
    FDOM track_bar.nodemap = G0.V /\
    lhs'.V = rule_link.lhs.V /\
    rhs'.V = rule_link.rhs.V ==>
    BIJ ($' (compose_morphism (track lhs' rule_link.inf m G)
      <| nodemap := track_bar.nodemap;
         edgemap := track_bar.edgemap |>).nodemap)
      G0.V (dpo lhs' rule_link.inf rhs' m G).V
Proof
  rpt strip_tac >> simp[compose_morphism_def] >>
  `(dpo lhs' rule_link.inf rhs' m G).V = IMAGE tag_nodeid_left G.V`
     by (irule link_dpo_V >> simp[]) >>
  `FINITE G.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  `BIJ ($' (track lhs' rule_link.inf m G).nodemap) G.V
       (IMAGE tag_nodeid_left G.V)`
     by (irule link_track_nodemap_BIJ >> simp[]) >>
  `FDOM (track lhs' rule_link.inf m G).nodemap = G.V`
     by (irule link_track_nodemap_FDOM >> simp[]) >>
  ASM_REWRITE_TAC[] >>
  irule (iffRL BIJ_CONG) >>
  qexists_tac `($' (track lhs' rule_link.inf m G).nodemap) o
               ($' track_bar.nodemap)` >>
  conj_tac
  >- (rw[] >> irule (cj 2 f_o_f_DEF) >>
      simp[cj 1 f_o_f_DEF] >>
      metis_tac[BIJ_DEF, INJ_DEF])
  >- (irule BIJ_COMPOSE >> qexists_tac `G.V` >> simp[])
QED

(* -------------------------------------------------------------------------- *)
(* Sub-theorem: INJ of edgemap under link step                                *)
(* -------------------------------------------------------------------------- *)

Theorem link_step_edgemap_INJ:
  !G0 G track_bar lhs' rhs' m.
    wf_hostgraph G0 /\ wf_hostgraph G /\ FINITE G0.E /\
    minimal_extension G0 track_bar G /\
    is_match lhs' rule_link.inf m G /\
    lhs'.E = rule_link.lhs.E /\
    rhs'.E = rule_link.rhs.E /\
    wf_hostgraph lhs' /\ wf_hostgraph rhs' /\
    wf_hostgraph (dpo lhs' rule_link.inf rhs' m G) ==>
    INJ ($' (FUN_FMAP
      (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
           then tag_edgeid_right
                  (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                   then edgeid "e0" else edgeid "e1")
           else tag_edgeid_left (track_bar.edgemap ' e))
      G0.E)) G0.E (dpo lhs' rule_link.inf rhs' m G).E
Proof
  rpt strip_tac >>
  (* Re-derive facts from minimal_extension *)
  `INJ ($' track_bar.edgemap) G0.E G.E` by
    fs[minimal_extension_def, is_inj_morphism_def] >>
  (* Match facts *)
  `FDOM m.edgemap = lhs'.E` by fs match_morphism_ss >>
  `INJ ($' m.edgemap) lhs'.E G.E` by fs match_inj_ss >>
  `lhs'.E = {edgeid "e1"; edgeid "e0"}` by (gvs[] >> EVAL_TAC) >>
  `rhs'.E = {edgeid "e2"; edgeid "e1"; edgeid "e0"}` by (gvs[] >> EVAL_TAC) >>
  `m.edgemap ' (edgeid "e0") <> m.edgemap ' (edgeid "e1")` by
    (strip_tac >>
     `edgeid "e0" IN lhs'.E /\ edgeid "e1" IN lhs'.E` by (gvs[] >> EVAL_TAC) >>
     `edgeid "e0" = edgeid "e1"` by metis_tac[INJ_DEF] >> fs[]) >>
  `deletion_deleted_edges lhs' m =
   {m.edgemap ' (edgeid "e0"); m.edgemap ' (edgeid "e1")}` by
    (simp[dpoTheory.deletion_deleted_edges_def] >> gvs[] >>
     simp[EXTENSION] >> metis_tac[]) >>
  qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
  qabbrev_tac `G'0 = dpo lhs' rule_link.inf rhs' m G` >>
  `FINITE D.E` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def] >>
     fs wf_ss) >>
  `FINITE rhs'.E` by simp[] >>
  `G'0.E = edgeid_coprod D.E rhs'.E` by
    (simp[Abbr `G'0`, Abbr `D`, dpoTheory.dpo_def, dpoTheory.gluing_def,
          dpoTheory.gluing_edges_def, dpoTheory.deletion_def]) >>
  simp[INJ_DEF] >> conj_tac
  (* Range condition *)
  >- (rpt strip_tac >> pop_assum mp_tac >> simp[FUN_FMAP_DEF] >>
      strip_tac >>
      simp[dpoTheory.edgeid_coprod_def] >>
      Cases_on `track_bar.edgemap ' x = m.edgemap ' (edgeid "e0") \/
                track_bar.edgemap ' x = m.edgemap ' (edgeid "e1")` >> simp[]
      >- (Cases_on `m.edgemap ' (edgeid "e0") = track_bar.edgemap ' x` >> simp[])
      >- (DISJ1_TAC >> qexists_tac `track_bar.edgemap ' x` >> simp[] >>
          simp[Abbr `D`, dpoTheory.deletion_def,
               dpoTheory.deletion_remaining_edges_def] >>
          `track_bar.edgemap ' x IN G.E` by
            (qpat_x_assum `INJ ($' track_bar.edgemap) G0.E G.E` mp_tac >>
             simp[INJ_DEF] >> metis_tac[]) >>
          gvs[]))
  (* Injectivity *)
  >> rpt strip_tac >>
  qpat_x_assum `_ = _` mp_tac >>
  simp[FUN_FMAP_DEF] >> strip_tac >>
  Cases_on `track_bar.edgemap ' x = m.edgemap ' (edgeid "e0") \/
            track_bar.edgemap ' x = m.edgemap ' (edgeid "e1")` >>
  Cases_on `track_bar.edgemap ' y = m.edgemap ' (edgeid "e0") \/
            track_bar.edgemap ' y = m.edgemap ' (edgeid "e1")`
  (* Both deleted *)
  >- (fs[] >>
      Cases_on `m.edgemap ' (edgeid "e0") = track_bar.edgemap ' x` >>
      Cases_on `m.edgemap ' (edgeid "e0") = track_bar.edgemap ' y` >> fs[]
      >- (`track_bar.edgemap ' x = track_bar.edgemap ' y` by simp[] >>
          metis_tac[INJ_DEF])
      >- (fs[taggingTheory.tag_edgeid_right_def,
              graphTheory.edgeid_absrep] >>
          qpat_x_assum `dest_edgeid _ = _` mp_tac >>
          ASM_REWRITE_TAC[] >> simp[graphTheory.edgeid_absrep])
      >- (fs[taggingTheory.tag_edgeid_right_def,
              graphTheory.edgeid_absrep] >>
          qpat_x_assum `dest_edgeid _ = _` mp_tac >>
          ASM_REWRITE_TAC[] >> simp[graphTheory.edgeid_absrep])
      >- (`track_bar.edgemap ' x = track_bar.edgemap ' y` by simp[] >>
          metis_tac[INJ_DEF]))
  (* x deleted, y surviving *)
  >- (fs[] >> metis_tac[taggingTheory.tag_disjoint])
  (* x surviving, y deleted *)
  >- (fs[] >> metis_tac[taggingTheory.tag_disjoint])
  (* Both surviving *)
  >- (fs[] >>
      `track_bar.edgemap ' x = track_bar.edgemap ' y` by
        (fs[taggingTheory.tag_edgeid_left_def, graphTheory.edgeid_absrep] >>
         Cases_on `track_bar.edgemap ' x` >> Cases_on `track_bar.edgemap ' y` >>
         fs[graphTheory.dest_edgeid_def]) >>
      metis_tac[INJ_DEF])
QED

(* -------------------------------------------------------------------------- *)
(* Sub-theorem: source/target preservation (pointwise) under link step        *)
(* -------------------------------------------------------------------------- *)

Theorem link_step_source_target_pointwise:
  !G0 G track_bar lhs' rhs' m.
    wf_hostgraph G0 /\ wf_hostgraph G /\ FINITE G0.E /\
    minimal_extension G0 track_bar G /\
    is_match lhs' rule_link.inf m G /\
    lhs'.V = rule_link.lhs.V /\
    lhs'.E = rule_link.lhs.E /\
    lhs'.s = rule_link.lhs.s /\ lhs'.t = rule_link.lhs.t /\
    rhs'.V = rule_link.rhs.V /\
    rhs'.E = rule_link.rhs.E /\
    rhs'.s = rule_link.rhs.s /\ rhs'.t = rule_link.rhs.t /\
    wf_hostgraph lhs' /\ wf_hostgraph rhs' /\
    wf_hostgraph (dpo lhs' rule_link.inf rhs' m G) ==>
    !e. e IN G0.E ==>
      FUN_FMAP
        (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
             then tag_edgeid_right
                    (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                     then edgeid "e0" else edgeid "e1")
             else tag_edgeid_left (track_bar.edgemap ' e)) G0.E ' e
        IN FDOM (dpo lhs' rule_link.inf rhs' m G).s /\
      FUN_FMAP
        (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
             then tag_edgeid_right
                    (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                     then edgeid "e0" else edgeid "e1")
             else tag_edgeid_left (track_bar.edgemap ' e)) G0.E ' e
        IN FDOM (dpo lhs' rule_link.inf rhs' m G).t /\
      (dpo lhs' rule_link.inf rhs' m G).s ' (FUN_FMAP
        (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
             then tag_edgeid_right
                    (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                     then edgeid "e0" else edgeid "e1")
             else tag_edgeid_left (track_bar.edgemap ' e)) G0.E ' e) =
      (compose_morphism (track lhs' rule_link.inf m G)
        <| nodemap := track_bar.nodemap;
           edgemap := track_bar.edgemap |>).nodemap ' (G0.s ' e) /\
      (dpo lhs' rule_link.inf rhs' m G).t ' (FUN_FMAP
        (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
             then tag_edgeid_right
                    (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                     then edgeid "e0" else edgeid "e1")
             else tag_edgeid_left (track_bar.edgemap ' e)) G0.E ' e) =
      (compose_morphism (track lhs' rule_link.inf m G)
        <| nodemap := track_bar.nodemap;
           edgemap := track_bar.edgemap |>).nodemap ' (G0.t ' e)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  (* Re-derive facts from minimal_extension *)
  `FDOM track_bar.edgemap = G0.E` by fs me_inj_ss >>
  `BIJ ($' track_bar.nodemap) G0.V G.V` by fs[minimal_extension_def] >>
  `FDOM track_bar.nodemap = G0.V` by fs me_inj_ss >>
  `INJ ($' track_bar.edgemap) G0.E G.E` by
    fs[minimal_extension_def, is_inj_morphism_def] >>
  (* Match facts *)
  `FDOM m.edgemap = lhs'.E` by fs match_morphism_ss >>
  `FRANGE m.edgemap SUBSET G.E` by fs match_morphism_ss >>
  `FDOM m.nodemap = lhs'.V` by fs match_morphism_ss >>
  `m.nodemap f_o_f lhs'.s = G.s f_o_f m.edgemap` by fs match_source_ss >>
  `m.nodemap f_o_f lhs'.t = G.t f_o_f m.edgemap` by fs match_target_ss >>
  `INJ ($' m.edgemap) lhs'.E G.E` by fs match_inj_ss >>
  `lhs'.E = {edgeid "e1"; edgeid "e0"}` by (gvs[] >> EVAL_TAC) >>
  `rhs'.E = {edgeid "e2"; edgeid "e1"; edgeid "e0"}` by (gvs[] >> EVAL_TAC) >>
  `m.edgemap ' (edgeid "e0") <> m.edgemap ' (edgeid "e1")` by
    (strip_tac >>
     `edgeid "e0" IN lhs'.E /\ edgeid "e1" IN lhs'.E` by (gvs[] >> EVAL_TAC) >>
     `edgeid "e0" = edgeid "e1"` by metis_tac[INJ_DEF] >> fs[]) >>
  `deletion_deleted_edges lhs' m =
   {m.edgemap ' (edgeid "e0"); m.edgemap ' (edgeid "e1")}` by
    (simp[dpoTheory.deletion_deleted_edges_def] >> gvs[] >>
     simp[EXTENSION] >> metis_tac[]) >>
  qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
  qabbrev_tac `G'0 = dpo lhs' rule_link.inf rhs' m G` >>
  `FINITE G0.V` by fs wf_ss >>
  `wf_graph D` by
    (simp[Abbr `D`] >>
     irule hostgraphTheory.wf_partial_hostgraph_IMP_wf_graph >>
     irule dpoTheory.deletion_preserves_wf_graph >> simp[] >> EVAL_TAC) >>
  `FINITE D.E` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def] >>
     fs wf_ss) >>
  `FINITE rhs'.E` by simp[] >>
  `G'0.E = edgeid_coprod D.E rhs'.E` by
    (simp[Abbr `G'0`, Abbr `D`, dpoTheory.dpo_def, dpoTheory.gluing_def,
          dpoTheory.gluing_edges_def, dpoTheory.deletion_def]) >>
  STRIP_ASSUME_TAC rule_link_structure >>
  (* DPO source facts for right-tagged edges *)
  sg `G'0.s ' (tag_edgeid_right (edgeid "e0")) =
      tag_nodeid_left (m.nodemap ' (rhs'.s ' (edgeid "e0")))`
  >- (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
      qpat_x_assum `rule_link.rhs.s ' (edgeid "e0") = nodeid "n0"`
        (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
      qpat_x_assum `rhs'.s = rule_link.rhs.s`
        (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
      irule dpoTheory.gluing_s_apply_right_tagged_in_interface >>
      simp[] >> fs[wf_hostgraph_def] >>
      EVAL_TAC)
  >- (
  sg `G'0.s ' (tag_edgeid_right (edgeid "e1")) =
      tag_nodeid_left (m.nodemap ' (rhs'.s ' (edgeid "e1")))`
  >- (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
      qpat_x_assum `rule_link.rhs.s ' (edgeid "e1") = nodeid "n1"`
        (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
      qpat_x_assum `rhs'.s = rule_link.rhs.s`
        (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
      irule dpoTheory.gluing_s_apply_right_tagged_in_interface >>
      simp[] >> fs[wf_hostgraph_def] >>
      EVAL_TAC)
  >- (
  (* Compose/track chain helper *)
  `FINITE G.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  sg `!v. v IN G0.V ==>
          (compose_morphism (track lhs' rule_link.inf m G)
            <| nodemap := track_bar.nodemap; edgemap := track_bar.edgemap |>).nodemap ' v =
          tag_nodeid_left (track_bar.nodemap ' v)`
  >- (rpt strip_tac >>
      simp[morphismTheory.compose_morphism_def] >>
      `v IN FDOM ((track lhs' rule_link.inf m G).nodemap f_o_f track_bar.nodemap)` by
        (simp[f_o_f_DEF] >> simp[] >>
         `track_bar.nodemap ' v IN G.V` by
           metis_tac[BIJ_DEF, INJ_DEF] >>
         `FDOM (track lhs' rule_link.inf m G).nodemap = G.V` by
           (irule link_track_nodemap_FDOM >>
            metis_tac[wf_hostgraph_IMP_finite_sets]) >>
         simp[]) >>
      drule (cj 2 f_o_f_DEF) >> simp[] >> DISCH_TAC >> simp[] >>
      `rule_link.inf = rule_link.lhs.V` by EVAL_TAC >>
      `deletion_remaining_nodes lhs' m rule_link.inf G = G.V` by
        (simp[dpoTheory.deletion_remaining_nodes_def,
              dpoTheory.deletion_deleted_nodes_def] >>
         gvs[] >> simp[DIFF_EQ_EMPTY, SUBSET_REFL]) >>
      irule trackTheory.track_nodemap_apply >> simp[] >>
      metis_tac[BIJ_DEF, INJ_DEF])
  >- (
  (* Now the actual pointwise proof *)
  `FUN_FMAP (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
                 then tag_edgeid_right
                        (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                         then edgeid "e0" else edgeid "e1")
                 else tag_edgeid_left (track_bar.edgemap ' e)) G0.E ' e =
   (if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
    then tag_edgeid_right
           (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
            then edgeid "e0" else edgeid "e1")
    else tag_edgeid_left (track_bar.edgemap ' e))` by simp[FUN_FMAP_DEF] >>
  pop_assum (fn th => PURE_REWRITE_TAC [th]) >>
  `track_bar.edgemap ' e IN G.E` by
    (qpat_x_assum `INJ ($' track_bar.edgemap) G0.E G.E` mp_tac >>
     simp[INJ_DEF] >> metis_tac[]) >>
  `track_bar.edgemap ' e IN FDOM G.s /\ track_bar.edgemap ' e IN FDOM G.t /\
   G.s ' (track_bar.edgemap ' e) = track_bar.nodemap ' (G0.s ' e) /\
   G.t ' (track_bar.edgemap ' e) = track_bar.nodemap ' (G0.t ' e)` by
    (drule_all minimal_extension_pointwise >> strip_tac >>
     first_x_assum (mp_tac o Q.SPEC `e`) >>
     simp[]) >>
  `G0.s ' e IN G0.V` by
    (fs (wf_ss @ [FRANGE_DEF, SUBSET_DEF]) >> metis_tac[]) >>
  `G0.t ' e IN G0.V` by
    (fs (wf_ss @ [FRANGE_DEF, SUBSET_DEF]) >> metis_tac[]) >>
  Cases_on `track_bar.edgemap ' e IN deletion_deleted_edges lhs' m`
  >- (
    gvs[]
    >- (
      `tag_edgeid_right (edgeid "e0") IN G'0.E` by
        (simp[dpoTheory.edgeid_coprod_def] >> DISJ2_TAC >>
         qexists_tac `edgeid "e0"` >> gvs[] >> EVAL_TAC) >>
      `tag_edgeid_right (edgeid "e0") IN FDOM G'0.s /\
       tag_edgeid_right (edgeid "e0") IN FDOM G'0.t` by
        metis_tac[wf_hostgraph_FDOM_st] >>
      `(m.nodemap f_o_f rule_link.lhs.s) ' (edgeid "e0") =
       m.nodemap ' (rule_link.lhs.s ' (edgeid "e0"))` by
        (irule f_o_f_apply >> simp[] >> EVAL_TAC) >>
      `(G.s f_o_f m.edgemap) ' (edgeid "e0") =
       G.s ' (m.edgemap ' (edgeid "e0"))` by
        (irule f_o_f_apply >> gvs[] >> EVAL_TAC) >>
      `m.nodemap ' (nodeid "n0") = G.s ' (m.edgemap ' (edgeid "e0"))` by
        gvs[] >>
      `G'0.t ' (tag_edgeid_right (edgeid "e0")) =
       tag_nodeid_left (m.nodemap ' (rhs'.t ' (edgeid "e0")))` by
        (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
         qpat_x_assum `rule_link.rhs.t ' (edgeid "e0") = nodeid "n1"`
           (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
         qpat_x_assum `rhs'.t = rule_link.rhs.t`
           (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
         irule dpoTheory.gluing_t_apply_right_tagged_in_interface >>
         simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
         fs[wf_hostgraph_def] >> EVAL_TAC >>
         simp[IMAGE_FINITE]) >>
      `(m.nodemap f_o_f rule_link.lhs.t) ' (edgeid "e0") =
       m.nodemap ' (rule_link.lhs.t ' (edgeid "e0"))` by
        (irule f_o_f_apply >> simp[] >> EVAL_TAC) >>
      `(G.t f_o_f m.edgemap) ' (edgeid "e0") =
       G.t ' (m.edgemap ' (edgeid "e0"))` by
        (irule f_o_f_apply >> gvs[] >> EVAL_TAC) >>
      `m.nodemap ' (nodeid "n1") = G.t ' (m.edgemap ' (edgeid "e0"))` by
        gvs[] >>
      gvs[])
    >- (
      `tag_edgeid_right (edgeid "e1") IN G'0.E` by
        (simp[dpoTheory.edgeid_coprod_def] >> DISJ2_TAC >>
         qexists_tac `edgeid "e1"` >> gvs[] >> EVAL_TAC) >>
      `tag_edgeid_right (edgeid "e1") IN FDOM G'0.s /\
       tag_edgeid_right (edgeid "e1") IN FDOM G'0.t` by
        metis_tac[wf_hostgraph_FDOM_st] >>
      `(m.nodemap f_o_f rule_link.lhs.s) ' (edgeid "e1") =
       m.nodemap ' (rule_link.lhs.s ' (edgeid "e1"))` by
        (irule f_o_f_apply >> simp[] >> EVAL_TAC) >>
      `(G.s f_o_f m.edgemap) ' (edgeid "e1") =
       G.s ' (m.edgemap ' (edgeid "e1"))` by
        (irule f_o_f_apply >> gvs[] >> EVAL_TAC) >>
      `m.nodemap ' (nodeid "n1") = G.s ' (m.edgemap ' (edgeid "e1"))` by
        gvs[] >>
      `G'0.t ' (tag_edgeid_right (edgeid "e1")) =
       tag_nodeid_left (m.nodemap ' (rhs'.t ' (edgeid "e1")))` by
        (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
         qpat_x_assum `rule_link.rhs.t ' (edgeid "e1") = nodeid "n2"`
           (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
         qpat_x_assum `rhs'.t = rule_link.rhs.t`
           (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
         irule dpoTheory.gluing_t_apply_right_tagged_in_interface >>
         simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
         fs[wf_hostgraph_def] >> EVAL_TAC >>
         simp[IMAGE_FINITE]) >>
      `(m.nodemap f_o_f rule_link.lhs.t) ' (edgeid "e1") =
       m.nodemap ' (rule_link.lhs.t ' (edgeid "e1"))` by
        (irule f_o_f_apply >> simp[] >> EVAL_TAC) >>
      `(G.t f_o_f m.edgemap) ' (edgeid "e1") =
       G.t ' (m.edgemap ' (edgeid "e1"))` by
        (irule f_o_f_apply >> gvs[] >> EVAL_TAC) >>
      `m.nodemap ' (nodeid "n2") = G.t ' (m.edgemap ' (edgeid "e1"))` by
        gvs[] >>
      gvs[]))
  >- (
    gvs[] >>
    `track_bar.edgemap ' e IN deletion_remaining_edges lhs' m G` by
      (simp[dpoTheory.deletion_remaining_edges_def] >> gvs[]) >>
    `tag_edgeid_left (track_bar.edgemap ' e) IN G'0.E` by
      (simp[dpoTheory.edgeid_coprod_def] >> DISJ1_TAC >>
       simp[Abbr `D`, dpoTheory.deletion_def] >>
       qexists_tac `track_bar.edgemap ' e` >> simp[]) >>
    `tag_edgeid_left (track_bar.edgemap ' e) IN FDOM G'0.s /\
     tag_edgeid_left (track_bar.edgemap ' e) IN FDOM G'0.t` by
      metis_tac[wf_hostgraph_FDOM_st] >>
    `track_bar.edgemap ' e IN D.E` by simp[Abbr `D`, dpoTheory.deletion_def] >>
    `G'0.s ' (tag_edgeid_left (track_bar.edgemap ' e)) =
     tag_nodeid_left (G.s ' (track_bar.edgemap ' e))` by
      (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
       `(gluing_s rule_link.inf m D rhs') '
        (tag_edgeid_left (track_bar.edgemap ' e)) =
        tag_nodeid_left (D.s ' (track_bar.edgemap ' e))` by
         (irule dpoTheory.gluing_s_apply_left_tagged >> simp[] >>
          fs[wf_hostgraph_def]) >>
       `D.s ' (track_bar.edgemap ' e) = G.s ' (track_bar.edgemap ' e)` by
         (fs[Abbr `D`, dpoTheory.deletion_def, LET_THM, DRESTRICT_DEF]) >>
       gvs[]) >>
    `G'0.t ' (tag_edgeid_left (track_bar.edgemap ' e)) =
     tag_nodeid_left (G.t ' (track_bar.edgemap ' e))` by
      (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
       `(gluing_t (gluing_edges (deletion lhs' rule_link.inf m G) rhs')
                  rule_link.inf m (deletion lhs' rule_link.inf m G) rhs') '
        (tag_edgeid_left (track_bar.edgemap ' e)) =
        tag_nodeid_left ((deletion lhs' rule_link.inf m G).t ' (track_bar.edgemap ' e))` by
         (irule dpoTheory.gluing_t_apply_left_tagged >> simp[] >>
          fs[wf_hostgraph_def] >>
          simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
          metis_tac[IMAGE_FINITE]) >>
       `(deletion lhs' rule_link.inf m G).t ' (track_bar.edgemap ' e) =
        G.t ' (track_bar.edgemap ' e)` by
         (fs[Abbr `D`, dpoTheory.deletion_def, LET_THM, DRESTRICT_DEF]) >>
       gvs[]) >>
    gvs[]))))
QED

(* -------------------------------------------------------------------------- *)
(* Sub-theorem: reachability of edges not in FRANGE under link step           *)
(* -------------------------------------------------------------------------- *)

Theorem link_step_reachability:
  !G0 G m0 track_bar lhs' rhs' m.
    wf_hostgraph G0 /\ wf_hostgraph G /\ FINITE G0.E /\
    minimal_extension G0 track_bar G /\
    tc_loop_invariant G0 G m0 /\
    extends_morphism m0 track_bar /\
    is_match lhs' rule_link.inf m G /\
    lhs'.V = rule_link.lhs.V /\
    lhs'.E = rule_link.lhs.E /\
    lhs'.s = rule_link.lhs.s /\ lhs'.t = rule_link.lhs.t /\
    rhs'.V = rule_link.rhs.V /\
    rhs'.E = rule_link.rhs.E /\
    rhs'.s = rule_link.rhs.s /\ rhs'.t = rule_link.rhs.t /\
    wf_hostgraph lhs' /\ wf_hostgraph rhs' /\
    wf_hostgraph (dpo lhs' rule_link.inf rhs' m G) ==>
    !e. e IN (dpo lhs' rule_link.inf rhs' m G).E /\
        e NOTIN FRANGE (FUN_FMAP
          (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (track_bar.edgemap ' e))
          G0.E) ==>
        ?v w. v IN G0.V /\ w IN G0.V /\
              (compose_morphism (track lhs' rule_link.inf m G)
                <| nodemap := track_bar.nodemap;
                   edgemap := track_bar.edgemap |>).nodemap ' v =
              (dpo lhs' rule_link.inf rhs' m G).s ' e /\
              (compose_morphism (track lhs' rule_link.inf m G)
                <| nodemap := track_bar.nodemap;
                   edgemap := track_bar.edgemap |>).nodemap ' w =
              (dpo lhs' rule_link.inf rhs' m G).t ' e /\
              reachable_in G0 v w
Proof
  rpt strip_tac >>
  fs[minimal_extension_def, edge_path_justified_def, generated_edges_def] >>
  `minimally_extends G0 m0 G` by fs[tc_loop_invariant_def] >>
  `track_bar.nodemap = m0.nodemap` by fs[extends_morphism_def] >>
  qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
  `FDOM track_bar.edgemap = G0.E` by
    fs[is_inj_morphism_def, morphismTheory.is_morphism_def,
       morphismTheory.is_premorphism_def, morphismTheory.morphism_dom_ran_def] >>
  `FINITE G.V` by fs wf_ss >>
  `e IN edgeid_coprod D.E rhs'.E` by
    gvs[Abbr `D`, dpoTheory.dpo_def, dpoTheory.gluing_def,
        dpoTheory.gluing_edges_def, LET_THM] >>
  `FDOM (track lhs' rule_link.inf m G).nodemap = G.V` by
    (irule link_track_nodemap_FDOM >> simp[]) >>
  Cases_on `is_left_tagged_edgeid e`
  (* ===== Case 1: Left-tagged edge ===== *)
  >- (
    sg `e IN IMAGE tag_edgeid_left D.E`
    >- (gvs[dpoTheory.edgeid_coprod_def, IN_UNION, IN_IMAGE]
        >- (qexists_tac `x` >> gvs[])
        >- (`~is_left_tagged_edgeid (tag_edgeid_right x)` by
              metis_tac[taggingTheory.correct_tagging,
                        taggingTheory.is_left_tagged_edgeid_def,
                        taggingTheory.is_right_tagged_edgeid_def,
                        arithmeticTheory.ODD_EVEN] >> gvs[])) >>
    gvs[IN_IMAGE] >>
    sg `x IN G.E`
    >- fs[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def] >>
    sg `x NOTIN FRANGE track_bar.edgemap`
    >- (CCONTR_TAC >> fs[FRANGE_DEF] >>
        `x NOTIN deletion_deleted_edges lhs' m` by
          (fs[Abbr `D`, dpoTheory.deletion_def,
              dpoTheory.deletion_remaining_edges_def] >> gvs[]) >>
        first_x_assum (qspec_then `x'` mp_tac) >> gvs[]) >>
    `?v w. v IN G0.V /\ w IN G0.V /\ m0.nodemap ' v = G.s ' x /\
           m0.nodemap ' w = G.t ' x /\ reachable_in G0 v w` by
      (first_x_assum (qspec_then `x` mp_tac) >> simp[FRANGE_DEF] >>
       metis_tac[]) >>
    qexistsl [`v`, `w`] >> simp[] >>
    simp[morphismTheory.compose_morphism_def] >>
    sg `D.s ' x = G.s ' x`
    >- (fs[Abbr `D`, dpoTheory.deletion_def, LET_THM,
           finite_mapTheory.DRESTRICT_DEF] >>
        `x IN FDOM G.s` by fs wf_ss >> gvs[]) >>
    sg `D.t ' x = G.t ' x`
    >- (fs[Abbr `D`, dpoTheory.deletion_def, LET_THM,
           finite_mapTheory.DRESTRICT_DEF] >>
        `x IN FDOM G.t` by fs wf_ss >> gvs[]) >>
    `wf_graph D` by
      (simp[Abbr `D`] >>
       irule hostgraphTheory.wf_partial_hostgraph_IMP_wf_graph >>
       irule dpoTheory.deletion_preserves_wf_graph >> simp[] >> EVAL_TAC) >>
    sg `gluing_s rule_link.inf m D rhs' ' (tag_edgeid_left x) =
        tag_nodeid_left (D.s ' x)`
    >- (irule dpoTheory.gluing_s_apply_left_tagged >> simp[] >>
        fs[wf_hostgraph_def]) >>
    `FINITE D.E` by
      fs[Abbr `D`, dpoTheory.deletion_def,
         dpoTheory.deletion_remaining_edges_def,
         wf_hostgraph_def, wf_graph_def] >>
    `FINITE rhs'.E` by fs wf_ss >>
    sg `gluing_t (gluing_edges D rhs') rule_link.inf m D rhs' '
        (tag_edgeid_left x) = tag_nodeid_left (D.t ' x)`
    >- (irule dpoTheory.gluing_t_apply_left_tagged >> simp[] >>
        simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
        fs[wf_hostgraph_def] >> simp[] >>
        `rule_link.rhs.E = {edgeid "e2"; edgeid "e1"; edgeid "e0"}`
          by EVAL_TAC >> gvs[]) >>
    sg `(dpo lhs' rule_link.inf rhs' m G).s ' (tag_edgeid_left x) =
        tag_nodeid_left (G.s ' x)`
    >- (simp[dpoTheory.dpo_def, dpoTheory.gluing_def, LET_THM] >>
        gvs[Abbr `D`]) >>
    sg `(dpo lhs' rule_link.inf rhs' m G).t ' (tag_edgeid_left x) =
        tag_nodeid_left (G.t ' x)`
    >- (simp[dpoTheory.dpo_def, dpoTheory.gluing_def, LET_THM] >> gvs[]) >>
    gvs[] >>
    conj_tac
    >- (`G.s ' x IN G.V` by
          (`FRANGE G.s SUBSET G.V` by fs wf_ss >>
           `x IN FDOM G.s` by fs wf_ss >>
           `G.s ' x IN FRANGE G.s` by (simp[FRANGE_DEF] >> metis_tac[]) >>
           fs[SUBSET_DEF]) >>
        `((track lhs' rule_link.inf m G).nodemap f_o_f m0.nodemap) ' v =
         (track lhs' rule_link.inf m G).nodemap ' (m0.nodemap ' v)` by
          (irule f_o_f_apply >> simp[] >>
           fs[minimally_extends_def, BIJ_DEF, SURJ_DEF]) >>
        gvs[] >> irule trackTheory.track_nodemap_apply >>
        metis_tac[dpoTheory.wf_hostgraph_IMP_finite_remaining_elements,
                  link_no_node_deletion])
    >- (`G.t ' x IN G.V` by
          (`FRANGE G.t SUBSET G.V` by fs wf_ss >>
           `x IN FDOM G.t` by fs wf_ss >>
           `G.t ' x IN FRANGE G.t` by (simp[FRANGE_DEF] >> metis_tac[]) >>
           fs[SUBSET_DEF]) >>
        `((track lhs' rule_link.inf m G).nodemap f_o_f m0.nodemap) ' w =
         (track lhs' rule_link.inf m G).nodemap ' (m0.nodemap ' w)` by
          (irule f_o_f_apply >> simp[] >>
           fs[minimally_extends_def, BIJ_DEF, SURJ_DEF]) >>
        gvs[] >> irule trackTheory.track_nodemap_apply >>
        metis_tac[dpoTheory.wf_hostgraph_IMP_finite_remaining_elements,
                  link_no_node_deletion]))
  (* ===== Case 2: Right-tagged edge ===== *)
  >- (
    gvs[dpoTheory.edgeid_coprod_def, IN_UNION, IN_IMAGE]
    >- (`is_left_tagged_edgeid (tag_edgeid_left x)` by
          metis_tac[taggingTheory.correct_tagging] >> gvs[])
    >- (
    `rule_link.rhs.E = {edgeid "e2"; edgeid "e1"; edgeid "e0"}` by EVAL_TAC >>
    `x = edgeid "e0" \/ x = edgeid "e1" \/ x = edgeid "e2"` by gvs[] >>
    (* Common match morphism facts *)
    `FDOM m.edgemap = lhs'.E` by
      fs[dpoTheory.is_match_def, morphismTheory.is_inj_morphism_def,
         morphismTheory.is_morphism_def, morphismTheory.is_premorphism_def,
         morphismTheory.morphism_dom_ran_def] >>
    `FRANGE m.edgemap SUBSET G.E` by
      fs[dpoTheory.is_match_def, morphismTheory.is_inj_morphism_def,
         morphismTheory.is_morphism_def, morphismTheory.is_premorphism_def,
         morphismTheory.morphism_dom_ran_def] >>
    `edgeid "e0" IN lhs'.E` by (gvs[] >> EVAL_TAC) >>
    `edgeid "e1" IN lhs'.E` by (gvs[] >> EVAL_TAC) >>
    `m.edgemap ' (edgeid "e0") IN G.E` by
      (gvs[SUBSET_DEF, FRANGE_DEF] >> metis_tac[]) >>
    `m.edgemap ' (edgeid "e1") IN G.E` by
      (gvs[SUBSET_DEF, FRANGE_DEF] >> metis_tac[]) >>
    `?v0 w0. v0 IN G0.V /\ w0 IN G0.V /\
             m0.nodemap ' v0 = G.s ' (m.edgemap ' (edgeid "e0")) /\
             m0.nodemap ' w0 = G.t ' (m.edgemap ' (edgeid "e0")) /\
             reachable_in G0 v0 w0` by
      (irule edge_in_G_has_reachable_preimages >> simp[]) >>
    `?v1 w1. v1 IN G0.V /\ w1 IN G0.V /\
             m0.nodemap ' v1 = G.s ' (m.edgemap ' (edgeid "e1")) /\
             m0.nodemap ' w1 = G.t ' (m.edgemap ' (edgeid "e1")) /\
             reachable_in G0 v1 w1` by
      (irule edge_in_G_has_reachable_preimages >> simp[]) >>
    `FDOM m.nodemap = lhs'.V` by
      fs[dpoTheory.is_match_def, morphismTheory.is_inj_morphism_def,
         morphismTheory.is_morphism_def, morphismTheory.is_premorphism_def,
         morphismTheory.morphism_dom_ran_def] >>
    `FRANGE m.nodemap SUBSET G.V` by
      fs[dpoTheory.is_match_def, morphismTheory.is_inj_morphism_def,
         morphismTheory.is_morphism_def, morphismTheory.is_premorphism_def,
         morphismTheory.morphism_dom_ran_def] >>
    STRIP_ASSUME_TAC rule_link_structure >>
    `G.s ' (m.edgemap ' (edgeid "e0")) = m.nodemap ' (nodeid "n0")` by
      (irule match_preserves_source_apply >> simp[] >>
       qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
    `G.t ' (m.edgemap ' (edgeid "e0")) = m.nodemap ' (nodeid "n1")` by
      (irule match_preserves_target_apply >> simp[] >>
       qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
    `G.s ' (m.edgemap ' (edgeid "e1")) = m.nodemap ' (nodeid "n1")` by
      (irule match_preserves_source_apply >> simp[] >>
       qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
    `G.t ' (m.edgemap ' (edgeid "e1")) = m.nodemap ' (nodeid "n2")` by
      (irule match_preserves_target_apply >> simp[] >>
       qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
    `rhs'.V = rule_link.inf` by (gvs[] >> EVAL_TAC) >>
    `wf_graph D` by
      (simp[Abbr `D`] >>
       irule hostgraphTheory.wf_partial_hostgraph_IMP_wf_graph >>
       irule dpoTheory.deletion_preserves_wf_graph >> simp[] >> EVAL_TAC) >>
    (* Helper for node membership in G.V *)
    `!n. n IN rule_link.lhs.V ==>
         n IN FDOM m.nodemap /\ m.nodemap ' n IN G.V` by
      (rpt strip_tac >> gvs[] >>
       `m.nodemap ' n IN FRANGE m.nodemap` by
         (simp[FRANGE_DEF] >> metis_tac[]) >>
       fs[SUBSET_DEF]) >>
    `nodeid "n0" IN rule_link.lhs.V` by EVAL_TAC >>
    `nodeid "n1" IN rule_link.lhs.V` by EVAL_TAC >>
    `nodeid "n2" IN rule_link.lhs.V` by EVAL_TAC >>
    (* Helper for DPO source of right-tagged edges *)
    `!eid nid. eid IN rhs'.E /\ rhs'.s ' eid = nid /\ nid IN rule_link.inf ==>
     (dpo lhs' rule_link.inf rhs' m G).s ' (tag_edgeid_right eid) =
     tag_nodeid_left (m.nodemap ' nid)` by
      (rpt strip_tac >>
       PURE_REWRITE_TAC[dpoTheory.dpo_def, dpoTheory.gluing_def, LET_THM] >>
       BETA_TAC >> simp_tac (srw_ss()) [] >>
       qpat_assum `rhs'.s ' eid = nid` (fn th =>
         ONCE_REWRITE_TAC[GSYM th]) >>
       irule dpoTheory.gluing_s_apply_right_tagged_in_interface >>
       simp[] >> gvs[] >> fs[wf_hostgraph_def]) >>
    (* Helper for DPO target of right-tagged edges *)
    `!eid nid. eid IN rhs'.E /\ rhs'.t ' eid = nid /\ nid IN rule_link.inf ==>
     (dpo lhs' rule_link.inf rhs' m G).t ' (tag_edgeid_right eid) =
     tag_nodeid_left (m.nodemap ' nid)` by
      (rpt strip_tac >>
       PURE_REWRITE_TAC[dpoTheory.dpo_def, dpoTheory.gluing_def, LET_THM] >>
       BETA_TAC >> simp_tac (srw_ss()) [] >>
       `FINITE D.E` by
         fs[Abbr `D`, dpoTheory.deletion_def,
            dpoTheory.deletion_remaining_edges_def,
            wf_hostgraph_def, wf_graph_def] >>
       `FINITE rhs'.E` by fs wf_ss >>
       `FINITE (gluing_edges D rhs')` by
         simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
       qpat_assum `rhs'.t ' eid = nid` (fn th =>
         ONCE_REWRITE_TAC[GSYM th]) >>
       irule dpoTheory.gluing_t_apply_right_tagged_in_interface >>
       simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
       gvs[] >> fs[wf_hostgraph_def]) >>
    (* Helper for composed morphism *)
    `!u. u IN G0.V /\ m0.nodemap ' u IN G.V ==>
     (compose_morphism (track lhs' rule_link.inf m G)
       <| nodemap := m0.nodemap;
          edgemap := track_bar.edgemap |>).nodemap ' u =
     tag_nodeid_left (m0.nodemap ' u)` by
      (rpt strip_tac >>
       simp[morphismTheory.compose_morphism_def] >>
       `((track lhs' rule_link.inf m G).nodemap f_o_f m0.nodemap) ' u =
        (track lhs' rule_link.inf m G).nodemap ' (m0.nodemap ' u)` by
         (irule f_o_f_apply >> simp[] >>
          fs[minimally_extends_def, BIJ_DEF, SURJ_DEF]) >>
       gvs[] >> irule trackTheory.track_nodemap_apply >>
       metis_tac[dpoTheory.wf_hostgraph_IMP_finite_remaining_elements,
                 link_no_node_deletion]) >>
    (* Pre-establish membership facts so gvs can fire the helpers *)
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
    (* Sub-case: x = edgeid "e0" — edge from n0 to n1 *)
    >- (qexistsl [`v0`, `w0`] >> gvs[])
    (* Sub-case: x = edgeid "e1" — edge from n1 to n2 *)
    >- (qexistsl [`v1`, `w1`] >> gvs[])
    (* Sub-case: x = edgeid "e2" — shortcut n0 to n2 via transitivity *)
    >- (`m0.nodemap ' w0 = m0.nodemap ' v1` by gvs[] >>
        `w0 = v1` by
          (fs[minimally_extends_def, BIJ_DEF, INJ_DEF] >> metis_tac[]) >>
        `reachable_in G0 v0 w1` by
          (irule reachable_in_trans >> qexists_tac `w0` >> gvs[]) >>
        qexistsl [`v0`, `w1`] >> gvs[])))
QED

(* Wrapper: link_step_reachability stated in terms of edge_path_justified *)
Theorem link_step_edge_path_justified:
  !G0 G m0 track_bar lhs' rhs' m.
    wf_hostgraph G0 /\ wf_hostgraph G /\ FINITE G0.E /\
    minimal_extension G0 track_bar G /\
    tc_loop_invariant G0 G m0 /\
    extends_morphism m0 track_bar /\
    is_match lhs' rule_link.inf m G /\
    lhs'.V = rule_link.lhs.V /\
    lhs'.E = rule_link.lhs.E /\
    lhs'.s = rule_link.lhs.s /\ lhs'.t = rule_link.lhs.t /\
    rhs'.V = rule_link.rhs.V /\
    rhs'.E = rule_link.rhs.E /\
    rhs'.s = rule_link.rhs.s /\ rhs'.t = rule_link.rhs.t /\
    wf_hostgraph lhs' /\ wf_hostgraph rhs' /\
    wf_hostgraph (dpo lhs' rule_link.inf rhs' m G) ==>
    edge_path_justified G0
      <| nodemap :=
          (compose_morphism (track lhs' rule_link.inf m G)
            <| nodemap := track_bar.nodemap;
               edgemap := track_bar.edgemap |>).nodemap;
         edgemap := FUN_FMAP
          (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (track_bar.edgemap ' e))
          G0.E |>
      (dpo lhs' rule_link.inf rhs' m G)
Proof
  rpt strip_tac >>
  SIMP_TAC (srw_ss()) [edge_path_justified_def, generated_edges_def] >>
  MATCH_MP_TAC link_step_reachability >>
  qexists_tac `m0` >> simp[]
QED

(* tag_nodeid_left is injective: equality of tagged values iff equality *)
Theorem tag_nodeid_left_11:
  tag_nodeid_left a = tag_nodeid_left b <=> (a = b)
Proof
  rpt strip_tac >> eq_tac >-
  (mp_tac taggingTheory.INJ_tag_nodeid >> simp[INJ_DEF]) >-
  simp[]
QED

(* Link step preserves parallel_free_extension.
   Key: the NAC ~has_edge(n0,n2) prevents creating parallel edges. *)
Theorem link_step_parallel_free:
  !G0 G track_bar lhs' rhs' m.
    wf_hostgraph G0 /\ wf_hostgraph G /\ FINITE G0.E /\
    minimal_extension G0 track_bar G /\
    is_match lhs' rule_link.inf m G /\
    lhs'.V = rule_link.lhs.V /\
    lhs'.E = rule_link.lhs.E /\
    lhs'.s = rule_link.lhs.s /\ lhs'.t = rule_link.lhs.t /\
    rhs'.V = rule_link.rhs.V /\
    rhs'.E = rule_link.rhs.E /\
    rhs'.s = rule_link.rhs.s /\ rhs'.t = rule_link.rhs.t /\
    wf_hostgraph lhs' /\ wf_hostgraph rhs' /\
    wf_hostgraph (dpo lhs' rule_link.inf rhs' m G) /\
    ~has_edge G (m.nodemap ' (nodeid "n0")) (m.nodemap ' (nodeid "n2")) ==>
    parallel_free_extension
      <| nodemap :=
          (compose_morphism (track lhs' rule_link.inf m G)
            <| nodemap := track_bar.nodemap;
               edgemap := track_bar.edgemap |>).nodemap;
         edgemap := FUN_FMAP
          (\e. if track_bar.edgemap ' e IN deletion_deleted_edges lhs' m
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = track_bar.edgemap ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (track_bar.edgemap ' e))
          G0.E |>
      (dpo lhs' rule_link.inf rhs' m G)
Proof
  rpt strip_tac >>
  simp[parallel_free_extension_def] >>
  (* ---- Extract from minimal_extension ---- *)
  `parallel_free_extension track_bar G` by fs[minimal_extension_def] >>
  `FDOM track_bar.edgemap = G0.E` by fs me_inj_ss >>
  `FRANGE track_bar.edgemap SUBSET G.E` by fs me_inj_ss >>
  `INJ ($' track_bar.edgemap) G0.E G.E` by
    fs[minimal_extension_def, is_inj_morphism_def] >>
  (* ---- Extract from is_match ---- *)
  `FDOM m.edgemap = lhs'.E` by fs match_morphism_ss >>
  `FRANGE m.edgemap SUBSET G.E` by fs match_morphism_ss >>
  `INJ ($' m.edgemap) lhs'.E G.E` by fs match_inj_ss >>
  `INJ ($' m.nodemap) lhs'.V G.V` by fs match_inj_ss >>
  (* ---- Rule structure ---- *)
  `lhs'.E = {edgeid "e1"; edgeid "e0"}` by (gvs[] >> EVAL_TAC) >>
  `rhs'.E = {edgeid "e2"; edgeid "e1"; edgeid "e0"}` by (gvs[] >> EVAL_TAC) >>
  `lhs'.V = {nodeid "n2"; nodeid "n1"; nodeid "n0"}` by (gvs[] >> EVAL_TAC) >>
  STRIP_ASSUME_TAC rule_link_structure >>
  sg `m.edgemap ' (edgeid "e0") <> m.edgemap ' (edgeid "e1")`
  >- (strip_tac >>
      `edgeid "e0" IN lhs'.E /\ edgeid "e1" IN lhs'.E` by (gvs[] >> EVAL_TAC) >>
      `edgeid "e0" = edgeid "e1"` by metis_tac[INJ_DEF] >> fs[])
  >- (
  `deletion_deleted_edges lhs' m =
   {m.edgemap ' (edgeid "e0"); m.edgemap ' (edgeid "e1")}` by
    (simp[dpoTheory.deletion_deleted_edges_def] >> gvs[] >>
     simp[EXTENSION] >> metis_tac[]) >>
  (* ---- DPO structural setup ---- *)
  qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
  qabbrev_tac `G'0 = dpo lhs' rule_link.inf rhs' m G` >>
  `wf_graph D` by
    (simp[Abbr `D`] >>
     irule hostgraphTheory.wf_partial_hostgraph_IMP_wf_graph >>
     irule dpoTheory.deletion_preserves_wf_graph >> simp[] >> EVAL_TAC) >>
  `wf_graph rhs'` by fs[wf_hostgraph_def] >>
  `FINITE D.E` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def] >> fs wf_ss) >>
  `FINITE rhs'.E` by simp[] >>
  `G'0.E = edgeid_coprod D.E rhs'.E` by
    (simp[Abbr `G'0`, Abbr `D`, dpoTheory.dpo_def, dpoTheory.gluing_def,
          dpoTheory.gluing_edges_def, dpoTheory.deletion_def]) >>
  `D.E SUBSET G.E` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def] >>
     simp[SUBSET_DEF] >> metis_tac[]) >>
  `FINITE (gluing_edges D rhs')` by
    simp[dpoTheory.gluing_edges_def, dpoTheory.edgeid_coprod_def] >>
  (* ---- Matched edge source/target in G ---- *)
  `G.s ' (m.edgemap ' (edgeid "e0")) = m.nodemap ' (nodeid "n0")` by
    (irule match_preserves_source_apply >> simp[] >>
     qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
  `G.t ' (m.edgemap ' (edgeid "e0")) = m.nodemap ' (nodeid "n1")` by
    (irule match_preserves_target_apply >> simp[] >>
     qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
  `G.s ' (m.edgemap ' (edgeid "e1")) = m.nodemap ' (nodeid "n1")` by
    (irule match_preserves_source_apply >> simp[] >>
     qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
  `G.t ' (m.edgemap ' (edgeid "e1")) = m.nodemap ' (nodeid "n2")` by
    (irule match_preserves_target_apply >> simp[] >>
     qexistsl [`rule_link.inf`, `lhs'`] >> gvs[] >> EVAL_TAC) >>
  (* ---- Matched edges in G.E, deleted edges not in D.E ---- *)
  `m.edgemap ' (edgeid "e0") IN G.E /\ m.edgemap ' (edgeid "e1") IN G.E` by
    (`edgeid "e0" IN FDOM m.edgemap /\ edgeid "e1" IN FDOM m.edgemap` by
       simp[] >>
     metis_tac[FRANGE_FLOOKUP, FLOOKUP_DEF, SUBSET_DEF]) >>
  `m.edgemap ' (edgeid "e0") NOTIN D.E /\
   m.edgemap ' (edgeid "e1") NOTIN D.E` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def] >> simp[]) >>
  (* ---- D.s/D.t preserves G.s/G.t for surviving edges ---- *)
  `FDOM G.s = G.E /\ FDOM G.t = G.E` by fs wf_ss >>
  `!x. x IN D.E ==> D.s ' x = G.s ' x /\ D.t ' x = G.t ' x` by
    (rpt strip_tac >>
     `D.s = DRESTRICT G.s D.E /\ D.t = DRESTRICT G.t D.E` by
       simp[Abbr `D`, dpoTheory.deletion_def, LET_THM] >>
     gvs[DRESTRICT_DEF] >> metis_tac[SUBSET_DEF]) >>
  (* ---- DPO source/target for left-tagged edges ---- *)
  `!x. x IN D.E ==>
       G'0.s ' (tag_edgeid_left x) = tag_nodeid_left (G.s ' x) /\
       G'0.t ' (tag_edgeid_left x) = tag_nodeid_left (G.t ' x)` by
    (rpt strip_tac
     >- (`D.s ' x = G.s ' x` by (res_tac >> gvs[]) >>
         simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
              dpoTheory.gluing_s_apply_left_tagged])
     >- (`D.t ' x = G.t ' x` by (res_tac >> gvs[]) >>
         simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
              dpoTheory.gluing_t_apply_left_tagged])) >>
  (* ---- Interface membership for rhs edges (enables conditional rewrites) ---- *)
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
     simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def,
          dpoTheory.gluing_s_apply_right_tagged_in_interface,
          dpoTheory.gluing_t_apply_right_tagged_in_interface]) >>
  (* ==== Main proof: contradiction on parallel edges ==== *)
  rpt strip_tac >>
  SPOSE_NOT_THEN strip_assume_tac >>
  (* Now have: e IN G'0.E, e generated, e' IN G'0.E, e' ≠ e,
     G'0.s ' e' = G'0.s ' e, G'0.t ' e' = G'0.t ' e *)
  `e' IN G'0.E` by fs[] >>
  (* Decompose e, e' via edgeid_coprod *)
  `e IN IMAGE tag_edgeid_left D.E \/
   e IN IMAGE tag_edgeid_right rhs'.E` by
    gvs[dpoTheory.edgeid_coprod_def] >>
  `e' IN IMAGE tag_edgeid_left D.E \/
   e' IN IMAGE tag_edgeid_right rhs'.E` by
    gvs[dpoTheory.edgeid_coprod_def] >>
  (* ========== Case analysis on e and e' ========== *)
  fs[IN_IMAGE] >> rpt BasicProvers.VAR_EQ_TAC
  (* This creates 4 cases: (left,left), (left,right), (right,left), (right,right) *)
  (* ---- Case 1: e = tag_edgeid_left x, e' = tag_edgeid_left x' ---- *)
  >- (`x <> x'` by
        (strip_tac >> gvs[] >>
         metis_tac[taggingTheory.INJ_tag_edgeid, INJ_DEF]) >>
      `G.s ' x' = G.s ' x /\ G.t ' x' = G.t ' x` by
        (res_tac >> gvs[tag_nodeid_left_11]) >>
      (* x is generated in G: x NOTIN FRANGE track_bar.edgemap *)
      `x NOTIN FRANGE track_bar.edgemap` by
        (simp[FRANGE_DEF] >> Q.X_GEN_TAC `y` >> rpt strip_tac >>
         first_x_assum (qspec_then `y` mp_tac) >>
         `y IN G0.E` by metis_tac[] >>
         `track_bar.edgemap ' y NOTIN deletion_deleted_edges lhs' m` by
           (strip_tac >> `x IN deletion_deleted_edges lhs' m` by metis_tac[] >>
            gvs[]) >>
         simp[]) >>
      (* x, x' in G.E, same source/target, different => contradicts parallel_free *)
      `x IN G.E /\ x' IN G.E` by metis_tac[SUBSET_DEF] >>
      fs[parallel_free_extension_def] >> metis_tac[])
  (* ---- Case 2: e = tag_edgeid_left x, e' = tag_edgeid_right x' ---- *)
  >- (`x IN G.E` by metis_tac[SUBSET_DEF] >>
      (* x is generated in G *)
      `x NOTIN FRANGE track_bar.edgemap` by
        (simp[FRANGE_DEF] >> Q.X_GEN_TAC `y` >> rpt strip_tac >>
         first_x_assum (qspec_then `y` mp_tac) >>
         `y IN G0.E` by metis_tac[] >>
         `track_bar.edgemap ' y NOTIN deletion_deleted_edges lhs' m` by
           (strip_tac >> `x IN deletion_deleted_edges lhs' m` by metis_tac[] >>
            gvs[]) >>
         simp[]) >>
      (* Source/target of x and x' match *)
      `G'0.s ' (tag_edgeid_left x) = tag_nodeid_left (G.s ' x) /\
       G'0.t ' (tag_edgeid_left x) = tag_nodeid_left (G.t ' x)` by
        (res_tac >> gvs[]) >>
      `G'0.s ' (tag_edgeid_right x') =
         tag_nodeid_left (m.nodemap ' (rhs'.s ' x')) /\
       G'0.t ' (tag_edgeid_right x') =
         tag_nodeid_left (m.nodemap ' (rhs'.t ' x'))` by (res_tac >> gvs[]) >>
      `G.s ' x = m.nodemap ' (rhs'.s ' x') /\
       G.t ' x = m.nodemap ' (rhs'.t ' x')` by
        gvs[tag_nodeid_left_11] >>
      (* x' IN {e0, e1, e2} — case split *)
      `x' = edgeid "e0" \/ x' = edgeid "e1" \/ x' = edgeid "e2"` by
        (qpat_x_assum `rhs'.E = _` SUBST_ALL_TAC >> fs[IN_INSERT]) >>
      gvs[]
      (* x' = e0: m.edgemap ' e0 is parallel to x in G *)
      >- (fs[parallel_free_extension_def] >> metis_tac[])
      (* x' = e1: m.edgemap ' e1 is parallel to x in G *)
      >- (fs[parallel_free_extension_def] >> metis_tac[])
      (* x' = e2: has_edge G n0 n2, contradiction *)
      >- (fs[pathTheory.has_edge_def] >> metis_tac[]))
  (* ---- Case 3: e = tag_edgeid_right x, e' = tag_edgeid_left x' ---- *)
  >- (`x' IN G.E` by metis_tac[SUBSET_DEF] >>
      (* Source/target match *)
      `G'0.s ' (tag_edgeid_right x) =
         tag_nodeid_left (m.nodemap ' (rhs'.s ' x)) /\
       G'0.t ' (tag_edgeid_right x) =
         tag_nodeid_left (m.nodemap ' (rhs'.t ' x))` by (res_tac >> gvs[]) >>
      `G'0.s ' (tag_edgeid_left x') = tag_nodeid_left (G.s ' x') /\
       G'0.t ' (tag_edgeid_left x') = tag_nodeid_left (G.t ' x')` by
        (res_tac >> gvs[]) >>
      `G.s ' x' = m.nodemap ' (rhs'.s ' x) /\
       G.t ' x' = m.nodemap ' (rhs'.t ' x)` by
        gvs[tag_nodeid_left_11] >>
      (* x IN {e0, e1, e2} — case split *)
      `x = edgeid "e0" \/ x = edgeid "e1" \/ x = edgeid "e2"` by
        (qpat_x_assum `rhs'.E = _` SUBST_ALL_TAC >> fs[IN_INSERT]) >>
      gvs[]
      (* x = e0: show m.edgemap ' e0 NOTIN FRANGE track_bar.edgemap *)
      >- (`m.edgemap ' (edgeid "e0") NOTIN FRANGE track_bar.edgemap` by
            (simp[FRANGE_DEF] >> Q.X_GEN_TAC `y` >> rpt strip_tac >>
             first_x_assum (qspec_then `y` mp_tac) >>
             `y IN G0.E` by metis_tac[] >>
             `track_bar.edgemap ' y IN deletion_deleted_edges lhs' m` by
               metis_tac[] >>
             simp[]) >>
          fs[parallel_free_extension_def] >> metis_tac[])
      (* x = e1: similar *)
      >- (`m.edgemap ' (edgeid "e1") NOTIN FRANGE track_bar.edgemap` by
            (simp[FRANGE_DEF] >> Q.X_GEN_TAC `y` >> rpt strip_tac >>
             first_x_assum (qspec_then `y` mp_tac) >>
             `y IN G0.E` by metis_tac[] >>
             `track_bar.edgemap ' y IN deletion_deleted_edges lhs' m` by
               metis_tac[] >>
             simp[]) >>
          fs[parallel_free_extension_def] >> metis_tac[])
      (* x = e2: has_edge G n0 n2, contradiction *)
      >- (fs[pathTheory.has_edge_def] >> metis_tac[]))
  (* ---- Case 4: e = tag_edgeid_right x, e' = tag_edgeid_right x' ---- *)
  >- (`x <> x'` by
        (strip_tac >> gvs[] >>
         metis_tac[taggingTheory.INJ_tag_edgeid, INJ_DEF]) >>
      `G'0.s ' (tag_edgeid_right x) =
         tag_nodeid_left (m.nodemap ' (rhs'.s ' x)) /\
       G'0.t ' (tag_edgeid_right x) =
         tag_nodeid_left (m.nodemap ' (rhs'.t ' x))` by (res_tac >> gvs[]) >>
      `G'0.s ' (tag_edgeid_right x') =
         tag_nodeid_left (m.nodemap ' (rhs'.s ' x')) /\
       G'0.t ' (tag_edgeid_right x') =
         tag_nodeid_left (m.nodemap ' (rhs'.t ' x'))` by (res_tac >> gvs[]) >>
      `m.nodemap ' (rhs'.s ' x) = m.nodemap ' (rhs'.s ' x') /\
       m.nodemap ' (rhs'.t ' x) = m.nodemap ' (rhs'.t ' x')` by
        gvs[tag_nodeid_left_11] >>
      (* x, x' IN {e0, e1, e2}, x ≠ x', same endpoints => contradiction *)
      `x = edgeid "e0" \/ x = edgeid "e1" \/ x = edgeid "e2"` by
        (qpat_x_assum `rhs'.E = _` SUBST_ALL_TAC >> fs[IN_INSERT]) >>
      `x' = edgeid "e0" \/ x' = edgeid "e1" \/ x' = edgeid "e2"` by
        (qpat_x_assum `rhs'.E = _` SUBST_ALL_TAC >> fs[IN_INSERT]) >>
      gvs[] >>
      (* All 6 distinct pairs: rhs'.s/t differ, so m.nodemap images differ by INJ.
         metis_tac[INJ_DEF] diverges with many universals; use targeted SPECL. *)
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
  )
QED

(* Helper: instantiate_rule success implies NAC: no edge n0→n2 *)
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

(* -------------------------------------------------------------------------- *)
(* Inductive step: link preserves total edge embedding                        *)
(* -------------------------------------------------------------------------- *)

Theorem link_preserves_total:
  !G0 G m0 track_bar G' m'.
    wf_hostgraph G0 /\
    tc_loop_invariant G0 G m0 /\
    tc_loop_invariant_total G0 G track_bar /\
    extends_morphism m0 track_bar /\
    step program (running (term_rscall {ruleid "link"}), [(G, id_track G)])
                 (final, [(G', m')]) ==>
    ?track_bar'. tc_loop_invariant_total G0 G' track_bar' /\
                 extends_morphism (compose_morphism m' m0) track_bar'
Proof
  rpt strip_tac >> fs[tc_loop_invariant_total_def] >>
  (* Extract facts from minimal_extension for later use.
     FDOM equalities are safe: gvs[] does NOT substitute them. *)
  `FDOM track_bar.nodemap = G0.V` by fs me_inj_ss >>
  `FDOM track_bar.edgemap = G0.E` by fs me_inj_ss >>
  `BIJ ($' track_bar.nodemap) G0.V G.V` by fs[minimal_extension_def] >>
  `INJ ($' track_bar.edgemap) G0.E G.E` by
    fs[minimal_extension_def, is_inj_morphism_def] >>
  `FRANGE track_bar.nodemap SUBSET G.V` by fs me_inj_ss >>
  `FRANGE track_bar.edgemap SUBSET G.E` by fs me_inj_ss >>
  `preserve_edgelabels G0 track_bar G` by fs me_inj_ss >>
  `preserve_nodelabels G0 track_bar G` by fs me_inj_ss >>
  `FINITE G0.E` by fs wf_ss >>
  `FINITE G0.V` by fs wf_ss >>
  (* Get wf/unmarked/unrooted from link_preserves_invariant *)
  `tc_loop_invariant G0 G' (compose_morphism m' m0)` by
    (irule link_preserves_invariant >> metis_tac[]) >>
  `wf_hostgraph G'` by fs[tc_loop_invariant_def] >>
  `unmarked_hostgraph G'` by fs[tc_loop_invariant_def] >>
  `unrooted_hostgraph G'` by fs[tc_loop_invariant_def] >>
  (* Now destructure the step for minimal_extension proof *)
  qpat_x_assum `step _ _ _` mp_tac >>
  simp[Once semTheory.step_cases] >> strip_tac >>
  gvs[push_stack_def, pop_stack_def, id_track_def] >>
  `r = rule_link` by
    gvs[program_def, FUPDATE_LIST_THM, FLOOKUP_UPDATE] >>
  gvs[semTheory.apply_ruleinstance_def, semTheory.instantiate_rule_def] >>
  (* Establish structural facts *)
  `lhs'.V = rule_link.lhs.V` by
    metis_tac[semTheory.instantiate_rulegraph_preserves_V] >>
  `rhs'.V = rule_link.rhs.V` by
    metis_tac[semTheory.instantiate_rulegraph_preserves_V] >>
  `lhs'.E = rule_link.lhs.E /\ lhs'.s = rule_link.lhs.s /\ lhs'.t = rule_link.lhs.t`
    by metis_tac[semTheory.instantiate_rulegraph_preserves_structure] >>
  `rhs'.E = rule_link.rhs.E /\ rhs'.s = rule_link.rhs.s /\ rhs'.t = rule_link.rhs.t`
    by metis_tac[semTheory.instantiate_rulegraph_preserves_structure] >>
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
  (* Derive label facts before abbreviations *)
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
  (* Abbreviations *)
  qabbrev_tac `D = deletion lhs' rule_link.inf m G` >>
  qabbrev_tac `G'0 = dpo lhs' rule_link.inf rhs' m G` >>
  `FINITE G0.E` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  `FINITE G0.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  (* Witness the updated track_bar *)
  qabbrev_tac `m_E = track_bar.edgemap` >>
  qexists_tac `<| nodemap :=
    (compose_morphism (track lhs' rule_link.inf m G)
      <| nodemap := track_bar.nodemap;
         edgemap := track_bar.edgemap |>).nodemap;
    edgemap := FUN_FMAP
      (\e. if m_E ' e IN deletion_deleted_edges lhs' m
           then tag_edgeid_right
                  (if m.edgemap ' (edgeid "e0") = m_E ' e
                   then edgeid "e0" else edgeid "e1")
           else tag_edgeid_left (m_E ' e))
      (FDOM m_E) |>` >>
  (* Hoisted shared facts *)
  `wf_hostgraph G'0` by
    (simp[Abbr `G'0`] >> irule dpoTheory.wf_dpo >> simp[] >> EVAL_TAC) >>
  `wf_graph D` by
    (simp[Abbr `D`] >>
     irule hostgraphTheory.wf_partial_hostgraph_IMP_wf_graph >>
     irule dpoTheory.deletion_preserves_wf_graph >> simp[] >> EVAL_TAC) >>
  (* Establish premorphism facts from is_match *)
  `FDOM m.edgemap = lhs'.E` by
    fs match_morphism_ss >>
  `FRANGE m.edgemap SUBSET G.E` by
    fs match_morphism_ss >>
  `FDOM m.nodemap = lhs'.V` by
    fs match_morphism_ss >>
  `m.nodemap f_o_f lhs'.s = G.s f_o_f m.edgemap` by
    fs match_source_ss >>
  `m.nodemap f_o_f lhs'.t = G.t f_o_f m.edgemap` by
    fs match_target_ss >>
  `INJ ($' m.edgemap) lhs'.E G.E` by
    fs match_inj_ss >>
  (* Key structural facts about rule_link *)
  `lhs'.E = {edgeid "e1"; edgeid "e0"}` by (gvs[] >> EVAL_TAC) >>
  `rhs'.E = {edgeid "e2"; edgeid "e1"; edgeid "e0"}` by (gvs[] >> EVAL_TAC) >>
  `m.edgemap ' (edgeid "e0") <> m.edgemap ' (edgeid "e1")` by
    (strip_tac >>
     `edgeid "e0" IN lhs'.E /\ edgeid "e1" IN lhs'.E` by (gvs[] >> EVAL_TAC) >>
     `edgeid "e0" = edgeid "e1"` by metis_tac[INJ_DEF] >> fs[]) >>
  `deletion_deleted_edges lhs' m =
   {m.edgemap ' (edgeid "e0"); m.edgemap ' (edgeid "e1")}` by
    (simp[dpoTheory.deletion_deleted_edges_def] >> gvs[] >>
     simp[EXTENSION] >> metis_tac[]) >>
  `FINITE D.E` by
    (simp[Abbr `D`, dpoTheory.deletion_def,
          dpoTheory.deletion_remaining_edges_def] >>
     fs wf_ss) >>
  `FINITE rhs'.E` by simp[] >>
  `G'0.E = edgeid_coprod D.E rhs'.E` by
    (simp[Abbr `G'0`, Abbr `D`, dpoTheory.dpo_def, dpoTheory.gluing_def,
          dpoTheory.gluing_edges_def, dpoTheory.deletion_def]) >>
  (* Helper: membership in G'0.E via edgeid_coprod *)
  STRIP_ASSUME_TAC rule_link_structure >>
  (* DPO source facts for right-tagged edges *)
  sg `G'0.s ' (tag_edgeid_right (edgeid "e0")) =
      tag_nodeid_left (m.nodemap ' (rhs'.s ' (edgeid "e0")))`
  >- (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
      qpat_x_assum `rule_link.rhs.s ' (edgeid "e0") = nodeid "n0"`
        (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
      qpat_x_assum `rhs'.s = rule_link.rhs.s`
        (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
      irule dpoTheory.gluing_s_apply_right_tagged_in_interface >>
      simp[] >> fs[wf_hostgraph_def] >>
      EVAL_TAC)
  >- (
  sg `G'0.s ' (tag_edgeid_right (edgeid "e1")) =
      tag_nodeid_left (m.nodemap ' (rhs'.s ' (edgeid "e1")))`
  >- (simp[Abbr `G'0`, dpoTheory.dpo_def, dpoTheory.gluing_def] >>
      qpat_x_assum `rule_link.rhs.s ' (edgeid "e1") = nodeid "n1"`
        (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
      qpat_x_assum `rhs'.s = rule_link.rhs.s`
        (fn th => PURE_ONCE_REWRITE_TAC[GSYM th] >> ASSUME_TAC th) >>
      irule dpoTheory.gluing_s_apply_right_tagged_in_interface >>
      simp[] >> fs[wf_hostgraph_def] >>
      EVAL_TAC)
  >- (
  (* Compose/track chain helper *)
  `FINITE G.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  sg `!v. v IN G0.V ==>
          (compose_morphism (track lhs' rule_link.inf m G)
            <| nodemap := track_bar.nodemap; edgemap := track_bar.edgemap |>).nodemap ' v =
          tag_nodeid_left (track_bar.nodemap ' v)`
  >- (rpt strip_tac >>
      simp[morphismTheory.compose_morphism_def] >>
      `v IN FDOM ((track lhs' rule_link.inf m G).nodemap f_o_f track_bar.nodemap)` by
        (simp[f_o_f_DEF] >> simp[] >>
         `track_bar.nodemap ' v IN G.V` by
           metis_tac[BIJ_DEF, INJ_DEF] >>
         `FDOM (track lhs' rule_link.inf m G).nodemap = G.V` by
           (irule link_track_nodemap_FDOM >>
            metis_tac[wf_hostgraph_IMP_finite_sets]) >>
         simp[]) >>
      drule (cj 2 f_o_f_DEF) >> simp[] >> DISCH_TAC >> simp[] >>
      `rule_link.inf = rule_link.lhs.V` by EVAL_TAC >>
      `deletion_remaining_nodes lhs' m rule_link.inf G = G.V` by
        (simp[dpoTheory.deletion_remaining_nodes_def,
              dpoTheory.deletion_deleted_nodes_def] >>
         gvs[] >> simp[DIFF_EQ_EMPTY, SUBSET_REFL]) >>
      irule trackTheory.track_nodemap_apply >> simp[] >>
      metis_tac[BIJ_DEF, INJ_DEF])
  >- (
  `G'0.V = IMAGE tag_nodeid_left G.V` by
    (simp[Abbr `G'0`] >> irule link_dpo_V >> simp[]) >>
  (* ===== Split: minimal_extension vs extends_morphism ===== *)
  conj_tac
  >- (
  PURE_ONCE_REWRITE_TAC[minimal_extension_def] >>
  (* Prove is_inj_morphism, BIJ, and reachability                *)
  (* Strategy: prove old-style facts, then assemble into          *)
  (* is_inj_morphism via is_morphism / is_premorphism hierarchy   *)
  (* ============ O1: FDOM nodemap = G0.V ============ *)
  `FDOM (compose_morphism (track lhs' rule_link.inf m G)
      <| nodemap := track_bar.nodemap; edgemap := track_bar.edgemap |>).nodemap = G0.V` by
    (simp[morphismTheory.compose_morphism_def, f_o_f_DEF, EXTENSION] >>
     rw[] >> EQ_TAC >> rw[] >>
     simp[] >>
     `track_bar.nodemap ' x IN G.V` by
       metis_tac[BIJ_DEF, INJ_DEF] >>
     `FDOM (track lhs' rule_link.inf m G).nodemap = G.V` by
       (irule link_track_nodemap_FDOM >>
        metis_tac[wf_hostgraph_IMP_finite_sets]) >>
     simp[]) >>
  (* ============ O3: BIJ nodemap ============ *)
  `BIJ ($' (compose_morphism (track lhs' rule_link.inf m G)
      <| nodemap := track_bar.nodemap; edgemap := track_bar.edgemap |>).nodemap) G0.V G'0.V` by
    (rw[BIJ_DEF, INJ_DEF, SURJ_DEF] >> rpt conj_tac
     (* Range *)
     >- (qexists_tac `track_bar.nodemap ' x` >> simp[] >>
         metis_tac[BIJ_DEF, INJ_DEF])
     (* Injectivity *)
     >- (`INJ tag_nodeid_left UNIV UNIV` by simp[taggingTheory.INJ_tag_nodeid] >>
         `track_bar.nodemap ' x = track_bar.nodemap ' y` by
           (qpat_x_assum `INJ tag_nodeid_left _ _` mp_tac >> rw[INJ_DEF]) >>
         qpat_x_assum `BIJ _ G0.V G.V`
           (fn th => STRIP_ASSUME_TAC (REWRITE_RULE[BIJ_DEF] th)) >>
         qpat_x_assum `INJ _ G0.V G.V` mp_tac >> rw[INJ_DEF])
     (* Range again *)
     >- (qexists_tac `track_bar.nodemap ' x` >> simp[] >>
         metis_tac[BIJ_DEF, INJ_DEF])
     (* Surjectivity *)
     >- (`?u. u IN G0.V /\ track_bar.nodemap ' u = x'` by
           (qpat_x_assum `BIJ _ G0.V G.V` mp_tac >>
            rw[BIJ_DEF, SURJ_DEF] >> metis_tac[]) >>
         qexists_tac `u` >> conj_tac >- gvs[] >>
         res_tac >> gvs[])) >>
  (* ============ O4: INJ edgemap ============ *)
  `INJ ($' (FUN_FMAP
      (\e. if m_E ' e IN deletion_deleted_edges lhs' m
           then tag_edgeid_right
                  (if m.edgemap ' (edgeid "e0") = m_E ' e
                   then edgeid "e0" else edgeid "e1")
           else tag_edgeid_left (m_E ' e))
      (FDOM m_E))) G0.E G'0.E` by
    (qunabbrev_tac `m_E` >> qunabbrev_tac `G'0` >>
     qpat_assum `FDOM track_bar.edgemap = G0.E` (fn th => REWRITE_TAC[th]) >>
     irule link_step_edgemap_INJ >> simp[] >> EVAL_TAC) >>
  (* ============ O5: Source/target preservation (pointwise) ============ *)
  `!e. e IN G0.E ==>
        FUN_FMAP
          (\e. if m_E ' e IN deletion_deleted_edges lhs' m
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = m_E ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (m_E ' e)) G0.E ' e IN FDOM G'0.s /\
        FUN_FMAP
          (\e. if m_E ' e IN deletion_deleted_edges lhs' m
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = m_E ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (m_E ' e)) G0.E ' e IN FDOM G'0.t /\
        G'0.s ' (FUN_FMAP
          (\e. if m_E ' e IN deletion_deleted_edges lhs' m
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = m_E ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (m_E ' e)) G0.E ' e) =
        (compose_morphism (track lhs' rule_link.inf m G)
          <| nodemap := track_bar.nodemap; edgemap := track_bar.edgemap |>).nodemap ' (G0.s ' e) /\
        G'0.t ' (FUN_FMAP
          (\e. if m_E ' e IN deletion_deleted_edges lhs' m
               then tag_edgeid_right
                      (if m.edgemap ' (edgeid "e0") = m_E ' e
                       then edgeid "e0" else edgeid "e1")
               else tag_edgeid_left (m_E ' e)) G0.E ' e) =
        (compose_morphism (track lhs' rule_link.inf m G)
          <| nodemap := track_bar.nodemap; edgemap := track_bar.edgemap |>).nodemap ' (G0.t ' e)` by
    (qunabbrev_tac `m_E` >> qunabbrev_tac `G'0` >>
     MATCH_MP_TAC link_step_source_target_pointwise >> simp[] >> EVAL_TAC) >>
  (* ============ O5b: Rootedness preservation (pointwise) ============ *)
  sg `!v. v IN FDOM G0.p ==>
        (compose_morphism (track lhs' rule_link.inf m G)
          <| nodemap := track_bar.nodemap; edgemap := track_bar.edgemap |>).nodemap ' v IN FDOM G'0.p /\
        (G'0.p ' ((compose_morphism (track lhs' rule_link.inf m G)
          <| nodemap := track_bar.nodemap; edgemap := track_bar.edgemap |>).nodemap ' v) <=>
         G0.p ' v)`
  >- (rpt strip_tac
      >- (* track_bar'.nodemap ' v IN FDOM G'0.p *)
         (`v IN G0.V` by (fs wf_ss >> metis_tac[SUBSET_DEF]) >>
          res_tac >> gvs[] >>
          `track_bar.nodemap ' v IN G.V` by metis_tac[BIJ_DEF, INJ_DEF] >>
          `FDOM G'0.p = G'0.V` by metis_tac[unrooted_hostgraph_def] >>
          gvs[IN_IMAGE] >> metis_tac[])
      >- (* G'0.p ' (track_bar'.nodemap ' v) <=> G0.p ' v *)
         (`v IN G0.V` by (fs wf_ss >> metis_tac[SUBSET_DEF]) >>
          res_tac >> gvs[] >>
          `track_bar.nodemap ' v IN G.V` by metis_tac[BIJ_DEF, INJ_DEF] >>
          `tag_nodeid_left (track_bar.nodemap ' v) IN G'0.V` by
            (simp[IN_IMAGE] >> metis_tac[]) >>
          `~G'0.p ' (tag_nodeid_left (track_bar.nodemap ' v))` by
            metis_tac[unrooted_hostgraph_def] >>
          `~G.p ' (track_bar.nodemap ' v)` by
            metis_tac[unrooted_hostgraph_def] >>
          `G.p ' (track_bar.nodemap ' v) <=> G0.p ' v` by
            (drule_all minimal_extension_pointwise >> strip_tac >>
             first_x_assum (mp_tac o Q.SPEC `v`) >> simp[]) >>
          gvs[]))
  >- (
  (* ============ O8+O9: Use factored label-preservation lemmas ============ *)
  `preserve_edgelabels G0
    <| nodemap :=
      (compose_morphism (track lhs' rule_link.inf m G)
        <| nodemap := track_bar.nodemap;
           edgemap := track_bar.edgemap |>).nodemap;
      edgemap := FUN_FMAP
        (\e. if m_E ' e IN deletion_deleted_edges lhs' m
             then tag_edgeid_right
                    (if m.edgemap ' (edgeid "e0") = m_E ' e
                     then edgeid "e0" else edgeid "e1")
             else tag_edgeid_left (m_E ' e))
        (FDOM m_E) |> G'0` by
    (qunabbrev_tac `m_E` >> qunabbrev_tac `G'0` >>
     qpat_assum `FDOM track_bar.edgemap = G0.E` (fn th => REWRITE_TAC[th]) >>
     irule link_step_preserves_edgelabels >> simp[] >> EVAL_TAC) >>
  `preserve_nodelabels G0
    <| nodemap :=
      (compose_morphism (track lhs' rule_link.inf m G)
        <| nodemap := track_bar.nodemap;
           edgemap := track_bar.edgemap |>).nodemap;
      edgemap := FUN_FMAP
        (\e. if m_E ' e IN deletion_deleted_edges lhs' m
             then tag_edgeid_right
                    (if m.edgemap ' (edgeid "e0") = m_E ' e
                     then edgeid "e0" else edgeid "e1")
             else tag_edgeid_left (m_E ' e))
        (FDOM m_E) |> G'0` by
    (qunabbrev_tac `m_E` >> qunabbrev_tac `G'0` >>
     qpat_assum `FDOM track_bar.edgemap = G0.E` (fn th => REWRITE_TAC[th]) >>
     irule link_step_preserves_nodelabels >> simp[] >> EVAL_TAC) >>
  (* ============ Assembly: is_inj_morphism + BIJ + reachability ============ *)
  `!e. e IN G0.E ==> m_E ' e IN FDOM G.s /\ m_E ' e IN FDOM G.t /\
   G.s ' (m_E ' e) = track_bar.nodemap ' (G0.s ' e) /\
   G.t ' (m_E ' e) = track_bar.nodemap ' (G0.t ' e)` by
    (rpt strip_tac >> drule_all minimal_extension_pointwise >> strip_tac >>
     first_x_assum (mp_tac o Q.SPEC `e`) >> simp[Abbr `m_E`]) >>
  (* ============ Compositional is_inj_morphism proof ============ *)
  (* Layer 1: morphism_dom_ran *)
  `morphism_dom_ran G0
    <| nodemap :=
      (compose_morphism (track lhs' rule_link.inf m G)
        <| nodemap := track_bar.nodemap;
           edgemap := track_bar.edgemap |>).nodemap;
      edgemap := FUN_FMAP
        (\e. if m_E ' e IN deletion_deleted_edges lhs' m
             then tag_edgeid_right
                    (if m.edgemap ' (edgeid "e0") = m_E ' e
                     then edgeid "e0" else edgeid "e1")
             else tag_edgeid_left (m_E ' e))
        (FDOM m_E) |> G'0` by
    (qunabbrev_tac `m_E` >> qunabbrev_tac `G'0` >>
     qpat_assum `FDOM track_bar.edgemap = G0.E` (fn th => REWRITE_TAC[th]) >>
     irule link_step_morphism_dom_ran >> simp[] >> EVAL_TAC) >>
  (* Layer 2: preserve_source *)
  `preserve_source G0
    <| nodemap :=
      (compose_morphism (track lhs' rule_link.inf m G)
        <| nodemap := track_bar.nodemap;
           edgemap := track_bar.edgemap |>).nodemap;
      edgemap := FUN_FMAP
        (\e. if m_E ' e IN deletion_deleted_edges lhs' m
             then tag_edgeid_right
                    (if m.edgemap ' (edgeid "e0") = m_E ' e
                     then edgeid "e0" else edgeid "e1")
             else tag_edgeid_left (m_E ' e))
        (FDOM m_E) |> G'0` by
    (qunabbrev_tac `m_E` >> qunabbrev_tac `G'0` >>
     qpat_assum `FDOM track_bar.edgemap = G0.E` (fn th => REWRITE_TAC[th]) >>
     irule link_step_preserve_source >> simp[] >> EVAL_TAC) >>
  (* Layer 3: preserve_target *)
  `preserve_target G0
    <| nodemap :=
      (compose_morphism (track lhs' rule_link.inf m G)
        <| nodemap := track_bar.nodemap;
           edgemap := track_bar.edgemap |>).nodemap;
      edgemap := FUN_FMAP
        (\e. if m_E ' e IN deletion_deleted_edges lhs' m
             then tag_edgeid_right
                    (if m.edgemap ' (edgeid "e0") = m_E ' e
                     then edgeid "e0" else edgeid "e1")
             else tag_edgeid_left (m_E ' e))
        (FDOM m_E) |> G'0` by
    (qunabbrev_tac `m_E` >> qunabbrev_tac `G'0` >>
     qpat_assum `FDOM track_bar.edgemap = G0.E` (fn th => REWRITE_TAC[th]) >>
     irule link_step_preserve_target >> simp[] >> EVAL_TAC) >>
  (* Layer 4: preserve_defined_rootedness *)
  `preserve_defined_rootedness G0
    <| nodemap :=
      (compose_morphism (track lhs' rule_link.inf m G)
        <| nodemap := track_bar.nodemap;
           edgemap := track_bar.edgemap |>).nodemap;
      edgemap := FUN_FMAP
        (\e. if m_E ' e IN deletion_deleted_edges lhs' m
             then tag_edgeid_right
                    (if m.edgemap ' (edgeid "e0") = m_E ' e
                     then edgeid "e0" else edgeid "e1")
             else tag_edgeid_left (m_E ' e))
        (FDOM m_E) |> G'0` by
    (qunabbrev_tac `m_E` >> qunabbrev_tac `G'0` >>
     qpat_assum `FDOM track_bar.edgemap = G0.E` (fn th => REWRITE_TAC[th]) >>
     irule link_step_preserve_rootedness >> simp[] >> EVAL_TAC) >>
  (* Compose layers *)
  `is_premorphism G0
    <| nodemap :=
      (compose_morphism (track lhs' rule_link.inf m G)
        <| nodemap := track_bar.nodemap;
           edgemap := track_bar.edgemap |>).nodemap;
      edgemap := FUN_FMAP
        (\e. if m_E ' e IN deletion_deleted_edges lhs' m
             then tag_edgeid_right
                    (if m.edgemap ' (edgeid "e0") = m_E ' e
                     then edgeid "e0" else edgeid "e1")
             else tag_edgeid_left (m_E ' e))
        (FDOM m_E) |> G'0` by
    simp[is_premorphism_def] >>
  `is_morphism G0
    <| nodemap :=
      (compose_morphism (track lhs' rule_link.inf m G)
        <| nodemap := track_bar.nodemap;
           edgemap := track_bar.edgemap |>).nodemap;
      edgemap := FUN_FMAP
        (\e. if m_E ' e IN deletion_deleted_edges lhs' m
             then tag_edgeid_right
                    (if m.edgemap ' (edgeid "e0") = m_E ' e
                     then edgeid "e0" else edgeid "e1")
             else tag_edgeid_left (m_E ' e))
        (FDOM m_E) |> G'0` by
    simp[is_morphism_def] >>
  (* BIJ of composed nodemap: composition of two bijections *)
  `G'0.V = IMAGE tag_nodeid_left G.V`
     by (simp[Abbr `G'0`] >> irule link_dpo_V >> simp[]) >>
  `BIJ ($' (track lhs' rule_link.inf m G).nodemap) G.V
       (IMAGE tag_nodeid_left G.V)` by (irule link_track_nodemap_BIJ >> simp[]) >>
  `FDOM (track lhs' rule_link.inf m G).nodemap = G.V`
     by (irule link_track_nodemap_FDOM >> simp[]) >>
  `BIJ ($'
    (compose_morphism (track lhs' rule_link.inf m G)
      <| nodemap := track_bar.nodemap;
         edgemap := track_bar.edgemap |>).nodemap) G0.V G'0.V` by
    (qunabbrev_tac `G'0` >>
     irule link_step_nodemap_BIJ >> simp[]) >>
  rpt conj_tac
  (* is_inj_morphism — from is_morphism + INJ *)
  >- (ONCE_REWRITE_TAC[is_inj_morphism_def] >>
      simp_tac (srw_ss()) [] >>
      metis_tac[BIJ_DEF])
  (* BIJ — now in assumptions *)
  >- (simp[] >> metis_tac[])
  (* edge_path_justified *)
  >- (qunabbrev_tac `m_E` >> qunabbrev_tac `G'0` >>
      qpat_assum `FDOM track_bar.edgemap = G0.E` (fn th => REWRITE_TAC[th]) >>
      MATCH_MP_TAC link_step_edge_path_justified >>
      qexists_tac `m0` >> gvs[])
  (* parallel_free_extension *)
  >- (
    `~has_edge G (m.nodemap ' (nodeid "n0")) (m.nodemap ' (nodeid "n2"))` by
      metis_tac[link_rule_NAC_no_edge] >>
    qunabbrev_tac `m_E` >> qunabbrev_tac `G'0` >>
    qpat_assum `FDOM track_bar.edgemap = G0.E` (fn th => REWRITE_TAC[th]) >>
    MATCH_MP_TAC link_step_parallel_free >>
    gvs[])
  ))
  >>
  (* ============ extends_morphism (compose m' m0) track_bar' ============ *)
  simp[extends_morphism_def] >>
  conj_tac
  >- (
    (* Nodemap: f_o_f with FUN_FMAP I is identity *)
    simp[morphismTheory.compose_morphism_def] >>
    `track_bar.nodemap = m0.nodemap` by fs[extends_morphism_def] >>
    gvs[] >>
    `FDOM (track lhs' rule_link.inf m G).nodemap = G.V` by (
      irule link_track_nodemap_FDOM >> fs[wf_hostgraph_IMP_finite_sets]) >>
    `FINITE G.V` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
    `(track lhs' rule_link.inf m G).nodemap f_o_f FUN_FMAP I G.V =
     (track lhs' rule_link.inf m G).nodemap` suffices_by simp[] >>
    simp[finite_mapTheory.fmap_EXT, finite_mapTheory.f_o_f_DEF,
         finite_mapTheory.FUN_FMAP_DEF, pred_setTheory.EXTENSION] >>
    rw[finite_mapTheory.FUN_FMAP_DEF] >>
    rpt strip_tac >> eq_tac >> rpt strip_tac >>
    gvs[finite_mapTheory.FUN_FMAP_DEF])
  >- (
    (* Edgemap: for surviving edges, values agree *)
    simp[morphismTheory.compose_morphism_def] >>
    `FINITE G.E` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
    rpt strip_tac >>
    fs[finite_mapTheory.f_o_f_DEF] >>
    pop_assum mp_tac >> simp[finite_mapTheory.f_o_f_DEF] >>
    strip_tac >>
    `m0.edgemap ' e IN G.E` by (
      qpat_x_assum `_ IN FDOM (FUN_FMAP I G.E)` mp_tac >>
      simp[finite_mapTheory.FUN_FMAP_DEF]) >>
    `FUN_FMAP I G.E ' (m0.edgemap ' e) = m0.edgemap ' e` by
      simp[finite_mapTheory.FUN_FMAP_DEF] >>
    gvs[] >>
    `FINITE (deletion_remaining_edges lhs' m G)` by
      metis_tac[dpoTheory.wf_hostgraph_IMP_finite_remaining_elements] >>
    fs[finite_mapTheory.FUN_FMAP_DEF, FDOM_track_edgemap] >>
    simp[finite_mapTheory.f_o_f_DEF] >>
    `FDOM (track lhs' rule_link.inf m G).edgemap =
     deletion_remaining_edges lhs' m G` by fs[FDOM_track_edgemap] >>
    `m0.edgemap ' e = m_E ' e` by (
      qpat_x_assum `extends_morphism _ _` mp_tac >>
      simp[extends_morphism_def] >> strip_tac >>
      `e IN FDOM m0.edgemap` by fs[] >> fs[Abbr `m_E`]) >>
    gvs[] >>
    sg `(((track lhs' rule_link.inf m G).edgemap f_o_f FUN_FMAP I G.E)
         f_o_f m0.edgemap) ' e = tag_edgeid_left (m_E ' e)`
    >- (
      sg `(((track lhs' rule_link.inf m G).edgemap f_o_f FUN_FMAP I G.E)
           f_o_f m0.edgemap) ' e =
          ((track lhs' rule_link.inf m G).edgemap f_o_f FUN_FMAP I G.E) '
          (m0.edgemap ' e)`
      >- (irule f_o_f_apply >>
          conj_tac >- (
            simp[finite_mapTheory.f_o_f_DEF, finite_mapTheory.FUN_FMAP_DEF,
                 FDOM_track_edgemap] >> fs[]) >>
          fs[])
      >- (gvs[] >>
          `((track lhs' rule_link.inf m G).edgemap f_o_f FUN_FMAP I G.E) '
           (m_E ' e) =
           (track lhs' rule_link.inf m G).edgemap '
           (FUN_FMAP I G.E ' (m_E ' e))`
            by (irule f_o_f_apply >> fs[]) >>
          gvs[track_edgemap_apply]))
    >- (pop_assum (fn th => REWRITE_TAC[th]) >>
        `e IN G0.E` by (
          fs[tc_loop_invariant_def, minimally_extends_def,
             trackTheory.is_track_morphism_def,
             morphismTheory.partial_dom_ran_def] >>
          metis_tac[SUBSET_DEF]) >>
        `m_E ' e NOTIN deletion_deleted_edges lhs' m` by
          fs[trackTheory.edge_survives_iff] >>
        gvs[finite_mapTheory.FUN_FMAP_DEF]))
  ))))
QED
(* -------------------------------------------------------------------------- *)
(* Helper: link body succeeds or fails, preserving total edge embedding       *)
(* -------------------------------------------------------------------------- *)

Theorem link_body_succeeds_or_fails_total:
  !G0 G m0 track_bar c.
    wf_hostgraph G0 /\
    tc_loop_invariant G0 G m0 /\
    tc_loop_invariant_total G0 G track_bar /\
    extends_morphism m0 track_bar /\
    steps program (running (term_rscall {ruleid "link"}), [(G, id_track G)]) c /\
    ~can_step c ==>
    (?H mH. c = (final, [(H, mH)]) /\
            tc_loop_invariant G0 H (compose_morphism mH m0) /\
            ?track_bar'. tc_loop_invariant_total G0 H track_bar' /\
                         extends_morphism (compose_morphism mH m0) track_bar') \/
    (c = (failed, [(G, id_track G)]))
Proof
  rpt strip_tac >>
  `wf_hostgraph G` by fs[tc_loop_invariant_total_def] >>
  (* Get structural result from link_body_succeeds_or_fails *)
  `(?H' mH'. c = (final, [(H', mH')]) /\
             tc_loop_invariant G0 H' (compose_morphism mH' m0)) \/
   (c = (failed, [(G, id_track G)]))` by
    metis_tac[link_body_succeeds_or_fails]
  (* Success case: strengthen with total edge embedding *)
  >- (DISJ1_TAC >>
      qexistsl [`H'`, `mH'`] >> simp[] >> gvs[] >>
      `step program (running (term_rscall {ruleid "link"}), [(G, id_track G)])
                    (final, [(H', mH')])` by
        (irule rscall_steps_to_step >> simp[]) >>
      `?track_bar'. tc_loop_invariant_total G0 H' track_bar' /\
                    extends_morphism (compose_morphism mH' m0) track_bar'` by
        metis_tac[link_preserves_total] >>
      metis_tac[])
  (* Failed case *)
  >- (DISJ2_TAC >> simp[])
QED

(* -------------------------------------------------------------------------- *)
(* Main correctness theorem                                                   *)
(* -------------------------------------------------------------------------- *)

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
         rule := FEMPTY |+ (ruleid "link",rule_link)|> = program` by simp[program_def, FUPDATE_LIST] >>
      gvs[program_wf])
  >- (
    conj_tac >- simp[proc_Main_def, programTheory.no_intermediate_terms_def] >>
    `<|proc := FEMPTY |+ ("Main",proc_Main);
       rule := FEMPTY |+ (ruleid "link",rule_link)|> = program` by simp[program_def, FUPDATE_LIST] >> fs[] >>
    rpt strip_tac >> gvs[proc_Main_def] >>
    mp_tac (ISPECL [``program``, ``term_rscall {ruleid "link"}``,
                    ``\G:hostgraph m:morphism.
                        tc_loop_invariant G0 G m /\
                        ?track_bar. tc_loop_invariant_total G0 G track_bar /\
                                    extends_morphism m track_bar``,
                    ``\G:hostgraph m:morphism. is_transitive G``]
            gp2LogicTheory.WSPEC_alap_allowing_failure) >>
    simp[] >> impl_tac
    >- (rpt conj_tac
        >- simp[program_wf]
        >- EVAL_TAC
        >- (rpt strip_tac >>
            `(?H mH. c' = (final, [(H, mH)]) /\
                     tc_loop_invariant G0 H (compose_morphism mH m) /\
                     ?track_bar'. tc_loop_invariant_total G0 H track_bar' /\
                                  extends_morphism (compose_morphism mH m) track_bar') \/
             (c' = (failed, [(G, id_track G)]))` by
              (irule link_body_succeeds_or_fails_total >> metis_tac[])
            >- (DISJ1_TAC >> qexistsl [`H`, `mH`] >> gvs[] >>
                qexists_tac `track_bar'` >> gvs[])
            >- (DISJ2_TAC >> gvs[] >> metis_tac[]))
        >- (rpt strip_tac >>
            irule link_failure_implies_transitive >>
            metis_tac[tc_loop_invariant_def])
        >- (rpt strip_tac >>
            metis_tac[tc_invariant_implies_morphism_wf]))
    >- (
      (* Establish initial invariant *)
      `tc_loop_invariant_total G0 G0 (id_track G0)` by
        (irule tc_invariant_total_initial >> simp[]) >>
      `tc_loop_invariant G0 G0 (id_track G0)` by
        (irule tc_invariant_initial >> simp[]) >>
      disch_tac >> first_x_assum (qspec_then `id_track G0` mp_tac) >>
      simp[gp2LogicTheory.WSPEC_def] >> strip_tac >>
      first_x_assum (qspecl_then [`G0`, `c`] mp_tac) >> impl_tac
      >- (conj_tac >- metis_tac[] >>
          conj_tac
          >- (conj_tac >- metis_tac[] >>
              qexists_tac `id_track G0` >> simp[] >>
              simp[extends_morphism_def])
          >> metis_tac[])
      >- (
        strip_tac >> qexistsl [`H`, `m`] >> simp[] >>
        (* Extract from combined invariant *)
        `tc_loop_invariant G0 H (compose_morphism m (id_track G0))` by gvs[] >>
        (* Simplify compose_morphism m (id_track G0) = m *)
        sg `compose_morphism m (id_track G0) = m`
        >- (fs[tc_loop_invariant_def, minimally_extends_def] >>
            irule trackTheory.compose_morphism_id_track_right >> simp[] >>
            fs[trackTheory.is_track_morphism_def, morphismTheory.partial_dom_ran_def] >>
            mp_tac steps_to_stack_tracks >> disch_tac >>
            first_x_assum (qspecl_then [`program`, `term_rscall {ruleid "link"}`, `G0`, `H`, `m`] mp_tac) >>
            impl_tac >- simp[program_wf] >>
            simp[semPropsTheory.stack_tracks_morphism_def, trackTheory.is_track_morphism_def,
                 morphismTheory.partial_dom_ran_def])
        >- (gvs[] >>
            qexists_tac `track_bar` >> simp[] >>
            metis_tac[tc_invariant_termination]))))
QED

val () = export_theory ()
