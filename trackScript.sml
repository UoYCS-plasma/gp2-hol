open HolKernel boolLib bossLib Parse

open graphTheory hostgraphTheory morphismTheory dpoTheory taggingTheory
open pred_setTheory finite_mapTheory pairTheory arithmeticTheory

val () = new_theory "track"

(* TRACK MORPHISM DEFINITION                                          *)

(* ------------------------------------------------------------------
   A track morphism tr : G -> H tracks nodes/edges through a DPO step.

   - G = source graph
   - H = dpo L Iface R m G (result after applying rule)
   - tr maps surviving elements to their positions in H

   A track morphism preserves structure (source/target) and is injective,
   but does NOT preserve rootedness. This allows rules to change the
   rootedness of interface nodes (re-rooting).

   The domain is the surviving elements (deletion), which is a subset
   of G.V/G.E. This partiality allows composition of tracks from
   multiple transformation steps.
   ------------------------------------------------------------------ *)

Definition is_track_morphism_def:
  is_track_morphism G tr H <=>
    partial_dom_ran G tr H /\
    partial_preserve_source G tr H /\
    partial_preserve_target G tr H /\
    INJ (FAPPLY tr.nodemap) (FDOM tr.nodemap) H.V /\
    INJ (FAPPLY tr.edgemap) (FDOM tr.edgemap) H.E
End

(* A partial injective premorphism (which includes rootedness) implies track morphism *)
Theorem is_partial_inj_premorphism_IMP_track_morphism:
  !G tr H. is_partial_inj_premorphism G tr H ==> is_track_morphism G tr H
Proof
  rw[is_partial_inj_premorphism_def, is_partial_premorphism_def, is_track_morphism_def]
QED

(* HELPER LEMMAS FOR FUN_FMAP AND COMPOSITION                         *)

(* Simplified FUN_FMAP application lemma *)
Theorem FUN_FMAP_APPLY:
  !f s x. FINITE s /\ x IN s ==> FUN_FMAP f s ' x = f x
Proof
  metis_tac[FUN_FMAP_DEF]
QED

(* Domain of f_o_f is subset of second argument's domain *)
Theorem FDOM_f_o_f_SUBSET:
  !f g. FDOM (f f_o_f g) SUBSET FDOM g
Proof
  rw[f_o_f_DEF, SUBSET_DEF]
QED

(* Range of f_o_f is subset of first argument's range *)
Theorem FRANGE_f_o_f_SUBSET:
  !f g. FRANGE (f f_o_f g) SUBSET FRANGE f
Proof
  rw[f_o_f_DEF, FRANGE_DEF, SUBSET_DEF]
  >> qexists_tac `g ' x'` >> simp[f_o_f_DEF]
QED

(* Composition of INJ maps is INJ *)
Theorem INJ_f_o_f:
  !f g A B C.
    INJ ($' g) A B /\
    INJ ($' f) B C /\
    FDOM g SUBSET A /\
    FRANGE g SUBSET B /\
    FDOM f SUBSET B ==>
    INJ ($' (f f_o_f g)) (FDOM (f f_o_f g)) C
Proof
  rw[INJ_DEF, f_o_f_DEF]
  >- (fs[FRANGE_DEF, SUBSET_DEF] >> metis_tac[])
  >- (`g ' x IN FRANGE g /\ g ' y IN FRANGE g` by (rw[FRANGE_DEF] >> metis_tac[])
      >> `g ' x IN B /\ g ' y IN B` by metis_tac[SUBSET_DEF]
      >> `g ' x = g ' y` by metis_tac[]
      >> `x IN A /\ y IN A` by metis_tac[SUBSET_DEF]
      >> metis_tac[])
QED

(* TRACK MORPHISM CONSTRUCTION                                        *)

(* ------------------------------------------------------------------
   Construct track morphism from a DPO step.

   tr(v) = tag_nodeid_left v   for v in D.V (surviving nodes)
   tr(e) = tag_edgeid_left e   for e in D.E (surviving edges)
   ------------------------------------------------------------------ *)

Definition track_def:
  track (L:hostgraph) (Iface:nodeid set) (m:morphism) (G:hostgraph) =
    let surviving_nodes = deletion_remaining_nodes L m Iface G in
    let surviving_edges = deletion_remaining_edges L m G in
    <| nodemap := FUN_FMAP tag_nodeid_left surviving_nodes ;
       edgemap := FUN_FMAP tag_edgeid_left surviving_edges
    |>
End

(* DOMAIN LEMMAS                                                      *)

Theorem FDOM_track_nodemap:
  !L Iface m G. FINITE (deletion_remaining_nodes L m Iface G) ==>
    FDOM (track L Iface m G).nodemap = deletion_remaining_nodes L m Iface G
Proof
  rw[track_def, FUN_FMAP_DEF]
QED

Theorem FDOM_track_edgemap:
  !L Iface m G. FINITE (deletion_remaining_edges L m G) ==>
    FDOM (track L Iface m G).edgemap = deletion_remaining_edges L m G
Proof
  rw[track_def, FUN_FMAP_DEF]
QED

(* The domain equals D.V and D.E *)
Theorem FDOM_track_nodemap_eq_deletion_V:
  !L Iface m G.
    let D = deletion L Iface m G in
    FINITE D.V ==>
    FDOM (track L Iface m G).nodemap = D.V
Proof
  rw[track_def, deletion_def, FUN_FMAP_DEF]
QED

Theorem FDOM_track_edgemap_eq_deletion_E:
  !L Iface m G.
    let D = deletion L Iface m G in
    FINITE D.E ==>
    FDOM (track L Iface m G).edgemap = D.E
Proof
  rw[track_def, deletion_def, FUN_FMAP_DEF]
QED

(* APPLICATION LEMMAS                                                 *)

Theorem track_nodemap_apply:
  !L Iface m G v.
    FINITE (deletion_remaining_nodes L m Iface G) /\
    v IN deletion_remaining_nodes L m Iface G ==>
    (track L Iface m G).nodemap ' v = tag_nodeid_left v
Proof
  rw[track_def, FUN_FMAP_DEF]
QED

Theorem track_edgemap_apply:
  !L Iface m G e.
    FINITE (deletion_remaining_edges L m G) /\
    e IN deletion_remaining_edges L m G ==>
    (track L Iface m G).edgemap ' e = tag_edgeid_left e
Proof
  rw[track_def, FUN_FMAP_DEF]
QED

(* SURVIVAL CHARACTERIZATION                                          *)

(* A node survives iff it's not deleted *)
Theorem node_survives_iff:
  !L Iface m G v.
    v IN deletion_remaining_nodes L m Iface G <=>
    v IN G.V /\ ~(v IN deletion_deleted_nodes L m Iface)
Proof
  rw[deletion_remaining_nodes_def]
QED

(* An edge survives iff it's not deleted *)
Theorem edge_survives_iff:
  !L m G e.
    e IN deletion_remaining_edges L m G <=>
    e IN G.E /\ ~(e IN deletion_deleted_edges L m)
Proof
  rw[deletion_remaining_edges_def]
QED

(* A node is deleted iff it's matched from L.V DIFF Iface *)
Theorem node_deleted_iff:
  !L m Iface v.
    v IN deletion_deleted_nodes L m Iface <=>
    ?u. u IN L.V /\ ~(u IN Iface) /\ m.nodemap ' u = v
Proof
  rw[deletion_deleted_nodes_def, IN_IMAGE] >> metis_tac[]
QED

(* An edge is deleted iff it's matched from L.E *)
Theorem edge_deleted_iff:
  !L m e.
    e IN deletion_deleted_edges L m <=>
    ?f. f IN L.E /\ m.edgemap ' f = e
Proof
  rw[deletion_deleted_edges_def, IN_IMAGE] >> metis_tac[]
QED

(* RANGE LEMMAS - WHERE TRACKED ELEMENTS GO                           *)

Theorem track_node_in_gluing:
  !L Iface m G R v.
    let D = deletion L Iface m G in
    FINITE D.V /\ v IN D.V ==>
    (track L Iface m G).nodemap ' v IN gluing_nodes D Iface R
Proof
  rw[track_def, deletion_def, FUN_FMAP_DEF,
     gluing_nodes_def, nodeid_coprod_def] >>
  DISJ1_TAC >> qexists_tac `v` >> rw[]
QED

Theorem track_edge_in_gluing:
  !L Iface m G R e.
    let D = deletion L Iface m G in
    FINITE D.E /\ e IN D.E ==>
    (track L Iface m G).edgemap ' e IN gluing_edges D R
Proof
  rw[track_def, deletion_def, FUN_FMAP_DEF,
     gluing_edges_def, edgeid_coprod_def] >>
  DISJ1_TAC >> qexists_tac `e` >> rw[]
QED

(* INJECTIVITY                                                        *)

Theorem track_nodemap_INJ:
  !L Iface m G.
    let D = deletion L Iface m G in
    FINITE D.V ==>
    INJ (FAPPLY (track L Iface m G).nodemap) D.V UNIV
Proof
  rw[track_def, deletion_def, FUN_FMAP_DEF, INJ_DEF] >>
  Cases_on `x` >> Cases_on `y` >>
  fs[tag_nodeid_left_def, dest_nodeid_def]
QED

Theorem track_edgemap_INJ:
  !L Iface m G.
    let D = deletion L Iface m G in
    FINITE D.E ==>
    INJ (FAPPLY (track L Iface m G).edgemap) D.E UNIV
Proof
  rw[track_def, deletion_def, FUN_FMAP_DEF, INJ_DEF] >>
  Cases_on `x` >> Cases_on `y` >>
  fs[tag_edgeid_left_def, dest_edgeid_def]
QED

(* HELPER LEMMA FOR GLUING_P DOMAIN                                   *)

(* Domain of gluing_p equals its node set argument *)
Theorem FDOM_gluing_p:
  !V Kv m H R. FINITE V ==> FDOM (gluing_p V Kv m H R) = V
Proof
  rpt strip_tac >>
  rw[gluing_p_def, FDOM_FUPDATE_LIST, listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  `(\nid. FST (if is_left_tagged_nodeid nid then
      if (?k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid) then
        (nid,R.p ' @k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid)
      else (nid,H.p ' (untag_nodeid nid))
    else (nid,R.p ' (untag_nodeid nid)))) = (\nid. nid)`
      by (rw[FUN_EQ_THM] >> rw[]) >>
  simp[] >> simp[listTheory.SET_TO_LIST_INV]
QED

(* MAIN THEOREM: TRACK IS A VALID TRACK MORPHISM                      *)

(* ------------------------------------------------------------------
   Main theorem: track produces a valid track morphism (is_inj_premorphism)
   from the context D to the result H.

   Preconditions:
   - wf_hostgraph L, R, G
   - Iface SUBSET L.V (interface is subset of LHS nodes)
   - Iface SUBSET R.V (interface is subset of RHS nodes)
   - is_match L Iface m G (valid match with dangling condition)
   ------------------------------------------------------------------ *)

Theorem track_is_track_morphism:
  !(L:hostgraph) Iface R m G.
    wf_hostgraph L /\ wf_hostgraph R /\ wf_hostgraph G /\
    Iface SUBSET L.V /\ Iface SUBSET R.V /\
    is_match L Iface m G ==>
    is_track_morphism G (track L Iface m G) (dpo L Iface R m G)
Proof
  rpt strip_tac \\
  qabbrev_tac `D = deletion L Iface m G` \\
  qabbrev_tac `H = dpo L Iface R m G` \\
  qabbrev_tac `tr = track L Iface m G` \\
  (* Establish well-formedness and finiteness facts *)
  `FINITE G.V /\ FINITE G.E` by fs[wf_hostgraph_def, wf_graph_def] \\
  `FINITE L.E` by fs[wf_hostgraph_def, wf_graph_def] \\
  `wf_graph G` by fs[wf_hostgraph_def] \\
  `wf_graph R /\ FINITE R.V /\ FINITE R.E` by fs[wf_hostgraph_def, wf_graph_def] \\
  `wf_partial_hostgraph D` by (unabbrev_all_tac \\ irule deletion_preserves_wf_graph \\ rw[]) \\
  `wf_graph D` by fs[wf_partial_hostgraph_def] \\
  `FINITE D.V /\ FINITE D.E` by fs[wf_graph_def] \\
  `wf_hostgraph H` by (unabbrev_all_tac >> irule wf_dpo >> simp[]) \\
  `wf_graph H` by fs[wf_hostgraph_def] \\
  (* Establish deletion structure facts *)
  `D.V = deletion_remaining_nodes L m Iface G` by rw[Abbr `D`, deletion_def] \\
  `D.E = deletion_remaining_edges L m G` by rw[Abbr `D`, deletion_def] \\
  `D.s = DRESTRICT G.s D.E` by rw[Abbr `D`, deletion_def] \\
  `D.t = DRESTRICT G.t D.E` by rw[Abbr `D`, deletion_def] \\
  `FDOM D.s = D.E /\ FDOM D.t = D.E` by fs[wf_graph_def] \\
  `FRANGE D.s SUBSET D.V /\ FRANGE D.t SUBSET D.V` by fs[wf_graph_def] \\
  `D.V SUBSET G.V` by rw[Abbr `D`, deletion_def, deletion_remaining_nodes_def] \\
  `D.E SUBSET G.E` by rw[Abbr `D`, deletion_def, deletion_remaining_edges_def] \\
  (* Establish track structure facts *)
  `tr.nodemap = FUN_FMAP tag_nodeid_left D.V` by
    rw[Abbr `tr`, track_def, Abbr `D`, deletion_def,
       deletion_remaining_nodes_def, deletion_remaining_edges_def] \\
  `tr.edgemap = FUN_FMAP tag_edgeid_left D.E` by
    rw[Abbr `tr`, track_def, Abbr `D`, deletion_def,
       deletion_remaining_nodes_def, deletion_remaining_edges_def] \\
  `FDOM tr.nodemap = D.V` by metis_tac[FUN_FMAP_DEF] \\
  `FDOM tr.edgemap = D.E` by metis_tac[FUN_FMAP_DEF] \\
  (* Expand is_track_morphism and prove 5 properties *)
  rw[is_track_morphism_def]
  (* 1. partial_dom_ran *)
  >- (rw[partial_dom_ran_def]
      >- metis_tac[SUBSET_DEF]
      >- metis_tac[SUBSET_DEF]
      >- (rw[FRANGE_DEF, SUBSET_DEF] >> rpt strip_tac \\
          `x' IN D.V` by metis_tac[FUN_FMAP_DEF] \\
          `tr.nodemap ' x' = tag_nodeid_left x'` by metis_tac[FUN_FMAP_DEF] \\
          simp[] \\ unabbrev_all_tac \\
          rw[dpo_def, gluing_def, gluing_nodes_def, nodeid_coprod_def] \\
          DISJ1_TAC >> qexists_tac `x'` >> simp[FUN_FMAP_DEF] \\
          gvs[FUN_FMAP_DEF])
      >- (rw[FRANGE_DEF, SUBSET_DEF] >> rpt strip_tac \\
          `x' IN D.E` by metis_tac[FUN_FMAP_DEF] \\
          `tr.edgemap ' x' = tag_edgeid_left x'` by metis_tac[FUN_FMAP_DEF] \\
          simp[] \\ unabbrev_all_tac \\
          rw[dpo_def, gluing_def, gluing_edges_def, edgeid_coprod_def] \\
          DISJ1_TAC >> qexists_tac `x'` >> gvs[FUN_FMAP_DEF]))
  (* 2. partial_preserve_source *)
  >- (rw[partial_preserve_source_def, SUBMAP_DEF]
      >- (simp[f_o_f_DEF] >> rpt strip_tac
          >- (gvs[f_o_f_DEF, FUN_FMAP_DEF] \\
              `FDOM G.s = G.E` by fs[wf_graph_def] \\
              `x IN D.E` by (fs[f_o_f_DEF] >> metis_tac[FUN_FMAP_DEF]) \\
              metis_tac[SUBSET_DEF])
          >- (gvs[FUN_FMAP_DEF] \\
              `x IN deletion_remaining_edges L m G` by
                (fs[f_o_f_DEF] >> metis_tac[FUN_FMAP_DEF]) \\
              `(DRESTRICT G.s (deletion_remaining_edges L m G)) ' x IN
               FRANGE (DRESTRICT G.s (deletion_remaining_edges L m G))` by
                (simp[IN_FRANGE] >> qexists_tac `x` >> simp[]) \\
              `x IN FDOM G.s` by (fs[wf_graph_def] >> metis_tac[SUBSET_DEF]) \\
              `(DRESTRICT G.s (deletion_remaining_edges L m G)) ' x = G.s ' x` by
                (simp[DRESTRICT_DEF] >> fs[IN_INTER]) \\
              metis_tac[SUBSET_DEF]))
      >- (simp[f_o_f_DEF] \\
          `x IN deletion_remaining_edges L m G` by
            (fs[f_o_f_DEF] >> metis_tac[FUN_FMAP_DEF]) \\
          `FUN_FMAP tag_edgeid_left (deletion_remaining_edges L m G) ' x =
           tag_edgeid_left x` by gvs[FUN_FMAP_DEF] \\
          simp[] \\
          `x IN FDOM G.s` by (fs[wf_graph_def] >> metis_tac[SUBSET_DEF]) \\
          `(DRESTRICT G.s (deletion_remaining_edges L m G)) ' x = G.s ' x` by
            (simp[DRESTRICT_DEF] >> fs[IN_INTER]) \\
          unabbrev_all_tac >> rw[dpo_def, gluing_def] \\
          qabbrev_tac `DD = deletion L Iface m G` \\
          `wf_partial_hostgraph DD` by
            (simp[Abbr `DD`] \\ irule deletion_preserves_wf_graph \\ rw[]) \\
          `wf_graph DD` by fs[wf_partial_hostgraph_def] \\
          `x IN DD.E` by simp[Abbr `DD`, deletion_def] \\
          `gluing_s Iface m DD R ' (tag_edgeid_left x) =
           tag_nodeid_left (DD.s ' x)` by
            (irule gluing_s_apply_left_tagged >> simp[]) \\
          simp[] \\
          `DD.s ' x = G.s ' x` by
            (simp[Abbr `DD`, deletion_def, DRESTRICT_DEF, IN_INTER]) \\
          `DD.V = deletion_remaining_nodes L m Iface G` by
            simp[Abbr `DD`, deletion_def] \\
          `FDOM DD.s = DD.E` by fs[wf_graph_def] \\
          `FRANGE DD.s SUBSET DD.V` by fs[wf_graph_def] \\
          `DD.s ' x IN FRANGE DD.s` by (simp[IN_FRANGE] >> qexists_tac `x` >> gvs[]) \\
          `G.s ' x IN deletion_remaining_nodes L m Iface G` by metis_tac[SUBSET_DEF] \\
          `(FUN_FMAP tag_nodeid_left (deletion_remaining_nodes L m Iface G) f_o_f G.s) ' x =
           FUN_FMAP tag_nodeid_left (deletion_remaining_nodes L m Iface G) ' (G.s ' x)` by
            gvs[f_o_f_DEF, FUN_FMAP_DEF] \\
          `FUN_FMAP tag_nodeid_left (deletion_remaining_nodes L m Iface G) ' (G.s ' x) =
           tag_nodeid_left (G.s ' x)` by gvs[FUN_FMAP_DEF] \\
          metis_tac[]))
  (* 3. partial_preserve_target *)
  >- (rw[partial_preserve_target_def, SUBMAP_DEF] >> simp[f_o_f_DEF] >> rpt strip_tac
      >- (gvs[f_o_f_DEF, FUN_FMAP_DEF] \\
          `FDOM G.t = G.E` by fs[wf_graph_def] \\
          `x IN D.E` by (fs[f_o_f_DEF] >> metis_tac[FUN_FMAP_DEF]) \\
          metis_tac[SUBSET_DEF])
      >- (gvs[FUN_FMAP_DEF] \\
          `x IN deletion_remaining_edges L m G` by
            (fs[f_o_f_DEF] >> metis_tac[FUN_FMAP_DEF]) \\
          `(DRESTRICT G.t (deletion_remaining_edges L m G)) ' x IN
           FRANGE (DRESTRICT G.t (deletion_remaining_edges L m G))` by
            (simp[IN_FRANGE] >> qexists_tac `x` >> simp[]) \\
          `x IN FDOM G.t` by (fs[wf_graph_def] >> metis_tac[SUBSET_DEF]) \\
          `(DRESTRICT G.t (deletion_remaining_edges L m G)) ' x = G.t ' x` by
            (simp[DRESTRICT_DEF] >> fs[IN_INTER]) \\
          metis_tac[SUBSET_DEF])
      >- (`x IN deletion_remaining_edges L m G` by
            (fs[f_o_f_DEF] >> metis_tac[FUN_FMAP_DEF]) \\
          `FUN_FMAP tag_edgeid_left (deletion_remaining_edges L m G) ' x =
           tag_edgeid_left x` by gvs[FUN_FMAP_DEF] \\
          simp[] \\
          `x IN FDOM G.t` by (fs[wf_graph_def] >> metis_tac[SUBSET_DEF]) \\
          unabbrev_all_tac >> rw[dpo_def, gluing_def] \\
          qabbrev_tac `DD = deletion L Iface m G` \\
          `wf_partial_hostgraph DD` by
            (simp[Abbr `DD`] \\ irule deletion_preserves_wf_graph \\ rw[]) \\
          `wf_graph DD` by fs[wf_partial_hostgraph_def] \\
          `FINITE DD.E` by fs[wf_graph_def] \\
          `FINITE R.E` by fs[wf_hostgraph_def, wf_graph_def] \\
          `x IN DD.E` by simp[Abbr `DD`, deletion_def] \\
          sg `gluing_t (gluing_edges DD R) Iface m DD R ' (tag_edgeid_left x) =
              tag_nodeid_left (DD.t ' x)`
          >- (irule gluing_t_apply_left_tagged \\
              simp[gluing_edges_def, edgeid_coprod_def] >>
              simp[IMAGE_FINITE, FINITE_UNION] \\
              metis_tac[IMAGE_FINITE])
          >- (simp[] \\
              `DD.t ' x = G.t ' x` by
                (simp[Abbr `DD`, deletion_def, DRESTRICT_DEF, IN_INTER]) \\
              `DD.V = deletion_remaining_nodes L m Iface G` by
                simp[Abbr `DD`, deletion_def] \\
              `FDOM DD.t = DD.E` by fs[wf_graph_def] \\
              `FRANGE DD.t SUBSET DD.V` by fs[wf_graph_def] \\
              `DD.t ' x IN FRANGE DD.t` by
                (simp[IN_FRANGE] >> qexists_tac `x` >> gvs[]) \\
              `G.t ' x IN deletion_remaining_nodes L m Iface G` by
                metis_tac[SUBSET_DEF] \\
              `(DRESTRICT G.t (deletion_remaining_edges L m G)) ' x = G.t ' x` by
                (simp[DRESTRICT_DEF] >> fs[IN_INTER]) \\
              simp[] \\
              `(FUN_FMAP tag_nodeid_left (deletion_remaining_nodes L m Iface G) f_o_f G.t) ' x =
               FUN_FMAP tag_nodeid_left (deletion_remaining_nodes L m Iface G) ' (G.t ' x)` by
                gvs[f_o_f_DEF, FUN_FMAP_DEF] \\
              `FUN_FMAP tag_nodeid_left (deletion_remaining_nodes L m Iface G) ' (G.t ' x) =
               tag_nodeid_left (G.t ' x)` by gvs[FUN_FMAP_DEF] \\
              metis_tac[])))
  (* 4. INJ nodemap *)
  >- (rw[INJ_DEF, FUN_FMAP_DEF]
      >- (`FUN_FMAP tag_nodeid_left (deletion_remaining_nodes L m Iface G) ' x =
           tag_nodeid_left x` by gvs[FUN_FMAP_DEF] \\
          simp[] \\ unabbrev_all_tac \\
          rw[dpo_def, gluing_def, gluing_nodes_def, tag_nodeid_coprod_membership])
      >- (`FUN_FMAP tag_nodeid_left (deletion_remaining_nodes L m Iface G) ' x =
           tag_nodeid_left x` by gvs[FUN_FMAP_DEF] \\
          `FUN_FMAP tag_nodeid_left (deletion_remaining_nodes L m Iface G) ' y =
           tag_nodeid_left y` by gvs[FUN_FMAP_DEF] \\
          gvs[tag_nodeid_left_def] \\
          Cases_on `x` >> Cases_on `y` >> gvs[dest_nodeid_def]))
  (* 5. INJ edgemap *)
  >- (rw[INJ_DEF, FUN_FMAP_DEF]
      >- (`FUN_FMAP tag_edgeid_left (deletion_remaining_edges L m G) ' x =
           tag_edgeid_left x` by gvs[FUN_FMAP_DEF] \\
          simp[] \\ unabbrev_all_tac \\
          rw[dpo_def, gluing_def, gluing_edges_def, tag_edgeid_coprod_membership])
      >- (`FUN_FMAP tag_edgeid_left (deletion_remaining_edges L m G) ' x =
           tag_edgeid_left x` by gvs[FUN_FMAP_DEF] \\
          `FUN_FMAP tag_edgeid_left (deletion_remaining_edges L m G) ' y =
           tag_edgeid_left y` by gvs[FUN_FMAP_DEF] \\
          gvs[tag_edgeid_left_def] \\
          Cases_on `x` >> Cases_on `y` >> gvs[dest_edgeid_def]))
QED

(* USEFUL COROLLARIES                                                 *)

(* The context D is a subgraph of G *)
Theorem deletion_subgraph_of_G:
  !L Iface m G.
    (deletion L Iface m G).V SUBSET G.V /\
    (deletion L Iface m G).E SUBSET G.E
Proof
  rw[deletion_def, deletion_remaining_nodes_def, deletion_remaining_edges_def]
QED

(* If nothing is deleted, track is total on G *)
Theorem track_total_when_no_deletion:
  !L Iface m G.
    Iface = L.V /\ L.E = {} /\ FINITE G.V /\ FINITE G.E ==>
    FDOM (track L Iface m G).nodemap = G.V /\
    FDOM (track L Iface m G).edgemap = G.E
Proof
  rw[track_def, deletion_remaining_nodes_def, deletion_remaining_edges_def,
     deletion_deleted_nodes_def, deletion_deleted_edges_def, FUN_FMAP_DEF] >>
  `L.V DIFF Iface = {}` by (rw[EXTENSION] >> metis_tac[]) >> simp[]
QED

(* Track is empty when everything is deleted *)
Theorem track_empty_when_all_deleted:
  !L Iface m G.
    deletion_remaining_nodes L m Iface G = {} /\
    deletion_remaining_edges L m G = {} ==>
    (track L Iface m G).nodemap = FEMPTY /\
    (track L Iface m G).edgemap = FEMPTY
Proof
  rw[track_def, FUN_FMAP_DEF]
QED

(* IDENTITY TRACK MORPHISM                                            *)

(* ------------------------------------------------------------------
   Identity track morphism: maps G to itself.
   Used to initialize track chains and for no-op transformations.
   ------------------------------------------------------------------ *)

Definition id_track_def:
  id_track (G:hostgraph) =
    <| nodemap := FUN_FMAP I G.V ;
       edgemap := FUN_FMAP I G.E |>
End

Theorem FDOM_id_track_nodemap:
  !G. FINITE G.V ==> FDOM (id_track G).nodemap = G.V
Proof
  rw[id_track_def, FUN_FMAP_DEF]
QED

Theorem FDOM_id_track_edgemap:
  !G. FINITE G.E ==> FDOM (id_track G).edgemap = G.E
Proof
  rw[id_track_def, FUN_FMAP_DEF]
QED

Theorem id_track_nodemap_apply:
  !G v. FINITE G.V /\ v IN G.V ==> (id_track G).nodemap ' v = v
Proof
  rw[id_track_def, FUN_FMAP_DEF]
QED

Theorem id_track_edgemap_apply:
  !G e. FINITE G.E /\ e IN G.E ==> (id_track G).edgemap ' e = e
Proof
  rw[id_track_def, FUN_FMAP_DEF]
QED

Theorem id_track_is_track_morphism:
  !(G:hostgraph). wf_graph G /\ FINITE G.V /\ FINITE G.E ==>
    is_track_morphism G (id_track G) G
Proof
  rw[is_track_morphism_def, partial_dom_ran_def,
     partial_preserve_source_def, partial_preserve_target_def, id_track_def,
     SUBMAP_DEF, f_o_f_DEF, FUN_FMAP_DEF, INJ_DEF]
  >- fs[wf_graph_def]
  >- (`FRANGE G.s SUBSET G.V` by fs[wf_graph_def]
      \\ `x IN FDOM G.s` by fs[wf_graph_def]
      \\ `G.s ' x IN FRANGE G.s` by (rw[IN_FRANGE] >> metis_tac[])
      \\ metis_tac[SUBSET_DEF])
  >- (simp[f_o_f_DEF]
      \\ `G.s ' x IN G.V` by (fs[wf_graph_def, IN_FRANGE, SUBSET_DEF] >> metis_tac[])
      \\ `x IN FDOM (FUN_FMAP I G.V f_o_f G.s)` by (simp[f_o_f_DEF, FUN_FMAP_DEF] >> fs[wf_graph_def])
      \\ `(FUN_FMAP I G.V f_o_f G.s) ' x = FUN_FMAP I G.V ' (G.s ' x)` by simp[f_o_f_DEF]
      \\ `FUN_FMAP I G.V ' (G.s ' x) = G.s ' x` by simp[FUN_FMAP_DEF]
      \\ metis_tac[])
  >- fs[wf_graph_def]
  >- (`FDOM G.t = G.E` by fs[wf_graph_def]
      \\ `x IN FDOM G.t` by metis_tac[]
      \\ `G.t ' x IN FRANGE G.t` by (rw[IN_FRANGE] >> metis_tac[])
      \\ `FRANGE G.t SUBSET G.V` by fs[wf_graph_def]
      \\ metis_tac[SUBSET_DEF])
  >- (`G.t ' x IN G.V` by (fs[wf_graph_def, IN_FRANGE, SUBSET_DEF] >> metis_tac[])
      \\ `x IN FDOM (FUN_FMAP I G.V f_o_f G.t)` by (simp[f_o_f_DEF, FUN_FMAP_DEF] >> fs[wf_graph_def])
      \\ `(FUN_FMAP I G.V f_o_f G.t) ' x = FUN_FMAP I G.V ' (G.t ' x)` by simp[f_o_f_DEF]
      \\ `FUN_FMAP I G.V ' (G.t ' x) = G.t ' x` by simp[FUN_FMAP_DEF]
      \\ metis_tac[])
QED

(* Composition of track morphisms is a track morphism. *)
Theorem compose_is_track_morphism:
  !G0 G1 G2 tr1 tr2.
    is_track_morphism G0 tr1 G1 /\
    is_track_morphism G1 tr2 G2 ==>
    is_track_morphism G0 (compose_morphism tr2 tr1) G2
Proof
  rw[is_track_morphism_def, compose_morphism_def]
  (* partial_dom_ran *)
  >- (fs[partial_dom_ran_def]
      \\ rpt conj_tac
      >- metis_tac[FDOM_f_o_f_SUBSET, SUBSET_TRANS]
      >- metis_tac[FDOM_f_o_f_SUBSET, SUBSET_TRANS]
      >- metis_tac[FRANGE_f_o_f_SUBSET, SUBSET_TRANS]
      >- metis_tac[FRANGE_f_o_f_SUBSET, SUBSET_TRANS])
  (* partial_preserve_source *)
  >- (fs[partial_preserve_source_def, SUBMAP_DEF]
      \\ rpt strip_tac
      (* Domain inclusion *)
      >- (gvs[f_o_f_DEF]
          \\ `tr1.edgemap ' x IN FDOM G1.s` by
               (first_x_assum (qspec_then `tr1.edgemap ' x` mp_tac) >> simp[])
          \\ `G1.s ' (tr1.edgemap ' x) IN FDOM tr2.nodemap` by
               (first_x_assum (qspec_then `tr1.edgemap ' x` mp_tac) >> simp[])
          \\ `G1.s ' (tr1.edgemap ' x) = tr1.nodemap ' (G0.s ' x)` by
               (last_x_assum (qspec_then `x` mp_tac) >> simp[f_o_f_DEF])
          \\ metis_tac[])
      (* Value equality *)
      >- (gvs[f_o_f_DEF]
          \\ `tr1.edgemap ' x IN FDOM G1.s` by
               (first_x_assum (qspec_then `tr1.edgemap ' x` mp_tac) >> simp[])
          \\ `x IN FDOM G0.s /\ G0.s ' x IN FDOM tr1.nodemap` by
               (last_x_assum (qspec_then `x` mp_tac) >> simp[])
          \\ `tr1.nodemap ' (G0.s ' x) IN FDOM tr2.nodemap` by
               (first_x_assum (qspec_then `tr1.edgemap ' x` mp_tac) >> simp[]
                >> last_x_assum (qspec_then `x` mp_tac) >> simp[f_o_f_DEF])
          \\ `x IN FDOM ((tr2.nodemap f_o_f tr1.nodemap) f_o_f G0.s)` by simp[f_o_f_DEF]
          \\ `((tr2.nodemap f_o_f tr1.nodemap) f_o_f G0.s) ' x =
              (tr2.nodemap f_o_f tr1.nodemap) ' (G0.s ' x)` by simp[f_o_f_DEF]
          \\ `(tr2.nodemap f_o_f tr1.nodemap) ' (G0.s ' x) =
              tr2.nodemap ' (tr1.nodemap ' (G0.s ' x))` by simp[f_o_f_DEF]
          \\ metis_tac[]))
  (* partial_preserve_target *)
  >- (fs[partial_preserve_target_def, SUBMAP_DEF] >> rpt strip_tac
      (* Domain inclusion *)
      >- (gvs[f_o_f_DEF]
          \\ `tr1.edgemap ' x IN FDOM G1.t` by
               (first_x_assum (qspec_then `tr1.edgemap ' x` mp_tac) >> simp[])
          \\ `G1.t ' (tr1.edgemap ' x) IN FDOM tr2.nodemap` by
               (first_x_assum (qspec_then `tr1.edgemap ' x` mp_tac) >> simp[])
          \\ `G1.t ' (tr1.edgemap ' x) = tr1.nodemap ' (G0.t ' x)` by
               (last_x_assum (qspec_then `x` mp_tac) >> simp[f_o_f_DEF])
          \\ metis_tac[])
      (* Value equality *)
      >- (gvs[f_o_f_DEF]
          \\ `x IN FDOM G0.t /\ G0.t ' x IN FDOM tr1.nodemap` by
               (last_x_assum (qspec_then `x` mp_tac) >> simp[])
          \\ `tr1.edgemap ' x IN FDOM G1.t` by
               (first_x_assum (qspec_then `tr1.edgemap ' x` mp_tac) >> simp[])
          \\ `G1.t ' (tr1.edgemap ' x) IN FDOM tr2.nodemap` by
               (first_x_assum (qspec_then `tr1.edgemap ' x` mp_tac) >> simp[])
          \\ `G1.t ' (tr1.edgemap ' x) = tr1.nodemap ' (G0.t ' x)` by
               (last_x_assum (qspec_then `x` mp_tac) >> simp[f_o_f_DEF])
          \\ `tr1.nodemap ' (G0.t ' x) IN FDOM tr2.nodemap` by metis_tac[]
          \\ `x IN FDOM ((tr2.nodemap f_o_f tr1.nodemap) f_o_f G0.t)` by simp[f_o_f_DEF]
          \\ `((tr2.nodemap f_o_f tr1.nodemap) f_o_f G0.t) ' x =
              (tr2.nodemap f_o_f tr1.nodemap) ' (G0.t ' x)` by simp[f_o_f_DEF]
          \\ `(tr2.nodemap f_o_f tr1.nodemap) ' (G0.t ' x) =
              tr2.nodemap ' (tr1.nodemap ' (G0.t ' x))` by simp[f_o_f_DEF]
          \\ metis_tac[]))
  (* INJ nodemap *)
  >- (rw[INJ_DEF, f_o_f_DEF]
      >- (fs[INJ_DEF] >> metis_tac[])
      >- (`tr1.nodemap ' x = tr1.nodemap ' y` by (fs[INJ_DEF] >> metis_tac[])
          \\ fs[INJ_DEF] >> metis_tac[]))
  (* INJ edgemap *)
  >- (rw[INJ_DEF, f_o_f_DEF]
      >- (fs[INJ_DEF] >> metis_tac[])
      >- (`tr1.edgemap ' x = tr1.edgemap ' y` by (fs[INJ_DEF] >> metis_tac[])
          \\ fs[INJ_DEF] >> metis_tac[]))
QED

(* INDUCED SUBGRAPH                                                    *)

(* ------------------------------------------------------------------
   The subgraph of G induced by a morphism's domain.
   Given a morphism tr, this extracts the subgraph of G corresponding
   to FDOM tr.nodemap and FDOM tr.edgemap.
   ------------------------------------------------------------------ *)

Definition induced_subgraph_def:
  induced_subgraph (G:hostgraph) tr =
    <| V := FDOM tr.nodemap;
       E := FDOM tr.edgemap;
       s := DRESTRICT G.s (FDOM tr.edgemap);
       t := DRESTRICT G.t (FDOM tr.edgemap);
       l := DRESTRICT G.l (FDOM tr.nodemap);
       m := DRESTRICT G.m (FDOM tr.edgemap);
       p := DRESTRICT G.p (FDOM tr.nodemap)
    |>
End

(* Basic accessors *)
Theorem induced_subgraph_V:
  !G tr. (induced_subgraph G tr).V = FDOM tr.nodemap
Proof
  rw[induced_subgraph_def]
QED

Theorem induced_subgraph_E:
  !G tr. (induced_subgraph G tr).E = FDOM tr.edgemap
Proof
  rw[induced_subgraph_def]
QED

(* Domain is subset of G *)
Theorem induced_subgraph_V_SUBSET:
  !G tr. FDOM tr.nodemap SUBSET G.V ==>
    (induced_subgraph G tr).V SUBSET G.V
Proof
  rw[induced_subgraph_def]
QED

Theorem induced_subgraph_E_SUBSET:
  !G tr. FDOM tr.edgemap SUBSET G.E ==>
    (induced_subgraph G tr).E SUBSET G.E
Proof
  rw[induced_subgraph_def]
QED

(* For id_track: induced_subgraph equals G *)
Theorem induced_subgraph_id_track:
  !(G:hostgraph). FINITE G.V /\ FINITE G.E /\
    FDOM G.s = G.E /\ FDOM G.t = G.E /\
    FDOM G.l = G.V /\ FDOM G.m = G.E /\ FDOM G.p SUBSET G.V ==>
    induced_subgraph G (id_track G) = G
Proof
  rw[induced_subgraph_def, id_track_def, FUN_FMAP_DEF] >>
  rw[graph_component_equality] >>
  rw[fmap_EXT, DRESTRICT_DEF, FDOM_DRESTRICT] >>
  rw[EXTENSION] >> metis_tac[SUBSET_DEF]
QED

(* For composition: domain stays within original *)
Theorem FDOM_compose_SUBSET:
  !tr1 tr2.
    FDOM (compose_morphism tr2 tr1).nodemap SUBSET FDOM tr1.nodemap /\
    FDOM (compose_morphism tr2 tr1).edgemap SUBSET FDOM tr1.edgemap
Proof
  rw[compose_morphism_def, f_o_f_DEF, SUBSET_DEF]
QED

Theorem induced_subgraph_compose_SUBSET:
  !G tr1 tr2.
    (induced_subgraph G (compose_morphism tr2 tr1)).V SUBSET
      (induced_subgraph G tr1).V /\
    (induced_subgraph G (compose_morphism tr2 tr1)).E SUBSET
      (induced_subgraph G tr1).E
Proof
  rw[induced_subgraph_def] >>
  metis_tac[FDOM_compose_SUBSET]
QED

(* Key relationship: induced_subgraph G (track ...) has same V,E as deletion *)
Theorem induced_subgraph_track_V:
  !L Iface m G.
    FINITE (deletion_remaining_nodes L m Iface G) ==>
    (induced_subgraph G (track L Iface m G)).V = (deletion L Iface m G).V
Proof
  rw[induced_subgraph_def, FDOM_track_nodemap, deletion_def]
QED

Theorem induced_subgraph_track_E:
  !L Iface m G.
    FINITE (deletion_remaining_edges L m G) ==>
    (induced_subgraph G (track L Iface m G)).E = (deletion L Iface m G).E
Proof
  rw[induced_subgraph_def, FDOM_track_edgemap, deletion_def]
QED

(* The s and t fields also match *)
Theorem induced_subgraph_track_s:
  !L Iface m G.
    FINITE (deletion_remaining_edges L m G) ==>
    (induced_subgraph G (track L Iface m G)).s = (deletion L Iface m G).s
Proof
  rw[induced_subgraph_def, FDOM_track_edgemap, deletion_def]
QED

Theorem induced_subgraph_track_t:
  !L Iface m G.
    FINITE (deletion_remaining_edges L m G) ==>
    (induced_subgraph G (track L Iface m G)).t = (deletion L Iface m G).t
Proof
  rw[induced_subgraph_def, FDOM_track_edgemap, deletion_def]
QED

(* Additional id_track lemmas                                                *)

(* FRANGE of id_track nodemap is G.V *)
Theorem FRANGE_id_track_nodemap:
  !G. FINITE G.V ==> FRANGE (id_track G).nodemap = G.V
Proof
  rw[id_track_def]
QED

(* FRANGE of id_track edgemap is G.E *)
Theorem FRANGE_id_track_edgemap:
  !G. FINITE G.E ==> FRANGE (id_track G).edgemap = G.E
Proof
  rw[id_track_def]
QED

(* id_track nodemap is a bijection on G.V *)
Theorem id_track_nodemap_BIJ:
  !G. FINITE G.V ==> BIJ ($' (id_track G).nodemap) G.V G.V
Proof
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF, id_track_nodemap_apply] >>
  qexists_tac `x` >> simp[id_track_nodemap_apply]
QED

(* id_track edgemap is a bijection on G.E *)
Theorem id_track_edgemap_BIJ:
  !G. FINITE G.E ==> BIJ ($' (id_track G).edgemap) G.E G.E
Proof
  rw[BIJ_DEF, INJ_DEF, SURJ_DEF, id_track_edgemap_apply] >>
  qexists_tac `x` >> simp[id_track_edgemap_apply]
QED

(* Helper: composing a finite map with the identity map is the identity *)
Theorem f_o_f_identity:
  !S (f:'a |-> 'b). FINITE S /\ FDOM f SUBSET S ==> (f f_o_f FUN_FMAP I S = f)
Proof
  rpt strip_tac >> rw[fmap_EXT, f_o_f_DEF]
  >- (
    `!x. x IN S' ==> FUN_FMAP I S' ' x = x` by simp[FUN_FMAP_DEF] >>
    simp[EXTENSION] >> rpt strip_tac >> EQ_TAC >> rpt strip_tac >> gvs[]
    >- metis_tac[SUBSET_DEF]
    >- (fs[] >> first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
        rpt strip_tac >> gvs[] >> `x IN S'` by metis_tac[SUBSET_DEF] >> gvs[]))
  >- (`FUN_FMAP I S' ' x = x` by simp[FUN_FMAP_DEF] >> simp[])
QED

(* id_track is an injective morphism G -> G *)
Theorem id_track_is_inj_morphism:
  !(G:hostgraph). wf_hostgraph G ==>
    is_inj_morphism G (id_track G) G
Proof
  rpt strip_tac >>
  `FINITE G.V /\ FINITE G.E` by metis_tac[wf_hostgraph_IMP_finite_sets] >>
  simp[is_inj_morphism_def, is_inj_premorphism_def,
       is_morphism_def, is_premorphism_def, morphism_dom_ran_def,
       FDOM_id_track_nodemap, FDOM_id_track_edgemap,
       FRANGE_id_track_nodemap, FRANGE_id_track_edgemap,
       INJ_DEF, id_track_nodemap_apply, id_track_edgemap_apply] >>
  rpt conj_tac >>
  simp[preserve_source_def, preserve_target_def,
       preserve_defined_rootedness_def, preserve_edgelabels_def,
       preserve_nodelabels_def, id_track_def]
  (* preserve_source: FUN_FMAP I V f_o_f s = s f_o_f FUN_FMAP I E *)
  >- (`G.s f_o_f FUN_FMAP I G.E = G.s` by
        (irule f_o_f_identity >> fs[wf_hostgraph_def, wf_graph_def]) >>
      simp[] >> simp[fmap_EXT, cj 1 f_o_f_DEF, FUN_FMAP_DEF, EXTENSION] >>
      fs[wf_hostgraph_def, wf_graph_def] >>
      conj_tac
      >- (rw[] >> eq_tac >> rw[] >> fs[SUBSET_DEF, IN_FRANGE] >> metis_tac[])
      >- (rw[] >>
          `x IN FDOM (FUN_FMAP I G.V f_o_f G.s)` by
            (simp[cj 1 f_o_f_DEF, FUN_FMAP_DEF]) >>
          drule (cj 2 f_o_f_DEF) >> simp[FUN_FMAP_DEF]))
  (* preserve_target *)
  >- (`G.t f_o_f FUN_FMAP I G.E = G.t` by
        (irule f_o_f_identity >> fs[wf_hostgraph_def, wf_graph_def]) >>
      simp[] >> simp[fmap_EXT, cj 1 f_o_f_DEF, FUN_FMAP_DEF, EXTENSION] >>
      fs[wf_hostgraph_def, wf_graph_def] >>
      conj_tac
      >- (rw[] >> eq_tac >> rw[] >> fs[SUBSET_DEF, IN_FRANGE] >> metis_tac[])
      >- (rw[] >>
          `x IN FDOM (FUN_FMAP I G.V f_o_f G.t)` by
            (simp[cj 1 f_o_f_DEF, FUN_FMAP_DEF]) >>
          drule (cj 2 f_o_f_DEF) >> simp[FUN_FMAP_DEF]))
  (* preserve_defined_rootedness *)
  >- (simp[SUBMAP_DEF, cj 1 f_o_f_DEF, FUN_FMAP_DEF] >>
      fs[wf_hostgraph_def, wf_graph_def] >> rw[] >>
      simp[cj 2 f_o_f_DEF, FUN_FMAP_DEF] >>
      `x IN G.V` by metis_tac[SUBSET_DEF] >> simp[FUN_FMAP_DEF] >>
      `x IN FDOM (G.p f_o_f FUN_FMAP I G.V)` by
        (simp[cj 1 f_o_f_DEF, FUN_FMAP_DEF] >> metis_tac[SUBSET_DEF]) >>
      drule (cj 2 f_o_f_DEF) >> simp[FUN_FMAP_DEF] >>
      `x IN G.V` by metis_tac[SUBSET_DEF] >> simp[FUN_FMAP_DEF])
  (* preserve_edgelabels: m = m f_o_f FUN_FMAP I E *)
  >- (irule EQ_SYM >> irule f_o_f_identity >>
      fs[wf_hostgraph_def, wf_graph_def])
  (* preserve_nodelabels: l = l f_o_f FUN_FMAP I V *)
  >- (irule EQ_SYM >> irule f_o_f_identity >>
      fs[wf_hostgraph_def, wf_graph_def])
QED

(* id_track is a left identity for compose_morphism (morphismTheory version).
   Note: morphismTheory.compose_morphism m2 m1 = m2.nodemap f_o_f m1.nodemap
   So compose_morphism (id_track G) tr applies id to the RANGE of tr.
   This equals tr when FRANGE tr ⊆ G (the identity domain). *)
Theorem compose_morphism_id_track_left:
  !G tr. wf_hostgraph G /\
         FRANGE tr.nodemap SUBSET G.V /\
         FRANGE tr.edgemap SUBSET G.E ==>
         compose_morphism (id_track G) tr = tr
Proof
  rpt strip_tac >>
  simp[compose_morphism_def, id_track_def, morphism_component_equality] >>
  `FINITE G.V /\ FINITE G.E` by
    (drule wf_hostgraph_IMP_wf_graph >> simp[wf_graph_def]) >>
  conj_tac >> rw[fmap_EXT, f_o_f_DEF]
  >- (simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >>
      fs[SUBSET_DEF, FRANGE_DEF] >> metis_tac[])
  >- (`tr.nodemap ' x IN G.V` by (fs[SUBSET_DEF, FRANGE_DEF] >> metis_tac[]) >>
      simp[FUN_FMAP_DEF])
  >- (simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >>
      fs[SUBSET_DEF, FRANGE_DEF] >> metis_tac[])
  >- (`tr.edgemap ' x IN G.E` by (fs[SUBSET_DEF, FRANGE_DEF] >> metis_tac[]) >>
      simp[FUN_FMAP_DEF])
QED

(* id_track is a right identity for compose_morphism.
   compose_morphism tr (id_track G) applies id to the DOMAIN of tr.
   This equals tr when FDOM tr ⊆ G (the identity domain). *)
Theorem compose_morphism_id_track_right:
  !G tr. wf_hostgraph G /\
         FDOM tr.nodemap SUBSET G.V /\
         FDOM tr.edgemap SUBSET G.E ==>
         compose_morphism tr (id_track G) = tr
Proof
  rpt strip_tac >>
  simp[compose_morphism_def, id_track_def, morphism_component_equality] >>
  `FINITE G.V /\ FINITE G.E` by
    (drule wf_hostgraph_IMP_wf_graph >> simp[wf_graph_def]) >>
  conj_tac >> rw[fmap_EXT, f_o_f_DEF]
  >- (simp[EXTENSION] >> rw[] >> eq_tac >> rw[]
      >- gvs[FUN_FMAP_DEF]
      >- fs[SUBSET_DEF]
      >- (`x IN G.V` by fs[SUBSET_DEF] >> simp[FUN_FMAP_DEF]))
  >- simp[FUN_FMAP_DEF]
  >- (simp[EXTENSION] >> rw[] >> eq_tac >> rw[]
      >- gvs[FUN_FMAP_DEF]
      >- fs[SUBSET_DEF]
      >- (`x IN G.E` by fs[SUBSET_DEF] >> simp[FUN_FMAP_DEF]))
  >- simp[FUN_FMAP_DEF]
QED

val () = export_theory ()
