open HolKernel Parse bossLib boolLib
open finite_mapTheory pred_setTheory string_numTheory alistTheory arithmeticTheory intLib listTheory


open hostgraphTheory rulegraphTheory morphismTheory graphTheory taggingTheory

val () = new_theory "dpo";
(*
  Thesis Brian: Definition 2.15 (Dangling Condition). Given a rule ⟨L←K →R⟩and a
  graph G, an injective morphism g: L→G satisfies the dangling condition if
  no edge in EG−gE(EL) is incident to a node in gV(VL−VK).  *)

Definition satisfy_dangling_condition_remove_edges_def:
  satisfy_dangling_condition_remove_edges m L = IMAGE (FAPPLY m.edgemap) L.E
End
Definition satisfy_dangling_condition_remaining_edges_def:
  satisfy_dangling_condition_remaining_edges G m L = G.E DIFF satisfy_dangling_condition_remove_edges m L
End
Definition satisfy_dangling_condition_deleted_nodes_def:
  satisfy_dangling_condition_deleted_nodes m L Kv = IMAGE (FAPPLY m.nodemap) (L.V DIFF Kv)
End

Definition satisfy_dangling_condition_def:
  satisfy_dangling_condition L Kv m G =
    let removed_edges = IMAGE (FAPPLY m.edgemap) L.E in
    let remaining_edges = G.E DIFF removed_edges in
    let deleted_nodes = IMAGE (FAPPLY m.nodemap) (L.V DIFF Kv) in
    (!e. e IN remaining_edges ==>
         ~(G.s ' e IN deleted_nodes) /\
         ~(G.t ' e IN deleted_nodes))
End

Theorem satisfy_dangling_condition_alt:
  satisfy_dangling_condition L Kv m G =
    !e. e IN satisfy_dangling_condition_remaining_edges G m L ==>
         ~(G.s ' e IN satisfy_dangling_condition_deleted_nodes m L Kv) /\
         ~(G.t ' e IN satisfy_dangling_condition_deleted_nodes m L Kv)
Proof
  rw[satisfy_dangling_condition_def, satisfy_dangling_condition_remaining_edges_def,
  satisfy_dangling_condition_remove_edges_def, satisfy_dangling_condition_deleted_nodes_def]
QED

Definition is_match_def:
  is_match L Kv m G <=>
    is_inj_morphism L m G /\
    satisfy_dangling_condition L Kv m G
End


Theorem dangling_condition_IMP_FRANGE_s_excludes_deleted_nodes:
    wf_graph G /\ wf_graph L /\  Kv SUBSET L.V /\ satisfy_dangling_condition L Kv m G ==>
    FRANGE (DRESTRICT G.s (satisfy_dangling_condition_remaining_edges G m L))
      SUBSET G.V DIFF satisfy_dangling_condition_deleted_nodes m L Kv
Proof
  rpt strip_tac
 \\ `FDOM G.s = G.E /\ FRANGE G.s SUBSET G.V` by fs[wf_graph_def]
  \\ fs [satisfy_dangling_condition_alt, SUBSET_DEF]
  \\ gvs[FRANGE_DEF, DRESTRICT_DEF]
  \\ rw[]
  \\ RES_TAC
   \\ rw[]
QED


Definition deletion_deleted_nodes_def:
  deletion_deleted_nodes L m Kv = IMAGE (FAPPLY m.nodemap) (L.V DIFF Kv)
End

Definition deletion_remaining_nodes_def:
  deletion_remaining_nodes L m Kv G = G.V DIFF deletion_deleted_nodes L m Kv
End

Definition deletion_deleted_edges_def:
  deletion_deleted_edges L m = IMAGE (FAPPLY m.edgemap) L.E
End

Definition deletion_remaining_edges_def:
  deletion_remaining_edges L m G = G.E DIFF deletion_deleted_edges L m
End

Definition deletion_relabling_nodes_def:
  deletion_relabling_nodes L m Kv G = deletion_remaining_nodes L m Kv G DIFF IMAGE (FAPPLY m.nodemap) Kv
End

Theorem wf_hostgraph_IMP_finite_remaining_elements:
  !G l m Kv. wf_hostgraph G ==>
    FINITE (deletion_remaining_nodes L m Kv G) /\ FINITE (deletion_remaining_edges L m G)
Proof
  rw[wf_hostgraph_IMP_finite_sets, deletion_remaining_nodes_def, deletion_remaining_edges_def]
QED

Theorem deletion_remaining_elements_SUBSET_base:
  !L m Kv G. deletion_remaining_edges L m G SUBSET G.E /\
             deletion_remaining_nodes L m Kv G SUBSET G.V
Proof
  rw[deletion_remaining_edges_def, deletion_remaining_nodes_def]
QED

Theorem dangling_condition_IMP_endpoint_range_in_remaining_nodes:
  !G L Kv m. wf_graph G /\ wf_graph L /\ satisfy_dangling_condition L Kv m G
    ==> FRANGE (DRESTRICT G.s (deletion_remaining_edges L m G)) SUBSET deletion_remaining_nodes L m Kv G /\
        FRANGE (DRESTRICT G.t (deletion_remaining_edges L m G)) SUBSET deletion_remaining_nodes L m Kv G
Proof
     rw[deletion_remaining_edges_def, deletion_remaining_nodes_def]
  \\ fs[wf_graph_def,SUBSET_DEF, FRANGE_DEF, DRESTRICT_DEF]
  \\ rw[]
  \\ gvs[deletion_deleted_edges_def, deletion_deleted_nodes_def, satisfy_dangling_condition_def]
  \\ RES_TAC
  \\ rw[]
QED

Theorem dangling_condition_IMP_rootedness_domain_subset_remaining:
  !G L m Kv. wf_graph L /\ satisfy_dangling_condition L Kv m G
    ==> FDOM (DRESTRICT G.p (deletion_relabling_nodes L m Kv G)) SUBSET deletion_remaining_nodes L m Kv G
Proof
  rw[deletion_relabling_nodes_def, SUBSET_DEF]
  \\ rw[dangling_condition_IMP_endpoint_range_in_remaining_nodes]
  \\ fs[FDOM_DRESTRICT]
QED

Theorem DRESTRICT_relabelling_domain_subset_remaining_nodes:
  !L m Kv G f. FDOM (DRESTRICT f (deletion_relabling_nodes L m Kv G)) SUBSET deletion_remaining_nodes L m Kv G
Proof
  rw[deletion_relabling_nodes_def, FDOM_DRESTRICT, SUBSET_DEF]
QED

Theorem wf_graph_IMP_deletion_remaining_SUBSET_base:
  !L m Kv G. wf_graph G ==>
    deletion_remaining_nodes L m Kv G SUBSET G.V /\
    deletion_remaining_edges L m G SUBSET G.E
Proof
  rw [deletion_remaining_nodes_def,deletion_remaining_edges_def]
QED

Theorem IMAGE_DISJOINT_SUBSET:
  A' SUBSET A /\ B' SUBSET B /\ IMAGE f A INTER IMAGE g B = {}
    ==> IMAGE f A' INTER IMAGE g B' = {}
Proof
  rw [EXTENSION, IN_IMAGE, IN_INTER, NOT_IN_EMPTY, SUBSET_DEF] >>
  metis_tac []
QED

Theorem deletion_remaining_elements_uniqueness:
  !G L m Kv. wf_graph (G: ('a,'b) graph) /\ wf_graph (L: ('a,'b) graph) /\ is_premorphism L m G ==>
    IMAGE dest_nodeid (deletion_remaining_nodes L m Kv G) INTER
    IMAGE dest_edgeid (deletion_remaining_edges L m G) = {}
Proof
  rpt strip_tac
  \\ `item_uniqueness G` by (fs[wf_graph_def])
  \\ fs[item_uniqueness_def]
  \\ irule IMAGE_DISJOINT_SUBSET
  \\ qexistsl [`G.V`, `G.E`]
  \\ rw[deletion_remaining_nodes_def, deletion_remaining_edges_def]
QED

Definition deletion_def:
  deletion (L:hostgraph) (Kv: nodeid set) m (G: hostgraph): hostgraph =
    let VD = deletion_remaining_nodes L m Kv G in
    let ED = deletion_remaining_edges L m G in
    <| V := VD;
       E := ED;
       s := DRESTRICT G.s ED;
       t := DRESTRICT G.t ED;
       m := DRESTRICT G.m ED;
       l := DRESTRICT G.l (deletion_relabling_nodes L m Kv G);
       p := DRESTRICT G.p (deletion_relabling_nodes L m Kv G)
    |>
End

Theorem deletion_preserves_wf_graph:
  !G L Kv m. wf_hostgraph G /\ wf_hostgraph L /\ Kv SUBSET L.V /\ is_match L Kv m G
    ==> wf_partial_hostgraph (deletion L Kv m G)
Proof
  rpt strip_tac
  \\ rw[wf_partial_hostgraph_def, wf_graph_def, deletion_def]
  \\ rw[wf_hostgraph_IMP_finite_remaining_elements]
  >- (
        irule wf_graph_IMP_FDOM_DRESTRICT_s_eq
    \\ rw[wf_hostgraph_IMP_wf_graph]
    \\ rw[deletion_remaining_elements_SUBSET_base]
  )
  >- (
    fs[is_match_def, wf_hostgraph_IMP_wf_graph, dangling_condition_IMP_endpoint_range_in_remaining_nodes]
  )
  >- (
        irule wf_graph_IMP_FDOM_DRESTRICT_t_eq
    \\ rw[wf_hostgraph_IMP_wf_graph]
    \\ rw[deletion_remaining_elements_SUBSET_base]
  )
  >- (
    fs[is_match_def, wf_hostgraph_IMP_wf_graph, dangling_condition_IMP_endpoint_range_in_remaining_nodes]
  )

  >- (
    fs[is_match_def, wf_hostgraph_IMP_wf_graph,dangling_condition_IMP_rootedness_domain_subset_remaining]
  )

  >- (
    fs[is_match_def, is_inj_morphism_def, is_morphism_def, wf_hostgraph_def, item_uniqueness_def ,deletion_remaining_elements_uniqueness]
  )

  >- (
    rw[DRESTRICT_relabelling_domain_subset_remaining_nodes]
  )

  >- (
       irule wf_graph_IMP_FDOM_DRESTRICT_m_eq
    \\ rw[deletion_remaining_elements_SUBSET_base]
  )

  (* hostgraph_labels_spine: preserved via DRESTRICT *)
  >- (
    fs[hostgraph_labels_spine_def, wf_hostgraph_def] >>
    conj_tac >| [
      irule FEVERY_SUBMAP >> qexists_tac `G.l` >> simp[DRESTRICT_SUBMAP],
      irule FEVERY_SUBMAP >> qexists_tac `G.m` >> simp[DRESTRICT_SUBMAP]
    ]
  )
QED

(* Helper: FEVERY over FEMPTY |++ kvl reduces to EVERY over kvl *)
Theorem FEVERY_FEMPTY_FUPDATE_LIST:
  !P kvl. ALL_DISTINCT (MAP FST kvl) ==> (FEVERY P (FEMPTY |++ kvl) <=> EVERY P kvl)
Proof
  rpt strip_tac >>
  drule FEVERY_FUPDATE_LIST >>
  disch_then (qspecl_then [`FEMPTY`, `P`] mp_tac) >>
  simp[DRESTRICT_FEMPTY, FEVERY_FEMPTY]
QED

(* Helper lemma: interface nodes (mapped by m) remain in the deletion result *)
Theorem interface_nodes_in_deletion:
  !G L Kv m n. wf_hostgraph G /\ wf_hostgraph L /\ Kv SUBSET L.V /\
               is_match L Kv m G /\ n IN Kv
    ==> m.nodemap ' n IN (deletion L Kv m G).V
Proof
  rpt strip_tac
  \\ fs[deletion_def, deletion_remaining_nodes_def, deletion_deleted_nodes_def]
  \\ fs[is_match_def, is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]
  \\ conj_tac
  >- (
    `n IN L.V` by fs[SUBSET_DEF]
    \\ `m.nodemap ' n IN FRANGE m.nodemap` by (fs[FRANGE_DEF] >> metis_tac[])
    \\ fs[SUBSET_DEF]
  )
  >- (
    rw[] >> rpt strip_tac
    \\ Cases_on `x IN L.V`
    >- (
      DISJ2_TAC
      \\ `n = x` by (fs[INJ_DEF] >> first_x_assum irule >> fs[SUBSET_DEF])
      \\ fs[]
    )
    >- (DISJ1_TAC >> fs[])
  )
QED

Definition nodeid_coprod_def:
  nodeid_coprod (a: nodeid set) (b: nodeid set) =
    IMAGE tag_nodeid_left a UNION IMAGE tag_nodeid_right b
End

Definition edgeid_coprod_def:
  edgeid_coprod (a: edgeid set) (b: edgeid set) =
    IMAGE tag_edgeid_left a UNION IMAGE tag_edgeid_right b
End

Theorem coprod_finite:
  (!A B. FINITE A /\ FINITE B ==> FINITE (nodeid_coprod A B)) /\
  (!A B. FINITE A /\ FINITE B  ==> FINITE (edgeid_coprod A B))
Proof
  rw[nodeid_coprod_def, edgeid_coprod_def]
QED


Theorem tag_nodeid_coprod_membership:
 (!x A B. tag_nodeid_left x IN nodeid_coprod A B <=> x IN A) /\
 (!x A B. tag_nodeid_right x IN nodeid_coprod A B <=> x IN B)
Proof
  assume_tac INJ_tag_nodeid
  \\ rw[nodeid_coprod_def, INJ_DEF]
  \\ EQ_TAC
  \\ metis_tac[tag_disjoint]
QED

Theorem tag_edgeid_coprod_membership:
 (!x A B. tag_edgeid_left x IN edgeid_coprod A B <=> x IN A) /\
 (!x A B. tag_edgeid_right x IN edgeid_coprod A B <=> x IN B)
Proof
  assume_tac INJ_tag_edgeid
  \\ rw[edgeid_coprod_def, INJ_DEF]
  \\ EQ_TAC
  \\ metis_tac[tag_disjoint]
QED

Definition gluing_nodes_def:
  gluing_nodes H Kv R = nodeid_coprod H.V (R.V DIFF Kv)
End

Definition gluing_edges_def:
  gluing_edges H R = edgeid_coprod H.E R.E
End

Theorem finite_gluing_nodes_edges:
  !H R. wf_graph H /\ wf_graph R
    ==> FINITE (gluing_edges H R) /\ (!Kv. FINITE (gluing_nodes H Kv R))
Proof
  rw[gluing_edges_def, gluing_nodes_def]
  \\ fs[wf_graph_def, coprod_finite]
QED

Definition gluing_s_mapping_def:
  gluing_s_mapping H R d Kv eid =
    let ueid = untag_edgeid eid in
    if is_left_tagged_edgeid eid
    then (eid, tag_nodeid_left (H.s ' ueid))
    else let sn = R.s ' ueid in
        if sn IN Kv
        then (eid, tag_nodeid_left (d.nodemap ' sn))
        else (eid, tag_nodeid_right sn)
End

Theorem FST_gluing_s_mapping_in_domain:
  !H R m Kv e. FST (gluing_s_mapping H R m Kv e) = e
Proof
  rpt strip_tac
  \\ fs[gluing_edges_def, gluing_s_mapping_def]
  \\ Cases_on `is_left_tagged_edgeid e`
  \\ fs[]
  \\ Cases_on `R.s ' (untag_edgeid e) ∈ Kv `
  \\ fs[]
QED

Theorem gluing_s_mapping_INJ:
  !H R d Kv. INJ (gluing_s_mapping H R d Kv) (gluing_edges H R) UNIV
Proof
  rw[INJ_DEF]
  \\ metis_tac [FST_gluing_s_mapping_in_domain]
QED


Definition gluing_s_def:
  gluing_s Kv d H R = alist_to_fmap (MAP (gluing_s_mapping H R d Kv) (SET_TO_LIST $ gluing_edges H R))
End

Theorem IMAGE_MAP:
  ∀f g xs. IMAGE f (set (MAP g xs)) = { f (g x) | x ∈ set xs }
Proof
  rw[EXTENSION, IMAGE_DEF, MEM_MAP]
  \\ metis_tac[]
QED

Theorem untag_edgeid_coprod_membership:
  (!x A B. x IN edgeid_coprod A B /\ is_left_tagged_edgeid x ==> untag_edgeid x IN A) /\
  (!x A B. x IN edgeid_coprod A B /\ is_right_tagged_edgeid x ==> untag_edgeid x IN B)
Proof
  rpt strip_tac
  \\ fs[edgeid_coprod_def]
  \\ fs[is_tagged_iff_exists]
  \\ metis_tac[tag_edgeid_coprod_membership]
QED

Theorem SND_gluing_s_mapping_in_gluing_nodes:
  !x H R m Kv. x IN gluing_edges H R /\ wf_graph H /\ wf_graph R /\
               (!n. n IN Kv ==> m.nodemap ' n IN H.V)
    ==> SND (gluing_s_mapping H R m Kv x) IN gluing_nodes H Kv R
Proof
  rpt strip_tac
  \\ fs[gluing_edges_def, gluing_s_mapping_def]
  \\ Cases_on `is_left_tagged_edgeid x`
  >- (
    rw[]
    \\ drule (CONJUNCT1 untag_edgeid_coprod_membership) >> rw[]
    \\ `H.s ' (untag_edgeid x) IN H.V` by (fs[wf_graph_def, FRANGE_DEF, SUBSET_DEF] >> metis_tac[])
    \\ rw[gluing_nodes_def, tag_nodeid_coprod_membership]
  )
  >- (
    rw[]
    >- (
      (* source node is in interface Kv, use morphism m *)
      rw[gluing_nodes_def, tag_nodeid_coprod_membership]
    )
    >- (
      (* source node is NOT in interface, it's in R.V DIFF Kv *)
      rw[gluing_nodes_def, tag_nodeid_coprod_membership]
      \\ drule (CONJUNCT2 untag_edgeid_coprod_membership)
      \\ `is_right_tagged_edgeid x` by (fs[is_left_tagged_edgeid_def, is_right_tagged_edgeid_def] >> metis_tac[ODD_EVEN])
      \\ rw[]
      \\ fs[wf_graph_def, FRANGE_DEF, SUBSET_DEF] >> metis_tac[]
    )
  )
QED


Definition gluing_t_def:
  gluing_t E Kv (d:morphism) (H: hostgraph) (R: hostgraph) =
    let
      entries =
        MAP (\eid. let
            ueid = untag_edgeid eid
            in
              if is_left_tagged_edgeid eid then
               (eid, tag_nodeid_left (H.t ' ueid))
              else
                let sn = R.t ' (untag_edgeid eid) in
               if sn IN Kv then
                 (eid, tag_nodeid_left (d.nodemap ' sn))
               else
                 (eid, tag_nodeid_right sn)
          )
          (SET_TO_LIST E)
    in
      FEMPTY |++ entries
End


(* gluing_l: Assigns labels to nodes in the glued graph.
   - Left-tagged nodes from H.V:
     - If the node is an interface node (in IMAGE m.nodemap Kv), get label from R
       via the inverse mapping: find k in Kv such that m.nodemap ' k = untag nid
     - Otherwise, get label from H.l
   - Right-tagged nodes from R.V DIFF Kv: get label from R.l

   This matches the thesis (Proposition 5): l_H(v) = l_R(v) if v in V_R. *)
Definition gluing_l_def:
  gluing_l V Kv (m: morphism) (H: hostgraph) (R: hostgraph) = let
    kv = MAP (\nid.
      if is_left_tagged_nodeid nid then
        let unid = untag_nodeid nid in
        (* Check if this is an interface node *)
        if ?k. k IN Kv /\ m.nodemap ' k = unid then
          (* Interface node: get label from R via inverse mapping *)
          let k = @k. k IN Kv /\ m.nodemap ' k = unid in
          (nid, R.l ' k)
        else
          (* Non-interface node from H *)
          (nid, H.l ' unid)
      else
        (* Right-tagged: get label from R *)
        (nid, R.l ' (untag_nodeid nid))
    ) (SET_TO_LIST V)
    in FEMPTY |++ kv
End

Definition gluing_m_def:
  gluing_m E (H: hostgraph) (R: hostgraph) = let
    ke = MAP (\eid. if is_left_tagged_edgeid eid
                        then (eid, H.m ' (untag_edgeid eid))
                        else (eid, R.m ' (untag_edgeid eid))
             ) (SET_TO_LIST E)
    in FEMPTY |++ ke
End


(* gluing_p: Assigns rootedness to nodes in the glued graph.
   Same structure as gluing_l - interface nodes get rootedness from R. *)
Definition gluing_p_def:
  gluing_p V Kv (m: morphism) (H: hostgraph) (R: hostgraph) = let
    kv = MAP (\nid.
      if is_left_tagged_nodeid nid then
        let unid = untag_nodeid nid in
        if ?k. k IN Kv /\ m.nodemap ' k = unid then
          let k = @k. k IN Kv /\ m.nodemap ' k = unid in
          (nid, R.p ' k)
        else
          (nid, H.p ' unid)
      else
        (nid, R.p ' (untag_nodeid nid))
    ) (SET_TO_LIST V)
    in FEMPTY |++ kv
End

Definition gluing_def:
  gluing (R:hostgraph) (Kv: nodeid set) (m: morphism) (H:hostgraph): hostgraph = let
    Vg = gluing_nodes H Kv R;
    Eg = gluing_edges H R
    in
    <| V := Vg;
       E := Eg;
       t := gluing_t Eg Kv m H R;
       s := gluing_s Kv m H R;
       m := gluing_m Eg H R;
       l := gluing_l Vg Kv m H R;
       p := gluing_p Vg Kv m H R
    |>
End

Theorem gluing_FINITE:
  !H R Kv. wf_graph H /\ wf_graph R ==> FINITE (gluing_nodes H Kv R) /\FINITE (gluing_edges H R)
Proof
  rw[wf_graph_def, gluing_nodes_def, gluing_edges_def]
  \\ fs[coprod_finite]
QED

Theorem MAP_FST_gluing_s_mapping_id:
  !H R m Kv. MAP FST (MAP (gluing_s_mapping H R m Kv) (SET_TO_LIST (gluing_edges H R))) = (SET_TO_LIST (gluing_edges H R))
Proof
  rpt strip_tac
  \\ rw[MAP_COMPOSE, combinTheory.o_DEF]
  \\ rw[FST_gluing_s_mapping_in_domain]
QED

Theorem FRANGE_gluing:
  !R Kb m L G Kv. wf_hostgraph G /\ wf_hostgraph L /\ Kv ⊆ L.V /\ is_match L Kv m G /\ wf_graph R
    ==> FRANGE (gluing R Kv m (deletion L Kv m G)).s SUBSET (gluing R Kv m (deletion L Kv m G)).V
Proof
  rpt strip_tac
  \\ qabbrev_tac `H = deletion L Kv m G`
  \\ `wf_partial_hostgraph H` by (unabbrev_all_tac >> irule deletion_preserves_wf_graph >> rw[])
  \\ `wf_graph H` by fs[wf_partial_hostgraph_def]
  \\ rw[gluing_def, SUBSET_DEF]
  \\ fs[gluing_s_def]
  \\ `x IN IMAGE SND (set (MAP (gluing_s_mapping H R m Kv) (SET_TO_LIST (gluing_edges H R))))` by (
    imp_res_tac (REWRITE_RULE [SUBSET_DEF] FRANGE_alist_to_fmap_SUBSET) >> fs[]
  )
  \\ fs[IN_IMAGE]
  \\ fs[MEM_MAP]
  \\ irule SND_gluing_s_mapping_in_gluing_nodes
  \\ rw[]
  >- (unabbrev_all_tac >> irule interface_nodes_in_deletion >> rw[])
  >- (
    fs[MEM_SET_TO_LIST]
    \\ `FINITE (gluing_edges H R)` by fs[gluing_FINITE]
    \\ fs[MEM_SET_TO_LIST]
  )
QED

Theorem FDOM_gluing_s_GLUING_EDGES:
  !H R Kv d. wf_graph H /\ wf_graph R ==> FDOM (gluing_s Kv d H R) = gluing_edges H R
Proof
  rpt strip_tac
  \\ rw[gluing_s_def]
  \\ rw[MAP_FST_gluing_s_mapping_id]
  \\ irule SET_TO_LIST_INV
  \\ rw[gluing_edges_def]
  \\ irule (CONJUNCT2 coprod_finite)
  \\ fs[wf_graph_def]
QED

(* Key lemma: applying gluing_s to a left-tagged edge gives left-tagged source *)
Theorem gluing_s_apply_left_tagged:
  !H R d Kv e. e IN H.E /\ wf_graph H /\ wf_graph R ==>
    (gluing_s Kv d H R) ' (tag_edgeid_left e) = tag_nodeid_left (H.s ' e)
Proof
  rpt strip_tac
  \\ rw[gluing_s_def]
  \\ irule alistTheory.ALOOKUP_SOME_FAPPLY_alist_to_fmap
  \\ irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM
  \\ conj_tac
  (* ALL_DISTINCT (MAP FST ...) *)
  >- (
    rw[MAP_FST_gluing_s_mapping_id]
    \\ irule ALL_DISTINCT_SET_TO_LIST
    \\ rw[gluing_edges_def, edgeid_coprod_def]
    \\ fs[wf_graph_def]
  )
  (* MEM (tag_edgeid_left e, tag_nodeid_left (H.s ' e)) ... *)
  \\ rw[MEM_MAP]
  \\ qexists_tac `tag_edgeid_left e`
  \\ conj_tac
  >- rw[gluing_s_mapping_def, correct_tagging, tag_untag_edgeid_inv]
  >- (
    `FINITE (gluing_edges H R)` by (rw[gluing_edges_def, edgeid_coprod_def] \\ fs[wf_graph_def])
    \\ fs[MEM_SET_TO_LIST]
    \\ rw[gluing_edges_def, edgeid_coprod_def]
  )
QED

(* Key lemma: applying gluing_t to a left-tagged edge gives left-tagged target *)
Theorem gluing_t_apply_left_tagged:
  !H R d Kv e. e IN H.E /\ wf_graph H /\ wf_graph R /\ FINITE (gluing_edges H R) ==>
    (gluing_t (gluing_edges H R) Kv d H R) ' (tag_edgeid_left e) = tag_nodeid_left (H.t ' e)
Proof
  rpt strip_tac
  \\ qabbrev_tac `entries = (MAP (λeid. let ueid = untag_edgeid eid in
                                         if is_left_tagged_edgeid eid then (eid,tag_nodeid_left (H.t ' ueid))
                                         else let sn = R.t ' ueid in
                                              if sn ∈ Kv then (eid,tag_nodeid_left (d.nodemap ' sn))
                                              else (eid,tag_nodeid_right sn))
                                  (SET_TO_LIST (gluing_edges H R)))`
  \\ `ALL_DISTINCT (MAP FST entries)` by (
    unabbrev_all_tac
    \\ rw[MAP_MAP_o, combinTheory.o_DEF]
    \\ simp[COND_RAND, pairTheory.FST]
    \\ irule ALL_DISTINCT_SET_TO_LIST
    \\ fs[]
  )
  \\ `MEM (tag_edgeid_left e, tag_nodeid_left (H.t ' e)) entries` by (
    unabbrev_all_tac
    \\ rw[MEM_MAP]
    \\ qexists_tac `tag_edgeid_left e`
    \\ conj_tac
    >- rw[correct_tagging, tag_untag_edgeid_inv]
    >- rw[MEM_SET_TO_LIST, gluing_edges_def, edgeid_coprod_def]
  )
  \\ `FLOOKUP (FEMPTY |++ entries) (tag_edgeid_left e) = SOME (tag_nodeid_left (H.t ' e))` by (
    irule alistTheory.mem_to_flookup
    \\ rw[]
  )
  \\ fs[flookup_thm, FDOM_FUPDATE_LIST]
  \\ pop_assum mp_tac
  \\ simp[gluing_t_def, LET_DEF]
QED

(* Key lemma: applying gluing_m to a left-tagged edge gives H's mark *)
Theorem gluing_m_apply_left_tagged:
  !H R e. e IN H.E /\ wf_graph H /\ wf_graph R /\ FINITE (gluing_edges H R) ==>
    (gluing_m (gluing_edges H R) H R) ' (tag_edgeid_left e) = H.m ' e
Proof
  rpt strip_tac
  \\ qabbrev_tac `entries = MAP (λeid. if is_left_tagged_edgeid eid
                                       then (eid,H.m ' (untag_edgeid eid))
                                       else (eid,R.m ' (untag_edgeid eid)))
                                (SET_TO_LIST (gluing_edges H R))`
  \\ `ALL_DISTINCT (MAP FST entries)` by (
    unabbrev_all_tac
    \\ rw[MAP_MAP_o, combinTheory.o_DEF]
    \\ simp[COND_RAND, pairTheory.FST]
    \\ irule ALL_DISTINCT_SET_TO_LIST
    \\ fs[]
  )
  \\ `MEM (tag_edgeid_left e, H.m ' e) entries` by (
    unabbrev_all_tac
    \\ rw[MEM_MAP]
    \\ qexists_tac `tag_edgeid_left e`
    \\ conj_tac
    >- rw[correct_tagging, tag_untag_edgeid_inv]
    >- rw[MEM_SET_TO_LIST, gluing_edges_def, edgeid_coprod_def]
  )
  \\ `FLOOKUP (FEMPTY |++ entries) (tag_edgeid_left e) = SOME (H.m ' e)` by (
    irule alistTheory.mem_to_flookup
    \\ rw[]
  )
  \\ fs[flookup_thm, FDOM_FUPDATE_LIST]
  \\ pop_assum mp_tac
  \\ simp[gluing_m_def, LET_DEF]
QED

(* Key lemma: applying gluing_l to a left-tagged non-interface node gives H's label *)
Theorem gluing_l_apply_left_tagged:
  !H R m Kv n.
    n IN H.V /\ wf_graph H /\ wf_graph R /\
    FINITE (gluing_nodes H Kv R) /\
    ~(?k. k IN Kv /\ m.nodemap ' k = n) ==>
    (gluing_l (gluing_nodes H Kv R) Kv m H R) ' (tag_nodeid_left n) = H.l ' n
Proof
  rpt strip_tac
  \\ qabbrev_tac `V = gluing_nodes H Kv R`
  \\ qabbrev_tac `entries = MAP (λnid.
       if is_left_tagged_nodeid nid then
         let unid = untag_nodeid nid in
         if ∃k. k ∈ Kv ∧ m.nodemap ' k = unid
         then (nid,R.l ' (@k. k ∈ Kv ∧ m.nodemap ' k = unid))
         else (nid,H.l ' unid)
       else (nid,R.l ' (untag_nodeid nid))) (SET_TO_LIST V)`
  \\ `ALL_DISTINCT (MAP FST entries)` by (
    unabbrev_all_tac
    \\ rw[MAP_MAP_o, combinTheory.o_DEF]
    \\ simp[COND_RAND, pairTheory.FST]
    \\ irule ALL_DISTINCT_SET_TO_LIST
    \\ fs[]
  )
  \\ `MEM (tag_nodeid_left n, H.l ' n) entries` by (
    unabbrev_all_tac
    \\ rw[MEM_MAP]
    \\ qexists_tac `tag_nodeid_left n`
    \\ conj_tac
    >- rw[correct_tagging, tag_untag_nodeid_inv]
    >- rw[MEM_SET_TO_LIST, gluing_nodes_def, tag_nodeid_coprod_membership]
  )
  \\ `FLOOKUP (FEMPTY |++ entries) (tag_nodeid_left n) = SOME (H.l ' n)` by (
    irule alistTheory.mem_to_flookup
    \\ rw[]
  )
  \\ fs[flookup_thm, FDOM_FUPDATE_LIST]
  \\ pop_assum mp_tac
  \\ simp[gluing_l_def, LET_DEF, Abbr `V`, Abbr `entries`]
QED

(* Key lemma: applying gluing_p to a left-tagged non-interface node gives H's rootedness *)
Theorem gluing_p_apply_left_tagged:
  !H R m Kv n.
    n IN H.V /\ wf_graph H /\ wf_graph R /\
    FINITE (gluing_nodes H Kv R) /\
    ~(?k. k IN Kv /\ m.nodemap ' k = n) ==>
    (gluing_p (gluing_nodes H Kv R) Kv m H R) ' (tag_nodeid_left n) = H.p ' n
Proof
  rpt strip_tac
  \\ qabbrev_tac `V = gluing_nodes H Kv R`
  \\ qabbrev_tac `entries = MAP (λnid.
       if is_left_tagged_nodeid nid then
         let unid = untag_nodeid nid in
         if ∃k. k ∈ Kv ∧ m.nodemap ' k = unid
         then (nid,R.p ' (@k. k ∈ Kv ∧ m.nodemap ' k = unid))
         else (nid,H.p ' unid)
       else (nid,R.p ' (untag_nodeid nid))) (SET_TO_LIST V)`
  \\ `ALL_DISTINCT (MAP FST entries)` by (
    unabbrev_all_tac
    \\ rw[MAP_MAP_o, combinTheory.o_DEF]
    \\ simp[COND_RAND, pairTheory.FST]
    \\ irule ALL_DISTINCT_SET_TO_LIST
    \\ fs[]
  )
  \\ `MEM (tag_nodeid_left n, H.p ' n) entries` by (
    unabbrev_all_tac
    \\ rw[MEM_MAP]
    \\ qexists_tac `tag_nodeid_left n`
    \\ conj_tac
    >- rw[correct_tagging, tag_untag_nodeid_inv]
    >- rw[MEM_SET_TO_LIST, gluing_nodes_def, tag_nodeid_coprod_membership]
  )
  \\ `FLOOKUP (FEMPTY |++ entries) (tag_nodeid_left n) = SOME (H.p ' n)` by (
    irule alistTheory.mem_to_flookup
    \\ rw[]
  )
  \\ fs[flookup_thm, FDOM_FUPDATE_LIST]
  \\ pop_assum mp_tac
  \\ simp[gluing_p_def, LET_DEF, Abbr `V`, Abbr `entries`]
QED

(* Helper for gluing_t: FDOM *)
Theorem FDOM_gluing_t:
  !E Kv d H R. FINITE E ==> FDOM (gluing_t E Kv d H R) = E
Proof
  rpt strip_tac
  \\ rw[gluing_t_def, LET_DEF, FDOM_FUPDATE_LIST]
  \\ rw[MAP_MAP_o, combinTheory.o_DEF]
  \\ simp[COND_RAND, pairTheory.FST]
  \\ simp[SET_TO_LIST_INV]
QED

(* Helper for gluing_t: FRANGE subset - analogous to FRANGE_gluing for source *)
Theorem FRANGE_gluing_t:
  !R L G Kv m. wf_hostgraph G /\ wf_hostgraph L /\ Kv ⊆ L.V /\ is_match L Kv m G /\ wf_graph R
    ==> FRANGE (gluing R Kv m (deletion L Kv m G)).t SUBSET (gluing R Kv m (deletion L Kv m G)).V
Proof
  rpt strip_tac
  \\ qabbrev_tac `H = deletion L Kv m G`
  \\ `wf_partial_hostgraph H` by (unabbrev_all_tac >> irule deletion_preserves_wf_graph >> rw[])
  \\ `wf_graph H` by fs[wf_partial_hostgraph_def]
  \\ rw[gluing_def, SUBSET_DEF, gluing_t_def, LET_DEF]
  \\ `FINITE (gluing_edges H R)` by (imp_res_tac gluing_FINITE >> fs[])
  \\ qpat_x_assum `x IN FRANGE _` mp_tac
  \\ rw[Once (REWRITE_RULE [SUBSET_DEF] FRANGE_FUPDATE_LIST_SUBSET)]
  \\ fs[FRANGE_FEMPTY, MEM_MAP]
  \\ imp_res_tac (REWRITE_RULE [SUBSET_DEF] FRANGE_FUPDATE_LIST_SUBSET)
  \\ gvs[FRANGE_FEMPTY]
  \\ gvs[MEM_MAP]
  \\ Cases_on `is_left_tagged_edgeid eid` >> fs[]
  >- (
    rw[gluing_nodes_def, tag_nodeid_coprod_membership]
    \\ fs[gluing_edges_def]
    \\ imp_res_tac (CONJUNCT1 untag_edgeid_coprod_membership)
    \\ fs[wf_graph_def]
    \\ `H.t ' (untag_edgeid eid) IN FRANGE H.t` by (rw[FRANGE_DEF] >> qexists `untag_edgeid eid` >> fs[])
    \\ fs[SUBSET_DEF]
  )
  >- (
    Cases_on `R.t ' (untag_edgeid eid) IN Kv` >> fs[]
    >- (
      rw[gluing_nodes_def, tag_nodeid_coprod_membership]
      \\ unabbrev_all_tac
      \\ rw[deletion_def, LET_DEF, deletion_remaining_nodes_def]
      >- (
        fs[is_match_def, is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]
        \\ `R.t ' (untag_edgeid eid) IN FDOM m.nodemap` by fs[SUBSET_DEF]
        \\ metis_tac[FRANGE_FLOOKUP, FLOOKUP_DEF, SUBSET_DEF]
      )
      >- (
        rw[deletion_deleted_nodes_def]
        \\ fs[is_match_def, is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]
        \\ Cases_on `x IN L.V`
        >- (fs[] \\ `R.t ' (untag_edgeid eid) = x` by fs[INJ_DEF, SUBSET_DEF] \\ fs[])
        >- fs[]
      )
    )
    >- (
      rw[gluing_nodes_def, tag_nodeid_coprod_membership]
      \\ fs[gluing_edges_def]
      \\ `is_right_tagged_edgeid eid` by fs[is_left_tagged_edgeid_def, is_right_tagged_edgeid_def, ODD_EVEN]
      \\ imp_res_tac (CONJUNCT2 untag_edgeid_coprod_membership)
      \\ fs[wf_graph_def]
      \\ metis_tac[FRANGE_FLOOKUP, FLOOKUP_DEF, SUBSET_DEF]
    )
  )
QED

(* Helper for gluing_l: FDOM *)
Theorem FDOM_gluing_l:
  !V Kv m H R. FINITE V ==> FDOM (gluing_l V Kv m H R) = V
Proof
  rpt strip_tac
  \\ rw[gluing_l_def, LET_DEF, FDOM_FUPDATE_LIST]
  \\ rw[MAP_MAP_o, combinTheory.o_DEF]
  \\ `MAP (\nid. FST (if is_left_tagged_nodeid nid then
        if ?k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid then
          (nid, R.l ' (@k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid))
        else (nid, H.l ' (untag_nodeid nid))
      else (nid, R.l ' (untag_nodeid nid)))) (SET_TO_LIST V) =
     MAP (\nid. nid) (SET_TO_LIST V)` by (
    rw[MAP_EQ_f] >> rw[])
  \\ fs[MAP_ID]
  \\ simp[SET_TO_LIST_INV]
QED

(* Helper for gluing_m: FDOM *)
Theorem FDOM_gluing_m:
  !E H R. FINITE E ==> FDOM (gluing_m E H R) = E
Proof
  rpt strip_tac
  \\ rw[gluing_m_def, LET_DEF, FDOM_FUPDATE_LIST]
  \\ rw[MAP_MAP_o, combinTheory.o_DEF]
  \\ simp[COND_RAND, pairTheory.FST]
  \\ simp[SET_TO_LIST_INV]
QED

(* Helper for gluing_p: FDOM SUBSET *)
Theorem FDOM_gluing_p_SUBSET:
  !V Kv m H R. FINITE V ==> FDOM (gluing_p V Kv m H R) SUBSET V
Proof
  rpt strip_tac
  \\ rw[gluing_p_def, LET_DEF, FDOM_FUPDATE_LIST]
  \\ rw[MAP_MAP_o, combinTheory.o_DEF]
  \\ `MAP (\nid. FST (if is_left_tagged_nodeid nid then
        if ?k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid then
          (nid, R.p ' (@k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid))
        else (nid, H.p ' (untag_nodeid nid))
      else (nid, R.p ' (untag_nodeid nid)))) (SET_TO_LIST V) =
     MAP (\nid. nid) (SET_TO_LIST V)` by (
    rw[MAP_EQ_f] >> rw[])
  \\ fs[MAP_ID]
  \\ simp[SET_TO_LIST_INV]
  \\ rw[SUBSET_REFL]
QED

(* Helper for item_uniqueness - requires that original graphs have disjoint
   node/edge namespaces which is preserved by tagging *)
Theorem gluing_item_uniqueness:
  !H R Kv m. wf_graph H /\ wf_graph R /\ item_uniqueness H /\ item_uniqueness R
    ==> item_uniqueness <| V := gluing_nodes H Kv R;
                           E := gluing_edges H R;
                           s := gluing_s Kv m H R;
                           t := gluing_t (gluing_edges H R) Kv m H R;
                           l := gluing_l (gluing_nodes H Kv R) Kv m H R;
                           m := gluing_m (gluing_edges H R) H R;
                           p := gluing_p (gluing_nodes H Kv R) Kv m H R |>
Proof
  rpt strip_tac
  \\ rw[item_uniqueness_def, gluing_nodes_def, gluing_edges_def, nodeid_coprod_def, edgeid_coprod_def]
  \\ rw[UNION_OVER_INTER]
  >- (
    rw[GSYM DISJOINT_DEF]
    >- (
      rw[DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_IMAGE]
      \\ CCONTR_TAC
      \\ fs[]
      \\ fs[tag_nodeid_left_def, tag_edgeid_left_def]
      \\ fs[nodeid_absrep, edgeid_absrep]
      \\ fs[item_uniqueness_def, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_IMAGE]
      \\ metis_tac[]
    )
    >- (
      rw[DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_IMAGE]
      \\ CCONTR_TAC >> fs[]
      \\ fs[tag_nodeid_right_def, tag_edgeid_left_def, nodeid_absrep, edgeid_absrep]
      \\ `EVEN (2 * s2n (dest_edgeid x'⁴'))` by rw[EVEN_DOUBLE]
      \\ intLib.ARITH_TAC
    )
  )
  >- (
    rw[UNION_OVER_INTER]
    \\ rw[GSYM DISJOINT_DEF, DISJOINT_UNION]
    >- (
      rw[DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_IMAGE] >> CCONTR_TAC >> fs[]
      \\ fs[tag_nodeid_left_def, tag_edgeid_right_def, nodeid_absrep, edgeid_absrep]
      \\ intLib.ARITH_TAC
    )
    >- (
      rw[DISJOINT_DEF, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_IMAGE] >> CCONTR_TAC >> fs[]
      \\ fs[tag_nodeid_right_def, tag_edgeid_right_def, nodeid_absrep, edgeid_absrep]
      \\ fs[item_uniqueness_def, EXTENSION, NOT_IN_EMPTY, IN_INTER, IN_IMAGE]
      \\ metis_tac[]
    )
  )
QED

(* Helper: gluing_l preserves spine property when both source graphs have it *)
Theorem gluing_l_spine:
  !V Kv m H R.
    FINITE V /\ hostgraph_labels_spine H /\ hostgraph_labels_spine R /\
    wf_hostgraph R /\ wf_partial_hostgraph H /\
    Kv SUBSET R.V /\
    (!n. n IN V /\ is_left_tagged_nodeid n /\
         ~(?k. k IN Kv /\ m.nodemap ' k = untag_nodeid n) ==>
         untag_nodeid n IN FDOM H.l) /\
    (!n. n IN V /\ ~is_left_tagged_nodeid n ==> untag_nodeid n IN R.V)
    ==> FEVERY (is_hostlabel_spine o FST o SND) (gluing_l V Kv m H R)
Proof
  rpt strip_tac
  \\ rw[gluing_l_def, LET_DEF]
  \\ qabbrev_tac `kvl = MAP (λnid. if is_left_tagged_nodeid nid then
        if ?k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid then
          (nid, R.l ' (@k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid))
        else (nid, H.l ' (untag_nodeid nid))
      else (nid, R.l ' (untag_nodeid nid))) (SET_TO_LIST V)`
  \\ `ALL_DISTINCT (MAP FST kvl)` by (
    unabbrev_all_tac >> rw[MAP_MAP_o, combinTheory.o_DEF]
    \\ `MAP (λnid. FST (if is_left_tagged_nodeid nid then
          if ?k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid then
            (nid, R.l ' (@k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid))
          else (nid, H.l ' (untag_nodeid nid))
        else (nid, R.l ' (untag_nodeid nid)))) (SET_TO_LIST V) =
       MAP (λnid. nid) (SET_TO_LIST V)` by (rw[MAP_EQ_f] >> rw[])
    \\ fs[MAP_ID]
    \\ irule ALL_DISTINCT_SET_TO_LIST >> fs[]
  )
  \\ drule FEVERY_FEMPTY_FUPDATE_LIST
  \\ disch_then (fn th => rw[th])
  \\ unabbrev_all_tac >> rw[EVERY_MEM, MEM_MAP]
  \\ Cases_on `is_left_tagged_nodeid nid` >> rw[]
  >- (
    fs[hostgraph_labels_spine_def, FEVERY_DEF]
    \\ first_x_assum irule
    \\ SELECT_ELIM_TAC >> conj_tac >- metis_tac[]
    \\ rw[] >> fs[wf_hostgraph_def, SUBSET_DEF]
  )
  >- (
    fs[hostgraph_labels_spine_def, FEVERY_DEF]
    \\ first_x_assum irule
    \\ first_x_assum irule
    \\ fs[SET_TO_LIST_IN_MEM]
  )
  >- (
    fs[hostgraph_labels_spine_def, FEVERY_DEF]
    \\ first_x_assum irule
    \\ fs[wf_hostgraph_def]
  )
QED

(* Helper: gluing_m preserves spine property when both source graphs have it *)
Theorem gluing_m_spine:
  !E H R.
    FINITE E /\ hostgraph_labels_spine H /\ hostgraph_labels_spine R /\
    wf_hostgraph R /\ wf_partial_hostgraph H /\
    (!e. e IN E /\ is_left_tagged_edgeid e ==> untag_edgeid e IN FDOM H.m) /\
    (!e. e IN E /\ ~is_left_tagged_edgeid e ==> untag_edgeid e IN FDOM R.m)
    ==> FEVERY (is_hostlabel_spine o FST o SND) (gluing_m E H R)
Proof
  rpt strip_tac
  \\ rw[gluing_m_def, LET_DEF]
  \\ qabbrev_tac `kvl = MAP (λeid. if is_left_tagged_edgeid eid then
        (eid, H.m ' (untag_edgeid eid))
      else (eid, R.m ' (untag_edgeid eid))) (SET_TO_LIST E)`
  \\ `ALL_DISTINCT (MAP FST kvl)` by (
    unabbrev_all_tac >> rw[MAP_MAP_o, combinTheory.o_DEF]
    \\ `MAP (λeid. FST (if is_left_tagged_edgeid eid then
          (eid, H.m ' (untag_edgeid eid))
        else (eid, R.m ' (untag_edgeid eid)))) (SET_TO_LIST E) =
       MAP (λeid. eid) (SET_TO_LIST E)` by (rw[MAP_EQ_f] >> rw[])
    \\ fs[MAP_ID]
    \\ irule ALL_DISTINCT_SET_TO_LIST >> fs[]
  )
  \\ drule FEVERY_FEMPTY_FUPDATE_LIST
  \\ disch_then (fn th => rw[th])
  \\ unabbrev_all_tac >> rw[EVERY_MEM, MEM_MAP]
  \\ Cases_on `is_left_tagged_edgeid eid` >> rw[]
  >- (fs[hostgraph_labels_spine_def, FEVERY_DEF] >> first_x_assum irule)
  >- (fs[hostgraph_labels_spine_def, FEVERY_DEF] >> first_x_assum irule)
QED

(* Helper: right-tagged nodes in gluing_nodes have untag in R.V *)
Theorem gluing_nodes_right_tagged_untag_in_R:
  !H Kv R n.
    n IN gluing_nodes H Kv R /\ ~is_left_tagged_nodeid n ==>
    untag_nodeid n IN R.V
Proof
  rw[gluing_nodes_def, nodeid_coprod_def, IN_UNION, IN_IMAGE]
  >- fs[is_left_tagged_nodeid_def, tag_nodeid_left_def, nodeid_absrep, EVEN_DOUBLE]
  >- fs[tag_untag_nodeid_inv, IN_DIFF]
QED

(* Helper: left-tagged nodes in gluing_nodes not in interface have untag in deletion label domain *)
Theorem not_left_tagged_right[simp]:
  !x. ~is_left_tagged_nodeid (tag_nodeid_right x)
Proof
  rw[is_left_tagged_nodeid_def, tag_nodeid_right_def, nodeid_absrep, EVEN_ADD, EVEN_DOUBLE]
QED

Theorem gluing_nodes_left_tagged_not_interface_in_deletion_l:
  !L Kv m G n.
    wf_hostgraph G /\ wf_hostgraph L /\ Kv SUBSET L.V /\ is_match L Kv m G /\
    n IN gluing_nodes (deletion L Kv m G) Kv R /\ is_left_tagged_nodeid n /\
    ~(?k. k IN Kv /\ m.nodemap ' k = untag_nodeid n) ==>
    untag_nodeid n IN FDOM (deletion L Kv m G).l
Proof
  rw[gluing_nodes_def, nodeid_coprod_def, IN_UNION, IN_IMAGE]
  \\ fs[tag_untag_nodeid_inv]
  \\ rw[deletion_def, LET_DEF, FDOM_DRESTRICT]
  >- (fs[wf_hostgraph_def, deletion_def, LET_DEF, deletion_remaining_nodes_def, IN_DIFF, SUBSET_DEF])
  >- (rw[deletion_relabling_nodes_def, IN_DIFF, IN_IMAGE] >> fs[deletion_def, LET_DEF])
QED

(* Helper: left-tagged edges in gluing_edges have untag in deletion mark domain *)
Theorem gluing_edges_left_tagged_in_deletion_m:
  !L Kv m G e.
    wf_hostgraph G /\ wf_hostgraph L /\ is_match L Kv m G /\
    e IN gluing_edges (deletion L Kv m G) R /\ is_left_tagged_edgeid e ==>
    untag_edgeid e IN FDOM (deletion L Kv m G).m
Proof
  rw[gluing_edges_def, edgeid_coprod_def, IN_UNION, IN_IMAGE]
  \\ fs[tag_untag_edgeid_inv]
  \\ rw[deletion_def, LET_DEF, FDOM_DRESTRICT, deletion_remaining_edges_def, IN_DIFF]
  \\ fs[wf_hostgraph_def, deletion_def, LET_DEF, deletion_remaining_edges_def, IN_DIFF]
  \\ fs[is_left_tagged_edgeid_def, tag_edgeid_right_def, edgeid_absrep, EVEN_ADD, EVEN_DOUBLE]
QED

(* Helper: right-tagged edges in gluing_edges have untag in R.m domain *)
Theorem gluing_edges_right_tagged_in_R_m:
  !H R e.
    wf_hostgraph R /\
    e IN gluing_edges H R /\ ~is_left_tagged_edgeid e ==>
    untag_edgeid e IN FDOM R.m
Proof
  rw[gluing_edges_def, edgeid_coprod_def, IN_UNION, IN_IMAGE]
  >- fs[is_left_tagged_edgeid_def, tag_edgeid_left_def, edgeid_absrep, EVEN_DOUBLE]
  >- fs[tag_untag_edgeid_inv, wf_hostgraph_def]
QED

Theorem wf_gluing:
  !R G L Kv m H. wf_hostgraph R /\ wf_hostgraph G /\ wf_hostgraph L /\
                 Kv SUBSET L.V /\ Kv SUBSET R.V /\
                 is_match L Kv m G /\ H = deletion L Kv m G
    ==> wf_hostgraph (gluing R Kv m H)
Proof
  rpt strip_tac >> rw[wf_hostgraph_def, gluing_def, LET_DEF]
  >- (
    qabbrev_tac `H = deletion L Kv m G`
    \\ `wf_partial_hostgraph H` by (unabbrev_all_tac >> irule deletion_preserves_wf_graph >> rw[])
    \\ `wf_graph H` by fs[wf_partial_hostgraph_def]
    \\ `wf_graph R` by fs[wf_hostgraph_def]
    \\ rw[wf_graph_def]
    >- (imp_res_tac gluing_FINITE >> fs[])
    >- (fs[] \\ imp_res_tac gluing_FINITE >> fs[])
    >- (irule FDOM_gluing_s_GLUING_EDGES >> fs[])
    >- (drule_all FRANGE_gluing >> strip_tac >> unabbrev_all_tac >> fs[gluing_def, LET_DEF])
    >- (irule FDOM_gluing_t >> fs[] \\ imp_res_tac gluing_FINITE >> fs[])
    >- (drule_all FRANGE_gluing_t >> strip_tac >> unabbrev_all_tac >> fs[gluing_def, LET_DEF])
    >- (irule FDOM_gluing_p_SUBSET >> fs[] \\ imp_res_tac gluing_FINITE >> fs[])
    >- (irule gluing_item_uniqueness >> fs[wf_graph_def])
  )
  >- (
    `wf_partial_hostgraph (deletion L Kv m G)` by (irule deletion_preserves_wf_graph >> fs[])
    \\ `wf_graph (deletion L Kv m G)` by fs[wf_partial_hostgraph_def]
    \\ `wf_graph R` by fs[wf_hostgraph_def]
    \\ imp_res_tac finite_gluing_nodes_edges
    \\ irule FDOM_gluing_l >> fs[]
  )
  >- (
    `wf_partial_hostgraph (deletion L Kv m G)` by (irule deletion_preserves_wf_graph >> fs[])
    \\ `wf_graph (deletion L Kv m G)` by fs[wf_partial_hostgraph_def]
    \\ `wf_graph R` by fs[wf_hostgraph_def]
    \\ imp_res_tac finite_gluing_nodes_edges
    \\ irule FDOM_gluing_m >> fs[]
  )
  (* hostgraph_labels_spine: spine preserved through gluing *)
  >- (
    `wf_partial_hostgraph (deletion L Kv m G)` by (irule deletion_preserves_wf_graph >> fs[])
    \\ `wf_graph (deletion L Kv m G)` by fs[wf_partial_hostgraph_def]
    \\ `wf_graph R` by fs[wf_hostgraph_def]
    \\ imp_res_tac finite_gluing_nodes_edges
    \\ `hostgraph_labels_spine R` by fs[wf_hostgraph_def]
    \\ `hostgraph_labels_spine (deletion L Kv m G)` by fs[wf_partial_hostgraph_def]
    \\ rw[hostgraph_labels_spine_def]
    >- (
      irule gluing_l_spine
      \\ conj_tac >- (rpt strip_tac >> drule gluing_nodes_right_tagged_untag_in_R >> fs[])
      \\ conj_tac >- (rpt strip_tac >> drule_all gluing_nodes_left_tagged_not_interface_in_deletion_l >> fs[])
      \\ fs[]
    )
    >- (
      irule gluing_m_spine
      \\ conj_tac >- (rpt strip_tac >> drule_all gluing_edges_left_tagged_in_deletion_m >> fs[])
      \\ conj_tac >- (rpt strip_tac >> drule_all gluing_edges_right_tagged_in_R_m >> fs[])
      \\ fs[]
    )
  )
QED

(* Key lemma: applying gluing_s to a right-tagged edge with source in interface *)
Theorem gluing_s_apply_right_tagged_in_interface:
  !H R d Kv e.
    e IN R.E /\ wf_graph H /\ wf_graph R /\
    R.s ' e IN Kv ==>
    (gluing_s Kv d H R) ' (tag_edgeid_right e) = tag_nodeid_left (d.nodemap ' (R.s ' e))
Proof
  rpt strip_tac
  \\ rw[gluing_s_def]
  \\ irule alistTheory.ALOOKUP_SOME_FAPPLY_alist_to_fmap
  \\ irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM
  \\ conj_tac
  (* ALL_DISTINCT (MAP FST ...) *)
  >- (
    rw[MAP_FST_gluing_s_mapping_id]
    \\ irule ALL_DISTINCT_SET_TO_LIST
    \\ rw[gluing_edges_def, edgeid_coprod_def]
    \\ fs[wf_graph_def]
  )
  (* MEM entry in list *)
  \\ rw[MEM_MAP]
  \\ qexists_tac `tag_edgeid_right e`
  \\ conj_tac
  >- (
    (* For right-tagged: is_left_tagged is FALSE *)
    `~is_left_tagged_edgeid (tag_edgeid_right e)` by (
      rw[is_left_tagged_edgeid_def, tag_edgeid_right_def, edgeid_absrep]
      \\ rw[arithmeticTheory.EVEN_ODD, GSYM arithmeticTheory.ADD1, arithmeticTheory.ODD_DOUBLE])
    \\ rw[gluing_s_mapping_def, tag_untag_edgeid_inv]
  )
  >- (
    `FINITE (gluing_edges H R)` by (rw[gluing_edges_def, edgeid_coprod_def] \\ fs[wf_graph_def])
    \\ fs[MEM_SET_TO_LIST]
    \\ rw[gluing_edges_def, edgeid_coprod_def]
  )
QED

(* Key lemma: applying gluing_t to a right-tagged edge with target in interface *)
Theorem gluing_t_apply_right_tagged_in_interface:
  !H R d Kv e.
    e IN R.E /\ wf_graph H /\ wf_graph R /\
    FINITE (gluing_edges H R) /\
    R.t ' e IN Kv ==>
    (gluing_t (gluing_edges H R) Kv d H R) ' (tag_edgeid_right e) = tag_nodeid_left (d.nodemap ' (R.t ' e))
Proof
  rpt strip_tac
  \\ qabbrev_tac `entries = (MAP (λeid. let ueid = untag_edgeid eid in
                                         if is_left_tagged_edgeid eid then (eid,tag_nodeid_left (H.t ' ueid))
                                         else let sn = R.t ' ueid in
                                              if sn ∈ Kv then (eid,tag_nodeid_left (d.nodemap ' sn))
                                              else (eid,tag_nodeid_right sn))
                                  (SET_TO_LIST (gluing_edges H R)))`
  \\ `ALL_DISTINCT (MAP FST entries)` by (
    unabbrev_all_tac
    \\ rw[MAP_MAP_o, combinTheory.o_DEF]
    \\ simp[COND_RAND, pairTheory.FST]
    \\ irule ALL_DISTINCT_SET_TO_LIST
    \\ fs[]
  )
  \\ `~is_left_tagged_edgeid (tag_edgeid_right e)` by (
    rw[is_left_tagged_edgeid_def, tag_edgeid_right_def, edgeid_absrep]
    \\ rw[arithmeticTheory.EVEN_ODD, GSYM arithmeticTheory.ADD1, arithmeticTheory.ODD_DOUBLE])
  \\ `MEM (tag_edgeid_right e, tag_nodeid_left (d.nodemap ' (R.t ' e))) entries` by (
    unabbrev_all_tac
    \\ rw[MEM_MAP]
    \\ qexists_tac `tag_edgeid_right e`
    \\ conj_tac
    >- rw[tag_untag_edgeid_inv]
    >- rw[MEM_SET_TO_LIST, gluing_edges_def, edgeid_coprod_def]
  )
  \\ `FLOOKUP (FEMPTY |++ entries) (tag_edgeid_right e) = SOME (tag_nodeid_left (d.nodemap ' (R.t ' e)))` by (
    irule alistTheory.mem_to_flookup
    \\ rw[]
  )
  \\ fs[flookup_thm, FDOM_FUPDATE_LIST]
  \\ pop_assum mp_tac
  \\ simp[gluing_t_def, LET_DEF]
QED

Definition dpo_def:
  dpo L K R m G = gluing R K m (deletion L K m G)
End

(* Main theorem: DPO construction preserves well-formedness.
   Given well-formed LHS (L), RHS (R), and host graph (G),
   with interface K subset of both L.V and R.V, and a valid match m,
   the result of DPO rewriting is well-formed. *)
Theorem wf_dpo:
  !L K R m G.
    wf_hostgraph L /\ wf_hostgraph R /\ wf_hostgraph G /\
    K SUBSET L.V /\ K SUBSET R.V /\ is_match L K m G
    ==> wf_hostgraph (dpo L K R m G)
Proof
  rpt strip_tac >>
  simp[dpo_def] >>
  irule wf_gluing >>
  simp[] >>
  qexistsl_tac [`G`, `L`] >>
  simp[]
QED


(* Helper: gluing_m preserves unmarked property when both source graphs are unmarked *)
Theorem gluing_m_unmarked:
  !E H R.
    FINITE E /\
    FEVERY (IS_NONE o SND o SND) H.m /\ FEVERY (IS_NONE o SND o SND) R.m /\
    (!e. e IN E /\ is_left_tagged_edgeid e ==> untag_edgeid e IN FDOM H.m) /\
    (!e. e IN E /\ ~is_left_tagged_edgeid e ==> untag_edgeid e IN FDOM R.m)
    ==> FEVERY (IS_NONE o SND o SND) (gluing_m E H R)
Proof
  rpt strip_tac \\ rw[gluing_m_def, LET_DEF] \\
  qabbrev_tac `kvl = MAP (\eid. if is_left_tagged_edgeid eid then
      (eid, H.m ' (untag_edgeid eid)) else (eid, R.m ' (untag_edgeid eid)))
      (SET_TO_LIST E)` \\
  `ALL_DISTINCT (MAP FST kvl)` by (
    unabbrev_all_tac >> rw[MAP_MAP_o, combinTheory.o_DEF] \\
    `MAP (\eid. FST (if is_left_tagged_edgeid eid then
        (eid, H.m ' (untag_edgeid eid)) else (eid, R.m ' (untag_edgeid eid))))
        (SET_TO_LIST E) = MAP (\eid. eid) (SET_TO_LIST E)` by
      (rw[MAP_EQ_f] >> rw[]) \\
    fs[MAP_ID] \\ irule ALL_DISTINCT_SET_TO_LIST >> fs[]) \\
  drule FEVERY_FEMPTY_FUPDATE_LIST \\ disch_then (fn th => rw[th]) \\
  unabbrev_all_tac >> rw[EVERY_MEM, MEM_MAP] \\
  Cases_on `is_left_tagged_edgeid eid` >> rw[]
  >- (fs[FEVERY_DEF] >> first_x_assum irule)
  >- (fs[FEVERY_DEF] >> first_x_assum irule)
QED

(* Helper: gluing_l preserves unmarked property when both source graphs are unmarked *)
Theorem gluing_l_unmarked:
  !V Kv m H R.
    FINITE V /\
    FEVERY (IS_NONE o SND o SND) H.l /\ FEVERY (IS_NONE o SND o SND) R.l /\
    (!n. n IN V /\ ~is_left_tagged_nodeid n ==> untag_nodeid n IN FDOM R.l) /\
    (!n. n IN V /\ is_left_tagged_nodeid n /\
         (?k. k IN Kv /\ m.nodemap ' k = untag_nodeid n) ==>
         (@k. k IN Kv /\ m.nodemap ' k = untag_nodeid n) IN FDOM R.l) /\
    (!n. n IN V /\ is_left_tagged_nodeid n /\
         ~(?k. k IN Kv /\ m.nodemap ' k = untag_nodeid n) ==>
         untag_nodeid n IN FDOM H.l)
    ==> FEVERY (IS_NONE o SND o SND) (gluing_l V Kv m H R)
Proof
  rpt strip_tac \\ rw[gluing_l_def, LET_DEF] \\
  qabbrev_tac `kvl = MAP (\nid. if is_left_tagged_nodeid nid then
      if ?k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid then
        (nid, R.l ' (@k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid))
      else (nid, H.l ' (untag_nodeid nid))
      else (nid, R.l ' (untag_nodeid nid))) (SET_TO_LIST V)` \\
  `ALL_DISTINCT (MAP FST kvl)` by (
    unabbrev_all_tac >> rw[MAP_MAP_o, combinTheory.o_DEF] \\
    `MAP (\nid. FST (if is_left_tagged_nodeid nid then
        if ?k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid then
          (nid, R.l ' (@k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid))
        else (nid, H.l ' (untag_nodeid nid))
        else (nid, R.l ' (untag_nodeid nid)))) (SET_TO_LIST V) =
       MAP (\nid. nid) (SET_TO_LIST V)` by (rw[MAP_EQ_f] >> rw[]) \\
    fs[MAP_ID] \\ irule ALL_DISTINCT_SET_TO_LIST >> fs[]) \\
  drule FEVERY_FEMPTY_FUPDATE_LIST \\ disch_then (fn th => rw[th]) \\
  unabbrev_all_tac >> rw[EVERY_MEM, MEM_MAP] \\
  Cases_on `is_left_tagged_nodeid nid` >> rw[]
  >- (fs[FEVERY_DEF] >> first_x_assum irule >> first_x_assum irule >>
      simp[] >> metis_tac[])
  >- (fs[FEVERY_DEF] >> first_x_assum irule >> first_x_assum irule >> simp[])
  >- (fs[FEVERY_DEF] >> first_x_assum irule >> first_x_assum irule >> simp[])
QED

(* Helper: gluing_p preserves unrooted property when both source graphs are unrooted *)
Theorem gluing_p_unrooted:
  !V Kv m H R.
    FINITE V /\
    (!n. n IN FDOM H.p ==> H.p ' n = F) /\
    (!n. n IN FDOM R.p ==> R.p ' n = F) /\
    (!n. n IN V /\ ~is_left_tagged_nodeid n ==> untag_nodeid n IN FDOM R.p) /\
    (!n. n IN V /\ is_left_tagged_nodeid n /\
         (?k. k IN Kv /\ m.nodemap ' k = untag_nodeid n) ==>
         (@k. k IN Kv /\ m.nodemap ' k = untag_nodeid n) IN FDOM R.p) /\
    (!n. n IN V /\ is_left_tagged_nodeid n /\
         ~(?k. k IN Kv /\ m.nodemap ' k = untag_nodeid n) ==>
         untag_nodeid n IN FDOM H.p)
    ==> FEVERY (\(nid,b). b = F) (gluing_p V Kv m H R)
Proof
  rpt strip_tac \\ rw[gluing_p_def, LET_DEF] \\
  qabbrev_tac `kvl = MAP (\nid. if is_left_tagged_nodeid nid then
      if ?k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid then
        (nid, R.p ' (@k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid))
      else (nid, H.p ' (untag_nodeid nid))
      else (nid, R.p ' (untag_nodeid nid))) (SET_TO_LIST V)` \\
  `ALL_DISTINCT (MAP FST kvl)` by (
    unabbrev_all_tac >> rw[MAP_MAP_o, combinTheory.o_DEF] \\
    `MAP (\nid. FST (if is_left_tagged_nodeid nid then
        if ?k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid then
          (nid, R.p ' (@k. k IN Kv /\ m.nodemap ' k = untag_nodeid nid))
        else (nid, H.p ' (untag_nodeid nid))
        else (nid, R.p ' (untag_nodeid nid)))) (SET_TO_LIST V) =
       MAP (\nid. nid) (SET_TO_LIST V)` by (rw[MAP_EQ_f] >> rw[]) \\
    fs[MAP_ID] \\ irule ALL_DISTINCT_SET_TO_LIST >> fs[]) \\
  drule FEVERY_FEMPTY_FUPDATE_LIST \\ disch_then (fn th => rw[th]) \\
  unabbrev_all_tac >> rw[EVERY_MEM, MEM_MAP] \\
  Cases_on `is_left_tagged_nodeid nid` >> rw[]
QED

(* TODO: Add re-numbering the ids (nodes,edges) *)
val () = export_theory ();
