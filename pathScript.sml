open HolKernel boolLib bossLib Parse
open graphTheory
open pred_setTheory finite_mapTheory pairTheory arithmeticTheory listTheory

val () = new_theory "path"

(* PATH DATATYPE                                                       *)

(* ------------------------------------------------------------------
   Paths: alternating sequence of nodes and edges
   A path is either:
   - PathEnd n: trivial path consisting of just node n
   - PathCons n e p: node n followed by edge e followed by path p
   ------------------------------------------------------------------ *)

Datatype:
  path =
    PathEnd nodeid
  | PathCons nodeid edgeid path
End

(* Start node of a path *)
Definition path_start_def:
  path_start (PathEnd n) = n /\
  path_start (PathCons n e p) = n
End

(* End node of a path *)
Definition path_end_def:
  path_end (PathEnd n) = n /\
  path_end (PathCons n e p) = path_end p
End

(* Length of a path (number of edges) *)
Definition path_length_def:
  path_length (PathEnd n) = 0 /\
  path_length (PathCons n e p) = SUC (path_length p)
End

(* Nodes occurring in a path *)
Definition path_nodes_def:
  path_nodes (PathEnd n) = {n} /\
  path_nodes (PathCons n e p) = n INSERT path_nodes p
End

(* Edges occurring in a path *)
Definition path_edges_def:
  path_edges (PathEnd n) = {} /\
  path_edges (PathCons n e p) = e INSERT path_edges p
End

(* Well-formed path in a graph G:
   - All nodes are in G.V
   - All edges are in G.E
   - Edge sources/targets match the path structure *)
Definition wf_path_def:
  wf_path G (PathEnd n) = (n IN G.V) /\
  wf_path G (PathCons n e p) =
    (n IN G.V /\
     e IN G.E /\
     G.s ' e = n /\
     G.t ' e = path_start p /\
     wf_path G p)
End

(* A path is non-trivial if it has at least one edge *)
Definition is_nontrivial_path_def:
  is_nontrivial_path (PathEnd _) = F /\
  is_nontrivial_path (PathCons _ _ _) = T
End

(* Path concatenation: append path q at the end of path p
   Precondition: path_end p = path_start q *)
Definition path_concat_def:
  path_concat (PathEnd n) q = q /\
  path_concat (PathCons n e p) q = PathCons n e (path_concat p q)
End

(* EDGE EXISTENCE AND REACHABILITY                                     *)

(* There exists a direct edge from v to w in G *)
Definition has_edge_def:
  has_edge G v w = ?e. e IN G.E /\ G.s ' e = v /\ G.t ' e = w
End

(* w is reachable from v in G via some path *)
Definition reachable_def:
  reachable G v w = ?p. wf_path G p /\ path_start p = v /\ path_end p = w
End

(* w is reachable from v via a non-trivial path (at least one edge) *)
Definition reachable_in_def:
  reachable_in G v w =
    ?p. wf_path G p /\ is_nontrivial_path p /\
        path_start p = v /\ path_end p = w
End

(* CYCLES AND ACYCLICITY                                               *)

(* A cycle is a non-trivial path where start = end *)
Definition is_cycle_def:
  is_cycle G p =
    (wf_path G p /\ is_nontrivial_path p /\ path_start p = path_end p)
End

(* A graph is acyclic if it contains no cycles *)
Definition acyclic_def:
  acyclic G = ~(?p. is_cycle G p)
End

(* TRANSITIVE GRAPHS                                                   *)

(* A graph is transitive if for every non-trivial path v ~> w
   with v <> w, there exists a direct edge v -> w *)
Definition is_transitive_def:
  is_transitive G =
    !v w. v IN G.V /\ w IN G.V /\ v <> w /\ reachable_in G v w
      ==> has_edge G v w
End

(* BASIC PATH LEMMAS                                                   *)

(* ------------------------------------------------------------------
   Path start/end properties
   ------------------------------------------------------------------ *)

Theorem path_start_end_trivial:
  !n. path_start (PathEnd n) = n /\ path_end (PathEnd n) = n
Proof
  rw[path_start_def, path_end_def]
QED

Theorem path_start_cons:
  !n e p. path_start (PathCons n e p) = n
Proof
  rw[path_start_def]
QED

Theorem path_end_cons:
  !n e p. path_end (PathCons n e p) = path_end p
Proof
  rw[path_end_def]
QED

(* Trivial path: start = end *)
Theorem path_trivial_start_eq_end:
  !n. path_start (PathEnd n) = path_end (PathEnd n)
Proof
  rw[path_start_def, path_end_def]
QED

(* ------------------------------------------------------------------
   Path length properties
   ------------------------------------------------------------------ *)

Theorem path_length_zero_iff:
  !p. path_length p = 0 <=> ?n. p = PathEnd n
Proof
  Cases_on `p` >> rw[path_length_def]
QED

Theorem path_length_nontrivial:
  !p. is_nontrivial_path p <=> path_length p > 0
Proof
  Cases_on `p` >> rw[is_nontrivial_path_def, path_length_def]
QED

(* ------------------------------------------------------------------
   Path concatenation lemmas
   ------------------------------------------------------------------ *)

Theorem path_concat_start:
  !p q. path_end p = path_start q ==>
    path_start (path_concat p q) = path_start p
Proof
  Induct_on `p` >> rw[path_concat_def, path_start_def, path_end_def]
QED

Theorem path_concat_end:
  !p q. path_end (path_concat p q) = path_end q
Proof
  Induct_on `p` >> rw[path_concat_def, path_end_def]
QED

(* Unconditional version for non-trivial paths *)
Theorem path_concat_start_nontrivial:
  !p q. is_nontrivial_path p ==>
    path_start (path_concat p q) = path_start p
Proof
  Cases_on `p` >> rw[path_concat_def, path_start_def, is_nontrivial_path_def]
QED

Theorem path_concat_length:
  !p q. path_length (path_concat p q) = path_length p + path_length q
Proof
  Induct_on `p` >> rw[path_concat_def, path_length_def]
QED

Theorem path_concat_nontrivial:
  !p q. is_nontrivial_path (path_concat p q) <=>
        is_nontrivial_path p \/ is_nontrivial_path q
Proof
  Induct_on `p` >> rw[path_concat_def, is_nontrivial_path_def]
QED

(* path_start is always in path_nodes - needed for concat lemmas *)
Theorem path_start_in_nodes:
  !p. path_start p IN path_nodes p
Proof
  Cases_on `p` >> rw[path_start_def, path_nodes_def]
QED

Theorem path_concat_nodes:
  !p q. path_end p = path_start q ==>
    path_nodes (path_concat p q) = path_nodes p UNION path_nodes q
Proof
  Induct_on `p`
  >- (
    rw[path_concat_def, path_nodes_def, path_end_def]
    >> rw[GSYM INSERT_SING_UNION]
    >> metis_tac[path_start_in_nodes, ABSORPTION]
  )
  >- rw[path_concat_def, path_nodes_def, path_end_def, INSERT_UNION_EQ]
QED

Theorem path_concat_edges:
  !p q. path_edges (path_concat p q) = path_edges p UNION path_edges q
Proof
  Induct_on `p` >> rw[path_concat_def, path_edges_def, INSERT_UNION_EQ]
QED

(* Well-formedness of concatenation requires matching endpoints *)
Theorem wf_path_concat:
  !G p q. wf_path G p /\ wf_path G q /\ path_end p = path_start q
    ==> wf_path G (path_concat p q)
Proof
  Induct_on `p`
  >- rw[path_concat_def, path_end_def]
  >- (
    rw[path_concat_def, wf_path_def, path_end_def]
    >> rw[path_concat_start]
  )
QED

(* Concatenation with trivial path *)
Theorem path_concat_trivial_left:
  !n q. path_concat (PathEnd n) q = q
Proof
  rw[path_concat_def]
QED

Theorem path_concat_trivial_right:
  !p n. path_end p = n ==> path_concat p (PathEnd n) = p
Proof
  Induct_on `p`
  >- rw[path_concat_def, path_end_def]
  >- rw[path_concat_def, path_end_def]
QED

(* ------------------------------------------------------------------
   Well-formed path properties
   ------------------------------------------------------------------ *)

Theorem wf_path_nodes_in_V:
  !G p. wf_path G p ==> path_nodes p SUBSET G.V
Proof
  Induct_on `p`
  >- rw[wf_path_def, path_nodes_def, SUBSET_DEF]
  >- (
    rw[wf_path_def, path_nodes_def, SUBSET_DEF]
    >> metis_tac[SUBSET_DEF]
  )
QED

Theorem wf_path_edges_in_E:
  !G p. wf_path G p ==> path_edges p SUBSET G.E
Proof
  Induct_on `p`
  >- rw[wf_path_def, path_edges_def, SUBSET_DEF]
  >- (
    rw[wf_path_def, path_edges_def, SUBSET_DEF]
    >> metis_tac[SUBSET_DEF]
  )
QED

Theorem wf_path_start_in_V:
  !G p. wf_path G p ==> path_start p IN G.V
Proof
  Cases_on `p` >> rw[wf_path_def, path_start_def]
QED

Theorem wf_path_end_in_V:
  !G p. wf_path G p ==> path_end p IN G.V
Proof
  Induct_on `p`
  >- rw[wf_path_def, path_end_def]
  >- rw[wf_path_def, path_end_def]
QED

(* ------------------------------------------------------------------
   wf_graph helper lemmas
   ------------------------------------------------------------------ *)

(* Edge endpoints are in the vertex set for well-formed graphs *)
Theorem wf_graph_edge_endpoints_in_V:
  !G e. wf_graph G /\ e IN G.E ==>
    G.s ' e IN G.V /\ G.t ' e IN G.V
Proof
  rw[wf_graph_def]
  >> `e IN FDOM G.s /\ e IN FDOM G.t` by metis_tac[]
  >> `G.s ' e IN FRANGE G.s` by (rw[FRANGE_DEF] >> metis_tac[])
  >> `G.t ' e IN FRANGE G.t` by (rw[FRANGE_DEF] >> metis_tac[])
  >> metis_tac[SUBSET_DEF]
QED

Theorem wf_graph_source_in_V:
  !G e. wf_graph G /\ e IN G.E ==> G.s ' e IN G.V
Proof
  metis_tac[wf_graph_edge_endpoints_in_V]
QED

Theorem wf_graph_target_in_V:
  !G e. wf_graph G /\ e IN G.E ==> G.t ' e IN G.V
Proof
  metis_tac[wf_graph_edge_endpoints_in_V]
QED

(* REACHABILITY LEMMAS                                                 *)

(* Reflexivity: every node reaches itself *)
Theorem reachable_refl:
  !G v. v IN G.V ==> reachable G v v
Proof
  rw[reachable_def]
  >> qexists_tac `PathEnd v`
  >> rw[wf_path_def, path_start_def, path_end_def]
QED

(* Transitivity: reachability composes *)
Theorem reachable_trans:
  !G u v w. reachable G u v /\ reachable G v w ==> reachable G u w
Proof
  rw[reachable_def]
  >> qexists_tac `path_concat p p'`
  >> `path_end p = path_start p'` by rw[]
  >> rw[path_concat_start, path_concat_end]
  >> irule wf_path_concat
  >> rw[]
QED

(* Direct edge implies reachable (requires wf_graph for v,w IN G.V) *)
Theorem has_edge_imp_reachable:
  !G v w. wf_graph G /\ has_edge G v w ==> reachable G v w
Proof
  rw[has_edge_def, reachable_def]
  >> qexists_tac `PathCons (G.s ' e) e (PathEnd (G.t ' e))`
  >> rw[wf_path_def, path_start_def, path_end_def]
  >> fs[wf_graph_def]
  >> `G.s ' e IN FRANGE G.s` by (rw[FRANGE_DEF] >> metis_tac[])
  >> `G.t ' e IN FRANGE G.t` by (rw[FRANGE_DEF] >> metis_tac[])
  >> fs[SUBSET_DEF]
QED

(* Direct edge implies reachable via non-trivial path *)
Theorem has_edge_imp_reachable_in:
  !G v w. wf_graph G /\ has_edge G v w ==> reachable_in G v w
Proof
  rw[has_edge_def, reachable_in_def]
  >> qexists_tac `PathCons (G.s ' e) e (PathEnd (G.t ' e))`
  >> rw[wf_path_def, path_start_def, path_end_def, is_nontrivial_path_def]
  >> fs[wf_graph_def]
  >> `G.s ' e IN FRANGE G.s` by (rw[FRANGE_DEF] >> metis_tac[])
  >> `G.t ' e IN FRANGE G.t` by (rw[FRANGE_DEF] >> metis_tac[])
  >> fs[SUBSET_DEF]
QED

(* reachable_in implies reachable *)
Theorem reachable_in_imp_reachable:
  !G v w. reachable_in G v w ==> reachable G v w
Proof
  rw[reachable_in_def, reachable_def]
  >> metis_tac[]
QED

(* Transitivity for reachable_in *)
Theorem reachable_in_trans:
  !G u v w. reachable_in G u v /\ reachable_in G v w ==> reachable_in G u w
Proof
  rw[reachable_in_def]
  >> qexists_tac `path_concat p p'`
  >> `path_end p = path_start p'` by rw[]
  >> rw[path_concat_start, path_concat_end, path_concat_nontrivial]
  >> irule wf_path_concat
  >> rw[]
QED

(* ------------------------------------------------------------------
   Non-trivial path decomposition
   ------------------------------------------------------------------ *)

(* A non-trivial path can be decomposed into first edge + rest *)
Theorem nontrivial_path_decompose:
  !p. is_nontrivial_path p ==>
    ?n e p'. p = PathCons n e p'
Proof
  Cases_on `p` >> rw[is_nontrivial_path_def]
QED

(* Single edge path *)
Theorem single_edge_path:
  !G v e w. wf_graph G /\ e IN G.E /\ G.s ' e = v /\ G.t ' e = w ==>
    wf_path G (PathCons v e (PathEnd w)) /\
    path_start (PathCons v e (PathEnd w)) = v /\
    path_end (PathCons v e (PathEnd w)) = w /\
    path_length (PathCons v e (PathEnd w)) = 1
Proof
  rw[wf_path_def, path_start_def, path_end_def, path_length_def]
  >> fs[wf_graph_def]
  >> `G.s ' e IN FRANGE G.s` by (rw[FRANGE_DEF] >> metis_tac[])
  >> `G.t ' e IN FRANGE G.t` by (rw[FRANGE_DEF] >> metis_tac[])
  >> fs[SUBSET_DEF]
QED

(* TRANSITIVITY CHARACTERIZATION                                       *)

(* Alternative: transitive iff closed under 2-step reachability *)
Theorem is_transitive_two_step:
  !G. is_transitive G ==>
    !v u w. v IN G.V /\ u IN G.V /\ w IN G.V /\
            has_edge G v u /\ has_edge G u w /\ v <> w
      ==> has_edge G v w
Proof
  rw[is_transitive_def]
  >> first_x_assum irule
  >> rw[reachable_in_def]
  >> fs[has_edge_def]
  >> qexists_tac `PathCons v e (PathCons u e' (PathEnd w))`
  >> rw[wf_path_def, path_start_def, path_end_def, is_nontrivial_path_def]
QED

(* Helper: two-step closure implies has_edge for any non-trivial path.
   By complete induction on path_length. *)
Theorem two_step_closed_path_has_edge:
  !G p. wf_graph G /\
        wf_path G p /\
        is_nontrivial_path p /\
        path_start p <> path_end p /\
        (* Two-step closure property *)
        (!v u w. v IN G.V /\ u IN G.V /\ w IN G.V /\
                 has_edge G v u /\ has_edge G u w ==> has_edge G v w)
        ==>
        has_edge G (path_start p) (path_end p)
Proof
  gen_tac >> completeInduct_on `path_length p` >>
  rpt strip_tac >> Cases_on `p`
  (* PathEnd - contradicts is_nontrivial_path *)
  >- fs[is_nontrivial_path_def]
  (* PathCons n e p' *)
  >> simp[path_start_def, path_end_def] >>
  Cases_on `p'`
  (* p' = PathEnd n' : single edge *)
  >- (
    fs[path_end_def, has_edge_def, wf_path_def, path_start_def] >>
    qexists_tac `e` >> simp[]
  )
  (* p' = PathCons n' e' p'' : use IH *)
  >> simp[path_end_def] >>
  rename1 `PathCons n' e' p''` >>
  Cases_on `n' = path_end p''`
  (* n' = path_end : direct edge *)
  >- (fs[has_edge_def, wf_path_def, path_start_def] >> qexists_tac `e` >> simp[])
  (* n' <> path_end : IH + 2-step closure *)
  >> fs[wf_path_def, path_start_def, path_length_def] >>
  (* Use IH *)
  qpat_assum `!m. m < _ ==> _` (qspec_then `SUC (path_length p'')` mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum (qspec_then `PathCons n' e' p''` mp_tac) >>
  simp[path_length_def, is_nontrivial_path_def, path_start_def, path_end_def] >>
  strip_tac >>
  `wf_path G (PathCons n' e' p'')` by fs[wf_path_def, path_start_def] >>
  `has_edge G n' (path_end p'')` by metis_tac[] >>
  `has_edge G n n'` by (fs[has_edge_def] >> qexists_tac `e` >> simp[]) >>
  `n IN G.V` by fs[] >>
  `n' IN G.V` by (
    fs[wf_graph_def] >>
    `G.t ' e IN FRANGE G.t` by (rw[FRANGE_DEF] >> metis_tac[]) >>
    fs[SUBSET_DEF]
  ) >>
  `path_end p'' IN G.V` by (irule wf_path_end_in_V >> fs[wf_path_def]) >>
  first_x_assum irule >> simp[] >> qexists_tac `n'` >> simp[]
QED

(* Converse: 2-step closure implies full transitivity *)
Theorem two_step_closed_is_transitive:
  !G. wf_graph G /\
      (!v u w. v IN G.V /\ u IN G.V /\ w IN G.V /\
               has_edge G v u /\ has_edge G u w ==> has_edge G v w)
      ==> is_transitive G
Proof
  rw[is_transitive_def, reachable_in_def] >>
  irule two_step_closed_path_has_edge >>
  rw[] >> metis_tac[]
QED

val () = export_theory ()
