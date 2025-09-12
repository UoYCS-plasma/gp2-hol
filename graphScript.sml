open HolKernel Parse bossLib boolLib stringLib finite_mapTheory pred_setTheory

val () = new_theory "graph";

Datatype:
  nodeid = nodeid string
End

Definition dest_nodeid_def:
  dest_nodeid (nodeid n) = n
End

Theorem nodeid_absrep:
  (!s. dest_nodeid (nodeid s) = s) /\
  (!n. nodeid (dest_nodeid n) = n)
Proof
  rw[dest_nodeid_def]
  \\ Cases_on `n`
  \\ rw[dest_nodeid_def]
QED

Datatype:
  edgeid = edgeid string
End

Definition dest_edgeid_def:
  dest_edgeid (edgeid e) = e
End

Theorem edgeid_absrep:
  (!s. dest_edgeid (edgeid s) = s) /\
  (!e. edgeid (dest_edgeid e) = e)
Proof
  rw[dest_edgeid_def]
  \\ Cases_on `e`
  \\ rw[dest_edgeid_def]
QED

Datatype: graph =
  <| V: nodeid set
   ; E: edgeid set
   ; s: edgeid |-> nodeid
   ; t: edgeid |-> nodeid
   ; l: nodeid |-> 'l
   ; m: edgeid |-> 'm
   ; p: nodeid |-> bool
  |>
End

(*
  Node/Edge ID Uniqueness
  Node IDs and edge IDs must be pairwise distinct within a single graph.
*)
Definition item_uniqueness_def:
  item_uniqueness (G: ('l, 'm) graph) <=>
    (IMAGE dest_nodeid G.V) INTER (IMAGE dest_edgeid G.E) = {}
End

Definition wf_graph_def:
  wf_graph G <=>
    FINITE G.V /\ FINITE G.E /\
    FDOM G.s = G.E /\ FRANGE G.s SUBSET G.V /\
    FDOM G.t = G.E /\ FRANGE G.t SUBSET G.V /\
    FDOM G.p SUBSET G.V /\
    item_uniqueness G
End

Definition count_outgoing_edges_def:
  count_outgoing_edges (G: ('l, 'm) graph) (n:nodeid) <=>
    if n IN G.V
    then SOME $ FCARD (finite_map$RRESTRICT G.s {n})
    else NONE
End

Definition count_incoming_edges_def:
  count_incoming_edges (G: ('l, 'm) graph) (n:nodeid) <=>
    if n IN G.V
    then SOME $ FCARD (finite_map$RRESTRICT G.t {n})
    else NONE
End

Theorem wf_graph_IMP_FDOM_DRESTRICT_s_eq:
  (!G A. wf_graph G ==> A SUBSET G.E ==> FDOM (DRESTRICT G.s A) = A)
Proof
  fs[wf_graph_def,FDOM_DRESTRICT,INTER_SUBSET_EQN]
QED

Theorem wf_graph_IMP_FDOM_DRESTRICT_t_eq:
  (!G A. wf_graph G ==> A SUBSET G.E ==> FDOM (DRESTRICT G.t A) = A)
Proof
  fs[wf_graph_def,FDOM_DRESTRICT,INTER_SUBSET_EQN]
QED


val () = export_theory ();
