open HolKernel boolLib bossLib
open graphTheory finite_mapTheory pred_setTheory

val () = new_theory "morphism"

(* MORPHISM DATA TYPE                                                  *)

Datatype: morphism =
  <| nodemap: nodeid |-> nodeid
   ; edgemap: edgeid |-> edgeid
  |>
End

(* Morphism composition: (m2 o m1) applies m1 first, then m2 *)
Definition compose_morphism_def:
  compose_morphism m2 m1 = <| nodemap := m2.nodemap f_o_f m1.nodemap
                            ; edgemap := m2.edgemap f_o_f m1.edgemap
                           |>
End

(* Identity morphism *)
Definition id_morphism_def:
  id_morphism G = <| nodemap := FUN_FMAP I G.V
                   ; edgemap := FUN_FMAP I G.E
                  |>
End

(* PARTIAL PREMORPHISMS (Base Concept)                                 *)
(* A partial premorphism is defined on a subset of G's nodes/edges.    *)
(* It preserves structure (source, target, rootedness) but not labels. *)
(* This corresponds to a partial function G ⇀ H.                       *)

(* Domain/range constraints for partial morphisms *)
Definition partial_dom_ran_def:
  partial_dom_ran G f H <=>
    FDOM f.nodemap SUBSET G.V /\
    FDOM f.edgemap SUBSET G.E /\
    FRANGE f.nodemap SUBSET H.V /\
    FRANGE f.edgemap SUBSET H.E
End

(* Preserve source: for tracked edges, source is tracked and commutes.
   Using SUBMAP elegantly captures both conditions:
   1. Tracked edges have tracked sources (domain inclusion)
   2. f(s(e)) = s(f(e)) for all tracked edges (value equality) *)
Definition partial_preserve_source_def:
  partial_preserve_source G f H <=>
    H.s f_o_f f.edgemap SUBMAP f.nodemap f_o_f G.s
End

(* Preserve target: analogous to source *)
Definition partial_preserve_target_def:
  partial_preserve_target G f H <=>
    H.t f_o_f f.edgemap SUBMAP f.nodemap f_o_f G.t
End

(* Preserve defined rootedness: partial version *)
Definition partial_preserve_rootedness_def:
  partial_preserve_rootedness G f H <=>
    DRESTRICT G.p (FDOM f.nodemap) SUBMAP H.p f_o_f f.nodemap
End

(* A partial premorphism: partial function preserving structure.
   Matches Brian's Definition 3.11 but allows partial domain. *)
Definition is_partial_premorphism_def:
  is_partial_premorphism G f H <=>
    partial_dom_ran G f H /\
    partial_preserve_source G f H /\
    partial_preserve_target G f H /\
    partial_preserve_rootedness G f H
End

(* PREMORPHISMS (Total - matches Brian's Definition 3.11)              *)
(* A premorphism is a total partial_premorphism.                       *)

(* Domain/range constraints for total morphisms *)
Definition morphism_dom_ran_def:
  morphism_dom_ran G f H <=>
    FDOM f.nodemap = G.V /\
    FDOM f.edgemap = G.E /\
    FRANGE f.nodemap SUBSET H.V /\
    FRANGE f.edgemap SUBSET H.E
End

(* For total morphisms, preserve_source simplifies to equality *)
Definition preserve_source_def:
  preserve_source G f H <=> f.nodemap f_o_f G.s = H.s f_o_f f.edgemap
End

Definition preserve_target_def:
  preserve_target G f H <=> f.nodemap f_o_f G.t = H.t f_o_f f.edgemap
End

Definition preserve_defined_rootedness_def:
  preserve_defined_rootedness G f H <=> G.p SUBMAP H.p f_o_f f.nodemap
End

(* A premorphism: total function preserving structure (no labels).
   This matches Brian's Definition 3.11 exactly. *)
Definition is_premorphism_def:
  is_premorphism G f H <=>
    morphism_dom_ran G f H /\
    preserve_source G f H /\
    preserve_target G f H /\
    preserve_defined_rootedness G f H
End

(* PARTIAL MORPHISMS (with label preservation)                         *)

(* Preserve edge labels: partial version *)
Definition partial_preserve_edgelabels_def:
  partial_preserve_edgelabels G f H <=>
    DRESTRICT G.m (FDOM f.edgemap) SUBMAP H.m f_o_f f.edgemap
End

(* Preserve node labels: partial version *)
Definition partial_preserve_nodelabels_def:
  partial_preserve_nodelabels G f H <=>
    DRESTRICT G.l (FDOM f.nodemap) SUBMAP H.l f_o_f f.nodemap
End

(* A partial morphism: partial premorphism that also preserves labels *)
Definition is_partial_morphism_def:
  is_partial_morphism G f H <=>
    is_partial_premorphism G f H /\
    partial_preserve_edgelabels G f H /\
    partial_preserve_nodelabels G f H
End

(* MORPHISMS (Total, with labels - matches Brian's Definition 3.6)     *)

(* Preserve edge labels: total version *)
Definition preserve_edgelabels_def:
  preserve_edgelabels G f H <=> G.m = H.m f_o_f f.edgemap
End

(* Preserve node labels: total version *)
Definition preserve_nodelabels_def:
   preserve_nodelabels G f H <=> G.l = H.l f_o_f f.nodemap
End

(* A morphism: premorphism that also preserves labels.
   This matches Brian's Definition 3.6 exactly. *)
Definition is_morphism_def:
  is_morphism G f H <=>
    is_premorphism G f H /\
    preserve_edgelabels G f H /\
    preserve_nodelabels G f H
End

(* INJECTIVE VARIANTS                                                  *)

(* Partial injective premorphism: what tracks need *)
Definition is_partial_inj_premorphism_def:
  is_partial_inj_premorphism G f H <=>
    is_partial_premorphism G f H /\
    INJ (FAPPLY f.nodemap) (FDOM f.nodemap) H.V /\
    INJ (FAPPLY f.edgemap) (FDOM f.edgemap) H.E
End

(* Injective premorphism: total, used for rule matching *)
Definition is_inj_premorphism_def:
  is_inj_premorphism G f H <=>
    is_premorphism G f H /\
    INJ (FAPPLY f.nodemap) G.V H.V /\
    INJ (FAPPLY f.edgemap) G.E H.E
End

(* Partial injective morphism *)
Definition is_partial_inj_morphism_def:
  is_partial_inj_morphism G f H <=>
    is_partial_morphism G f H /\
    INJ (FAPPLY f.nodemap) (FDOM f.nodemap) H.V /\
    INJ (FAPPLY f.edgemap) (FDOM f.edgemap) H.E
End

(* Injective morphism: total *)
Definition is_inj_morphism_def:
  is_inj_morphism G f H <=>
    is_morphism G f H /\
    INJ (FAPPLY f.nodemap) G.V H.V /\
    INJ (FAPPLY f.edgemap) G.E H.E
End

(* Surjective morphism *)
Definition is_surj_morphism_def:
  is_surj_morphism G f H <=>
    is_morphism G f H /\
    SURJ (FAPPLY f.nodemap) G.V H.V /\
    SURJ (FAPPLY f.edgemap) G.E H.E
End

(* Bijective morphism (isomorphism) *)
Definition is_bij_morphism_def:
  is_bij_morphism G f H <=>
    is_morphism G f H /\
    BIJ (FAPPLY f.nodemap) G.V H.V /\
    BIJ (FAPPLY f.edgemap) G.E H.E
End

(* HELPER LEMMAS                                                       *)

Theorem FUN_FMAP_I_f_o_f_left:
  !f P. FINITE P /\ FRANGE f SUBSET P ==> FUN_FMAP I P f_o_f f = f
Proof
  rpt strip_tac >> rw[fmap_EXT, f_o_f_DEF, FUN_FMAP_DEF] >>
  rw[EXTENSION, IN_INTER, GSPECIFICATION] >> rpt strip_tac >>
  EQ_TAC >> strip_tac >> simp[] >> fs[FRANGE_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem FUN_FMAP_I_f_o_f_right:
  !f P. FINITE P /\ FDOM f = P ==> f f_o_f FUN_FMAP I P = f
Proof
  rpt strip_tac >> rw[fmap_EXT, f_o_f_DEF] >-
  (rw[EXTENSION, IN_INTER, GSPECIFICATION] >> rpt strip_tac >>
   EQ_TAC >> strip_tac >> simp[] >>
   `FUN_FMAP I (FDOM f) ' x = I x` suffices_by simp[] >> rw[FUN_FMAP_DEF]) >-
  rw[FUN_FMAP_DEF]
QED

Theorem f_o_f_ASSOC:
  !f g h. (f f_o_f g) f_o_f h = f f_o_f (g f_o_f h)
Proof
  rw[fmap_EXT]
  >- (rw[f_o_f_DEF, EXTENSION] >> rpt strip_tac >> EQ_TAC >> strip_tac >> fs[]
      >- (`(g f_o_f h) ' x = g ' (h ' x)` by simp[f_o_f_DEF] >> simp[])
      >- (`(g f_o_f h) ' x = g ' (h ' x)` by simp[f_o_f_DEF] >> fs[]))
  >- (`x IN FDOM h /\ h ' x IN FDOM g /\ g ' (h ' x) IN FDOM f` by fs[f_o_f_DEF] >>
      `((f f_o_f g) f_o_f h) ' x = f ' (g ' (h ' x))` by simp[f_o_f_DEF] >>
      `(f f_o_f (g f_o_f h)) ' x = f ' (g ' (h ' x))` by simp[f_o_f_DEF] >>
      fs[])
QED

(* IMPLICATION THEOREMS: Total implies Partial                         *)

Theorem morphism_dom_ran_IMP_partial:
  !G f H. morphism_dom_ran G f H ==> partial_dom_ran G f H
Proof
  rw[morphism_dom_ran_def, partial_dom_ran_def, SUBSET_DEF]
QED

Theorem preserve_source_IMP_partial:
  !G f H. wf_graph G /\ wf_graph H /\ morphism_dom_ran G f H /\
          preserve_source G f H ==> partial_preserve_source G f H
Proof
  rw[preserve_source_def, partial_preserve_source_def, SUBMAP_DEF] >>
  fs[morphism_dom_ran_def, wf_graph_def] >>
  `FDOM (H.s f_o_f f.edgemap) = FDOM f.edgemap` by
    (rw[f_o_f_DEF, EXTENSION] >> EQ_TAC >> strip_tac >> fs[] >>
     `f.edgemap ' x IN FRANGE f.edgemap` by (rw[FRANGE_DEF] >> metis_tac[]) >>
     metis_tac[SUBSET_DEF]) >>
  `FDOM (f.nodemap f_o_f G.s) = G.E` by
    (rw[f_o_f_DEF, EXTENSION] >> EQ_TAC >> strip_tac >> fs[SUBSET_DEF] >>
     metis_tac[]) >>
  rw[] >> fs[f_o_f_DEF]
QED

Theorem preserve_target_IMP_partial:
  !G f H. wf_graph G /\ wf_graph H /\ morphism_dom_ran G f H /\
          preserve_target G f H ==> partial_preserve_target G f H
Proof
  rw[preserve_target_def, partial_preserve_target_def, SUBMAP_DEF] >>
  fs[morphism_dom_ran_def, wf_graph_def] >>
  `FDOM (H.t f_o_f f.edgemap) = FDOM f.edgemap` by
    (rw[f_o_f_DEF, EXTENSION] >> EQ_TAC >> strip_tac >> fs[] >>
     `f.edgemap ' x IN FRANGE f.edgemap` by (rw[FRANGE_DEF] >> metis_tac[]) >>
     metis_tac[SUBSET_DEF]) >>
  `FDOM (f.nodemap f_o_f G.t) = G.E` by
    (rw[f_o_f_DEF, EXTENSION] >> EQ_TAC >> strip_tac >> fs[SUBSET_DEF] >>
     metis_tac[]) >>
  rw[] >> fs[f_o_f_DEF]
QED

Theorem preserve_rootedness_IMP_partial:
  !G f H. morphism_dom_ran G f H /\
          preserve_defined_rootedness G f H ==>
          partial_preserve_rootedness G f H
Proof
  rw[preserve_defined_rootedness_def, partial_preserve_rootedness_def,
     SUBMAP_DEF, DRESTRICT_DEF, morphism_dom_ran_def] >>
  metis_tac[]
QED

Theorem is_premorphism_IMP_partial:
  !G f H. wf_graph G /\ wf_graph H /\ is_premorphism G f H ==>
          is_partial_premorphism G f H
Proof
  rw[is_premorphism_def, is_partial_premorphism_def] >>
  metis_tac[morphism_dom_ran_IMP_partial, preserve_source_IMP_partial,
            preserve_target_IMP_partial, preserve_rootedness_IMP_partial]
QED

Theorem is_morphism_IMP_partial:
  !G f H. wf_graph G /\ wf_graph H /\ is_morphism G f H ==>
          is_partial_morphism G f H
Proof
  rw[is_morphism_def, is_partial_morphism_def] >>
  `is_partial_premorphism G f H` by metis_tac[is_premorphism_IMP_partial] >>
  fs[is_premorphism_def, morphism_dom_ran_def,
     preserve_edgelabels_def, partial_preserve_edgelabels_def,
     preserve_nodelabels_def, partial_preserve_nodelabels_def,
     SUBMAP_DEF, DRESTRICT_DEF] >>
  rw[] >> fs[f_o_f_DEF]
QED

Theorem is_inj_premorphism_IMP_partial:
  !G f H. wf_graph G /\ wf_graph H /\ is_inj_premorphism G f H ==>
          is_partial_inj_premorphism G f H
Proof
  rw[is_inj_premorphism_def, is_partial_inj_premorphism_def] >>
  `is_partial_premorphism G f H` by metis_tac[is_premorphism_IMP_partial] >>
  fs[is_premorphism_def, morphism_dom_ran_def]
QED

Theorem is_inj_morphism_IMP_is_inj_premorphism:
  !G f H. is_inj_morphism G f H ==> is_inj_premorphism G f H
Proof
  rw[is_inj_morphism_def, is_inj_premorphism_def, is_morphism_def]
QED

Theorem is_inj_morphism_IMP_partial:
  !G f H. wf_graph G /\ wf_graph H /\ is_inj_morphism G f H ==>
          is_partial_inj_morphism G f H
Proof
  rw[is_inj_morphism_def, is_partial_inj_morphism_def] >>
  `is_partial_morphism G f H` by metis_tac[is_morphism_IMP_partial] >>
  fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def]
QED

(* IDENTITY MORPHISM THEOREMS                                          *)

Theorem id_morphism_is_morphism:
  !G. wf_graph G /\ FDOM G.l = G.V /\ FDOM G.m = G.E
      ==> is_morphism G (id_morphism G) G
Proof
  rw[is_morphism_def, is_premorphism_def, morphism_dom_ran_def,
     id_morphism_def, preserve_source_def, preserve_target_def,
     preserve_defined_rootedness_def, preserve_edgelabels_def,
     preserve_nodelabels_def, wf_graph_def]
  >- (`FUN_FMAP I G.V f_o_f G.s = G.s` by (irule FUN_FMAP_I_f_o_f_left >> simp[]) >>
      `G.s f_o_f FUN_FMAP I G.E = G.s` by (irule FUN_FMAP_I_f_o_f_right >> simp[]) >>
      simp[])
  >- (`FUN_FMAP I G.V f_o_f G.t = G.t` by (irule FUN_FMAP_I_f_o_f_left >> simp[]) >>
      `G.t f_o_f FUN_FMAP I G.E = G.t` by (irule FUN_FMAP_I_f_o_f_right >> simp[]) >>
      simp[])
  >- (rw[SUBMAP_DEF, f_o_f_DEF, FUN_FMAP_DEF] >> rpt strip_tac >> fs[SUBSET_DEF]
      >- (`x IN G.V` by metis_tac[] >> rw[FUN_FMAP_DEF])
      >- (`x IN G.V` by metis_tac[] >> rw[f_o_f_DEF, FUN_FMAP_DEF]))
  >- (irule (GSYM FUN_FMAP_I_f_o_f_right) >> simp[])
  >- (irule (GSYM FUN_FMAP_I_f_o_f_right) >> simp[])
QED

Theorem id_morphism_is_inj:
  !G. wf_graph G /\ FDOM G.l = G.V /\ FDOM G.m = G.E
      ==> is_inj_morphism G (id_morphism G) G
Proof
  rw[is_inj_morphism_def] >>
  `is_morphism G (id_morphism G) G` by metis_tac[id_morphism_is_morphism] >>
  rw[id_morphism_def, INJ_DEF, wf_graph_def] >>
  gvs[wf_graph_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def,
      FUN_FMAP_DEF]
QED

Theorem id_morphism_is_surj:
  !G. wf_graph G /\ FDOM G.l = G.V /\ FDOM G.m = G.E
      ==> is_surj_morphism G (id_morphism G) G
Proof
  rw[is_surj_morphism_def] >>
  `is_morphism G (id_morphism G) G` by metis_tac[id_morphism_is_morphism] >>
  rw[id_morphism_def, SURJ_DEF, wf_graph_def] >>
  gvs[wf_graph_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def,
      FUN_FMAP_DEF] >>
  qexists_tac `x` >> gvs[FUN_FMAP_DEF]
QED

Theorem id_morphism_is_bij:
  !G. wf_graph G /\ FDOM G.l = G.V /\ FDOM G.m = G.E
      ==> is_bij_morphism G (id_morphism G) G
Proof
  rw[is_bij_morphism_def, BIJ_DEF] >>
  `is_inj_morphism G (id_morphism G) G` by metis_tac[id_morphism_is_inj] >>
  `is_surj_morphism G (id_morphism G) G` by metis_tac[id_morphism_is_surj] >>
  fs[is_inj_morphism_def, is_surj_morphism_def]
QED

(* Identity is a partial injective premorphism *)
Theorem id_morphism_is_partial_inj_premorphism:
  !G. wf_graph G /\ FDOM G.l = G.V /\ FDOM G.m = G.E ==>
      is_partial_inj_premorphism G (id_morphism G) G
Proof
  rpt strip_tac >>
  `is_inj_morphism G (id_morphism G) G` by metis_tac[id_morphism_is_inj] >>
  `is_inj_premorphism G (id_morphism G) G`
    by metis_tac[is_inj_morphism_IMP_is_inj_premorphism] >>
  metis_tac[is_inj_premorphism_IMP_partial]
QED

(* MORPHISM COMPOSITION                                                *)

Theorem compose_is_morphism:
  !G H L m1 m2.
    is_morphism G m1 H /\ is_morphism H m2 L ==>
    is_morphism G (compose_morphism m2 m1) L
Proof
  rpt strip_tac >>
  fs[is_morphism_def, is_premorphism_def] >>
  rpt conj_tac
  (* morphism_dom_ran *)
  >- (rw[morphism_dom_ran_def, compose_morphism_def] >> rpt conj_tac
      (* FDOM nodemap = G.V *)
      >- (rw[f_o_f_DEF, EXTENSION] >> EQ_TAC >> strip_tac
          >> fs[morphism_dom_ran_def, FRANGE_DEF, SUBSET_DEF] >> metis_tac[])
      (* FDOM edgemap = G.E *)
      >- (rw[f_o_f_DEF, EXTENSION] >> EQ_TAC >> strip_tac
          >> fs[morphism_dom_ran_def, FRANGE_DEF, SUBSET_DEF] >> metis_tac[])
      (* FRANGE nodemap SUBSET L.V *)
      >- (rw[FRANGE_DEF, SUBSET_DEF, f_o_f_DEF] >> simp[f_o_f_DEF] >>
          fs[morphism_dom_ran_def, FRANGE_DEF, SUBSET_DEF] >> metis_tac[])
      (* FRANGE edgemap SUBSET L.E *)
      >- (rw[FRANGE_DEF, SUBSET_DEF, f_o_f_DEF] >> simp[f_o_f_DEF] >>
          fs[morphism_dom_ran_def, FRANGE_DEF, SUBSET_DEF] >> metis_tac[]))
  (* preserve_source *)
  >- (fs[preserve_source_def, compose_morphism_def] >> metis_tac[f_o_f_ASSOC])
  (* preserve_target *)
  >- (fs[preserve_target_def, compose_morphism_def] >> metis_tac[f_o_f_ASSOC])
  (* preserve_defined_rootedness *)
  >- (fs[preserve_defined_rootedness_def, compose_morphism_def, morphism_dom_ran_def] >>
      rw[SUBMAP_DEF] >> rpt strip_tac
      (* x IN FDOM (L.p f_o_f m2.nodemap f_o_f m1.nodemap) *)
      >- (simp[f_o_f_DEF] >>
          `x IN FDOM (H.p f_o_f m1.nodemap)` by fs[SUBMAP_DEF] >>
          `x IN FDOM m1.nodemap /\ m1.nodemap ' x IN FDOM H.p` by fs[f_o_f_DEF] >>
          `m1.nodemap ' x IN FDOM (L.p f_o_f m2.nodemap)` by fs[SUBMAP_DEF] >>
          fs[f_o_f_DEF] >> conj_tac
          >- (conj_tac >- metis_tac[] >>
              `m1.nodemap ' x IN FRANGE m1.nodemap` by (rw[FRANGE_DEF] >> metis_tac[]) >>
              fs[SUBSET_DEF])
          >- (fs[f_o_f_DEF] >>
              `m1.nodemap ' x IN FDOM m2.nodemap /\ m2.nodemap ' (m1.nodemap ' x) IN FDOM L.p`
                by fs[f_o_f_DEF] >>
              `x IN FDOM m1.nodemap` by metis_tac[] >>
              `m1.nodemap ' x IN FDOM m2.nodemap` by metis_tac[] >>
              SUBGOAL_THEN ``x IN FDOM (m2.nodemap f_o_f m1.nodemap)`` ASSUME_TAC
              >- (rw[f_o_f_DEF, EXTENSION] >> metis_tac[]) >>
              IMP_RES_TAC f_o_f_DEF >> fs[]))
      (* G.p ' x = (L.p f_o_f m2.nodemap f_o_f m1.nodemap) ' x *)
      >- (`x IN FDOM (H.p f_o_f m1.nodemap)` by fs[SUBMAP_DEF] >>
          `x IN FDOM m1.nodemap /\ m1.nodemap ' x IN FDOM H.p` by fs[f_o_f_DEF] >>
          `m1.nodemap ' x IN FDOM (L.p f_o_f m2.nodemap)` by fs[SUBMAP_DEF] >>
          `m1.nodemap ' x IN FDOM m2.nodemap /\ m2.nodemap ' (m1.nodemap ' x) IN FDOM L.p`
            by fs[f_o_f_DEF] >>
          `G.p ' x = (H.p f_o_f m1.nodemap) ' x` by fs[SUBMAP_DEF] >>
          IMP_RES_TAC f_o_f_DEF >> fs[] >>
          `H.p ' (m1.nodemap ' x) = (L.p f_o_f m2.nodemap) ' (m1.nodemap ' x)` by fs[SUBMAP_DEF] >>
          IMP_RES_TAC f_o_f_DEF >> fs[] >>
          ONCE_REWRITE_TAC[GSYM f_o_f_ASSOC] >>
          SUBGOAL_THEN ``x IN FDOM ((L.p f_o_f m2.nodemap) f_o_f m1.nodemap)`` ASSUME_TAC
          >- (rw[f_o_f_DEF] >> metis_tac[]) >>
          IMP_RES_TAC f_o_f_DEF >> fs[]))
  (* preserve_edgelabels *)
  >- (fs[preserve_edgelabels_def, compose_morphism_def] >> metis_tac[f_o_f_ASSOC])
  (* preserve_nodelabels *)
  >- (fs[preserve_nodelabels_def, compose_morphism_def] >> metis_tac[f_o_f_ASSOC])
QED

Theorem compose_inj_morphism:
  !G H L m1 m2.
    is_inj_morphism G m1 H /\ is_inj_morphism H m2 L ==>
    is_inj_morphism G (compose_morphism m2 m1) L
Proof
  rpt strip_tac >> rw[is_inj_morphism_def]
  (* is_morphism *)
  >- (irule compose_is_morphism >> fs[is_inj_morphism_def] >>
      qexists_tac `H` >> rw[])
  (* INJ nodemap *)
  >- (rw[INJ_DEF, compose_morphism_def]
      (* (m2.nodemap f_o_f m1.nodemap) ' x IN L.V *)
      >- (fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
          `x IN FDOM m1.nodemap` by rw[] >>
          `m1.nodemap ' x IN FRANGE m1.nodemap` by (rw[FRANGE_DEF] >> metis_tac[]) >>
          `m1.nodemap ' x IN H.V` by metis_tac[SUBSET_DEF] >>
          `m1.nodemap ' x IN FDOM m2.nodemap` by rw[] >>
          `m2.nodemap ' (m1.nodemap ' x) IN FRANGE m2.nodemap` by (rw[FRANGE_DEF] >> metis_tac[]) >>
          `m2.nodemap ' (m1.nodemap ' x) IN L.V` by metis_tac[SUBSET_DEF] >>
          `(m2.nodemap f_o_f m1.nodemap) ' x = m2.nodemap ' (m1.nodemap ' x)` by rw[f_o_f_DEF] >>
          rw[])
      (* injectivity: x = y *)
      >- (fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
          `x IN FDOM m1.nodemap /\ y IN FDOM m1.nodemap` by rw[] >>
          `m1.nodemap ' x IN FRANGE m1.nodemap /\ m1.nodemap ' y IN FRANGE m1.nodemap`
            by (rw[FRANGE_DEF] >> metis_tac[]) >>
          `m1.nodemap ' x IN H.V /\ m1.nodemap ' y IN H.V` by metis_tac[SUBSET_DEF] >>
          `m1.nodemap ' x IN FDOM m2.nodemap` by rw[] >>
          `x IN FDOM (m2.nodemap f_o_f m1.nodemap)` by (rw[f_o_f_DEF] >> rw[]) >>
          `(m2.nodemap f_o_f m1.nodemap) ' x = m2.nodemap ' (m1.nodemap ' x)`
            by metis_tac[f_o_f_DEF] >>
          `y IN FDOM (m2.nodemap f_o_f m1.nodemap)` by (rw[f_o_f_DEF] >> rw[]) >>
          `(m2.nodemap f_o_f m1.nodemap) ' y = m2.nodemap ' (m1.nodemap ' y)`
            by metis_tac[f_o_f_DEF] >>
          `m2.nodemap ' (m1.nodemap ' x) = m2.nodemap ' (m1.nodemap ' y)` by metis_tac[] >>
          `m1.nodemap ' x = m1.nodemap ' y` by metis_tac[INJ_DEF] >>
          metis_tac[INJ_DEF]))
  (* INJ edgemap *)
  >- (rw[INJ_DEF, compose_morphism_def] >>
      fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]
      (* (m2.edgemap f_o_f m1.edgemap) ' x IN L.E *)
      >- (`x IN FDOM m1.edgemap` by rw[] >>
          `m1.edgemap ' x IN FRANGE m1.edgemap` by (rw[FRANGE_DEF] >> metis_tac[]) >>
          `m1.edgemap ' x IN H.E` by metis_tac[SUBSET_DEF] >>
          `m1.edgemap ' x IN FDOM m2.edgemap` by rw[] >>
          `m2.edgemap ' (m1.edgemap ' x) IN FRANGE m2.edgemap` by (rw[FRANGE_DEF] >> metis_tac[]) >>
          `m2.edgemap ' (m1.edgemap ' x) IN L.E` by metis_tac[SUBSET_DEF] >>
          `(m2.edgemap f_o_f m1.edgemap) ' x = m2.edgemap ' (m1.edgemap ' x)` by rw[f_o_f_DEF] >>
          rw[])
      (* injectivity: x = y *)
      >- (`x IN FDOM m1.edgemap /\ y IN FDOM m1.edgemap` by rw[] >>
          `m1.edgemap ' x IN FRANGE m1.edgemap /\ m1.edgemap ' y IN FRANGE m1.edgemap`
            by (rw[FRANGE_DEF] >> metis_tac[]) >>
          `m1.edgemap ' x IN H.E /\ m1.edgemap ' y IN H.E` by metis_tac[SUBSET_DEF] >>
          `x IN FDOM (m2.edgemap f_o_f m1.edgemap) /\ y IN FDOM (m2.edgemap f_o_f m1.edgemap)`
            by rw[f_o_f_DEF] >>
          `(m2.edgemap f_o_f m1.edgemap) ' x = m2.edgemap ' (m1.edgemap ' x)`
            by metis_tac[f_o_f_DEF] >>
          `(m2.edgemap f_o_f m1.edgemap) ' y = m2.edgemap ' (m1.edgemap ' y)`
            by metis_tac[f_o_f_DEF] >>
          `m2.edgemap ' (m1.edgemap ' x) = m2.edgemap ' (m1.edgemap ' y)` by metis_tac[] >>
          `m1.edgemap ' x = m1.edgemap ' y` by metis_tac[INJ_DEF] >>
          metis_tac[INJ_DEF]))
QED

(* PARTIAL MORPHISM COMPOSITION                                        *)
(* Key theorem for track composition                                   *)

Theorem compose_partial_inj_premorphism:
  !G H L m1 m2.
    is_partial_inj_premorphism G m1 H /\
    is_partial_inj_premorphism H m2 L ==>
    is_partial_inj_premorphism G (compose_morphism m2 m1) L
Proof
  rpt strip_tac >>
  fs[is_partial_inj_premorphism_def, is_partial_premorphism_def] >>
  rpt conj_tac
  (* partial_dom_ran *)
  >- (rw[partial_dom_ran_def, compose_morphism_def] >> rpt conj_tac
      >- (rw[f_o_f_DEF, SUBSET_DEF] >> fs[partial_dom_ran_def, SUBSET_DEF])
      >- (rw[f_o_f_DEF, SUBSET_DEF] >> fs[partial_dom_ran_def, SUBSET_DEF])
      >- (rw[FRANGE_DEF, SUBSET_DEF, f_o_f_DEF] >> rpt strip_tac >>
          simp[f_o_f_DEF] >> fs[partial_dom_ran_def, FRANGE_DEF, SUBSET_DEF] >>
          metis_tac[])
      >- (rw[FRANGE_DEF, SUBSET_DEF, f_o_f_DEF] >> rpt strip_tac >>
          simp[f_o_f_DEF] >> fs[partial_dom_ran_def, FRANGE_DEF, SUBSET_DEF] >>
          metis_tac[]))
  (* partial_preserve_source *)
  >- (fs[partial_preserve_source_def, compose_morphism_def, SUBMAP_DEF] >>
      rpt strip_tac
      >- (gvs[f_o_f_DEF] >>
          `m1.edgemap ' x IN FDOM H.s`
            by (first_x_assum (qspec_then `m1.edgemap ' x` mp_tac) >> simp[]) >>
          `H.s ' (m1.edgemap ' x) = m1.nodemap ' (G.s ' x)`
            by (last_x_assum (qspec_then `x` mp_tac) >> simp[f_o_f_DEF]) >>
          `H.s ' (m1.edgemap ' x) IN FDOM m2.nodemap`
            by (first_x_assum (qspec_then `m1.edgemap ' x` mp_tac) >> simp[]) >>
          metis_tac[])
      >- (gvs[f_o_f_DEF] >> simp[f_o_f_DEF] >>
          `m1.edgemap ' x IN FDOM H.s`
            by (first_x_assum (qspec_then `m1.edgemap ' x` mp_tac) >> simp[]) >>
          `x IN FDOM G.s /\ G.s ' x IN FDOM m1.nodemap`
            by (last_x_assum (qspec_then `x` mp_tac) >> simp[]) >>
          `m1.nodemap ' (G.s ' x) IN FDOM m2.nodemap`
            by (first_x_assum (qspec_then `m1.edgemap ' x` mp_tac) >>
                simp[f_o_f_DEF] >> strip_tac >>
                last_x_assum (qspec_then `x` mp_tac) >>
                simp[f_o_f_DEF] >> metis_tac[]) >>
          simp[f_o_f_DEF]))
  (* partial_preserve_target *)
  >- (fs[partial_preserve_target_def, compose_morphism_def, SUBMAP_DEF] >>
      rpt strip_tac >> gvs[f_o_f_DEF]
      >- (`m1.edgemap ' x IN FDOM H.t`
            by (first_x_assum (qspec_then `m1.edgemap ' x` mp_tac) >> simp[]) >>
          `H.t ' (m1.edgemap ' x) = m1.nodemap ' (G.t ' x)`
            by (last_x_assum (qspec_then `x` mp_tac) >> simp[f_o_f_DEF]) >>
          `H.t ' (m1.edgemap ' x) IN FDOM m2.nodemap`
            by (first_x_assum (qspec_then `m1.edgemap ' x` mp_tac) >> simp[]) >>
          metis_tac[])
      >- (`m1.edgemap ' x IN FDOM H.t`
            by (first_x_assum (qspec_then `m1.edgemap ' x` mp_tac) >> simp[]) >>
          `x IN FDOM G.t /\ G.t ' x IN FDOM m1.nodemap`
            by (last_x_assum (qspec_then `x` mp_tac) >> simp[]) >>
          `m1.nodemap ' (G.t ' x) IN FDOM m2.nodemap`
            by (first_x_assum (qspec_then `m1.edgemap ' x` mp_tac) >>
                simp[f_o_f_DEF] >> strip_tac >>
                last_x_assum (qspec_then `x` mp_tac) >>
                simp[f_o_f_DEF] >> metis_tac[]) >>
          simp[f_o_f_DEF]))
  (* partial_preserve_rootedness *)
  >- (fs[partial_preserve_rootedness_def, compose_morphism_def, SUBMAP_DEF,
         DRESTRICT_DEF] >> rpt strip_tac >> fs[f_o_f_DEF])
  (* INJ nodemap *)
  >- (rw[INJ_DEF, compose_morphism_def]
      >- (fs[f_o_f_DEF, partial_dom_ran_def, FRANGE_DEF, SUBSET_DEF] >>
          metis_tac[])
      >- (fs[f_o_f_DEF] >>
          `m2.nodemap ' (m1.nodemap ' x) = m2.nodemap ' (m1.nodemap ' y)`
            by gvs[f_o_f_DEF] >>
          `m1.nodemap ' x IN FRANGE m1.nodemap /\
           m1.nodemap ' y IN FRANGE m1.nodemap`
            by (rw[FRANGE_DEF] >> metis_tac[]) >>
          fs[partial_dom_ran_def, SUBSET_DEF] >>
          `m1.nodemap ' x IN H.V /\ m1.nodemap ' y IN H.V` by metis_tac[] >>
          `m1.nodemap ' x = m1.nodemap ' y`
            by (fs[INJ_DEF] >> first_x_assum irule >> simp[]) >>
          fs[partial_dom_ran_def, SUBSET_DEF] >>
          `x IN G.V /\ y IN G.V` by metis_tac[] >>
          fs[INJ_DEF]))
  (* INJ edgemap *)
  >- (rw[INJ_DEF, compose_morphism_def]
      >- (fs[f_o_f_DEF, partial_dom_ran_def, FRANGE_DEF, SUBSET_DEF] >>
          metis_tac[])
      >- (fs[f_o_f_DEF] >>
          `m2.edgemap ' (m1.edgemap ' x) = m2.edgemap ' (m1.edgemap ' y)`
            by gvs[f_o_f_DEF] >>
          `m1.edgemap ' x IN FRANGE m1.edgemap /\
           m1.edgemap ' y IN FRANGE m1.edgemap`
            by (rw[FRANGE_DEF] >> metis_tac[]) >>
          fs[partial_dom_ran_def, SUBSET_DEF] >>
          `m1.edgemap ' x IN H.E /\ m1.edgemap ' y IN H.E` by metis_tac[] >>
          `m1.edgemap ' x = m1.edgemap ' y`
            by (fs[INJ_DEF] >> first_x_assum irule >> simp[]) >>
          fs[partial_dom_ran_def, SUBSET_DEF] >>
          `x IN G.E /\ y IN G.E` by metis_tac[] >>
          fs[INJ_DEF]))
QED

(* GRAPH EXTENSION                                                     *)

Definition extends_def:
  extends H G <=> ?m. is_inj_morphism H m G
End

Theorem extends_refl:
  !G. wf_graph G /\ FDOM G.l = G.V /\ FDOM G.m = G.E ==> extends G G
Proof
  rw[extends_def] >>
  qexists_tac `id_morphism G` >>
  irule id_morphism_is_inj >>
  rw[]
QED

Theorem extends_trans:
  !G H L. extends G H /\ extends H L ==> extends G L
Proof
  rw[extends_def] >>
  qexists_tac `compose_morphism m' m` >>
  irule compose_inj_morphism >>
  metis_tac[]
QED

(* COMPOSITION PROPERTIES                                              *)

(* compose_morphism is associative *)
Theorem compose_morphism_assoc:
  !m1 m2 m3. compose_morphism m3 (compose_morphism m2 m1) =
             compose_morphism (compose_morphism m3 m2) m1
Proof
  rw[compose_morphism_def, f_o_f_ASSOC]
QED

val () = export_theory ();
