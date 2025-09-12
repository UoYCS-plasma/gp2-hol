open HolKernel Parse bossLib boolLib;
open pred_setTheory pairTheory relationTheory finite_mapTheory;

(* Import HOL4's category theory *)
open categoryTheory;

open graphTheory hostgraphTheory morphismTheory;

val () = new_theory "categoryTheoryExt";

(* ============================================================
   PART 1: Spans and Cospans
   ============================================================ *)

(*
  A span in category C is a diagram: A <-f- S -g-> B
  A cospan in category C is a diagram: A -f-> S <-g- B
*)

Definition is_span_in_def:
  is_span_in c S A B f g <=>
    f :- S → A -:c /\
    g :- S → B -:c
End

Definition is_cospan_in_def:
  is_cospan_in c A B S f g <=>
    f :- A → S -:c /\
    g :- B → S -:c
End

(* ============================================================
   PART 2: Pushouts
   ============================================================ *)

(*
  A pushout of a span A <-f- S -g-> B is:
  - An object P
  - Morphisms i : A -> P and j : B -> P
  - Such that i o f = j o g (commutativity)
  - Universal: for any other (P', i', j') with i' o f = j' o g,
    there exists unique u : P -> P' with u o i = i' and u o j = j'

       S ---f---> A
       |          |
       g          i
       |          |
       v          v
       B ---j---> P
*)

Definition pushout_square_def:
  pushout_square c S A B P f g i j <=>
    (* All morphisms in category *)
    f :- S → A -:c /\
    g :- S → B -:c /\
    i :- A → P -:c /\
    j :- B → P -:c /\
    (* Commutativity: i o f = j o g *)
    (i o f -:c = j o g -:c)
End

Definition is_pushout_def:
  is_pushout c S A B P f g i j <=>
    pushout_square c S A B P f g i j /\
    (* Universal property *)
    (!P' i' j'.
      i' :- A → P' -:c /\
      j' :- B → P' -:c /\
      (i' o f -:c = j' o g -:c)
      ==>
      ?!u. u :- P → P' -:c /\
           (u o i -:c = i') /\
           (u o j -:c = j'))
End

(* ============================================================
   PART 3: Pullbacks (Dual to Pushouts)
   ============================================================ *)

Definition pullback_square_def:
  pullback_square c A B S P f g p q <=>
    (* All morphisms in category *)
    f :- A → S -:c /\
    g :- B → S -:c /\
    p :- P → A -:c /\
    q :- P → B -:c /\
    (* Commutativity: f o p = g o q *)
    (f o p -:c = g o q -:c)
End

Definition is_pullback_def:
  is_pullback c A B S P f g p q <=>
    pullback_square c A B S P f g p q /\
    (* Universal property *)
    (!P' p' q'.
      p' :- P' → A -:c /\
      q' :- P' → B -:c /\
      (f o p' -:c = g o q' -:c)
      ==>
      ?!u. u :- P' → P -:c /\
           (p o u -:c = p') /\
           (q o u -:c = q'))
End

(* Pushout in C is pullback in C^op *)
Theorem pushout_pullback_dual:
  !c S A B P f g i j.
    is_category c ==>
    (is_pushout c S A B P f g i j <=>
     is_pullback (op_cat c) A B S P (op_mor f) (op_mor g) (op_mor i) (op_mor j))
Proof
  rw[is_pushout_def, is_pullback_def, pushout_square_def, pullback_square_def] >>
  simp[op_cat_maps_to_in, op_mor_idem] >>
  EQ_TAC
  >- (
    (* Pushout => Pullback in opposite category *)
    strip_tac >> rpt conj_tac >> TRY (simp[])
    >- (
      (* Composition: i o f = j o g => f° o i° = g° o j° in c° *)
      `f ≈> i -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) >>
      `g ≈> j -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) >>
      qspec_then `f°` (qspec_then `i°` mp_tac) op_cat_compose_in >>
      simp[op_mor_idem] >>
      disch_then (qspec_then `c` mp_tac) >> simp[] >>
      strip_tac >>
      irule EQ_SYM >>
      qspec_then `g°` (qspec_then `j°` (qspec_then `c` mp_tac)) op_cat_compose_in >>
      simp[op_mor_idem])
    >- (
      (* Universal property direction *)
      rpt strip_tac \\
      `p' ≈> f° -:c°` by (fs[maps_to_in_def, composable_in_def, op_cat_maps_to_in] >>
        metis_tac[op_mor_idem]) \\
      `q' ≈> g° -:c°` by (fs[maps_to_in_def, composable_in_def, op_cat_maps_to_in] >>
        metis_tac[op_mor_idem]) \\
      `f ≈> p'° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
      `g ≈> q'° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
      `f° o p' -:c° = (p'° o f -:c)°` by
        (qspecl_then [`f°`, `p'`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
      `g° o q' -:c° = (q'° o g -:c)°` by
        (qspecl_then [`g°`, `q'`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
      `p'° o f -:c = q'° o g -:c` by metis_tac[op_mor_idem] \\
      `?!u'. u' :- P → P' -:c /\ u' o i -:c = p'° /\ u' o j -:c = q'°` by
        (first_x_assum (qspecl_then [`P'`, `p'°`, `q'°`] mp_tac) >> simp[]) \\
      simp[EXISTS_UNIQUE_THM] \\
      conj_tac
      >- (
        (* Existence *)
        `?u'. u' :- P → P' -:c /\ u' o i -:c = p'° /\ u' o j -:c = q'°` by
          fs[EXISTS_UNIQUE_THM] \\
        qexists_tac `u'°` >> simp[op_mor_idem] \\
        `i ≈> u' -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
        `i° o u'° -:c° = (u' o i -:c)°` by
          (qspecl_then [`i°`, `u'°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        `j ≈> u' -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
        `j° o u'° -:c° = (u' o j -:c)°` by
          (qspecl_then [`j°`, `u'°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        metis_tac[op_mor_idem])
      >- (
        (* Uniqueness *)
        rpt strip_tac \\
        `i ≈> u° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[op_mor_idem]) \\
        `j ≈> u° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[op_mor_idem]) \\
        `i° o u -:c° = (u° o i -:c)°` by
          (qspecl_then [`i°`, `u`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        `u° o i -:c = p'°` by metis_tac[op_mor_idem] \\
        `j° o u -:c° = (u° o j -:c)°` by
          (qspecl_then [`j°`, `u`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        `u° o j -:c = q'°` by metis_tac[op_mor_idem] \\
        `i ≈> u'° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[op_mor_idem]) >>
        `j ≈> u'° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[op_mor_idem]) \\
        `i° o u' -:c° = (u'° o i -:c)°` by
          (qspecl_then [`i°`, `u'`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) >>
        `u'° o i -:c = p'°` by metis_tac[op_mor_idem] >>
        `j° o u' -:c° = (u'° o j -:c)°` by
          (qspecl_then [`j°`, `u'`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) >>
        `u'° o j -:c = q'°` by metis_tac[op_mor_idem] \\
        `u° = u'°` by metis_tac[EXISTS_UNIQUE_THM] \\
        metis_tac[op_mor_idem])))
  >- (
    (* Pullback in opposite => Pushout *)
    strip_tac >> rpt conj_tac >> TRY (simp[])
    >- (
      (* Composition direction: f° o i° = g° o j° in c° => i o f = j o g in c *)
      `f ≈> i -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) >>
      `g ≈> j -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
      `f° o i° -:c° = (i o f -:c)°` by
        (qspecl_then [`f°`, `i°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
      `g° o j° -:c° = (j o g -:c)°` by
        (qspecl_then [`g°`, `j°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
      metis_tac[op_mor_idem])
    >- (
      (* Universal property direction *)
      rpt strip_tac \\
      `(i'°)° :- A → P' -:c` by simp[op_mor_idem] >>
      `(j'°)° :- B → P' -:c` by simp[op_mor_idem] \\
      `f ≈> i' -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) >>
      `g ≈> j' -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
      `f° o i'° -:c° = (i' o f -:c)°` by
        (qspecl_then [`f°`, `i'°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) >>
      `g° o j'° -:c° = (j' o g -:c)°` by
        (qspecl_then [`g°`, `j'°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
      `f° o i'° -:c° = g° o j'° -:c°` by metis_tac[] \\
      `?!u. u° :- P → P' -:c /\ i° o u -:c° = i'° /\ j° o u -:c° = j'°` by
        (first_x_assum (qspecl_then [`P'`, `i'°`, `j'°`] mp_tac) >> simp[op_mor_idem]) \\
      simp[EXISTS_UNIQUE_THM] >> conj_tac
      >- (
        (* Existence *)
        `?u. u° :- P → P' -:c /\ i° o u -:c° = i'° /\ j° o u -:c° = j'°` by
          fs[EXISTS_UNIQUE_THM] \\
        qexists_tac `u°` >> simp[op_mor_idem] \\
        `i ≈> u° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[op_mor_idem]) \\
        `j ≈> u° -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[op_mor_idem]) \\
        `i° o u -:c° = (u° o i -:c)°` by
          (qspecl_then [`i°`, `u`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        `j° o u -:c° = (u° o j -:c)°` by
          (qspecl_then [`j°`, `u`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        metis_tac[op_mor_idem])
      >- (
        (* Uniqueness *)
        rpt strip_tac \\
        `i ≈> u -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
        `j ≈> u -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
        `i ≈> u' -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
        `j ≈> u' -:c` by (fs[maps_to_in_def, composable_in_def] >> metis_tac[]) \\
        `i° o u° -:c° = (u o i -:c)°` by
          (qspecl_then [`i°`, `u°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        `j° o u° -:c° = (u o j -:c)°` by
          (qspecl_then [`j°`, `u°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        `i° o u'° -:c° = (u' o i -:c)°` by
          (qspecl_then [`i°`, `u'°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        `j° o u'° -:c° = (u' o j -:c)°` by
          (qspecl_then [`j°`, `u'°`, `c`] mp_tac op_cat_compose_in >> simp[op_mor_idem]) \\
        metis_tac[EXISTS_UNIQUE_THM, op_mor_idem])))
QED

(* ============================================================
   PART 4: Basic Pushout Properties
   ============================================================ *)

(* Pushouts are unique up to isomorphism.
   Note: This is existence of an isomorphism (iso_objs), not unique isomorphism
   (uiso_objs). The isomorphism is canonical (constructed via the universal
   property), but there may be other isomorphisms between pushout objects.
   This matches Brian's thesis Theorem 3.1 and the Isabelle uniqueness_po theorem. *)
Theorem pushout_unique_iso:
  !c S A B P1 P2 f g i1 j1 i2 j2.
    is_category c /\
    is_pushout c S A B P1 f g i1 j1 /\
    is_pushout c S A B P2 f g i2 j2
    ==>
    iso_objs c P1 P2
Proof
  rw[is_pushout_def, pushout_square_def, iso_objs_thm] >>
  (* Use the universal property to obtain u : P1 → P2 and v : P2 → P1 *)
  `?!u. u :- P1 → P2 -:c /\ u o i1 -:c = i2 /\ u o j1 -:c = j2` by
    (first_x_assum (qspecl_then [`P2`, `i2`, `j2`] mp_tac) >> simp[]) >>
  `?!u. u :- P2 → P1 -:c /\ u o i2 -:c = i1 /\ u o j2 -:c = j1` by
    (first_x_assum (qspecl_then [`P1`, `i1`, `j1`] mp_tac) >> simp[]) >>
  `?!u. u :- P2 → P2 -:c /\ u o i2 -:c = i2 /\ u o j2 -:c = j2` by
    (last_x_assum (qspecl_then [`P2`, `i2`, `j2`] mp_tac) >> simp[]) >>
  `?!u. u :- P1 → P1 -:c /\ u o i1 -:c = i1 /\ u o j1 -:c = j1` by
    (last_x_assum (qspecl_then [`P1`, `i1`, `j1`] mp_tac) >> simp[]) >>
  qabbrev_tac `u = @u. u :- P1 → P2 -:c /\ u o i1 -:c = i2 /\ u o j1 -:c = j2` >>
  qabbrev_tac `v = @u. u :- P2 → P1 -:c /\ u o i2 -:c = i1 /\ u o j2 -:c = j1` >>
  `u :- P1 → P2 -:c /\ u o i1 -:c = i2 /\ u o j1 -:c = j2` by
    (markerLib.UNABBREV_ALL_TAC >> SELECT_ELIM_TAC >> rpt strip_tac >>
     metis_tac[EXISTS_UNIQUE_THM]) >>
  `v :- P2 → P1 -:c /\ v o i2 -:c = i1 /\ v o j2 -:c = j1` by
    (markerLib.UNABBREV_ALL_TAC >> SELECT_ELIM_TAC >> rpt strip_tac >>
     metis_tac[EXISTS_UNIQUE_THM]) >>
  (* Show v o u = id P1 *)
  `v o u -:c :- P1 → P1 -:c` by metis_tac[maps_to_comp] >>
  `(v o u -:c) o i1 -:c = i1` by
    metis_tac[comp_assoc, maps_to_in_def, maps_to_def,
              composable_in_def, composable_def] >>
  `(v o u -:c) o j1 -:c = j1` by
    metis_tac[comp_assoc, maps_to_in_def, maps_to_def,
              composable_in_def, composable_def] >>
  `id P1 -:c :- P1 → P1 -:c` by
    (irule id_maps_to >> simp[] >> fs[maps_to_in_def, maps_to_def] >>
     metis_tac[is_category_def, category_axioms_def]) >>
  `(id P1 -:c) o i1 -:c = i1` by
    (irule id_comp2 >> fs[maps_to_in_def, maps_to_def]) >>
  `(id P1 -:c) o j1 -:c = j1` by
    (irule id_comp2 >> fs[maps_to_in_def, maps_to_def]) >>
  `v o u -:c = id P1 -:c` by
    (qpat_x_assum `?!u. u :- P1 → P1 -:c /\ _` mp_tac >>
     simp[EXISTS_UNIQUE_THM] >> metis_tac[]) >>
  (* Show u o v = id P2 *)
  `u o v -:c :- P2 → P2 -:c` by metis_tac[maps_to_comp] >>
  `(u o v -:c) o i2 -:c = i2` by
    metis_tac[comp_assoc, maps_to_in_def, maps_to_def,
              composable_in_def, composable_def] >>
  `(u o v -:c) o j2 -:c = j2` by
    metis_tac[comp_assoc, maps_to_in_def, maps_to_def,
              composable_in_def, composable_def] >>
  `id P2 -:c :- P2 → P2 -:c` by
    (irule id_maps_to >> simp[] >> fs[maps_to_in_def, maps_to_def] >>
     metis_tac[is_category_def, category_axioms_def]) >>
  `(id P2 -:c) o i2 -:c = i2` by
    (irule id_comp2 >> fs[maps_to_in_def, maps_to_def]) >>
  `(id P2 -:c) o j2 -:c = j2` by
    (irule id_comp2 >> fs[maps_to_in_def, maps_to_def]) >>
  `u o v -:c = id P2 -:c` by
    (qpat_x_assum `?!u. u :- P2 → P2 -:c /\ _` mp_tac >>
     simp[EXISTS_UNIQUE_THM] >> metis_tac[]) >>
  (* Now u is an isomorphism with inverse v *)
  qexists_tac `u` >> simp[iso_def] >> qexists_tac `v` >>
  simp[iso_pair_def, composable_in_def, composable_def] >>
  fs[maps_to_in_def, maps_to_def]
QED

(* If f is an isomorphism, j is an isomorphism *)
Theorem pushout_iso_stability:
  !c S A B P f g i j.
    is_category c /\
    is_pushout c S A B P f g i j /\
    iso c f
    ==>
    iso c j
Proof
  rw[is_pushout_def, iso_def] >>
  fs[pushout_square_def, iso_pair_def] >>
  (* Strategy: Construct inverse k : P → B using UP with cocone (g ∘ g', id_B)
     where g' is the inverse of f. Then show j ∘ k = id_P and k ∘ j = id_B. *)
  (* Establish type information for g' : A -> S' *)
  `g'.dom = f.cod` by fs[composable_in_def, composable_def] >>
  `g'.dom = A` by fs[maps_to_in_def, maps_to_def] >>
  `f.dom ∈ c.obj /\ f.cod ∈ c.obj /\ g'.dom ∈ c.obj /\ g'.cod ∈ c.obj`
    by metis_tac[composable_obj] >>
  `(g' o f -:c).cod = g'.cod` by (irule (cj 5 comp_mor_dom_cod) >> metis_tac[]) >>
  `(id f.dom -:c).cod = f.dom` by metis_tac[id_dom_cod] >>
  `g'.cod = f.dom` by metis_tac[] >>
  `f.dom = S'` by fs[maps_to_in_def, maps_to_def] >>
  `g'.cod = S'` by metis_tac[] >>
  (* Establish composability g' ≈> g *)
  `g'.cod = g.dom` by fs[maps_to_in_def, maps_to_def] >>
  `g' ∈ c.mor` by fs[composable_in_def] >>
  `g ∈ c.mor` by fs[maps_to_in_def] >>
  `g' ≈> g -:c` by simp[composable_in_def, composable_def] >>
  (* Form cocone (g o g', id B) *)
  `g' :- A → S' -:c` by fs[maps_to_in_def, maps_to_def] >>
  `g o g' -:c :- A → B -:c` by
    metis_tac[is_category_def, category_axioms_def, maps_to_in_def, maps_to_def] >>
  `B ∈ c.obj` by metis_tac[mor_obj, maps_to_in_def, maps_to_def] >>
  `id B -:c :- B → B -:c` by (irule id_maps_to >> simp[]) >>
  (* Verify commutativity: (g o g') o f = g = (id B) o g *)
  `f ≈> g' -:c /\ g' ≈> g -:c` by simp[] >>
  `(g o g' -:c) o f -:c = g o g' o f -:c -:c` by
    metis_tac[is_category_def, category_axioms_def] >>
  `g' o f -:c = id S' -:c` by metis_tac[] >>
  `g o id g.dom -:c -:c = g` by
    metis_tac[is_category_def, category_axioms_def, maps_to_in_def] >>
  `g.dom = S'` by fs[maps_to_in_def, maps_to_def] >>
  `g o id S' -:c -:c = g` by metis_tac[] >>
  `S' ∈ c.obj` by metis_tac[mor_obj, maps_to_in_def, maps_to_def] >>
  `g o g' o f -:c -:c = g` by metis_tac[] >>
  `(g o g' -:c) o f -:c = g` by metis_tac[] >>
  `(id g.cod -:c) o g -:c = g` by
    metis_tac[is_category_def, category_axioms_def, maps_to_in_def] >>
  `g.cod = B` by fs[maps_to_in_def, maps_to_def] >>
  `(id B -:c) o g -:c = g` by metis_tac[] >>
  `(g o g' -:c) o f -:c = (id B -:c) o g -:c` by metis_tac[] >>
  (* Use UP to get k : P → B *)
  `?!k. k :- P → B -:c /\ k o i -:c = g o g' -:c /\ k o j -:c = id B -:c` by
    (first_x_assum irule >> simp[]) >>
  qabbrev_tac `k = @u. u :- P → B -:c /\ u o i -:c = g o g' -:c /\
                        u o j -:c = id B -:c` >>
  `k :- P → B -:c /\ k o i -:c = g o g' -:c /\ k o j -:c = id B -:c` by
    (markerLib.UNABBREV_ALL_TAC >> SELECT_ELIM_TAC >> rpt strip_tac >>
     metis_tac[EXISTS_UNIQUE_THM]) >>
  (* Derive j o (g o g') = i from i o f = j o g and f o g' = id A *)
  `f o g' -:c = id A -:c` by metis_tac[] >>
  `A ∈ c.obj` by metis_tac[mor_obj, maps_to_in_def, maps_to_def] >>
  `i.dom = A` by fs[maps_to_in_def, maps_to_def] >>
  `i ∈ c.mor` by fs[maps_to_in_def] >>
  `i o id i.dom -:c -:c = i` by metis_tac[is_category_def, category_axioms_def] >>
  `i o id A -:c -:c = i` by metis_tac[] >>
  `g' ≈> f -:c` by
    (simp[composable_in_def, composable_def] >> fs[maps_to_in_def, maps_to_def]) >>
  `f ≈> i -:c` by
    (simp[composable_in_def, composable_def] >> fs[maps_to_in_def, maps_to_def]) >>
  `(i o f -:c) o g' -:c = i o f o g' -:c -:c` by
    metis_tac[is_category_def, category_axioms_def] >>
  `(j o g -:c) o g' -:c = (i o f -:c) o g' -:c` by metis_tac[] >>
  `g ≈> j -:c` by
    (simp[composable_in_def, composable_def] >> fs[maps_to_in_def, maps_to_def]) >>
  `(j o g -:c) o g' -:c = j o g o g' -:c -:c` by
    metis_tac[is_category_def, category_axioms_def] >>
  `i o f o g' -:c -:c = i` by metis_tac[] >>
  `(i o f -:c) o g' -:c = i` by metis_tac[] >>
  `(j o g -:c) o g' -:c = i` by metis_tac[] >>
  `j o g o g' -:c -:c = i` by metis_tac[] >>
  (* Establish composability for k *)
  `k.dom = P /\ k.cod = B` by fs[maps_to_in_def, maps_to_def] >>
  `j.dom = B /\ j.cod = P` by fs[maps_to_in_def, maps_to_def] >>
  `k ∈ c.mor` by fs[maps_to_in_def] >>
  `j ∈ c.mor` by fs[maps_to_in_def] >>
  `k ≈> j -:c` by simp[composable_in_def, composable_def] >>
  `j ≈> k -:c` by simp[composable_in_def, composable_def] >>
  `i.cod = P` by fs[maps_to_in_def, maps_to_def] >>
  `i ≈> k -:c` by simp[composable_in_def, composable_def] >>
  (* Show (j o k) o i = i and (j o k) o j = j *)
  `(j o k -:c) o i -:c = j o k o i -:c -:c` by
    metis_tac[is_category_def, category_axioms_def] >>
  `j o k o i -:c -:c = i` by metis_tac[] >>
  `(j o k -:c) o i -:c = i` by metis_tac[] >>
  `(j o k -:c) o j -:c = j o k o j -:c -:c` by
    metis_tac[is_category_def, category_axioms_def] >>
  `j o k o j -:c -:c = j o id B -:c -:c` by metis_tac[] >>
  `j o id j.dom -:c -:c = j` by metis_tac[is_category_def, category_axioms_def] >>
  `j o id B -:c -:c = j` by metis_tac[] >>
  `(j o k -:c) o j -:c = j` by metis_tac[] >>
  (* Apply UP uniqueness: j o k = id P *)
  `P ∈ c.obj` by metis_tac[mor_obj, maps_to_in_def, maps_to_def] >>
  `id P -:c :- P → P -:c` by (irule id_maps_to >> simp[]) >>
  `(id P -:c) o i -:c = i` by (irule id_comp2 >> fs[maps_to_in_def, maps_to_def]) >>
  `(id P -:c) o j -:c = j` by (irule id_comp2 >> fs[maps_to_in_def, maps_to_def]) >>
  `j o k -:c :- P → P -:c` by
    metis_tac[is_category_def, category_axioms_def, maps_to_in_def, maps_to_def] >>
  `?!u. u :- P → P -:c /\ u o i -:c = i /\ u o j -:c = j` by
    (first_x_assum irule >> simp[]) >>
  `j o k -:c = id P -:c` by
    (qpat_x_assum `?!u. u :- P → P -:c /\ _` mp_tac >>
     simp[EXISTS_UNIQUE_THM] >> metis_tac[]) >>
  (* Conclude iso_pair j k *)
  qexists_tac `k` >> simp[]
QED

(* ============================================================
   PART 5: Graph Category
   ============================================================ *)

(*
  We define the category of hostgraphs:
  - Objects: well-formed hostgraphs
  - Morphisms: graph homomorphisms (structure-preserving maps)
*)

(*
   Graph morphisms as categorical morphisms

   The map field holds a morphism record from morphismTheory:
     <| nodemap : nodeid |-> nodeid; edgemap : edgeid |-> edgeid |>
*)

(* Create categorical morphism from graph morphism *)
Definition mk_graph_mor_def:
  mk_graph_mor G f H = <| dom := G; cod := H; map := f |>
End

(* Identity map for graphs - using id_morphism from morphismTheory *)
Definition graph_id_map_def:
  graph_id_map G = id_morphism G
End

(* Composition of graph morphisms *)
Definition compose_morphism_def:
  compose_morphism f g =
    <| nodemap := g.nodemap f_o_f f.nodemap;
       edgemap := g.edgemap f_o_f f.edgemap |>
End

(* Composition for categorical morphisms *)
Definition graph_comp_def:
  graph_comp m1 m2 = compose_morphism m1.map m2.map
End

(* Pre-category construction (before extensionality wrapper) *)
Definition pre_hostgraph_cat_def:
  pre_hostgraph_cat =
    <| obj := { G | wf_hostgraph G };
       mor := { mk_graph_mor G f H |
                wf_hostgraph G /\
                wf_hostgraph H /\
                is_morphism G f H };
       id_map := graph_id_map;
       comp := graph_comp |>
End

(* Graph category with proper extensionality via mk_cat *)
Definition hostgraph_cat_def:
  hostgraph_cat = mk_cat pre_hostgraph_cat
End

(* Helper: morphism membership characterization *)
Theorem pre_hostgraph_cat_mor:
  !m. m IN pre_hostgraph_cat.mor <=>
      ?G f H. wf_hostgraph G /\ wf_hostgraph H /\
              is_morphism G f H /\
              m = mk_graph_mor G f H
Proof
  rw[pre_hostgraph_cat_def] >>
  simp[GSPECIFICATION] >>
  metis_tac[]
QED

(* Helper: finite map composition is associative *)
Theorem f_o_f_ASSOC:
  !f g h. (h f_o_f g) f_o_f f = h f_o_f (g f_o_f f)
Proof
  rw[fmap_EXT]
  >- (simp[f_o_f_DEF, EXTENSION] >> rw[] >> eq_tac >> rw[f_o_f_DEF] >>
      `(g f_o_f f) ' x = g ' (f ' x)` by fs[f_o_f_DEF] >> fs[])
  >- fs[f_o_f_DEF]
QED

(* Helper: compose_morphism is associative *)
Theorem compose_morphism_assoc:
  !f g h. compose_morphism f (compose_morphism g h) =
          compose_morphism (compose_morphism f g) h
Proof
  rw[compose_morphism_def, morphism_component_equality, f_o_f_ASSOC]
QED

(* Helper: identity morphism for well-formed graphs is a morphism *)
Theorem id_morphism_wf_hostgraph:
  !G. wf_hostgraph G ==> is_morphism G (id_morphism G) G
Proof
  rw[] >> irule id_morphism_is_morphism >> fs[wf_hostgraph_def]
QED

(* Helper: composition of morphisms is a morphism *)
Theorem compose_morphism_is_morphism:
  !G H K f g.
    is_morphism G f H /\ is_morphism H g K ==>
    is_morphism G (compose_morphism f g) K
Proof
  rw[is_morphism_def, is_premorphism_def, compose_morphism_def] >> rpt conj_tac
  (* morphism_dom_ran *)
  >- (fs[morphism_dom_ran_def] >> rpt conj_tac
      (* FDOM nodemap *)
      >- (`FRANGE f.nodemap ⊆ FDOM g.nodemap` by fs[] >>
          imp_res_tac FRANGE_SUBSET_FDOM_COMP_FDOM_EQUALITY >> fs[])
      (* FDOM edgemap *)
      >- (`FRANGE f.edgemap ⊆ FDOM g.edgemap` by fs[] >>
          imp_res_tac FRANGE_SUBSET_FDOM_COMP_FDOM_EQUALITY >> fs[])
      (* FRANGE nodemap *)
      >- (rw[FRANGE_DEF, SUBSET_DEF] >> rw[] >>
          `(g.nodemap f_o_f f.nodemap) ' x' = g.nodemap ' (f.nodemap ' x')` by
            (irule (cj 2 f_o_f_DEF) >> fs[FRANGE_DEF, SUBSET_DEF]) >>
          fs[FRANGE_DEF, SUBSET_DEF] >>
          first_x_assum irule >> qexists_tac `f.nodemap ' x'` >> fs[] \\
          fs[FRANGE_DEF, SUBSET_DEF] >> first_x_assum irule >>
          qexists_tac `x'` >> fs[] \\
          fs[f_o_f_DEF] \\ fs[] \\ metis_tac[])
      (* FRANGE edgemap *)
      >- (rw[FRANGE_DEF, SUBSET_DEF] >> rw[] \\
          `(g.edgemap f_o_f f.edgemap) ' x' = g.edgemap ' (f.edgemap ' x')` by
            (irule (cj 2 f_o_f_DEF) >> fs[FRANGE_DEF, SUBSET_DEF]) \\
          fs[FRANGE_DEF, SUBSET_DEF] >>
          first_x_assum irule >> qexists_tac `f.edgemap ' x'` >> fs[] \\
          first_x_assum irule >> qexists_tac `x'` \\
          conj_tac >- fs[f_o_f_DEF] >> fs[]))
  (* preserve_source *)
  >- (fs[preserve_source_def, morphism_dom_ran_def] \\ metis_tac[f_o_f_ASSOC])
  (* preserve_target *)
  >- (fs[preserve_target_def, morphism_dom_ran_def] >> metis_tac[f_o_f_ASSOC])
  (* preserve_defined_rootedness *)
  >- (fs[preserve_defined_rootedness_def, morphism_dom_ran_def] \\
      rw[SUBMAP_DEF, f_o_f_DEF]
      (* x ∈ G.V *)
      >- (`x IN FDOM (H.p f_o_f f.nodemap)` by fs[SUBMAP_DEF] >>
          fs[f_o_f_DEF] \\ fs[] \\ metis_tac[])
      (* f.nodemap ' x ∈ H.V *)
      >- (`x IN FDOM (H.p f_o_f f.nodemap)` by fs[SUBMAP_DEF] \\
          `x IN FDOM f.nodemap` by fs[f_o_f_DEF] \\
          fs[FRANGE_DEF, SUBSET_DEF] \\
          first_x_assum irule >> qexists_tac `x` >> fs[])
      (* (g.nodemap f_o_f f.nodemap) ' x ∈ FDOM K'.p *)
      >- (`x IN FDOM (H.p f_o_f f.nodemap)` by fs[SUBMAP_DEF] \\
          `f.nodemap ' x IN FDOM H.p` by fs[f_o_f_DEF] \\
          `f.nodemap ' x IN FDOM (K'.p f_o_f g.nodemap)` by fs[SUBMAP_DEF] \\
          `g.nodemap ' (f.nodemap ' x) IN FDOM K'.p` by fs[f_o_f_DEF] \\
          `x IN FDOM f.nodemap` by fs[f_o_f_DEF] \\
          `x IN FDOM (g.nodemap f_o_f f.nodemap)` by
            (fs[f_o_f_DEF, FRANGE_DEF, SUBSET_DEF] >> metis_tac[]) \\
          `(g.nodemap f_o_f f.nodemap) ' x = g.nodemap ' (f.nodemap ' x)` by
            (irule (cj 2 f_o_f_DEF) >> fs[]) \\
          fs[])
      (* G.p ' x ⇔ (K'.p f_o_f g.nodemap f_o_f f.nodemap) ' x *)
      >- (`x IN FDOM (H.p f_o_f f.nodemap)` by fs[SUBMAP_DEF] \\
          `G.p ' x = (H.p f_o_f f.nodemap) ' x` by fs[SUBMAP_DEF] \\
          `(H.p f_o_f f.nodemap) ' x = H.p ' (f.nodemap ' x)` by
            (irule (cj 2 f_o_f_DEF) >> fs[]) \\
          `f.nodemap ' x IN FDOM H.p` by fs[f_o_f_DEF] \\
          `H.p ' (f.nodemap ' x) = (K'.p f_o_f g.nodemap) ' (f.nodemap ' x)` by
            fs[SUBMAP_DEF] \\
          `f.nodemap ' x IN FDOM (K'.p f_o_f g.nodemap)` by fs[SUBMAP_DEF] \\
          `(K'.p f_o_f g.nodemap) ' (f.nodemap ' x) = K'.p ' (g.nodemap ' (f.nodemap ' x))` by
            (irule (cj 2 f_o_f_DEF) >> fs[]) \\
          `x IN FDOM f.nodemap` by fs[f_o_f_DEF] \\
          `(K'.p f_o_f g.nodemap f_o_f f.nodemap) = (K'.p f_o_f g.nodemap) f_o_f f.nodemap` by
            fs[f_o_f_ASSOC] \\
          rw[f_o_f_DEF] \\
          simp[Once f_o_f_DEF] \\
          Cases_on `x IN FDOM ((K'.p f_o_f g.nodemap) f_o_f f.nodemap)`
          >- (`((K'.p f_o_f g.nodemap) f_o_f f.nodemap) ' x = (K'.p f_o_f g.nodemap) ' (f.nodemap ' x)` by
                (irule (cj 2 f_o_f_DEF) >> fs[]) \\ fs[])
          >- (pop_assum mp_tac >> simp[f_o_f_DEF] \\ strip_tac
              >- metis_tac[]
              >- (`f.nodemap ' x IN FRANGE f.nodemap` by (rw[FRANGE_DEF] >> metis_tac[]) \\
                  fs[SUBSET_DEF] \\ metis_tac[])
              >- (`g.nodemap ' (f.nodemap ' x) IN FDOM K'.p` by fs[f_o_f_DEF]))))
  (* preserve_edgelabels *)
  >- (fs[preserve_edgelabels_def, morphism_dom_ran_def] \\ metis_tac[f_o_f_ASSOC])
  (* preserve_nodelabels *)
  >- (fs[preserve_nodelabels_def, morphism_dom_ran_def] >> metis_tac[f_o_f_ASSOC])
QED

(* Main theorem: hostgraph_cat is a category *)
Theorem is_category_hostgraph_cat:
  is_category hostgraph_cat
Proof
  rw[hostgraph_cat_def, is_category_mk_cat, category_axioms_def] >>
  rpt conj_tac
  (* Goal 1: f.dom IN obj *)
  >- fs[pre_hostgraph_cat_def, mk_graph_mor_def]
  (* Goal 2: f.cod IN obj *)
  >- fs[pre_hostgraph_cat_def, mk_graph_mor_def]
  (* Goal 3: id a :- a -> a *)
  >- (rw[maps_to_in_def, id_in_def, maps_to_def, pre_hostgraph_cat_def, restrict_def] >>
      rw[] >> fs[pre_hostgraph_cat_def] >>
      qexistsl_tac [`a`, `graph_id_map a`, `a`] >>
      rw[mk_graph_mor_def, graph_id_map_def] >>
      irule id_morphism_is_morphism >> fs[wf_hostgraph_def])
  (* Goal 4: f o id f.dom = f - right identity *)
  >- (rw[compose_in_def, id_in_def, pre_hostgraph_cat_def, restrict_def]
      >- (simp[graph_comp_def, compose_morphism_def, graph_id_map_def, id_morphism_def] >>
          fs[pre_hostgraph_cat_def, mk_graph_mor_def, GSPECIFICATION] >>
          PairCases_on `x` >> fs[] >>
          simp[morphism_component_equality] >>
          conj_tac >> irule FUN_FMAP_I_f_o_f_right >>
          fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def,
             wf_hostgraph_def, wf_graph_def])
      >- (fs[pre_hostgraph_cat_def, mk_graph_mor_def, GSPECIFICATION] >>
          PairCases_on `x` >> gvs[])
      >- (fs[pre_hostgraph_cat_def, mk_graph_mor_def, GSPECIFICATION] >>
          PairCases_on `x` >> fs[composable_in_def] >> gvs[graph_id_map_def] >>
          `is_morphism x0 (id_morphism x0) x0` by
            (irule id_morphism_is_morphism >> fs[wf_hostgraph_def]) >> fs[]))
  (* Goal 5: id f.cod o f = f - left identity *)
  >- (rw[compose_in_def, id_in_def, pre_hostgraph_cat_def, restrict_def]
      >- (simp[graph_comp_def, compose_morphism_def, graph_id_map_def, id_morphism_def] >>
          fs[pre_hostgraph_cat_def, mk_graph_mor_def, GSPECIFICATION] >>
          PairCases_on `x` >> fs[] >>
          simp[morphism_component_equality] >>
          conj_tac >> irule FUN_FMAP_I_f_o_f_left >>
          fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def,
             wf_hostgraph_def, wf_graph_def])
      >- (fs[pre_hostgraph_cat_def, mk_graph_mor_def, GSPECIFICATION] >>
          PairCases_on `x` >> gvs[])
      >- (fs[pre_hostgraph_cat_def, mk_graph_mor_def, GSPECIFICATION] >>
          PairCases_on `x` >> fs[composable_in_def] >> gvs[graph_id_map_def] >>
          `is_morphism x2 (id_morphism x2) x2` by
            (irule id_morphism_is_morphism >> fs[wf_hostgraph_def]) >> fs[]))
  (* Goal 6: Associativity - (h o g) o f = h o (g o f) *)
  >- (rw[pre_hostgraph_cat_def, compose_in_def, composable_in_def] >> simp[] >>
      fs[restrict_def, mk_graph_mor_def] >> gvs[] >> simp[graph_comp_def] \\
      fs[pre_hostgraph_cat_def, composable_in_def, mk_graph_mor_def, GSPECIFICATION] \\
      PairCases_on `x` >> PairCases_on `x'` >> PairCases_on `x''` >> gvs[] \\
      `is_morphism x'0 (compose_morphism x'1 x''1) x''2` by
        (irule compose_morphism_is_morphism >> qexistsl_tac [`x''0`] >> fs[]) \\
      `is_morphism x0 (compose_morphism x1 x'1) x''0` by
        (irule compose_morphism_is_morphism >> qexistsl_tac [`x'0`] >> fs[]) \\
      simp[] \\ simp[compose_morphism_assoc])
  (* Goal 7: Composition closure - g o f :- x -> z *)
  >- (rw[maps_to_in_def, compose_in_def, maps_to_def]
      >- (fs[restrict_def, composable_in_def, pre_hostgraph_cat_def,
             mk_graph_mor_def, GSPECIFICATION, maps_to_in_def, maps_to_def] \\
          gvs[] \\
          PairCases_on `x'` >> PairCases_on `x''` >> gvs[] \\
          simp[ELIM_UNCURRY] \\
          qexists_tac `(x'0, graph_comp <|dom := x'0; cod := x''0; map := x'1|>
                                        <|dom := x''0; cod := x''2; map := x''1|>, x''2)` \\
          simp[] \\
          `(∃x'. (x'0 = FST x' ∧ x''0 = SND (SND x') ∧ x'1 = FST (SND x')) ∧
                 wf_hostgraph (FST x') ∧ wf_hostgraph (SND (SND x')) ∧
                 is_morphism (FST x') (FST (SND x')) (SND (SND x')))`
            by (qexists_tac `(x'0, x'1, x''0)` >> simp[]) \\
          sg `∃x'. (x''0 = FST x' ∧ x''2 = SND (SND x') ∧ x''1 = FST (SND x')) ∧
                   wf_hostgraph (FST x') ∧ wf_hostgraph (SND (SND x')) ∧
                   is_morphism (FST x') (FST (SND x')) (SND (SND x'))`
          >- (qexists_tac `(x''0, x''1, x''2)` >> simp[] \\ gvs[])
          >- (simp[PULL_EXISTS] \\
              IF_CASES_TAC
              >- (simp[] \\ fs[graph_comp_def] \\
                  irule compose_morphism_is_morphism >>
                  qexistsl_tac [`SND (SND x'³')`] \\ gvs[])
              >- (sg `∃x'³' x'⁴'. ((FST x' = FST x'³' ∧ FST x'' = SND (SND x'³') ∧
                                    FST (SND x') = FST (SND x'³')) ∧
                                   wf_hostgraph (FST x'³') ∧
                                   wf_hostgraph (SND (SND x'³')) ∧
                                   is_morphism (FST x'³') (FST (SND x'³')) (SND (SND x'³'))) ∧
                                  (FST x'' = FST x'⁴' ∧ SND (SND x'') = SND (SND x'⁴') ∧
                                   FST (SND x'') = FST (SND x'⁴')) ∧
                                  wf_hostgraph (FST x'⁴') ∧
                                  wf_hostgraph (SND (SND x'⁴')) ∧
                                  is_morphism (FST x'⁴') (FST (SND x'⁴')) (SND (SND x'⁴'))`
                  >- (qexistsl_tac [`x'`, `x''`] \\ gvs[])
                  >- metis_tac[])))
      >- (fs[maps_to_in_def, maps_to_def, restrict_def, composable_in_def,
             pre_hostgraph_cat_def, mk_graph_mor_def, GSPECIFICATION] \\
          gvs[ELIM_UNCURRY] \\
          `(∃x'³'. (FST x' = FST x'³' ∧ SND (SND x') = SND (SND x'³') ∧
                   FST (SND x') = FST (SND x'³')) ∧
                  wf_hostgraph (FST x'³') ∧ wf_hostgraph (SND (SND x'³')) ∧
                  is_morphism (FST x'³') (FST (SND x'³')) (SND (SND x'³')))`
            by (qexists_tac `x'` >> simp[]) \\
          sg `∃x'⁴'. (SND (SND x') = FST x'⁴' ∧ SND (SND x'') = SND (SND x'⁴') ∧
                     FST (SND x'') = FST (SND x'⁴')) ∧
                    wf_hostgraph (FST x'⁴') ∧ wf_hostgraph (SND (SND x'⁴')) ∧
                    is_morphism (FST x'⁴') (FST (SND x'⁴')) (SND (SND x'⁴'))`
          >- (qexists_tac `(SND (SND x'), FST (SND x''), SND (SND x''))` \\
              simp[] \\ gvs[])
          >- (simp[] \\ IF_CASES_TAC >> simp[] \\ metis_tac[]))
      >- (fs[maps_to_in_def, maps_to_def, restrict_def, composable_in_def,
             pre_hostgraph_cat_def, mk_graph_mor_def, GSPECIFICATION] \\
          gvs[ELIM_UNCURRY] \\ IF_CASES_TAC >> simp[] >> metis_tac[]))
QED

(* ============================================================
   PART 6: Gluing Construction as Pushout
   ============================================================ *)

(*
  The gluing construction from dpoScript.sml creates a pushout:

       K ----b----> R
       |            |
       d            h
       |            |
       v            v
       D ----c----> H = gluing R K m D

  Where K is the interface, R is RHS, D is deletion result.
*)

(* Morphism from D to H (inclusion) *)
Definition gluing_inc_D_mor_def:
  gluing_inc_D_mor D =
    <| nodemap := FUN_FMAP I D.V;
       edgemap := FUN_FMAP I D.E |>
End

Definition gluing_inc_D_def:
  gluing_inc_D D H = mk_graph_mor D (gluing_inc_D_mor D) H
End

(* Morphism from R to H
   For nodes: if v is in the image of K under b, map via d; otherwise keep v
   Since b is injective, LINV gives the unique preimage *)
Definition gluing_inc_R_mor_def:
  gluing_inc_R_mor R K b d =
    <| nodemap := FUN_FMAP (\v. if v IN IMAGE (FAPPLY b.nodemap) K.V
                                then FAPPLY d.nodemap (LINV (FAPPLY b.nodemap) K.V v)
                                else v) R.V;
       edgemap := FUN_FMAP I R.E |>
End

Definition gluing_inc_R_def:
  gluing_inc_R R K D H b d =
    mk_graph_mor R (gluing_inc_R_mor R K b d) H
End

(* Main theorem: gluing forms a pushout square
   This requires H to be the pushout object with:
   - H.V = D.V ∪ (R.V DIFF IMAGE b.nodemap K.V)  -- nodes are union
   - H.E = D.E ∪ R.E                              -- edges are union
   - Source/target functions properly combined
   - The inclusion morphisms are valid
*)
Theorem gluing_is_pushout_square:
  !K R D H b d inc_R inc_D.
    wf_hostgraph K /\ wf_hostgraph R /\ wf_hostgraph D /\ wf_hostgraph H /\
    is_inj_morphism K b R /\
    is_inj_morphism K d D /\
    (* H is the pushout object *)
    H.V = D.V UNION (R.V DIFF IMAGE (FAPPLY b.nodemap) K.V) /\
    H.E = D.E UNION (R.E DIFF IMAGE (FAPPLY b.edgemap) K.E) /\
    (* inc_R and inc_D are valid morphisms *)
    is_morphism R inc_R H /\
    is_morphism D inc_D H /\
    (* Commutativity on nodes: for all n in K, inc_R(b(n)) = inc_D(d(n)) *)
    (!n. n IN K.V ==> inc_R.nodemap ' (b.nodemap ' n) = inc_D.nodemap ' (d.nodemap ' n)) /\
    (* Commutativity on edges: for all e in K, inc_R(b(e)) = inc_D(d(e)) *)
    (!e. e IN K.E ==> inc_R.edgemap ' (b.edgemap ' e) = inc_D.edgemap ' (d.edgemap ' e))
    ==>
    pushout_square hostgraph_cat K R D H
      (mk_graph_mor K b R)
      (mk_graph_mor K d D)
      (mk_graph_mor R inc_R H)
      (mk_graph_mor D inc_D H)
Proof
  rw[pushout_square_def]
  (* Goal 1: b is a morphism from K to R *)
  >- (rw[maps_to_in_def, maps_to_def, hostgraph_cat_def, pre_hostgraph_cat_def,
         mk_graph_mor_def] >> fs[is_inj_morphism_def])
  (* Goal 2: d is a morphism from K to D *)
  >- (rw[maps_to_in_def, maps_to_def, hostgraph_cat_def, pre_hostgraph_cat_def,
         mk_graph_mor_def] >> fs[is_inj_morphism_def])
  (* Goal 3: inc_R is a morphism from R to H *)
  >- rw[maps_to_in_def, maps_to_def, hostgraph_cat_def, pre_hostgraph_cat_def,
        mk_graph_mor_def]
  (* Goal 4: inc_D is a morphism from D to H *)
  >- rw[maps_to_in_def, maps_to_def, hostgraph_cat_def, pre_hostgraph_cat_def,
        mk_graph_mor_def]
  (* Goal 5: Commutativity inc_R o b = inc_D o d *)
  >- (`is_morphism K' b R /\ is_morphism K' d D` by fs[is_inj_morphism_def] >>
      rw[hostgraph_cat_def, compose_in_def, pre_hostgraph_cat_def] >>
      simp[mk_cat_def, graph_comp_def, restrict_def, composable_in_def,
           mk_graph_mor_def] >>
      rw[compose_morphism_def, morphism_component_equality]
      (* Nodemap commutativity *)
      >- (rw[fmap_eq_flookup, FLOOKUP_DEF, f_o_f_DEF] >>
          fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
          `x IN K'.V ==> b.nodemap ' x IN R.V`
            by (fs[SUBSET_DEF, FRANGE_DEF, IN_DEF] >> metis_tac[]) >>
          `x IN K'.V ==> d.nodemap ' x IN D.V`
            by (fs[SUBSET_DEF, FRANGE_DEF, IN_DEF] >> metis_tac[]) >>
          Cases_on `x IN K'.V` >> simp[])
      (* Edgemap commutativity *)
      >- (rw[fmap_eq_flookup, FLOOKUP_DEF, f_o_f_DEF] >>
          fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
          `x IN K'.E ==> b.edgemap ' x IN R.E`
            by (fs[SUBSET_DEF, FRANGE_DEF, IN_DEF] >> metis_tac[]) >>
          `x IN K'.E ==> d.edgemap ' x IN D.E`
            by (fs[SUBSET_DEF, FRANGE_DEF, IN_DEF] >> metis_tac[]) >>
          Cases_on `x IN K'.E` >> simp[]))
QED

(* Helper: FUNION of two morphisms is a morphism when domains partition the source

   This theorem captures the key property for the mediating morphism in a pushout:
   when we have morphisms f_D : D → P and f_R : R → P that agree on the overlap
   (via commutativity), their FUNION gives a morphism H → P where H is the gluing.

   The proof requires:
   1. morphism_dom_ran:
      - FDOM: FUNION gives D.V ∪ (R.V \ b(K.V)) = H.V
      - FRANGE: FRANGE_FUNION_SUBSET gives FRANGE ⊆ P.V ∪ P.V = P.V
   2. preserve_source/target:
      - For e ∈ D.E: use f_D's source/target preservation
      - For e ∈ R.E: use f_R's source/target preservation
   3. preserve_edgelabels/nodelabels:
      - H.l/H.m inherit from D or R based on membership
      - FUNION picks the appropriate morphism
   4. preserve_defined_rootedness:
      - H.p inherits from D or R, FUNION picks correct part
*)
(* Helper theorem A: FDOM of the combined nodemap equals H.V *)
Theorem gluing_med_morph_dom_nodemap:
  !D R Kg H f_D f_R b.
    H.V = D.V UNION (R.V DIFF IMAGE ($' b.nodemap) Kg.V) /\
    FDOM f_D.nodemap = D.V /\ FDOM f_R.nodemap = R.V
    ==>
    FDOM (FUNION f_D.nodemap
          (DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V))) = H.V
Proof
  rw[] >> simp[FDOM_DRESTRICT] >>
  `R.V INTER (R.V DIFF IMAGE ($' b.nodemap) Kg.V) =
   R.V DIFF IMAGE ($' b.nodemap) Kg.V` by (simp[EXTENSION] >> metis_tac[]) >>
  fs[]
QED

(* Helper theorem B: FRANGE of the combined nodemap is a subset of P.V *)
Theorem gluing_med_morph_ran_nodemap:
  !D R Kg P f_D f_R b.
    is_morphism D f_D P /\ is_morphism R f_R P /\
    FDOM f_D.nodemap = D.V /\ FDOM f_R.nodemap = R.V
    ==>
    FRANGE (FUNION f_D.nodemap
            (DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V))) SUBSET P.V
Proof
  rw[] >> simp[FRANGE_DEF, FUNION_DEF, DRESTRICT_DEF, SUBSET_DEF] >> rw[] >>
  Cases_on `x' IN D.V` >> simp[] >>
  fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def, SUBSET_DEF, FRANGE_DEF] >>
  metis_tac[]
QED

(* Helper theorem C: FRANGE of the combined edgemap is a subset of P.E *)
Theorem gluing_med_morph_ran_edgemap:
  !D R Kg P f_D f_R b.
    is_morphism D f_D P /\ is_morphism R f_R P /\
    FDOM f_D.edgemap = D.E /\ FDOM f_R.edgemap = R.E
    ==>
    FRANGE (FUNION f_D.edgemap
            (DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E))) SUBSET P.E
Proof
  rw[] >> simp[FRANGE_DEF, FUNION_DEF, DRESTRICT_DEF, SUBSET_DEF] >> rw[] >>
  Cases_on `x' IN D.E` >> simp[] >>
  fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def, SUBSET_DEF, FRANGE_DEF] >>
  metis_tac[]
QED

(* Helper theorem D: FDOM of the combined edgemap equals H.E *)
Theorem gluing_med_morph_dom_edgemap:
  !D R Kg H f_D f_R b.
    H.E = D.E UNION (R.E DIFF IMAGE ($' b.edgemap) Kg.E) /\
    FDOM f_D.edgemap = D.E /\ FDOM f_R.edgemap = R.E
    ==>
    FDOM (FUNION f_D.edgemap
          (DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E))) = H.E
Proof
  rw[] >> simp[FDOM_DRESTRICT] >>
  `R.E INTER (R.E DIFF IMAGE ($' b.edgemap) Kg.E) =
   R.E DIFF IMAGE ($' b.edgemap) Kg.E` by (simp[EXTENSION] >> metis_tac[]) >>
  fs[]
QED

(* NOTE: The gluing construction uses tagging (tag_nodeid_left/right, tag_edgeid_left/right)
   which ensures D and R have fully disjoint node/edge sets (by tag_disjoint theorem).
   Even-tagged IDs for D, odd-tagged for R means D.V ∩ R.V = ∅ and D.E ∩ R.E = ∅.
   This allows preserve_source/target proofs to proceed without commutativity conditions. *)
Theorem gluing_mediating_morphism:
  !D R Kg H P f_D f_R b.
    wf_hostgraph D /\ wf_hostgraph R /\ wf_hostgraph H /\ wf_hostgraph P /\
    is_morphism D f_D P /\
    is_morphism R f_R P /\
    H.V = D.V UNION (R.V DIFF IMAGE ($' b.nodemap) Kg.V) /\
    H.E = D.E UNION (R.E DIFF IMAGE ($' b.edgemap) Kg.E) /\
    (* Full disjointness - from tagging construction (even vs odd IDs) *)
    DISJOINT D.V R.V /\
    DISJOINT D.E R.E /\
    (* Domain conditions *)
    FDOM f_D.nodemap = D.V /\ FDOM f_D.edgemap = D.E /\
    FDOM f_R.nodemap = R.V /\ FDOM f_R.edgemap = R.E /\
    (* Rootedness domain conditions - GP2 semantics: every node has root status *)
    FDOM D.p = D.V /\ FDOM R.p = R.V /\ FDOM H.p = H.V /\
    (* H inherits structure from D and R *)
    (!e. e IN H.E ==> H.s ' e = if e IN D.E then D.s ' e else R.s ' e) /\
    (!e. e IN H.E ==> H.t ' e = if e IN D.E then D.t ' e else R.t ' e) /\
    (!v. v IN H.V ==> H.l ' v = if v IN D.V then D.l ' v else R.l ' v) /\
    (!e. e IN H.E ==> H.m ' e = if e IN D.E then D.m ' e else R.m ' e) /\
    (!v. v IN H.V ==> H.p ' v = if v IN D.V then D.p ' v else R.p ' v) /\
    (* Boundary consistency: edges not in interface have sources/targets not in interface *)
    (!e. e IN R.E /\ e NOTIN IMAGE ($' b.edgemap) Kg.E ==>
         R.s ' e NOTIN IMAGE ($' b.nodemap) Kg.V) /\
    (!e. e IN R.E /\ e NOTIN IMAGE ($' b.edgemap) Kg.E ==>
         R.t ' e NOTIN IMAGE ($' b.nodemap) Kg.V)
    ==>
    is_morphism H
      <| nodemap := FUNION f_D.nodemap
           (DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V));
         edgemap := FUNION f_D.edgemap
           (DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) |>
      P
Proof
  (* Proof outline:
     - morphism_dom_ran: use helper theorems
     - preserve_source/target: case split on D.E vs R.E DIFF, use DISJOINT + boundary consistency
       For R.E edges not in interface: boundary condition ensures source not in interface node image
     - preserve_defined_rootedness: case split on x ∈ D.V vs x ∈ R.V DIFF
     - preserve_edgelabels: case split on D.E vs R.E DIFF
     - preserve_nodelabels: case split on D.V vs R.V DIFF *)
  rpt strip_tac >> simp[is_morphism_def, is_premorphism_def] >>
  rpt conj_tac
  (* morphism_dom_ran *)
  >- (simp[morphism_dom_ran_def] >> rpt conj_tac
      >- (simp[FDOM_DRESTRICT] >>
          `R.V INTER (R.V DIFF IMAGE ($' b.nodemap) Kg.V) =
           R.V DIFF IMAGE ($' b.nodemap) Kg.V` by (simp[EXTENSION] >> metis_tac[]) >>
          simp[])
      >- (simp[FDOM_DRESTRICT] >>
          `R.E INTER (R.E DIFF IMAGE ($' b.edgemap) Kg.E) =
           R.E DIFF IMAGE ($' b.edgemap) Kg.E` by (simp[EXTENSION] >> metis_tac[]) >>
          simp[])
      >- (irule gluing_med_morph_ran_nodemap >> metis_tac[])
      >- (irule gluing_med_morph_ran_edgemap >> metis_tac[]))
  (* preserve_source - proved using boundary consistency *)
  >- (simp[preserve_source_def] >> rw[Once (GSYM fmap_EQ_THM)]
      (* Domain equality *)
      >- ((`FDOM H.s = H.E` by fs[wf_hostgraph_def, wf_graph_def] >>
           `FDOM P.s = P.E` by fs[wf_hostgraph_def, wf_graph_def] >>
           `FRANGE H.s SUBSET H.V` by fs[wf_hostgraph_def, wf_graph_def]) \\
          (`FDOM (f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) = H.V`
             by (simp[FDOM_DRESTRICT, EXTENSION] >> rw[] >> eq_tac >> rw[] >> fs[]) >>
           `FDOM (f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) = H.E`
             by (simp[FDOM_DRESTRICT, EXTENSION] >> rw[] >> eq_tac >> rw[] >> fs[])) \\
          simp[f_o_f_DEF, EXTENSION, IN_INTER] >> rw[] >> eq_tac >> rpt strip_tac >> gvs[]
          >- (`(f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x = f_D.edgemap ' x`
                by simp[FUNION_DEF] >>
              `FRANGE f_D.edgemap SUBSET P.E` by fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
              `f_D.edgemap ' x IN FRANGE f_D.edgemap` by (simp[FRANGE_DEF] >> qexists `x` >> fs[]) >>
              fs[SUBSET_DEF])
          >- (`(f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x = f_D.edgemap ' x`
                by simp[FUNION_DEF] >>
              `FRANGE f_D.edgemap SUBSET P.E` by fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
              `f_D.edgemap ' x IN FRANGE f_D.edgemap` by (simp[FRANGE_DEF] >> qexists `x` >> fs[]) >>
              fs[SUBSET_DEF])
          >- (`x NOTIN D.E` by (fs[DISJOINT_DEF, IN_INTER, EXTENSION] >> metis_tac[]) >>
              `(f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x = f_R.edgemap ' x`
                by (simp[FUNION_DEF, DRESTRICT_DEF] >> fs[IN_IMAGE]) >>
              `FRANGE f_R.edgemap SUBSET P.E` by fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
              `f_R.edgemap ' x IN FRANGE f_R.edgemap` by (simp[FRANGE_DEF] >> qexists `x` >> fs[]) >>
              fs[SUBSET_DEF])
          >- (`x NOTIN D.E` by (fs[DISJOINT_DEF, IN_INTER, EXTENSION] >> metis_tac[]) >>
              `(f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x = f_R.edgemap ' x`
                by (simp[FUNION_DEF, DRESTRICT_DEF] >> fs[IN_IMAGE]) >>
              `FRANGE f_R.edgemap SUBSET P.E` by fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
              `f_R.edgemap ' x IN FRANGE f_R.edgemap` by (simp[FRANGE_DEF] >> qexists `x` >> fs[]) >>
              fs[SUBSET_DEF])
          >- (disj1_tac >>
              `D.s ' x IN FRANGE D.s` by (simp[FRANGE_DEF] >> qexists `x` >> fs[wf_hostgraph_def, wf_graph_def]) >>
              fs[wf_hostgraph_def, wf_graph_def, SUBSET_DEF])
          >- ((`x NOTIN D.E` by (fs[DISJOINT_DEF, IN_INTER, EXTENSION] >> metis_tac[]) >> simp[]) \\
              (disj2_tac >> conj_tac
               >- (`R.s ' x IN FRANGE R.s` by (simp[FRANGE_DEF] >> qexists `x` >> fs[wf_hostgraph_def, wf_graph_def]) >>
                   fs[wf_hostgraph_def, wf_graph_def, SUBSET_DEF])
               >> rw[] >> spose_not_then strip_assume_tac >>
               `R.s ' x IN IMAGE ($' b.nodemap) Kg.V` by (simp[IN_IMAGE] >> qexists `x'` >> fs[]) >> fs[]) \\
              `x NOTIN IMAGE ($' b.edgemap) Kg.E` by (simp[IN_IMAGE] >> metis_tac[]) \\
              `R.s ' x NOTIN IMAGE ($' b.nodemap) Kg.V` by metis_tac[] \\
              `R.s ' x IN IMAGE ($' b.nodemap) Kg.V` by (simp[IN_IMAGE] >> metis_tac[])))
      (* Pointwise equality *)
      >- ((`FDOM H.s = H.E` by fs[wf_hostgraph_def, wf_graph_def] >>
           `x IN H.E` by (fs[f_o_f_DEF, IN_INTER] >> metis_tac[])) \\
          Cases_on `x IN D.E`
          (* D.E case *)
          >- ((`H.s ' x = D.s ' x` by (first_x_assum (qspec_then `x` mp_tac) >> simp[]) >>
               `D.s ' x IN D.V` by (`D.s ' x IN FRANGE D.s`
                 by (simp[FRANGE_DEF] >> qexists `x` >> fs[wf_hostgraph_def, wf_graph_def]) >>
                 fs[wf_hostgraph_def, wf_graph_def, SUBSET_DEF])) \\
              `(f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) ' (D.s ' x) =
               f_D.nodemap ' (D.s ' x)` by simp[FUNION_DEF] \\
              `(f_D.nodemap f_o_f D.s) ' x = (P.s f_o_f f_D.edgemap) ' x`
                by (fs[is_morphism_def, is_premorphism_def, preserve_source_def] >> metis_tac[]) \\
              `(f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x =
               f_D.edgemap ' x` by simp[FUNION_DEF] \\
              `x IN FDOM D.s` by fs[wf_hostgraph_def, wf_graph_def] \\
              `D.s ' x IN FDOM f_D.nodemap` by fs[] \\
              `x IN FDOM (f_D.nodemap f_o_f D.s)` by (simp[f_o_f_DEF] >> fs[]) \\
              `(f_D.nodemap f_o_f D.s) ' x = f_D.nodemap ' (D.s ' x)` by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
              `((f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) f_o_f H.s) ' x =
               (f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) ' (H.s ' x)`
                by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
              `f_D.edgemap ' x IN P.E`
                by (fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def, FRANGE_DEF, SUBSET_DEF] >> metis_tac[]) \\
              `x IN FDOM (P.s f_o_f (f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)))`
                by (simp[f_o_f_DEF, FUNION_DEF] >> fs[wf_hostgraph_def, wf_graph_def]) \\
              `(P.s f_o_f (f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E))) ' x =
               P.s ' ((f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x)`
                by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
              `x IN FDOM (P.s f_o_f f_D.edgemap)` by (simp[f_o_f_DEF] >> fs[wf_hostgraph_def, wf_graph_def]) \\
              `(P.s f_o_f f_D.edgemap) ' x = P.s ' (f_D.edgemap ' x)` by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
              metis_tac[])
          (* R.E case - uses boundary consistency *)
          >- (`x IN R.E` by (gvs[EXTENSION, DISJOINT_DEF, IN_INTER] >> metis_tac[]) \\
              `x NOTIN IMAGE ($' b.edgemap) Kg.E` by gvs[] \\
              `H.s ' x = R.s ' x` by (first_x_assum (qspec_then `x` mp_tac) >> simp[]) \\
              `R.s ' x NOTIN IMAGE ($' b.nodemap) Kg.V` by metis_tac[] \\
              sg `R.s ' x IN R.V`
              >- (sg `R.s ' x IN FRANGE R.s`
                  >- (simp[FRANGE_DEF] >> qexists `x` >> fs[wf_hostgraph_def, wf_graph_def])
                  >- fs[wf_hostgraph_def, wf_graph_def, SUBSET_DEF])
              >- (`(f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) ' (R.s ' x) =
                   f_R.nodemap ' (R.s ' x)`
                    by (simp[FUNION_DEF, DRESTRICT_DEF] >> fs[DISJOINT_DEF, IN_INTER, EXTENSION] >> metis_tac[]) \\
                  `(f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x =
                   f_R.edgemap ' x` by (simp[FUNION_DEF, DRESTRICT_DEF] >> fs[]) \\
                  `x IN FDOM (f_R.nodemap f_o_f R.s)` by (simp[f_o_f_DEF] >> fs[wf_hostgraph_def, wf_graph_def]) \\
                  `(f_R.nodemap f_o_f R.s) ' x = f_R.nodemap ' (R.s ' x)` by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
                  `(f_R.nodemap f_o_f R.s) ' x = (P.s f_o_f f_R.edgemap) ' x`
                    by (fs[is_morphism_def, is_premorphism_def, preserve_source_def] >> metis_tac[]) \\
                  `f_R.edgemap ' x IN P.E`
                    by (fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def, FRANGE_DEF, SUBSET_DEF] >> metis_tac[]) \\
                  `x IN FDOM (P.s f_o_f f_R.edgemap)` by (simp[f_o_f_DEF] >> fs[wf_hostgraph_def, wf_graph_def]) \\
                  `(P.s f_o_f f_R.edgemap) ' x = P.s ' (f_R.edgemap ' x)` by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
                  `x IN FDOM (P.s f_o_f (f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)))`
                    by (simp[f_o_f_DEF, FUNION_DEF, DRESTRICT_DEF] >> fs[wf_hostgraph_def, wf_graph_def]) \\
                  `(P.s f_o_f (f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E))) ' x =
                   P.s ' ((f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x)`
                    by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
                  `((f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) f_o_f H.s) ' x =
                   (f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) ' (H.s ' x)`
                    by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
                  metis_tac[]))))
  (* preserve_target - proved using boundary consistency (symmetric to preserve_source) *)
  >- (simp[preserve_target_def] >> rw[Once (GSYM fmap_EQ_THM)]
      (* Domain equality *)
      >- ((`FDOM H.t = H.E` by fs[wf_hostgraph_def, wf_graph_def] >>
           `FDOM P.t = P.E` by fs[wf_hostgraph_def, wf_graph_def] >>
           `FRANGE H.t SUBSET H.V` by fs[wf_hostgraph_def, wf_graph_def]) \\
          (`FDOM (f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) = H.V`
             by (simp[FDOM_DRESTRICT, EXTENSION] >> rw[] >> eq_tac >> rw[] >> fs[]) >>
           `FDOM (f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) = H.E`
             by (simp[FDOM_DRESTRICT, EXTENSION] >> rw[] >> eq_tac >> rw[] >> fs[])) \\
          simp[f_o_f_DEF, EXTENSION, IN_INTER] >> rw[] >> eq_tac >> rpt strip_tac >> gvs[]
          >- (`(f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x = f_D.edgemap ' x`
                by simp[FUNION_DEF] >>
              `FRANGE f_D.edgemap SUBSET P.E` by fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
              `f_D.edgemap ' x IN FRANGE f_D.edgemap` by (simp[FRANGE_DEF] >> qexists `x` >> fs[]) >>
              fs[SUBSET_DEF])
          >- (`(f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x = f_D.edgemap ' x`
                by simp[FUNION_DEF] >>
              `FRANGE f_D.edgemap SUBSET P.E` by fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
              `f_D.edgemap ' x IN FRANGE f_D.edgemap` by (simp[FRANGE_DEF] >> qexists `x` >> fs[]) >>
              fs[SUBSET_DEF])
          >- (`x NOTIN D.E` by (fs[DISJOINT_DEF, IN_INTER, EXTENSION] >> metis_tac[]) >>
              `(f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x = f_R.edgemap ' x`
                by (simp[FUNION_DEF, DRESTRICT_DEF] >> fs[IN_IMAGE]) >>
              `FRANGE f_R.edgemap SUBSET P.E` by fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
              `f_R.edgemap ' x IN FRANGE f_R.edgemap` by (simp[FRANGE_DEF] >> qexists `x` >> fs[]) >>
              fs[SUBSET_DEF])
          >- (`x NOTIN D.E` by (fs[DISJOINT_DEF, IN_INTER, EXTENSION] >> metis_tac[]) >>
              `(f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x = f_R.edgemap ' x`
                by (simp[FUNION_DEF, DRESTRICT_DEF] >> fs[IN_IMAGE]) >>
              `FRANGE f_R.edgemap SUBSET P.E` by fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
              `f_R.edgemap ' x IN FRANGE f_R.edgemap` by (simp[FRANGE_DEF] >> qexists `x` >> fs[]) >>
              fs[SUBSET_DEF])
          >- (disj1_tac >>
              `D.t ' x IN FRANGE D.t` by (simp[FRANGE_DEF] >> qexists `x` >> fs[wf_hostgraph_def, wf_graph_def]) >>
              fs[wf_hostgraph_def, wf_graph_def, SUBSET_DEF])
          >- ((`x NOTIN D.E` by (fs[DISJOINT_DEF, IN_INTER, EXTENSION] >> metis_tac[]) >> simp[]) \\
              (disj2_tac >> conj_tac
               >- (`R.t ' x IN FRANGE R.t` by (simp[FRANGE_DEF] >> qexists `x` >> fs[wf_hostgraph_def, wf_graph_def]) >>
                   fs[wf_hostgraph_def, wf_graph_def, SUBSET_DEF])
               >> rw[] >> spose_not_then strip_assume_tac >>
               `R.t ' x IN IMAGE ($' b.nodemap) Kg.V` by (simp[IN_IMAGE] >> qexists `x'` >> fs[]) >> fs[]) \\
              `x NOTIN IMAGE ($' b.edgemap) Kg.E` by (simp[IN_IMAGE] >> metis_tac[]) \\
              `R.t ' x NOTIN IMAGE ($' b.nodemap) Kg.V` by metis_tac[] \\
              `R.t ' x IN IMAGE ($' b.nodemap) Kg.V` by (simp[IN_IMAGE] >> metis_tac[])))
      (* Pointwise equality *)
      >- ((`FDOM H.t = H.E` by fs[wf_hostgraph_def, wf_graph_def] >>
           `x IN H.E` by (fs[f_o_f_DEF, IN_INTER] >> metis_tac[])) \\
          Cases_on `x IN D.E`
          (* D.E case *)
          >- ((`H.t ' x = D.t ' x` by (first_x_assum (qspec_then `x` mp_tac) >> simp[]) >>
               `D.t ' x IN D.V` by (`D.t ' x IN FRANGE D.t`
                 by (simp[FRANGE_DEF] >> qexists `x` >> fs[wf_hostgraph_def, wf_graph_def]) >>
                 fs[wf_hostgraph_def, wf_graph_def, SUBSET_DEF])) \\
              `(f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) ' (D.t ' x) =
               f_D.nodemap ' (D.t ' x)` by simp[FUNION_DEF] \\
              `(f_D.nodemap f_o_f D.t) ' x = (P.t f_o_f f_D.edgemap) ' x`
                by (fs[is_morphism_def, is_premorphism_def, preserve_target_def] >> metis_tac[]) \\
              `(f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x =
               f_D.edgemap ' x` by simp[FUNION_DEF] \\
              `x IN FDOM D.t` by fs[wf_hostgraph_def, wf_graph_def] \\
              `D.t ' x IN FDOM f_D.nodemap` by fs[] \\
              `x IN FDOM (f_D.nodemap f_o_f D.t)` by (simp[f_o_f_DEF] >> fs[]) \\
              `(f_D.nodemap f_o_f D.t) ' x = f_D.nodemap ' (D.t ' x)` by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
              `((f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) f_o_f H.t) ' x =
               (f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) ' (H.t ' x)`
                by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
              `f_D.edgemap ' x IN P.E`
                by (fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def, FRANGE_DEF, SUBSET_DEF] >> metis_tac[]) \\
              `x IN FDOM (P.t f_o_f (f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)))`
                by (simp[f_o_f_DEF, FUNION_DEF] >> fs[wf_hostgraph_def, wf_graph_def]) \\
              `(P.t f_o_f (f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E))) ' x =
               P.t ' ((f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x)`
                by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
              `x IN FDOM (P.t f_o_f f_D.edgemap)` by (simp[f_o_f_DEF] >> fs[wf_hostgraph_def, wf_graph_def]) \\
              `(P.t f_o_f f_D.edgemap) ' x = P.t ' (f_D.edgemap ' x)` by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
              metis_tac[])
          (* R.E case - uses boundary consistency *)
          >- (`x IN R.E` by (gvs[EXTENSION, DISJOINT_DEF, IN_INTER] >> metis_tac[]) \\
              `x NOTIN IMAGE ($' b.edgemap) Kg.E` by gvs[] \\
              `H.t ' x = R.t ' x` by (first_x_assum (qspec_then `x` mp_tac) >> simp[]) \\
              `R.t ' x NOTIN IMAGE ($' b.nodemap) Kg.V` by metis_tac[] \\
              sg `R.t ' x IN R.V`
              >- (sg `R.t ' x IN FRANGE R.t`
                  >- (simp[FRANGE_DEF] >> qexists `x` >> fs[wf_hostgraph_def, wf_graph_def])
                  >- fs[wf_hostgraph_def, wf_graph_def, SUBSET_DEF])
              >- (`(f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) ' (R.t ' x) =
                   f_R.nodemap ' (R.t ' x)`
                    by (simp[FUNION_DEF, DRESTRICT_DEF] >> fs[DISJOINT_DEF, IN_INTER, EXTENSION] >> metis_tac[]) \\
                  `(f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x =
                   f_R.edgemap ' x` by (simp[FUNION_DEF, DRESTRICT_DEF] >> fs[]) \\
                  `x IN FDOM (f_R.nodemap f_o_f R.t)` by (simp[f_o_f_DEF] >> fs[wf_hostgraph_def, wf_graph_def]) \\
                  `(f_R.nodemap f_o_f R.t) ' x = f_R.nodemap ' (R.t ' x)` by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
                  `(f_R.nodemap f_o_f R.t) ' x = (P.t f_o_f f_R.edgemap) ' x`
                    by (fs[is_morphism_def, is_premorphism_def, preserve_target_def] >> metis_tac[]) \\
                  `f_R.edgemap ' x IN P.E`
                    by (fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def, FRANGE_DEF, SUBSET_DEF] >> metis_tac[]) \\
                  `x IN FDOM (P.t f_o_f f_R.edgemap)` by (simp[f_o_f_DEF] >> fs[wf_hostgraph_def, wf_graph_def]) \\
                  `(P.t f_o_f f_R.edgemap) ' x = P.t ' (f_R.edgemap ' x)` by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
                  `x IN FDOM (P.t f_o_f (f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)))`
                    by (simp[f_o_f_DEF, FUNION_DEF, DRESTRICT_DEF] >> fs[wf_hostgraph_def, wf_graph_def]) \\
                  `(P.t f_o_f (f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E))) ' x =
                   P.t ' ((f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x)`
                    by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
                  `((f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) f_o_f H.t) ' x =
                   (f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) ' (H.t ' x)`
                    by (imp_res_tac (cj 2 f_o_f_DEF) >> fs[]) \\
                  metis_tac[]))))
  (* preserve_defined_rootedness *)
  >- (simp[preserve_defined_rootedness_def, SUBMAP_DEF, f_o_f_DEF] >>
      rw[FUNION_DEF, DRESTRICT_DEF, f_o_f_DEF]
      (* D case: derive f_D(x) ∈ FDOM P.p from morphism SUBMAP property *)
      >- (`D.p ⊑ P.p f_o_f f_D.nodemap` by fs[is_morphism_def, is_premorphism_def,
             preserve_defined_rootedness_def] >>
          `x IN FDOM D.p` by fs[] >>
          `x IN FDOM (P.p f_o_f f_D.nodemap)` by fs[SUBMAP_DEF] >> fs[f_o_f_DEF])
      >- (simp[f_o_f_DEF, FUNION_DEF, DRESTRICT_DEF] >>
          `(f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) ' x =
           f_D.nodemap ' x` by simp[FUNION_DEF] >>
          fs[f_o_f_DEF] >> simp[SimpRHS, f_o_f_DEF] >>
          (* Derive f_D(x) ∈ FDOM P.p from morphism SUBMAP property *)
          `D.p ⊑ P.p f_o_f f_D.nodemap` by
            fs[is_morphism_def, is_premorphism_def, preserve_defined_rootedness_def] >>
          `x IN FDOM (P.p f_o_f f_D.nodemap)` by
            (fs[SUBMAP_DEF] >> first_x_assum (qspec_then `x` mp_tac) >> simp[]) >>
          `f_D.nodemap ' x IN FDOM P.p` by fs[f_o_f_DEF] >>
          `D.p ' x = P.p ' (f_D.nodemap ' x)` by
            fs[is_morphism_def, is_premorphism_def, preserve_defined_rootedness_def,
               SUBMAP_DEF, f_o_f_DEF] >>
          `x IN FDOM (P.p f_o_f (f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)))` by
            (simp[f_o_f_DEF, FUNION_DEF] >>
             fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def, FRANGE_DEF, SUBSET_DEF]) >>
          imp_res_tac (cj 2 f_o_f_DEF) >> metis_tac[])
      (* R case: derive f_R(x) ∈ FDOM P.p from morphism SUBMAP property *)
      >- (`R.p ⊑ P.p f_o_f f_R.nodemap` by fs[is_morphism_def, is_premorphism_def,
             preserve_defined_rootedness_def] >>
          `x IN FDOM R.p` by fs[] >>
          `x IN FDOM (P.p f_o_f f_R.nodemap)` by fs[SUBMAP_DEF] >> fs[f_o_f_DEF])
      >- (`(f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) ' x =
           f_R.nodemap ' x` by (simp[FUNION_DEF, DRESTRICT_DEF] >> fs[IN_IMAGE] >> metis_tac[]) >>
          (* Derive f_R(x) ∈ FDOM P.p from morphism SUBMAP property *)
          `R.p ⊑ P.p f_o_f f_R.nodemap` by
            fs[is_morphism_def, is_premorphism_def, preserve_defined_rootedness_def] >>
          `x IN FDOM (P.p f_o_f f_R.nodemap)` by
            (fs[SUBMAP_DEF] >> first_x_assum (qspec_then `x` mp_tac) >> simp[]) >>
          `f_R.nodemap ' x IN FDOM P.p` by fs[f_o_f_DEF] >>
          `R.p ' x = P.p ' (f_R.nodemap ' x)` by
            fs[is_morphism_def, is_premorphism_def, preserve_defined_rootedness_def,
               SUBMAP_DEF, f_o_f_DEF] >>
          `x IN FDOM (P.p f_o_f (f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)))` by
            (simp[f_o_f_DEF, FUNION_DEF, DRESTRICT_DEF, IN_IMAGE] >>
             fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def, FRANGE_DEF, SUBSET_DEF]) >>
          imp_res_tac (cj 2 f_o_f_DEF) >> metis_tac[])
      >- (fs[] >> disj2_tac >> qexists_tac `x'` >> fs[]))
  (* preserve_edgelabels *)
  >- (simp[preserve_edgelabels_def] >> simp[fmap_EQ_THM, f_o_f_DEF] >>
      rw[Once (GSYM fmap_EQ_THM)]
      >- (`FDOM H.m = H.E` by fs[wf_hostgraph_def] >>
          `FDOM P.m = P.E` by fs[wf_hostgraph_def] >>
          simp[f_o_f_DEF, FUNION_DEF, DRESTRICT_DEF] >>
          `R.E INTER (R.E DIFF IMAGE ($' b.edgemap) Kg.E) = R.E DIFF IMAGE ($' b.edgemap) Kg.E`
            by (simp[EXTENSION] >> metis_tac[]) >>
          simp[EXTENSION, IN_IMAGE] >> rw[] >> rpt strip_tac >>
          fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def, FRANGE_DEF, SUBSET_DEF] >>
          metis_tac[])
      >- (`FDOM H.m = H.E` by fs[wf_hostgraph_def] >>
          `x IN H.E` by metis_tac[] >>
          Cases_on `x IN D.E`
          >- (`H.m ' x = D.m ' x` by metis_tac[] >>
              `D.m = P.m f_o_f f_D.edgemap` by fs[is_morphism_def, preserve_edgelabels_def] >>
              `x IN FDOM D.m` by fs[wf_hostgraph_def] >>
              `D.m ' x = P.m ' (f_D.edgemap ' x)` by
                (pop_assum mp_tac >> simp[f_o_f_DEF] >>
                 fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def,
                    FRANGE_DEF, SUBSET_DEF, wf_hostgraph_def] >> metis_tac[]) >>
              `(f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x =
               f_D.edgemap ' x` by simp[FUNION_DEF] >>
              `x IN FDOM (P.m f_o_f (f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)))` by
                (simp[f_o_f_DEF, FUNION_DEF] >>
                 fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def,
                    FRANGE_DEF, SUBSET_DEF, wf_hostgraph_def] >> metis_tac[]) >>
              imp_res_tac (cj 2 f_o_f_DEF) >> metis_tac[])
          >- (`x IN D.E \/ x IN (R.E DIFF IMAGE ($' b.edgemap) Kg.E)` by metis_tac[IN_UNION] >>
              `x IN R.E DIFF IMAGE ($' b.edgemap) Kg.E` by metis_tac[] >>
              `H.m ' x = R.m ' x` by metis_tac[] >>
              `R.m = P.m f_o_f f_R.edgemap` by fs[is_morphism_def, preserve_edgelabels_def] >>
              `x IN R.E` by fs[IN_DIFF] >>
              `x IN FDOM R.m` by fs[wf_hostgraph_def] >>
              `R.m ' x = P.m ' (f_R.edgemap ' x)` by
                (pop_assum mp_tac >> pop_assum mp_tac >> simp[f_o_f_DEF] >>
                 fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def,
                    FRANGE_DEF, SUBSET_DEF, wf_hostgraph_def] >> metis_tac[]) >>
              `(f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) ' x =
               f_R.edgemap ' x` by
                (simp[FUNION_DEF, DRESTRICT_DEF, IN_IMAGE] >> fs[IN_DIFF, IN_IMAGE] >> metis_tac[]) >>
              `x IN FDOM (P.m f_o_f (f_D.edgemap ⊌ DRESTRICT f_R.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)))` by
                (simp[f_o_f_DEF, FUNION_DEF, DRESTRICT_DEF, IN_DIFF, IN_IMAGE] >>
                 fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def,
                    FRANGE_DEF, SUBSET_DEF, wf_hostgraph_def, IN_DIFF, IN_IMAGE] >> metis_tac[]) >>
              imp_res_tac (cj 2 f_o_f_DEF) >> metis_tac[])))
  (* preserve_nodelabels *)
  >- (simp[preserve_nodelabels_def] >> rw[Once (GSYM fmap_EQ_THM)]
      >- (`FDOM H.l = H.V` by fs[wf_hostgraph_def] >>
          `FDOM P.l = P.V` by fs[wf_hostgraph_def] >>
          simp[f_o_f_DEF, FUNION_DEF, DRESTRICT_DEF, EXTENSION, IN_IMAGE] >>
          rw[] >> rpt strip_tac >>
          fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def, FRANGE_DEF, SUBSET_DEF, wf_hostgraph_def] >>
          metis_tac[])
      >- (`FDOM H.l = H.V` by fs[wf_hostgraph_def] >>
          `x IN H.V` by metis_tac[] >>
          Cases_on `x IN D.V`
          >- (`H.l ' x = D.l ' x` by metis_tac[] >>
              `D.l = P.l f_o_f f_D.nodemap` by fs[is_morphism_def, preserve_nodelabels_def] >>
              `x IN FDOM D.l` by fs[wf_hostgraph_def] >>
              `D.l ' x = P.l ' (f_D.nodemap ' x)` by
                (pop_assum mp_tac >> simp[f_o_f_DEF] >>
                 fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def,
                    FRANGE_DEF, SUBSET_DEF, wf_hostgraph_def] >> metis_tac[]) >>
              `(f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) ' x =
               f_D.nodemap ' x` by simp[FUNION_DEF] >>
              `x IN FDOM (P.l f_o_f (f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)))` by
                (simp[f_o_f_DEF, FUNION_DEF] >>
                 fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def,
                    FRANGE_DEF, SUBSET_DEF, wf_hostgraph_def] >> metis_tac[]) >>
              imp_res_tac (cj 2 f_o_f_DEF) >> metis_tac[])
          >- (`x IN D.V \/ x IN (R.V DIFF IMAGE ($' b.nodemap) Kg.V)` by metis_tac[IN_UNION] >>
              `x IN R.V DIFF IMAGE ($' b.nodemap) Kg.V` by metis_tac[] >>
              `H.l ' x = R.l ' x` by metis_tac[] >>
              `R.l = P.l f_o_f f_R.nodemap` by fs[is_morphism_def, preserve_nodelabels_def] >>
              `x IN R.V` by fs[IN_DIFF] >>
              `x IN FDOM R.l` by fs[wf_hostgraph_def] >>
              `R.l ' x = P.l ' (f_R.nodemap ' x)` by
                (pop_assum mp_tac >> pop_assum mp_tac >> simp[f_o_f_DEF] >>
                 fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def,
                    FRANGE_DEF, SUBSET_DEF, wf_hostgraph_def] >> metis_tac[]) >>
              `(f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) ' x =
               f_R.nodemap ' x` by
                (simp[FUNION_DEF, DRESTRICT_DEF, IN_IMAGE] >> fs[IN_DIFF, IN_IMAGE] >> metis_tac[]) >>
              `x IN FDOM (P.l f_o_f (f_D.nodemap ⊌ DRESTRICT f_R.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)))` by
                (simp[f_o_f_DEF, FUNION_DEF, DRESTRICT_DEF, IN_DIFF, IN_IMAGE] >>
                 fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def,
                    FRANGE_DEF, SUBSET_DEF, wf_hostgraph_def, IN_DIFF, IN_IMAGE] >> metis_tac[]) >>
              imp_res_tac (cj 2 f_o_f_DEF) >> metis_tac[])))
QED

(* Helper: composition with identity morphism in hostgraph_cat *)
Theorem hostgraph_comp_identity:
  !G H P f inc.
    wf_hostgraph G /\ wf_hostgraph H /\ wf_hostgraph P /\
    is_morphism G inc H /\
    is_morphism H f P /\
    (!v. v IN G.V ==> inc.nodemap ' v = v) /\
    (!e. e IN G.E ==> inc.edgemap ' e = e) /\
    FDOM f.nodemap = G.V /\
    FDOM f.edgemap = G.E
    ==>
    (mk_graph_mor H f P) o (mk_graph_mor G inc H) -:hostgraph_cat =
    mk_graph_mor G f P
Proof
  (* Composition with identity-like inclusion gives the original morphism.
     Key: f_o_f with identity on domain gives f back when domains match. *)
  rpt strip_tac >> simp[mk_graph_mor_def] >>
  sg `composable_in hostgraph_cat <|dom := G; cod := H; map := inc|>
        <|dom := H; cod := P; map := f|>`
  >- (simp[composable_in_def, hostgraph_cat_def, mk_cat_def,
           pre_hostgraph_cat_def] >>
      simp[mk_graph_mor_def] >> metis_tac[])
  >- (simp[Once compose_in_def, restrict_def, hostgraph_cat_def, mk_cat_def] >>
      simp[composable_in_def, hostgraph_cat_def, mk_cat_def,
           pre_hostgraph_cat_def, pre_hostgraph_cat_mor, mk_graph_mor_def] >>
      simp[graph_comp_def, compose_morphism_def] >>
      simp[morphism_component_equality] >>
      conj_tac >> simp[fmap_EQ_THM, f_o_f_DEF]
      >- (rw[fmap_EQ_THM, f_o_f_DEF] >>
          rw[Once (GSYM fmap_EQ_THM)]
          >- (simp[f_o_f_DEF] >>
              `FDOM inc.nodemap = G.V` by
                (fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def]) >>
              simp[] >> simp[EXTENSION] >> rw[] >> eq_tac >> rw[])
          >- (simp[f_o_f_DEF] >> fs[] >> fs[f_o_f_DEF] >>
              `FDOM inc.nodemap = G.V` by
                (fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def]) >>
              `x IN G.V` by fs[] >> fs[]))
      >- (rw[Once (GSYM fmap_EQ_THM)]
          >- (simp[f_o_f_DEF] >>
              `FDOM inc.edgemap = G.E` by
                (fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def]) >>
              simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >> fs[])
          >- (fs[f_o_f_DEF] >>
              `FDOM inc.edgemap = G.E` by
                (fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def]) >>
              `x IN G.E` by fs[] >> fs[] >> simp[f_o_f_DEF])))
QED

(* Helper: composition u o inc_R = i' in gluing pushout

   Key insight: inc_R is "almost identity" on R, and u extends i' via j'.

   For v ∈ R.V:
   - If v ∈ R.V \ b(K.V): inc_R(v) = v, u(v) = i'(v) from DRESTRICT part
   - If v = b(k): inc_R(b(k)) = d(k), u(d(k)) = j'(d(k)) = i'(b(k)) by commutativity
*)
Theorem gluing_comp_inc_R:
  !Kg R D H P' b d inc_R i' j' u.
    wf_hostgraph Kg /\ wf_hostgraph R /\ wf_hostgraph D /\ wf_hostgraph H /\
    wf_hostgraph P' /\
    is_inj_morphism Kg b R /\ is_inj_morphism Kg d D /\
    is_inj_morphism R inc_R H /\
    is_morphism R i'.map P' /\ is_morphism D j'.map P' /\
    H.V = D.V UNION (R.V DIFF IMAGE ($' b.nodemap) Kg.V) /\
    H.E = D.E UNION (R.E DIFF IMAGE ($' b.edgemap) Kg.E) /\
    (* inc_R is identity on R \ b(Kg), and maps b(Kg) to d(Kg) *)
    (!v. v IN R.V /\ v NOTIN IMAGE ($' b.nodemap) Kg.V ==> inc_R.nodemap ' v = v) /\
    (!e. e IN R.E /\ e NOTIN IMAGE ($' b.edgemap) Kg.E ==> inc_R.edgemap ' e = e) /\
    (!n. n IN Kg.V ==> inc_R.nodemap ' (b.nodemap ' n) = d.nodemap ' n) /\
    (!e. e IN Kg.E ==> inc_R.edgemap ' (b.edgemap ' e) = d.edgemap ' e) /\
    (* Commutativity: i' o b = j' o d *)
    (!n. n IN Kg.V ==> i'.map.nodemap ' (b.nodemap ' n) = j'.map.nodemap ' (d.nodemap ' n)) /\
    (!e. e IN Kg.E ==> i'.map.edgemap ' (b.edgemap ' e) = j'.map.edgemap ' (d.edgemap ' e)) /\
    (* u is the mediating morphism *)
    u.nodemap = FUNION j'.map.nodemap
         (DRESTRICT i'.map.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) /\
    u.edgemap = FUNION j'.map.edgemap
         (DRESTRICT i'.map.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) /\
    is_morphism H u P' /\
    (* Domain conditions *)
    FDOM i'.map.nodemap = R.V /\ FDOM i'.map.edgemap = R.E /\
    FDOM j'.map.nodemap = D.V /\ FDOM j'.map.edgemap = D.E /\
    FDOM inc_R.nodemap = R.V /\ FDOM inc_R.edgemap = R.E /\
    FDOM b.nodemap = Kg.V /\ FDOM b.edgemap = Kg.E /\
    FDOM d.nodemap = Kg.V /\ FDOM d.edgemap = Kg.E /\
    FRANGE b.nodemap SUBSET R.V /\ FRANGE d.nodemap SUBSET D.V /\
    (* Disjointness: fresh nodes from R don't overlap with D *)
    D.V INTER (R.V DIFF IMAGE ($' b.nodemap) Kg.V) = EMPTY /\
    D.E INTER (R.E DIFF IMAGE ($' b.edgemap) Kg.E) = EMPTY /\
    (* i' and j' are proper category morphisms *)
    i'.dom = R /\ i'.cod = P' /\ j'.dom = D /\ j'.cod = P'
    ==>
    mk_graph_mor H u P' o mk_graph_mor R inc_R H -:hostgraph_cat = i'
Proof
  rpt strip_tac \\
  `mk_graph_mor R inc_R H ≈> mk_graph_mor H u P' -:hostgraph_cat` by (
    simp[composable_in_def, hostgraph_cat_def, pre_hostgraph_cat_def,
         mk_graph_mor_def] >> fs[is_inj_morphism_def] >> metis_tac[]) \\
  imp_res_tac compose_in_thm >> simp[hostgraph_cat_def] >>
  `mk_graph_mor R inc_R H ≈> mk_graph_mor H u P' -:pre_hostgraph_cat` by (
    simp[composable_in_def, pre_hostgraph_cat_def, mk_graph_mor_def] >>
    fs[is_inj_morphism_def] >> metis_tac[]) >>
  simp[mk_cat_def, compose_def, restrict_def, mk_graph_mor_def] >>
  fs[mk_graph_mor_def] >>
  simp[pre_hostgraph_cat_def, graph_comp_def, compose_morphism_def,
       categoryTheory.morphism_component_equality,
       morphismTheory.morphism_component_equality] \\
  simp[GSYM fmap_EQ_THM, f_o_f_DEF] \\
  simp[DRESTRICT_DEF, FUNION_DEF] \\
  rpt conj_tac
  >- ((* nodemap domain *)
      simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >>
      Cases_on `?k. k IN Kg.V /\ x = b.nodemap ' k`
      >- (fs[] >> disj1_tac >>
          `d.nodemap ' k IN FRANGE d.nodemap` by
            (simp[FRANGE_DEF] >> qexists_tac `k` >> fs[]) >>
          fs[SUBSET_DEF])
      >- (disj2_tac >>
          `inc_R.nodemap ' x = x` by
            (first_x_assum (qspec_then `x` mp_tac) >> simp[IN_IMAGE] >> fs[]) >>
          fs[IN_IMAGE]))
  >- ((* nodemap values - batch-safe version *)
      rw[] >> Cases_on `?k. k IN Kg.V /\ x = b.nodemap ' k`
      >- (fs[] >> first_x_assum (qspec_then `k` mp_tac) >> simp[])
      >- ((* Case: x not in b(Kg.V), inc_R(x) in D.V - contradiction *)
          qpat_x_assum `!v. v IN i'.dom.V /\ _ ==> _` (qspec_then `x` mp_tac) \\
          impl_tac
          >- (rw[] >> spose_not_then strip_assume_tac >> fs[] \\
              first_x_assum (qspec_then `x'` mp_tac) >> simp[])
          >- (strip_tac >> fs[] \\
              `x IN j'.dom.V INTER (i'.dom.V DIFF IMAGE ($' b.nodemap) Kg.V)` by
                (simp[IN_INTER, IN_DIFF, IN_IMAGE] >> rw[] >>
                 first_x_assum (qspec_then `x''` mp_tac) >> simp[]) \\
              fs[EXTENSION] \\
              qpat_x_assum `!x'. x' NOTIN j'.dom.V \/ _ \/ _`
                (qspec_then `x` mp_tac) >> simp[] \\
              strip_tac >> first_x_assum (qspec_then `x''` mp_tac) >> simp[]))
      >- ((* Case: x = b(k), inc_R(x) not in D.V - contradiction *)
          fs[] >>
          `inc_R.nodemap ' x = d.nodemap ' k` by simp[] >>
          `d.nodemap ' k IN FRANGE d.nodemap` by
            (simp[FRANGE_DEF] >> qexists_tac `k` >> fs[]) >>
          fs[SUBSET_DEF] \\
          `d.nodemap ' k IN j'.dom.V` by (first_assum irule >> simp[]) >> fs[])
      >- ((* Case: x not in b(Kg.V), inc_R(x) not in D.V - trivial *)
          qpat_x_assum `!v. v IN i'.dom.V /\ _ ==> _` (qspec_then `x` mp_tac) \\
          impl_tac
          >- (rw[] >> spose_not_then strip_assume_tac >> fs[] \\
              first_x_assum (qspec_then `x'` mp_tac) >> simp[])
          >- simp[]))
  >- ((* edgemap domain *)
      simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >>
      Cases_on `?k. k IN Kg.E /\ x = b.edgemap ' k`
      >- (fs[] >> disj1_tac >>
          fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def,
             morphism_dom_ran_def, INJ_DEF])
      >- (disj2_tac >>
          `inc_R.edgemap ' x = x` by
            (first_x_assum (qspec_then `x` mp_tac) >> simp[IN_IMAGE] >> fs[]) >>
          fs[IN_IMAGE]))
  >- ((* edgemap values - batch-safe version *)
      rw[] >> Cases_on `?k. k IN Kg.E /\ x = b.edgemap ' k`
      >- (fs[] >> first_x_assum (qspec_then `k` mp_tac) >> simp[])
      >- ((* Case: x not in b(Kg.E), inc_R(x) in D.E - contradiction *)
          qpat_x_assum `!e. e IN i'.dom.E /\ _ ==> _` (qspec_then `x` mp_tac) \\
          impl_tac
          >- (rw[] >> spose_not_then strip_assume_tac >> fs[] \\
              first_x_assum (qspec_then `x'` mp_tac) >> simp[])
          >- (strip_tac >> fs[] >>
              `x IN j'.dom.E INTER (i'.dom.E DIFF IMAGE ($' b.edgemap) Kg.E)` by
                (simp[IN_INTER, IN_DIFF, IN_IMAGE] >> rw[] >>
                 first_x_assum (qspec_then `x''` mp_tac) >> simp[]) \\
              fs[EXTENSION] \\
              qpat_x_assum `!x'. x' NOTIN j'.dom.E \/ _ \/ _`
                (qspec_then `x` mp_tac) >> simp[] \\
              strip_tac >> first_x_assum (qspec_then `x''` mp_tac) >> simp[]))
      >- ((* Case: x = b(k), inc_R(x) not in D.E - contradiction *)
          fs[] >>
          `inc_R.edgemap ' x = d.edgemap ' k` by simp[] >>
          fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def,
             morphism_dom_ran_def, INJ_DEF] \\
          qpat_x_assum `!x. x IN Kg.E ==> d.edgemap ' x IN j'.dom.E`
            (qspec_then `k` mp_tac) >> simp[])
      >- ((* Case: x not in b(Kg.E), inc_R(x) not in D.E - trivial *)
          qpat_x_assum `!e. e IN i'.dom.E /\ _ ==> _` (qspec_then `x` mp_tac) \\
          impl_tac
          >- (rw[] >> spose_not_then strip_assume_tac >> fs[] \\
              first_x_assum (qspec_then `x'` mp_tac) >> simp[])
          >- simp[]))
QED

(* Helper: composition u o inc_D = j' in gluing pushout

   Key insight: inc_D is identity on D, and u's FUNION picks j' for D elements.

   For v ∈ D.V:
   - inc_D(v) = v (identity)
   - u(v) = (FUNION j'.nodemap ...)'v = j'.nodemap'v (since v ∈ FDOM j'.nodemap)
   Therefore (u o inc_D)(v) = u(inc_D(v)) = u(v) = j'(v)
*)
Theorem gluing_comp_inc_D:
  !Kg R D H P' b d inc_D i' j' u.
    wf_hostgraph Kg /\ wf_hostgraph R /\ wf_hostgraph D /\ wf_hostgraph H /\
    wf_hostgraph P' /\
    is_inj_morphism Kg b R /\ is_inj_morphism Kg d D /\
    is_inj_morphism D inc_D H /\
    is_morphism R i'.map P' /\ is_morphism D j'.map P' /\
    H.V = D.V UNION (R.V DIFF IMAGE ($' b.nodemap) Kg.V) /\
    H.E = D.E UNION (R.E DIFF IMAGE ($' b.edgemap) Kg.E) /\
    (* inc_D is identity on D *)
    (!v. v IN D.V ==> inc_D.nodemap ' v = v) /\
    (!e. e IN D.E ==> inc_D.edgemap ' e = e) /\
    (* u is the mediating morphism *)
    u.nodemap = FUNION j'.map.nodemap
         (DRESTRICT i'.map.nodemap (R.V DIFF IMAGE ($' b.nodemap) Kg.V)) /\
    u.edgemap = FUNION j'.map.edgemap
         (DRESTRICT i'.map.edgemap (R.E DIFF IMAGE ($' b.edgemap) Kg.E)) /\
    is_morphism H u P' /\
    (* Domain conditions *)
    FDOM i'.map.nodemap = R.V /\ FDOM i'.map.edgemap = R.E /\
    FDOM j'.map.nodemap = D.V /\ FDOM j'.map.edgemap = D.E /\
    FDOM inc_D.nodemap = D.V /\ FDOM inc_D.edgemap = D.E /\
    (* j' is a proper category morphism *)
    j'.dom = D /\ j'.cod = P'
    ==>
    mk_graph_mor H u P' o mk_graph_mor D inc_D H -:hostgraph_cat = j'
Proof
  rpt strip_tac >>
  `mk_graph_mor D inc_D H ≈> mk_graph_mor H u P' -:hostgraph_cat` by (
    simp[composable_in_def, hostgraph_cat_def, pre_hostgraph_cat_def,
         mk_graph_mor_def] >> fs[is_inj_morphism_def] >> metis_tac[]) >>
  imp_res_tac compose_in_thm >> fs[] >>
  simp[hostgraph_cat_def] >>
  `mk_graph_mor D inc_D H ≈> mk_graph_mor H u P' -:pre_hostgraph_cat` by (
    simp[composable_in_def, pre_hostgraph_cat_def, mk_graph_mor_def] >>
    fs[is_inj_morphism_def] >> metis_tac[]) >>
  simp[mk_cat_def, compose_def, restrict_def, mk_graph_mor_def] >>
  fs[mk_graph_mor_def] >>
  simp[pre_hostgraph_cat_def, graph_comp_def, compose_morphism_def,
       categoryTheory.morphism_component_equality,
       morphismTheory.morphism_component_equality] >>
  conj_tac >> simp[GSYM fmap_EQ_THM, f_o_f_DEF, FUNION_DEF] >>
  simp[EXTENSION] >> rw[] >> eq_tac >> rw[] >>
  first_x_assum (qspec_then `x` mp_tac) >> fs[]
QED

(* Helper lemmas for composition expansion in hostgraph_cat.
   These extract the nodemap/edgemap of a composition. *)

Theorem hostgraph_comp_nodemap:
  !u inc G H.
    wf_hostgraph G /\ wf_hostgraph H /\
    u IN hostgraph_cat.mor /\ u.dom = H /\
    mk_graph_mor G inc H ≈> u -:hostgraph_cat /\
    is_inj_morphism G inc H ==>
    (u o mk_graph_mor G inc H -:hostgraph_cat).map.nodemap =
    u.map.nodemap f_o_f inc.nodemap
Proof
  rpt strip_tac >>
  imp_res_tac compose_in_thm >> fs[] >>
  simp[compose_def, hostgraph_cat_def, mk_cat_def, restrict_def, composable_in_def,
       pre_hostgraph_cat_def, mk_graph_mor_def, is_inj_morphism_def] >>
  fs[hostgraph_cat_def, mk_cat_mor, pre_hostgraph_cat_mor, is_inj_morphism_def] >>
  fs[mk_graph_mor_def] >> simp[graph_comp_def, compose_morphism_def]
QED

Theorem hostgraph_comp_edgemap:
  !u inc G H.
    wf_hostgraph G /\ wf_hostgraph H /\
    u IN hostgraph_cat.mor /\ u.dom = H /\
    mk_graph_mor G inc H ≈> u -:hostgraph_cat /\
    is_inj_morphism G inc H ==>
    (u o mk_graph_mor G inc H -:hostgraph_cat).map.edgemap =
    u.map.edgemap f_o_f inc.edgemap
Proof
  rpt strip_tac >>
  imp_res_tac compose_in_thm >> fs[] >>
  simp[compose_def, hostgraph_cat_def, mk_cat_def, restrict_def, composable_in_def,
       pre_hostgraph_cat_def, mk_graph_mor_def, is_inj_morphism_def] >>
  fs[hostgraph_cat_def, mk_cat_mor, pre_hostgraph_cat_mor, is_inj_morphism_def] >>
  fs[mk_graph_mor_def] >> simp[graph_comp_def, compose_morphism_def]
QED

(* Helper: derive pointwise equality from f_o_f equality.
   Given f1 f_o_f g1 = f2 f_o_f g2 and appropriate domain/range conditions,
   we can conclude f1 ' (g1 ' x) = f2 ' (g2 ' x) for x in the common domain. *)
Theorem f_o_f_pointwise_eq:
  !f1 g1 f2 g2 S.
    f1 f_o_f g1 = f2 f_o_f g2 /\
    FDOM g1 = S /\ FDOM g2 = S /\
    FRANGE g1 SUBSET FDOM f1 /\
    FRANGE g2 SUBSET FDOM f2 ==>
    !x. x IN S ==> f1 ' (g1 ' x) = f2 ' (g2 ' x)
Proof
  rpt strip_tac >>
  `x IN FDOM (f1 f_o_f g1)` by
    (rw[f_o_f_DEF] >> `g1 ' x IN FRANGE g1` by (simp[FRANGE_DEF] >> metis_tac[]) >>
     metis_tac[SUBSET_DEF]) >>
  `x IN FDOM (f2 f_o_f g2)` by
    (rw[f_o_f_DEF] >> `g2 ' x IN FRANGE g2` by (simp[FRANGE_DEF] >> metis_tac[]) >>
     metis_tac[SUBSET_DEF]) >>
  `(f1 f_o_f g1) ' x = f1 ' (g1 ' x)` by metis_tac[f_o_f_DEF] >>
  `(f2 f_o_f g2) ' x = f2 ' (g2 ' x)` by metis_tac[f_o_f_DEF] >>
  metis_tac[]
QED

(* Helper: uniqueness of mediating morphism via joint surjectivity

   Key insight: inc_R and inc_D jointly cover H:
   - H.V = D.V ∪ (R.V \ b(K.V))
   - inc_D(v) = v for v ∈ D.V
   - inc_R(v) = v for v ∈ R.V \ b(K.V)

   So for any x ∈ H.V, either x ∈ D.V or x ∈ R.V \ b(K.V):
   - If x ∈ D.V: u(x) = u(inc_D(x)) = (u o inc_D)(x) = (u' o inc_D)(x) = u'(x)
   - If x ∈ R.V \ b(K.V): u(x) = u(inc_R(x)) = (u o inc_R)(x) = (u' o inc_R)(x) = u'(x)
*)
Theorem gluing_uniqueness:
  !Kg R D H P' b d inc_R inc_D u u'.
    wf_hostgraph Kg /\ wf_hostgraph R /\ wf_hostgraph D /\ wf_hostgraph H /\
    wf_hostgraph P' /\
    is_inj_morphism Kg b R /\ is_inj_morphism Kg d D /\
    is_inj_morphism R inc_R H /\ is_inj_morphism D inc_D H /\
    H.V = D.V UNION (R.V DIFF IMAGE ($' b.nodemap) Kg.V) /\
    H.E = D.E UNION (R.E DIFF IMAGE ($' b.edgemap) Kg.E) /\
    (* inc_D is identity on D *)
    (!v. v IN D.V ==> inc_D.nodemap ' v = v) /\
    (!e. e IN D.E ==> inc_D.edgemap ' e = e) /\
    (* inc_R is identity on R.V \ b(Kg.V) *)
    (!v. v IN R.V /\ v NOTIN IMAGE ($' b.nodemap) Kg.V ==> inc_R.nodemap ' v = v) /\
    (!e. e IN R.E /\ e NOTIN IMAGE ($' b.edgemap) Kg.E ==> inc_R.edgemap ' e = e) /\
    (* u and u' are morphisms H → P' *)
    u :- H → P' -:hostgraph_cat /\
    u' :- H → P' -:hostgraph_cat /\
    (* They agree on inc_R and inc_D compositions *)
    u o mk_graph_mor R inc_R H -:hostgraph_cat =
      u' o mk_graph_mor R inc_R H -:hostgraph_cat /\
    u o mk_graph_mor D inc_D H -:hostgraph_cat =
      u' o mk_graph_mor D inc_D H -:hostgraph_cat
    ==>
    u = u'
Proof
  rpt strip_tac >>
  rw[categoryTheory.morphism_component_equality] >>
  fs[maps_to_in_def, maps_to_def] >>
  rw[morphismTheory.morphism_component_equality]
  (* Nodemap equality *)
  >- (
    simp[GSYM fmap_EQ_THM] >> conj_tac
    >- (
      `u IN hostgraph_cat.mor /\ u' IN hostgraph_cat.mor` by fs[maps_to_in_def] >>
      fs[hostgraph_cat_def, mk_cat_mor, pre_hostgraph_cat_mor, mk_graph_mor_def] >>
      fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >> gvs[]
    )
    >- (
      rw[] >> Cases_on `x IN D.V`
      >- (
        (* x ∈ D.V: use inc_D composition equality *)
        `inc_D.nodemap ' x = x` by simp[] \\
        `u IN pre_hostgraph_cat.mor` by
          (qpat_x_assum `u IN hostgraph_cat.mor` mp_tac >> simp[hostgraph_cat_def, mk_cat_mor]) \\
        `u' IN pre_hostgraph_cat.mor` by
          (qpat_x_assum `u' IN hostgraph_cat.mor` mp_tac >> simp[hostgraph_cat_def, mk_cat_mor]) \\
        `mk_graph_mor D inc_D u'.dom IN hostgraph_cat.mor` by
          (simp[hostgraph_cat_def, mk_cat_mor, pre_hostgraph_cat_def, mk_graph_mor_def] >>
           fs[is_inj_morphism_def]) \\
        `mk_graph_mor D inc_D u'.dom IN pre_hostgraph_cat.mor` by
          (qpat_x_assum `mk_graph_mor D inc_D u'.dom IN hostgraph_cat.mor` mp_tac >>
           simp[hostgraph_cat_def, mk_cat_mor]) \\
        `mk_graph_mor D inc_D u'.dom ≈> u -:hostgraph_cat` by
          (simp[composable_in_def, hostgraph_cat_def, pre_hostgraph_cat_def,
                composable_def, mk_graph_mor_def] >> fs[is_inj_morphism_def]) \\
        `mk_graph_mor D inc_D u'.dom ≈> u' -:hostgraph_cat` by
          (simp[composable_in_def, hostgraph_cat_def, pre_hostgraph_cat_def,
                composable_def, mk_graph_mor_def] >> fs[is_inj_morphism_def]) \\
        `(u o mk_graph_mor D inc_D u'.dom -:hostgraph_cat).map.nodemap = u.map.nodemap f_o_f inc_D.nodemap` by
          (qspecl_then [`u`, `inc_D`, `D`, `u'.dom`] mp_tac hostgraph_comp_nodemap >>
           impl_tac >- gvs[] >> simp[]) \\
        `(u' o mk_graph_mor D inc_D u'.dom -:hostgraph_cat).map.nodemap = u'.map.nodemap f_o_f inc_D.nodemap` by
          (qspecl_then [`u'`, `inc_D`, `D`, `u'.dom`] mp_tac hostgraph_comp_nodemap >>
           impl_tac >- gvs[] >> simp[]) \\
        `u.map.nodemap f_o_f inc_D.nodemap = u'.map.nodemap f_o_f inc_D.nodemap` by
          (qpat_x_assum `u o mk_graph_mor D inc_D u'.dom -:hostgraph_cat = _`
           (mp_tac o Q.AP_TERM `(\m. m.map.nodemap)`) >> simp[]) \\
        `x IN FDOM (u.map.nodemap f_o_f inc_D.nodemap)` by
          (simp[f_o_f_DEF] >> fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]) \\
        `(u.map.nodemap f_o_f inc_D.nodemap) ' x = u.map.nodemap ' x` by simp[f_o_f_DEF] \\
        `x IN FDOM (u'.map.nodemap f_o_f inc_D.nodemap)` by
          (simp[f_o_f_DEF] >> qpat_x_assum `u' IN pre_hostgraph_cat.mor` mp_tac >>
           simp[pre_hostgraph_cat_def, mk_graph_mor_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
           strip_tac >> fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]) \\
        `(u'.map.nodemap f_o_f inc_D.nodemap) ' x = u'.map.nodemap ' x` by simp[f_o_f_DEF] \\
        metis_tac[]
      )
      >- (
        (* x ∉ D.V: must be in R.V \ b(K.V), use inc_R *)
        `x IN R.V /\ x NOTIN IMAGE ($' b.nodemap) Kg.V` by
          (fs[IN_UNION, IN_DIFF] >> qpat_x_assum `u IN hostgraph_cat.mor` mp_tac >>
           simp[hostgraph_cat_def, mk_cat_mor, pre_hostgraph_cat_def, mk_graph_mor_def,
                is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >> strip_tac >> gvs[]) \\
        `inc_R.nodemap ' x = x` by
          (qpat_x_assum `!v. v IN R.V /\ _ ==> inc_R.nodemap ' v = v` (qspec_then `x` mp_tac) >>
           impl_tac >- (simp[] >> fs[IN_IMAGE] >> metis_tac[]) >> simp[]) \\
        `u IN pre_hostgraph_cat.mor` by
          (qpat_x_assum `u IN hostgraph_cat.mor` mp_tac >> simp[hostgraph_cat_def, mk_cat_mor]) \\
        `u' IN pre_hostgraph_cat.mor` by
          (qpat_x_assum `u' IN hostgraph_cat.mor` mp_tac >> simp[hostgraph_cat_def, mk_cat_mor]) \\
        `mk_graph_mor R inc_R u'.dom IN hostgraph_cat.mor` by
          (simp[hostgraph_cat_def, mk_cat_mor, pre_hostgraph_cat_def, mk_graph_mor_def] >>
           fs[is_inj_morphism_def]) \\
        `mk_graph_mor R inc_R u'.dom IN pre_hostgraph_cat.mor` by
          (qpat_x_assum `mk_graph_mor R inc_R u'.dom IN hostgraph_cat.mor` mp_tac >>
           simp[hostgraph_cat_def, mk_cat_mor]) \\
        `mk_graph_mor R inc_R u'.dom ≈> u -:hostgraph_cat` by
          (simp[composable_in_def, hostgraph_cat_def, pre_hostgraph_cat_def,
                composable_def, mk_graph_mor_def] >> fs[is_inj_morphism_def]) \\
        `mk_graph_mor R inc_R u'.dom ≈> u' -:hostgraph_cat` by
          (simp[composable_in_def, hostgraph_cat_def, pre_hostgraph_cat_def,
                composable_def, mk_graph_mor_def] >> fs[is_inj_morphism_def]) \\
        `(u o mk_graph_mor R inc_R u'.dom -:hostgraph_cat).map.nodemap = u.map.nodemap f_o_f inc_R.nodemap` by
          (qspecl_then [`u`, `inc_R`, `R`, `u'.dom`] mp_tac hostgraph_comp_nodemap >>
           impl_tac >- gvs[] >> simp[]) \\
        `(u' o mk_graph_mor R inc_R u'.dom -:hostgraph_cat).map.nodemap = u'.map.nodemap f_o_f inc_R.nodemap` by
          (qspecl_then [`u'`, `inc_R`, `R`, `u'.dom`] mp_tac hostgraph_comp_nodemap >>
           impl_tac >- gvs[] >> simp[]) \\
        `u.map.nodemap f_o_f inc_R.nodemap = u'.map.nodemap f_o_f inc_R.nodemap` by
          (qpat_x_assum `u o mk_graph_mor R inc_R u'.dom -:hostgraph_cat = _`
           (mp_tac o Q.AP_TERM `(\m. m.map.nodemap)`) >> simp[]) \\
        `x IN FDOM (u.map.nodemap f_o_f inc_R.nodemap)` by
          (simp[f_o_f_DEF] >> fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]) \\
        `(u.map.nodemap f_o_f inc_R.nodemap) ' x = u.map.nodemap ' x` by simp[f_o_f_DEF] \\
        `x IN FDOM (u'.map.nodemap f_o_f inc_R.nodemap)` by
          (simp[f_o_f_DEF] >> qpat_x_assum `u' IN pre_hostgraph_cat.mor` mp_tac >>
           simp[pre_hostgraph_cat_def, mk_graph_mor_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
           strip_tac >> fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]) \\
        `(u'.map.nodemap f_o_f inc_R.nodemap) ' x = u'.map.nodemap ' x` by simp[f_o_f_DEF] \\
        metis_tac[]
      )
    )
  )
  (* Edgemap equality *)
  >- (
    simp[GSYM fmap_EQ_THM] >> conj_tac
    >- (
      `u IN hostgraph_cat.mor /\ u' IN hostgraph_cat.mor` by fs[maps_to_in_def] >>
      fs[hostgraph_cat_def, mk_cat_mor, pre_hostgraph_cat_mor, mk_graph_mor_def] >>
      fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >> gvs[]
    )
    >- (
      rw[] >> Cases_on `x IN D.E`
      >- (
        (* x ∈ D.E: similar to nodemap D case *)
        `inc_D.edgemap ' x = x` by simp[] \\
        `u IN pre_hostgraph_cat.mor` by
          (qpat_x_assum `u IN hostgraph_cat.mor` mp_tac >> simp[hostgraph_cat_def, mk_cat_mor]) \\
        `u' IN pre_hostgraph_cat.mor` by
          (qpat_x_assum `u' IN hostgraph_cat.mor` mp_tac >> simp[hostgraph_cat_def, mk_cat_mor]) \\
        `mk_graph_mor D inc_D u'.dom IN hostgraph_cat.mor` by
          (simp[hostgraph_cat_def, mk_cat_mor, pre_hostgraph_cat_def, mk_graph_mor_def] >>
           fs[is_inj_morphism_def]) \\
        `mk_graph_mor D inc_D u'.dom IN pre_hostgraph_cat.mor` by
          (qpat_x_assum `mk_graph_mor D inc_D u'.dom IN hostgraph_cat.mor` mp_tac >>
           simp[hostgraph_cat_def, mk_cat_mor]) \\
        `mk_graph_mor D inc_D u'.dom ≈> u -:hostgraph_cat` by
          (simp[composable_in_def, hostgraph_cat_def, pre_hostgraph_cat_def,
                composable_def, mk_graph_mor_def] >> fs[is_inj_morphism_def]) \\
        `mk_graph_mor D inc_D u'.dom ≈> u' -:hostgraph_cat` by
          (simp[composable_in_def, hostgraph_cat_def, pre_hostgraph_cat_def,
                composable_def, mk_graph_mor_def] >> fs[is_inj_morphism_def]) \\
        `(u o mk_graph_mor D inc_D u'.dom -:hostgraph_cat).map.edgemap = u.map.edgemap f_o_f inc_D.edgemap` by
          (qspecl_then [`u`, `inc_D`, `D`, `u'.dom`] mp_tac hostgraph_comp_edgemap >>
           impl_tac >- gvs[] >> simp[]) \\
        `(u' o mk_graph_mor D inc_D u'.dom -:hostgraph_cat).map.edgemap = u'.map.edgemap f_o_f inc_D.edgemap` by
          (qspecl_then [`u'`, `inc_D`, `D`, `u'.dom`] mp_tac hostgraph_comp_edgemap >>
           impl_tac >- gvs[] >> simp[]) \\
        `u.map.edgemap f_o_f inc_D.edgemap = u'.map.edgemap f_o_f inc_D.edgemap` by
          (qpat_x_assum `u o mk_graph_mor D inc_D u'.dom -:hostgraph_cat = _`
           (mp_tac o Q.AP_TERM `(\m. m.map.edgemap)`) >> simp[]) \\
        `x IN FDOM (u.map.edgemap f_o_f inc_D.edgemap)` by
          (simp[f_o_f_DEF] >> fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]) \\
        `(u.map.edgemap f_o_f inc_D.edgemap) ' x = u.map.edgemap ' x` by simp[f_o_f_DEF] \\
        `x IN FDOM (u'.map.edgemap f_o_f inc_D.edgemap)` by
          (simp[f_o_f_DEF] >> qpat_x_assum `u' IN pre_hostgraph_cat.mor` mp_tac >>
           simp[pre_hostgraph_cat_def, mk_graph_mor_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
           strip_tac >> fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]) \\
        `(u'.map.edgemap f_o_f inc_D.edgemap) ' x = u'.map.edgemap ' x` by simp[f_o_f_DEF] \\
        metis_tac[]
      )
      >- (
        (* x ∉ D.E: must be in R.E \ IMAGE b.edgemap Kg.E by the H.E hypothesis *)
        `x IN R.E /\ x NOTIN IMAGE ($' b.edgemap) Kg.E` by
          (fs[IN_UNION, IN_DIFF] >> qpat_x_assum `u IN hostgraph_cat.mor` mp_tac >>
           simp[hostgraph_cat_def, mk_cat_mor, pre_hostgraph_cat_def, mk_graph_mor_def,
                is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >> strip_tac >> gvs[]) \\
        (
          (* inc_R.edgemap ' x = x since x ∉ IMAGE b.edgemap Kg.E *)
          `inc_R.edgemap ' x = x` by
            (qpat_x_assum `!e. e IN R.E /\ _ ==> inc_R.edgemap ' e = e` (qspec_then `x` mp_tac) >>
             impl_tac >- (simp[] >> fs[IN_IMAGE] >> metis_tac[]) >> simp[]) \\
          `u IN pre_hostgraph_cat.mor` by
            (qpat_x_assum `u IN hostgraph_cat.mor` mp_tac >> simp[hostgraph_cat_def, mk_cat_mor]) \\
          `u' IN pre_hostgraph_cat.mor` by
            (qpat_x_assum `u' IN hostgraph_cat.mor` mp_tac >> simp[hostgraph_cat_def, mk_cat_mor]) \\
          `mk_graph_mor R inc_R u'.dom IN hostgraph_cat.mor` by
            (simp[hostgraph_cat_def, mk_cat_mor, pre_hostgraph_cat_def, mk_graph_mor_def] >>
             fs[is_inj_morphism_def]) \\
          `mk_graph_mor R inc_R u'.dom IN pre_hostgraph_cat.mor` by
            (qpat_x_assum `mk_graph_mor R inc_R u'.dom IN hostgraph_cat.mor` mp_tac >>
             simp[hostgraph_cat_def, mk_cat_mor]) \\
          `mk_graph_mor R inc_R u'.dom ≈> u -:hostgraph_cat` by
            (simp[composable_in_def, hostgraph_cat_def, pre_hostgraph_cat_def,
                  composable_def, mk_graph_mor_def] >> fs[is_inj_morphism_def]) \\
          `mk_graph_mor R inc_R u'.dom ≈> u' -:hostgraph_cat` by
            (simp[composable_in_def, hostgraph_cat_def, pre_hostgraph_cat_def,
                  composable_def, mk_graph_mor_def] >> fs[is_inj_morphism_def]) \\
          `(u o mk_graph_mor R inc_R u'.dom -:hostgraph_cat).map.edgemap = u.map.edgemap f_o_f inc_R.edgemap` by
            (qspecl_then [`u`, `inc_R`, `R`, `u'.dom`] mp_tac hostgraph_comp_edgemap >>
             impl_tac >- gvs[] >> simp[]) \\
          `(u' o mk_graph_mor R inc_R u'.dom -:hostgraph_cat).map.edgemap = u'.map.edgemap f_o_f inc_R.edgemap` by
            (qspecl_then [`u'`, `inc_R`, `R`, `u'.dom`] mp_tac hostgraph_comp_edgemap >>
             impl_tac >- gvs[] >> simp[]) \\
          `u.map.edgemap f_o_f inc_R.edgemap = u'.map.edgemap f_o_f inc_R.edgemap` by
            (qpat_x_assum `u o mk_graph_mor R inc_R u'.dom -:hostgraph_cat = _`
             (mp_tac o Q.AP_TERM `(\m. m.map.edgemap)`) >> simp[]) \\
          `x IN FDOM (u.map.edgemap f_o_f inc_R.edgemap)` by
            (simp[f_o_f_DEF] >> fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]) \\
          `(u.map.edgemap f_o_f inc_R.edgemap) ' x = u.map.edgemap ' x` by simp[f_o_f_DEF] \\
          `x IN FDOM (u'.map.edgemap f_o_f inc_R.edgemap)` by
            (simp[f_o_f_DEF] >> qpat_x_assum `u' IN pre_hostgraph_cat.mor` mp_tac >>
             simp[pre_hostgraph_cat_def, mk_graph_mor_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
             strip_tac >> fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]) \\
          `(u'.map.edgemap f_o_f inc_R.edgemap) ' x = u'.map.edgemap ' x` by simp[f_o_f_DEF] \\
          metis_tac[]
        )
      )
    )
  )
QED

(* Full pushout theorem with universal property

   Additional hypotheses for the universal property:
   - inc_D acts as identity on D (identity embedding)
   - inc_R maps nodes in b(K) to their d-images, otherwise identity
   - These ensure joint surjectivity onto H
   - DISJOINT conditions for proper gluing
   - Boundary consistency: edges not from interface have endpoints not from interface
   - H structure inheritance: H inherits labels/structure from D and R
*)
Theorem gluing_is_pushout:
  !K R D H b d inc_R inc_D.
    wf_hostgraph K /\ wf_hostgraph R /\ wf_hostgraph D /\ wf_hostgraph H /\
    is_inj_morphism K b R /\
    is_inj_morphism K d D /\
    H.V = D.V UNION (R.V DIFF IMAGE (FAPPLY b.nodemap) K.V) /\
    H.E = D.E UNION (R.E DIFF IMAGE (FAPPLY b.edgemap) K.E) /\
    is_inj_morphism R inc_R H /\
    is_inj_morphism D inc_D H /\
    (* inc_D is identity on D *)
    (!v. v IN D.V ==> inc_D.nodemap ' v = v) /\
    (!e. e IN D.E ==> inc_D.edgemap ' e = e) /\
    (* inc_R is identity on R \ b(K), and maps b(K) to d(K) *)
    (!v. v IN R.V /\ v NOTIN IMAGE (FAPPLY b.nodemap) K.V ==> inc_R.nodemap ' v = v) /\
    (!e. e IN R.E /\ e NOTIN IMAGE (FAPPLY b.edgemap) K.E ==> inc_R.edgemap ' e = e) /\
    (!n. n IN K.V ==> inc_R.nodemap ' (b.nodemap ' n) = d.nodemap ' n) /\
    (!e. e IN K.E ==> inc_R.edgemap ' (b.edgemap ' e) = d.edgemap ' e) /\
    (* DISJOINT conditions for proper gluing *)
    DISJOINT D.V R.V /\
    DISJOINT D.E R.E /\
    (* Boundary consistency: edges not from interface have endpoints not from interface *)
    (!e. e IN R.E /\ e NOTIN IMAGE (FAPPLY b.edgemap) K.E ==>
         R.s ' e NOTIN IMAGE (FAPPLY b.nodemap) K.V) /\
    (!e. e IN R.E /\ e NOTIN IMAGE (FAPPLY b.edgemap) K.E ==>
         R.t ' e NOTIN IMAGE (FAPPLY b.nodemap) K.V) /\
    (* H structure inheritance from D and R *)
    (!e. e IN H.E ==> H.s ' e = if e IN D.E then D.s ' e else R.s ' e) /\
    (!e. e IN H.E ==> H.t ' e = if e IN D.E then D.t ' e else R.t ' e) /\
    (!e. e IN H.E ==> H.m ' e = if e IN D.E then D.m ' e else R.m ' e) /\
    (!v. v IN H.V ==> H.l ' v = if v IN D.V then D.l ' v else R.l ' v) /\
    (!v. v IN H.V ==> (H.p ' v <=> if v IN D.V then D.p ' v else R.p ' v)) /\
    (* Rootedness fully defined (FDOM G.p = G.V, stronger than wf_graph's subset) *)
    FDOM D.p = D.V /\
    FDOM R.p = R.V /\
    FDOM H.p = H.V
    ==>
    is_pushout hostgraph_cat K R D H
      (mk_graph_mor K b R)
      (mk_graph_mor K d D)
      (mk_graph_mor R inc_R H)
      (mk_graph_mor D inc_D H)
Proof
  rw[is_pushout_def] >> rpt conj_tac
  >- (
    (* Pushout square commutativity: inc_R o b = inc_D o d *)
    irule gluing_is_pushout_square >>
    rpt conj_tac >> TRY (simp[] >> NO_TAC) >> TRY (fs[is_inj_morphism_def] >> NO_TAC)
    (* Edge and node commutativity: use INJ from is_inj_morphism *)
    >- (rw[] >> rpt strip_tac >> fs[is_inj_morphism_def, INJ_DEF])
    >- (rw[] >> rpt strip_tac >> fs[is_inj_morphism_def, INJ_DEF]))
  >- (
    (* Universal property: existence and uniqueness *)
    rpt strip_tac >> fs[EXISTS_UNIQUE_THM] >> conj_tac
    >- (
      (* === EXISTENCE === *)
      (* Extract morphism properties from maps_to_in *)
      `i' IN hostgraph_cat.mor` by fs[maps_to_in_def] >>
      `i'.dom = R` by fs[maps_to_in_def, maps_to_def] >>
      `i'.cod = P'` by fs[maps_to_in_def, maps_to_def] >>
      `is_morphism R i'.map P'` by (
        fs[hostgraph_cat_def, mk_cat_def, pre_hostgraph_cat_mor, mk_graph_mor_def] >>
        qpat_x_assum `i'.dom = R` (assume_tac o GSYM) >>
        qpat_x_assum `i'.cod = P'` (assume_tac o GSYM) >>
        qpat_x_assum `i' = _` (fn th => FULL_SIMP_TAC std_ss [th]) >> simp[]) >>
      `j' IN hostgraph_cat.mor` by fs[maps_to_in_def] >>
      `j'.dom = D` by fs[maps_to_in_def, maps_to_def] >>
      `j'.cod = P'` by fs[maps_to_in_def, maps_to_def] >>
      `is_morphism D j'.map P'` by (
        fs[hostgraph_cat_def, mk_cat_def, pre_hostgraph_cat_mor, mk_graph_mor_def] >>
        qpat_x_assum `j'.dom = D` (assume_tac o GSYM) >>
        qpat_x_assum `j'.cod = P'` (assume_tac o GSYM) >>
        qpat_x_assum `j' = _` (fn th => FULL_SIMP_TAC std_ss [th]) >> simp[]) >>
      `wf_hostgraph P'` by (
        qpat_x_assum `i' IN hostgraph_cat.mor` mp_tac >>
        simp[hostgraph_cat_def, mk_cat_def, pre_hostgraph_cat_mor] >>
        strip_tac >> gvs[mk_graph_mor_def]) >>
      `FDOM i'.map.nodemap = R.V` by fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
      `FDOM i'.map.edgemap = R.E` by fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
      `FDOM j'.map.nodemap = D.V` by fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
      `FDOM j'.map.edgemap = D.E` by fs[is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
      (* Cocone commutativity: derive from i' o b = j' o d using hostgraph_comp_edgemap/nodemap *)
      `FDOM b.edgemap = K'.E` by fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
      `FDOM b.nodemap = K'.V` by fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
      `FDOM d.edgemap = K'.E` by fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
      `FDOM d.nodemap = K'.V` by fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
      `FRANGE b.edgemap SUBSET R.E` by fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
      `FRANGE b.nodemap SUBSET R.V` by fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
      `FRANGE d.edgemap SUBSET D.E` by fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
      `FRANGE d.nodemap SUBSET D.V` by fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def] >>
      `mk_graph_mor K' b R ≈> i' -:hostgraph_cat` by
        (simp[composable_in_def, hostgraph_cat_def, mk_cat_def, pre_hostgraph_cat_mor, mk_graph_mor_def] >>
         fs[is_inj_morphism_def]) >>
      `mk_graph_mor K' d D ≈> j' -:hostgraph_cat` by
        (simp[composable_in_def, hostgraph_cat_def, mk_cat_def, pre_hostgraph_cat_mor, mk_graph_mor_def] >>
         fs[is_inj_morphism_def]) >>
      (* Derive edgemap cocone commutativity via f_o_f_pointwise_eq *)
      `(i' o mk_graph_mor K' b R -:hostgraph_cat).map.edgemap = i'.map.edgemap f_o_f b.edgemap` by
        (irule hostgraph_comp_edgemap >> simp[]) >>
      `(j' o mk_graph_mor K' d D -:hostgraph_cat).map.edgemap = j'.map.edgemap f_o_f d.edgemap` by
        (irule hostgraph_comp_edgemap >> simp[]) >>
      `(i' o mk_graph_mor K' b R -:hostgraph_cat).map = (j' o mk_graph_mor K' d D -:hostgraph_cat).map` by fs[] >>
      `i'.map.edgemap f_o_f b.edgemap = j'.map.edgemap f_o_f d.edgemap` by metis_tac[] >>
      `!e. e IN K'.E ==> i'.map.edgemap ' (b.edgemap ' e) = j'.map.edgemap ' (d.edgemap ' e)` by
        metis_tac[f_o_f_pointwise_eq] >>
      (* Derive nodemap cocone commutativity via f_o_f_pointwise_eq *)
      `(i' o mk_graph_mor K' b R -:hostgraph_cat).map.nodemap = i'.map.nodemap f_o_f b.nodemap` by
        (irule hostgraph_comp_nodemap >> simp[]) >>
      `(j' o mk_graph_mor K' d D -:hostgraph_cat).map.nodemap = j'.map.nodemap f_o_f d.nodemap` by
        (irule hostgraph_comp_nodemap >> simp[]) >>
      `i'.map.nodemap f_o_f b.nodemap = j'.map.nodemap f_o_f d.nodemap` by metis_tac[] >>
      `!n. n IN K'.V ==> i'.map.nodemap ' (b.nodemap ' n) = j'.map.nodemap ' (d.nodemap ' n)` by
        metis_tac[f_o_f_pointwise_eq] >>
      (* Construct the mediating morphism *)
      qexists_tac `mk_graph_mor H <| nodemap := j'.map.nodemap ⊌
        DRESTRICT i'.map.nodemap (R.V DIFF IMAGE ($' b.nodemap) K'.V);
        edgemap := j'.map.edgemap ⊌
        DRESTRICT i'.map.edgemap (R.E DIFF IMAGE ($' b.edgemap) K'.E) |> P'` >>
      rpt conj_tac
      >- ((* u :- H -> P' *)
        simp[maps_to_in_def, maps_to_def, hostgraph_cat_def, mk_cat_def,
             pre_hostgraph_cat_mor, mk_graph_mor_def] >>
        irule gluing_mediating_morphism >> simp[] >>
        rpt conj_tac >- fs[] >- fs[] >- (qexists_tac `D` >> simp[]))
      >- ((* u o inc_R = i' *)
        irule gluing_comp_inc_R >> simp[] >>
        rpt conj_tac
        >- fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]
        >- fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]
        >- (qexistsl_tac [`K'`, `b`, `d`, `j'`] >> simp[] >>
            fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def,
               morphism_dom_ran_def, DISJOINT_DEF, EXTENSION] >> metis_tac[])
        >- (irule gluing_mediating_morphism >> simp[] >>
            rpt conj_tac >- fs[] >- fs[] >- (qexists_tac `D` >> simp[])))
      >- ((* u o inc_D = j' *)
        irule gluing_comp_inc_D >> simp[] >>
        rpt conj_tac
        >- fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]
        >- fs[is_inj_morphism_def, is_morphism_def, is_premorphism_def, morphism_dom_ran_def]
        >- (irule gluing_mediating_morphism >> simp[] >>
            rpt conj_tac >- fs[] >- fs[] >- (qexists_tac `D` >> simp[]))
        >- (qexists_tac `K'` >> qexists_tac `R` >> qexists_tac `b` >> qexists_tac `d` >>
            Q.REFINE_EXISTS_TAC `mk_graph_mor A m B` >> simp[mk_graph_mor_def] >>
            metis_tac[])))
    >- (
      (* === UNIQUENESS === *)
      rpt strip_tac >> irule gluing_uniqueness >>
      qexistsl_tac [`D`, `H`, `K'`, `P'`, `R`, `b`, `d`, `inc_D`, `inc_R`] >> simp[] >>
      fs[maps_to_in_def, hostgraph_cat_def, mk_cat_def, pre_hostgraph_cat_mor, mk_graph_mor_def] >>
      qpat_x_assum `u = _` (fn th => FULL_SIMP_TAC std_ss [th]) >>
      `P' = H'³'` by fs[] >> fs[]))
QED

(*
  PROOF SKETCH for the universal property of gluing_is_pushout:

  === EXISTENCE ===
  Given: i' : R → P' and j' : D → P' with i' o b = j' o d

  Construct the mediating morphism u : H → P' as:
    u.nodemap = FUNION j'.map.nodemap
                       (DRESTRICT i'.map.nodemap (R.V DIFF b(K.V)))
    u.edgemap = FUNION j'.map.edgemap i'.map.edgemap

  Need to prove:
  1. is_morphism H u P' - the FUNION of two morphisms with compatible overlap
  2. u o inc_R = i' - follows because:
     - For v ∈ R.V \ b(K.V): inc_R(v) = v, u(v) = i'(v)
     - For v = b(k) ∈ b(K.V): inc_R(b(k)) = d(k), u(d(k)) = j'(d(k)) = i'(b(k))
       (by commutativity i' o b = j' o d)
  3. u o inc_D = j' - follows because inc_D is identity on D

  === UNIQUENESS ===
  Given: u, u' : H → P' with u o inc_R = u' o inc_R and u o inc_D = u' o inc_D

  Since H.V = D.V ∪ (R.V \ b(K.V)) and H.E = D.E ∪ R.E,
  and inc_R, inc_D jointly cover H (joint surjectivity),
  we have u = u' by extensionality.

  For any x ∈ H.V:
  - If x ∈ D.V: u(x) = u(inc_D(x)) = (u o inc_D)(x) = (u' o inc_D)(x) = u'(x)
  - If x ∈ R.V \ b(K.V): u(x) = u(inc_R(x)) = (u o inc_R)(x) = (u' o inc_R)(x) = u'(x)
*)

(* ============================================================
   PART 7: DPO as Double Pushout
   ============================================================ *)

(*
  A DPO rewriting step consists of two pushouts:

       L <---b---- K ----b'---> R
       |           |            |
       m           d            h
       |           |            |
       v           v            v
       G <---c---- D ----c'---> H

  The left square is a pushout-complement (finding D from G, L, K)
  The right square is a pushout (constructing H from D, R, K)
*)

Definition is_dpo_diagram_def:
  is_dpo_diagram c L K R G D H b b' m d c_mor c'_mor h <=>
    (* Left square: pushout complement *)
    is_pushout c K L D G b m d c_mor /\
    (* Right square: pushout *)
    is_pushout c K R D H b' d h c'_mor
End

(* DPO rewriting preserves well-formedness *)
Theorem dpo_preserves_wf:
  !L K R G D H b b' m d c_mor c'_mor h.
    is_dpo_diagram hostgraph_cat L K R G D H b b' m d c_mor c'_mor h /\
    wf_hostgraph G
    ==>
    wf_hostgraph H
Proof
  rw[is_dpo_diagram_def, hostgraph_cat_def] >>
  fs[is_pushout_def] >>
  fs[pushout_square_def] >>
  fs[maps_to_in_def, maps_to_def] >>
  fs[pre_hostgraph_cat_mor] >>
  fs[mk_graph_mor_def] >>
  `H = H'⁶'` by (qpat_x_assum `h = _` (fn th => FULL_SIMP_TAC std_ss [th]) >> fs[]) >>
  simp[]
QED

val () = export_theory();
