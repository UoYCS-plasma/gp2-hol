open HolKernel Parse bossLib boolLib string_numTheory arithmeticTheory intLib pred_setTheory
open graphTheory

val () = new_theory "tagging";

Definition tag_nodeid_left_def:
  tag_nodeid_left (n:nodeid) = nodeid $ n2s $ 2 * (s2n $ dest_nodeid n)
End

Definition tag_nodeid_right_def:
  tag_nodeid_right (n:nodeid) = nodeid $ n2s $ 2 * (s2n $ dest_nodeid n) +1
End

Definition untag_nodeid_def:
  untag_nodeid (n:nodeid) = nodeid $ n2s $ (s2n $ dest_nodeid n) DIV 2
End

Theorem tag_untag_nodeid_inv[simp]:
  (!n. untag_nodeid (tag_nodeid_left n) = n) /\
  (!n. untag_nodeid (tag_nodeid_right n) = n)
Proof
  rw[tag_nodeid_left_def, tag_nodeid_right_def, untag_nodeid_def]
  \\ Cases_on `n`
  \\ rw[dest_nodeid_def ]
QED


Definition is_left_tagged_nodeid_def:
  is_left_tagged_nodeid (n:nodeid) = EVEN (s2n (dest_nodeid n))
End

Definition is_right_tagged_nodeid_def:
  is_right_tagged_nodeid (n:nodeid) = ODD (s2n (dest_nodeid n))
End


Definition tag_edgeid_left_def:
  tag_edgeid_left (e: edgeid) = edgeid $ n2s $ 2 * (s2n $ dest_edgeid e)
End

Definition tag_edgeid_right_def:
  tag_edgeid_right (e: edgeid) = edgeid $ n2s $ 2 * (s2n $ dest_edgeid e) +1
End

Definition untag_edgeid_def:
  untag_edgeid (n:edgeid) = edgeid $ n2s $ (s2n $ dest_edgeid n) DIV 2
End

Theorem tag_untag_edgeid_inv[simp]:
  (!n. untag_edgeid (tag_edgeid_left n) = n) /\
  (!n. untag_edgeid (tag_edgeid_right n) = n)
Proof
  rw[tag_edgeid_left_def, tag_edgeid_right_def, untag_edgeid_def]
  \\ Cases_on `n`
  \\ rw[dest_edgeid_def ]
QED


Definition is_left_tagged_edgeid_def:
  is_left_tagged_edgeid (n:edgeid) = EVEN (s2n (dest_edgeid n))
End

Definition is_right_tagged_edgeid_def:
  is_right_tagged_edgeid (n:edgeid) = ODD (s2n (dest_edgeid n))
End

Theorem correct_tagging:
  (!nid. is_right_tagged_nodeid (tag_nodeid_right nid)) /\
  (!nid. is_left_tagged_nodeid (tag_nodeid_left nid)) /\
  (!eid. is_right_tagged_edgeid (tag_edgeid_right eid)) /\
  (!eid. is_left_tagged_edgeid (tag_edgeid_left eid))
Proof
  rw[tag_nodeid_left_def, tag_nodeid_right_def, tag_edgeid_left_def, tag_edgeid_right_def,
     is_left_tagged_nodeid_def, is_right_tagged_nodeid_def,
     is_left_tagged_edgeid_def, is_right_tagged_edgeid_def
    ]
  \\ rw[nodeid_absrep, edgeid_absrep]
  \\ metis_tac [ODD_DOUBLE, EVEN_DOUBLE, ADD1]
QED


val tagging_tac = rw[] >> rw[correct_tagging]
Theorem is_tagged_iff_exists:
  (!e. is_left_tagged_edgeid (e: edgeid) <=> ?e'. tag_edgeid_left e' = e) /\
  (!e. is_right_tagged_edgeid (e: edgeid) <=> ?e'. tag_edgeid_right e' = e) /\
  (!n. is_left_tagged_nodeid (n: nodeid) <=> ?n'. tag_nodeid_left n' = n) /\
  (!n. is_right_tagged_nodeid (n: nodeid) <=> ?n'. tag_nodeid_right n' = n)
Proof
rpt strip_tac
\\ EQ_TAC
\\ DISCH_TAC
>- (
     qexists `untag_edgeid e`
  \\ gvs[tag_edgeid_left_def, untag_edgeid_def, is_left_tagged_edgeid_def]
  \\ Cases_on `e`
  \\ fs[edgeid_absrep]
  \\ `!n. EVEN n ==> 2 * (n DIV 2) = n` by ARITH_TAC
  \\ RES_TAC
  \\ fs[]
  )
>- tagging_tac
>- (
     qexists `untag_edgeid e`
  \\ gvs[tag_edgeid_right_def, untag_edgeid_def, is_right_tagged_edgeid_def]
  \\ Cases_on `e`
  \\ fs[edgeid_absrep]
  \\ `!n. ODD n ==> 2 * (n DIV 2) + 1 = n` by ARITH_TAC
  \\ RES_TAC
  \\ fs[]
  )
>- tagging_tac
(* nodeids *)
>- (
     qexists `untag_nodeid n`
  \\ gvs[tag_nodeid_left_def, untag_nodeid_def, is_left_tagged_nodeid_def]
  \\ Cases_on `n`
  \\ fs[nodeid_absrep]
  \\ `!n. EVEN n ==> 2 * (n DIV 2) = n` by ARITH_TAC
  \\ RES_TAC
  \\ fs[]
  )
>- tagging_tac
>- (
     qexists `untag_nodeid n`
  \\ gvs[tag_nodeid_right_def, untag_nodeid_def, is_right_tagged_nodeid_def]
  \\ Cases_on `n`
  \\ fs[nodeid_absrep]
  \\ `!n. ODD n ==> 2 * (n DIV 2) + 1 = n` by ARITH_TAC
  \\ RES_TAC
  \\ fs[]
  )
>- tagging_tac
QED


Theorem INJ_tag_nodeid:
  INJ tag_nodeid_left UNIV UNIV /\ INJ tag_nodeid_right UNIV UNIV
Proof
  rw[INJ_DEF]
  \\ Cases_on `x`
  \\ Cases_on `y`
  \\ fs[dest_nodeid_def, tag_nodeid_left_def, tag_nodeid_right_def]
QED

Theorem INJ_tag_edgeid:
  INJ tag_edgeid_left UNIV UNIV /\ INJ tag_edgeid_right UNIV UNIV
Proof
  rw[INJ_DEF]
  \\ Cases_on `x`
  \\ Cases_on `y`
  \\ fs[dest_edgeid_def, tag_edgeid_left_def, tag_edgeid_right_def]
QED

Theorem tag_disjoint:
  (!x x'. tag_nodeid_left x <> tag_nodeid_right x') /\
  (!x x'. tag_edgeid_left x <> tag_edgeid_right x')
Proof
  rw[tag_nodeid_left_def, tag_nodeid_right_def, tag_edgeid_left_def, tag_edgeid_right_def]
  \\ intLib.COOPER_TAC
QED


val () = export_theory ();
