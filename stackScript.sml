
open HolKernel Parse boolLib bossLib listTheory

val () = new_theory "stack"

Type stack = ``:'a list``

Definition empty_stack_def:
  empty_stack <=> []
End

Definition push_stack_def:
  push_stack (e: 'a) (s:'a stack) <=> (e :: s)
End

Definition pop_stack_def:
  pop_stack (s: 'a stack) <=>
    case s of
      [] => NONE |
      h::hs => SOME (h, hs)
End

Definition pop2_stack_def:
  pop2_stack (s: 'a stack) <=>
    case s of
      [] => NONE |
      [h1] => NONE |
      h1::h2::hs => SOME ([h2], h1::hs)
End

Definition top_stack_def:
  top_stack (s: 'a stack) <=>
    case s of
      [] => NONE |
      h::hs => SOME h
End

Definition is_singleton_stack_def:
  is_singleton_stack (s: 'a stack) <=> LENGTH s = 1
End

Theorem pop_stack_suffix:
  !prefix rest h snd.
    LENGTH prefix >= 1 /\
    pop_stack (prefix ++ rest) = SOME (h, snd) ==>
    ?prefix'. snd = prefix' ++ rest /\ LENGTH prefix' = LENGTH prefix - 1
Proof
  Cases_on `prefix` >> simp[pop_stack_def] >> rpt strip_tac >>
  qexists_tac `t` >> simp[]
QED

Theorem pop2_stack_suffix:
  !prefix rest fst snd.
    LENGTH prefix >= 2 /\
    pop2_stack (prefix ++ rest) = SOME (fst, snd) ==>
    ?prefix'. snd = prefix' ++ rest /\ LENGTH prefix' = LENGTH prefix - 1
Proof
  Cases_on `prefix` >> simp[pop2_stack_def] >>
  Cases_on `t` >> simp[pop2_stack_def] >> rpt strip_tac >>
  qexists_tac `h::t'` >> simp[]
QED

Theorem pop_stack_append:
  !s rest h snd.
    LENGTH s >= 1 /\
    pop_stack (s ++ rest) = SOME (h, snd) ==>
    ?snd'. pop_stack s = SOME (h, snd') /\ snd = snd' ++ rest
Proof
  Cases_on `s` >> simp[pop_stack_def] >> rpt strip_tac >>
  qexists_tac `t` >> simp[]
QED

Theorem pop2_stack_append:
  !s rest fst snd.
    LENGTH s >= 2 /\
    pop2_stack (s ++ rest) = SOME (fst, snd) ==>
    ?snd'. pop2_stack s = SOME (fst, snd') /\ snd = snd' ++ rest
Proof
  Cases_on `s` >> simp[pop2_stack_def] >>
  Cases_on `t` >> simp[pop2_stack_def] >> rpt strip_tac >>
  qexists_tac `h::t'` >> simp[]
QED

Theorem pop2_stack_length:
  !s fst snd.
    pop2_stack s = SOME (fst, snd) ==>
    LENGTH snd = LENGTH s - 1 /\ LENGTH s >= 2
Proof
  Cases_on `s` >> simp[pop2_stack_def] >>
  Cases_on `t` >> simp[pop2_stack_def]
QED

Theorem pop_stack_length:
  !s h snd.
    pop_stack s = SOME (h, snd) ==>
    LENGTH snd = LENGTH s - 1 /\ LENGTH s >= 1
Proof
  Cases_on `s` >> simp[pop_stack_def]
QED

val () = export_theory ()
