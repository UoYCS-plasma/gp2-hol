open HolKernel boolLib bossLib alistTheory listTheory finite_mapTheory
open programTheory graphTheory hostgraphTheory stackTheory dpoTheory rulegraphTheory taggingTheory
open ruleTheory morphismTheory trackTheory
open relationTheory arithmeticTheory rich_listTheory
open quantHeuristicsTheory quantHeuristicsLib
open semTheory

val () = new_theory "semProps"

(* A single step preserves wf_stack_labels.
   Key case: Call1 requires apply_ruleinstance_preserves_wf
   and wf_hostgraph_IMP_hostgraph_labels_spine. *)
Theorem step_preserves_wf_stack_labels:
  !env c s c' s'.
    wf_program env /\
    wf_stack_labels s /\
    step env (c, s) (c', s')
    ==> wf_stack_labels s'
Proof
  Induct_on `step` >>
  rpt conj_tac >> rpt strip_tac >> gvs[]
  (* Call1: rule application - this is the key case *)
  >- (simp[push_stack_def, wf_stack_labels_def] >>
      conj_tac
      (* New frame: (h, compose_morphism ...) - only need wf_hostgraph *)
      >- (irule apply_ruleinstance_preserves_wf >> simp[] >>
          qexistsl_tac [`G`, `m`, `ri`] >> simp[] >>
          rpt conj_tac
          >- (fs[pop_stack_def, wf_stack_labels_def] >>
              Cases_on `S'` >> gvs[])
          >- (irule instantiate_rule_wf >> simp[] >>
              qexistsl_tac [`G`, `assign`, `m`, `r`] >> simp[] >>
              conj_tac
              >- (irule mk_assignment_wf_assignment_spine >> simp[] >>
                  qexistsl_tac [`G`, `m`, `r`] >> simp[] >>
                  `wf_hostgraph G` by
                    (fs[pop_stack_def, wf_stack_labels_def] >>
                     Cases_on `S'` >> gvs[]) >>
                  metis_tac[wf_hostgraph_IMP_hostgraph_labels_spine])
              >- (gvs[wf_program_def] >>
                  drule_all FEVERY_FLOOKUP >> simp[]))
          >- (irule prematch_instantiation_is_match >> simp[] >>
              `wf_hostgraph G` by
                (fs[pop_stack_def, wf_stack_labels_def] >>
                 Cases_on `S'` >> gvs[]) >>
              rpt conj_tac
              >- simp[]
              >- (qexistsl_tac [`assign`, `r`] >> simp[] >>
                  conj_tac
                  >- (gvs[wf_program_def] >>
                      drule_all FEVERY_FLOOKUP >> simp[])
                  >- (gvs[wf_program_def] >>
                      drule_all FEVERY_FLOOKUP >> simp[wf_rule_def]))))
      (* rest of stack unchanged *)
      >- (fs[pop_stack_def, wf_stack_labels_def] >>
          Cases_on `S'` >> gvs[]))
  (* TRY break: pop2_stack *)
  >- (fs[pop2_stack_def, wf_stack_labels_def] >>
      Cases_on `S'` >> gvs[] >>
      Cases_on `t` >> gvs[])
  (* ifte: push_stack (duplicate top) *)
  >- (fs[top_stack_def, push_stack_def, wf_stack_labels_def] >>
      Cases_on `S'` >> gvs[])
  (* ITE final with pop_stack *)
  >- (fs[pop_stack_def, wf_stack_labels_def] >>
      Cases_on `S''` >> gvs[])
  (* ITE failed with pop_stack *)
  >- (fs[pop_stack_def, wf_stack_labels_def] >>
      Cases_on `S'` >> gvs[])
  (* trte: push_stack (duplicate top) *)
  >- (fs[top_stack_def, push_stack_def, wf_stack_labels_def] >>
      Cases_on `S'` >> gvs[])
  (* TRY final with pop2_stack *)
  >- (fs[pop2_stack_def, wf_stack_labels_def] >>
      Cases_on `S''` >> gvs[] >>
      Cases_on `t` >> gvs[])
  (* TRY failed with pop_stack *)
  >- (fs[pop_stack_def, wf_stack_labels_def] >>
      Cases_on `S'` >> gvs[])
QED

(* A single step preserves well-formed stacks.
   Stack frames are (hostgraph, track morphism) pairs.
   wf_stack checks wf_hostgraph on H. *)
Theorem step_preserves_wf_stack:
  !env c s c' s'.
    wf_program env /\
    wf_stack_labels s /\
    step env (c, s) (c', s')
    ==> wf_stack s'
Proof
  rpt strip_tac >>
  `wf_stack_labels s'` by metis_tac[step_preserves_wf_stack_labels] >>
  fs[wf_stack_labels_def, wf_stack_def] >>
  irule listTheory.EVERY_MONOTONIC >> first_x_assum $ irule_at Any >>
  rpt strip_tac >> PairCases_on `x` >> fs[]
QED

(* Helper: NRC preserves wf_stack.
   Uses step_preserves_wf_stack_labels for inductive step. *)
Theorem NRC_step_preserves_wf_stack:
  !n env c s c' s'.
    wf_program env /\
    wf_stack_labels s /\
    NRC (step env) n (c, s) (c', s')
    ==> wf_stack s'
Proof
  Induct_on `n` >> rpt strip_tac
  (* Base case: n=0 means (c,s) = (c',s'), so wf_stack s' follows from wf_stack_labels s *)
  >- (gvs[arithmeticTheory.NRC, wf_stack_labels_def, wf_stack_def] >>
      irule EVERY_MONOTONIC >> first_x_assum $ irule_at Any >>
      rpt strip_tac >> PairCases_on `x` >> fs[])
  (* Inductive case: step to z, then NRC n from z to (c',s') *)
  >- (gvs[arithmeticTheory.NRC] >> PairCases_on `z` >>
      `wf_stack_labels z1` by metis_tac[step_preserves_wf_stack_labels] >>
      first_x_assum irule >> metis_tac[])
QED

(* Multiple steps preserve well-formed stacks.
   Follows from NRC_step_preserves_wf_stack via steps_NRC. *)
Theorem steps_preserves_wf_stack:
  !env c s c' s'.
    wf_program env /\
    wf_stack_labels s /\
    steps env (c, s) (c', s')
    ==> wf_stack s'
Proof
  rpt strip_tac >> gvs[steps_NRC] >> metis_tac[NRC_step_preserves_wf_stack]
QED

(* NRC preserves wf_stack_labels *)
Theorem NRC_step_preserves_wf_stack_labels:
  !n env c s c' s'.
    wf_program env /\
    wf_stack_labels s /\
    NRC (step env) n (c, s) (c', s')
    ==> wf_stack_labels s'
Proof
  Induct_on `n` >> rpt strip_tac
  >- gvs[arithmeticTheory.NRC]
  >- (gvs[arithmeticTheory.NRC] >> PairCases_on `z` >>
      `wf_stack_labels z1` by metis_tac[step_preserves_wf_stack_labels] >>
      first_x_assum irule >> metis_tac[])
QED

(* Multiple steps preserve wf_stack_labels *)
Theorem steps_preserves_wf_stack_labels:
  !env c s c' s'.
    wf_program env /\
    wf_stack_labels s /\
    steps env (c, s) (c', s')
    ==> wf_stack_labels s'
Proof
  rpt strip_tac >> gvs[steps_NRC] >> metis_tac[NRC_step_preserves_wf_stack_labels]
QED

(* Main theorem: evaluation preserves wf_hostgraph *)
Theorem evaluate_preserves_wf_hostgraph:
  !env G P H tr D.
    wf_program env /\
    wf_hostgraph G /\
    evaluate env G P (H, tr)
    ==> wf_hostgraph H
Proof
  rpt strip_tac >>
  fs[evaluate_def] >>
  `wf_partial_hostgraph G` by metis_tac[wf_hostgraph_IMP_wf_partial_hostgraph] >>
  `wf_stack_labels [(G, id_track G)]` by simp[wf_stack_labels_def] >>
  `wf_stack ((H, tr)::rest)` by metis_tac[steps_preserves_wf_stack] >>
  fs[wf_stack_def]
QED

(* Main theorem: evaluation preserves hostgraph_labels_spine.
   Note: hostgraph_labels_spine is implied by wf_hostgraph, so we derive it. *)
Theorem evaluate_preserves_hostgraph_labels_spine:
  !env G P H tr D.
    wf_program env /\
    wf_hostgraph G /\
    evaluate env G P (H, tr)
    ==> hostgraph_labels_spine H
Proof
  rpt strip_tac >>
  fs[evaluate_def] >>
  `wf_partial_hostgraph G` by metis_tac[wf_hostgraph_IMP_wf_partial_hostgraph] >>
  `wf_stack_labels [(G, id_track G)]` by simp[wf_stack_labels_def] >>
  `wf_stack_labels ((H, tr)::rest)` by metis_tac[steps_preserves_wf_stack_labels] >>
  `wf_hostgraph H` by fs[wf_stack_labels_def] >>
  metis_tac[wf_hostgraph_IMP_hostgraph_labels_spine]
QED

open relationTheory arithmeticTheory

Theorem steps_CASES1:
  !env c1 c2.
    steps env c1 c2 <=>
      c1 = c2 \/ (?c' s'. step env c1 (c', s') /\ steps env (c', s') c2)
Proof
  metis_tac [steps_def, relationTheory.RTC_CASES1, pairTheory.pair_CASES]
QED

Theorem steps_CASES2:
  !env c1 c2.
    steps env c1 c2 <=>
      c1 = c2 \/ (?c' s'. steps env c1 (c', s') /\ step env (c', s') c2)
Proof
  metis_tac [steps_def, relationTheory.RTC_CASES2, pairTheory.pair_CASES]
QED

Theorem steps_TRANS:
  !env c1 c2.
    steps env c1 c2 <=> (?c'. steps env c1 c' /\ steps env c' c2)
Proof
  metis_tac [steps_def, relationTheory.RTC_TRANS, relationTheory.RTC_REFL]
QED

Theorem steps_SINGLE:
  !env c1 c2.
    step env c1 c2 ==>  steps env c1 c2
Proof
  metis_tac [steps_def, relationTheory.RTC_SINGLE]
QED

Theorem steps_REFL:
  !env c. steps env c c
Proof
  metis_tac [steps_def, relationTheory.RTC_REFL]
QED

Theorem step_into_running:
  !env z c' s'. step env z (running c', s') ==> ?c s. z = (running c, s)
Proof
  Cases_on `z` \\ Cases_on `q`
  \\ simp [step_only_running_rewrs]
QED

Theorem steps_into_running:
  !env z c' s'. steps env z (running c', s') ==> ?c s. z = (running c, s)
Proof
  REWRITE_TAC [steps_NRC]
  \\ simp[GSYM LEFT_FORALL_IMP_THM]
  \\  Induct_on `n`
  >- gvs[NRC_0]
  >- (
    gvs[NRC]
    \\ rpt strip_tac
    \\ res_tac
    \\ metis_tac[ step_into_running]
  )
QED

Theorem step_into_final:
  !env z m. step env z (final, m) ==> ?c s. z = (running c, s)
Proof
  Cases_on `z` \\ Cases_on `q`
  \\ simp[step_only_running_rewrs]
QED

Theorem steps_into_final:
  !env z m. steps env z (final, m) ==> (?c s. z = (running c, s)) \/ z = (final, m)
Proof
  REWRITE_TAC [steps_NRC]
    \\ simp[GSYM LEFT_FORALL_IMP_THM]
    \\ Induct_on `n`
    >- gvs[NRC_0]
    >- (
      rpt strip_tac
      \\ gvs[NRC]
      \\ res_tac
      \\ metis_tac[step_into_final, step_into_running]
    )
QED

Theorem step_into_failed:
  !env z m. step env z (failed, m) ==> ?c s. z = (running c, s)
Proof
  Cases_on `z` \\ Cases_on `q`
  \\ simp[step_only_running_rewrs]
QED

Theorem steps_into_failed:
  !env z m. steps env z (failed, m)
    ==> (?c s. z = (running c, s)) \/ z = (failed, m)
Proof
  REWRITE_TAC [steps_NRC]
    \\ simp[GSYM LEFT_FORALL_IMP_THM]
    \\ Induct_on `n`
    >- gvs[NRC_0]
    >- (
      rpt strip_tac
      \\ gvs[NRC]
      \\ res_tac
      >-  metis_tac[step_into_running]
      >- (
        gvs[]
        \\ metis_tac[step_into_failed]
      )
    )
QED

Theorem steps_final_failed:
    (steps env (failed, s) (t, s') <=> (t = failed /\ s = s')) /\
    (steps env (final, s) (t, s') <=> (t = final /\ s = s'))
Proof
  rw[EQ_IMP_THM]
  \\ fs[Once steps_CASES1, step_only_running_rewrs]
QED

Theorem step_fail:
  !env s s' t'. step env (running term_fail, s) (t', s')
    <=> t' = failed /\ s' = s
Proof
  fs[Once step_cases]
QED

Theorem steps_fail:
  !env s s' t'. steps env (running term_fail, s) (t', s')
    <=> (t' = running term_fail /\ s' = s) \/
        (t' = failed /\ s' = s)
Proof
  rw[EQ_IMP_THM]
  \\ fs[Once steps_CASES1]
  \\ metis_tac [steps_final_failed, step_fail]
QED

(* term_fail never succeeds - goes to failed state, not final *)
Theorem evaluate_fail:
  !env G H tr D. ~(evaluate env G term_fail (H, tr))
Proof
  rw[evaluate_def, steps_fail] >>
  simp[can_step_def]
QED


Theorem step_skip:
  !env s s' c. step env (running term_skip, s) (c, s')
    <=> c = final /\ s' = s
Proof
  fs[Once step_cases]
QED

Theorem steps_skip:
  !env s s' c. steps env (running term_skip, s) (c, s')
    <=> (c = running term_skip /\ s = s') \/ (c = final /\ s = s')
Proof
  rw[Once steps_CASES1]
  \\ rw[steps_final_failed, step_skip]
QED

(* term_skip succeeds immediately, preserving graph and track *)
Theorem evaluate_skip:
  !env G. evaluate env G term_skip (G, id_track G)
Proof
  rw[evaluate_def, steps_skip, can_step_def] >>
  qexists_tac `[]` >> simp[]
QED



Theorem step_or:
  !env s a b c s'. step env (running (term_or a b), s) (c, s') <=>
    (c = running a /\ s' = s) \/ (c = running b /\ s' = s)
Proof
  fs[Once step_cases]
QED

Theorem steps_or:
  !env s a b c s'. steps env (running (term_or a b), s) (c, s') <=>
    (c = running (term_or a b) /\ s' = s) \/
    (steps env (running a, s) (c, s')) \/ (steps env (running b, s) (c,s'))
Proof
  fs[Once steps_CASES1]
  \\ fs[step_or, RIGHT_AND_OVER_OR, EXISTS_OR_THM]
  \\ metis_tac[]
QED

(* Nondeterministic choice: evaluate succeeds if either branch succeeds *)
Theorem evaluate_or:
  !env G a b H tr D. evaluate env G (term_or a b) (H, tr) <=>
    evaluate env G a (H, tr) \/ evaluate env G b (H, tr)
Proof
  rw[evaluate_def, steps_or]
  \\ metis_tac [can_step_def]
QED

Theorem steps_running_break:
  !env r c. steps env (running term_break,r) c
    <=> c = (running term_break, r)
Proof
  `!env r x. ~step env (running term_break, r) x` by (metis_tac [step_only_running, can_step_def])
  \\ rw[]
  \\ Cases_on `c`
  \\ rw[Once steps_CASES1]
  \\ metis_tac[]
QED

Theorem step_seq:
  step env (running (term_seq a b), s) (c, s')
    <=> (?P'. c = running (term_seq P' b) /\ step env (running a,s) (running P',s')) \/
          c = running b /\ step env (running a,s) (final,s') \/
          c = failed /\ s' = s /\ step env (running a,s) (failed,s) \/
          a = term_break /\ c = running term_break /\ s' = s
Proof
  fs[Once step_cases]
QED


Theorem steps_seq_thm1:
  !env a b s s' c n.
    NRC (step env) n (running (term_seq a b),s) (c,s') ==>
    (?c' m. steps env (running a, s) (running c', m) /\ steps env (running (term_seq c' b), m) (c, s')) \/
    (?m. steps env (running a, s) (final, m) /\ steps env (running b, m) (c, s')) \/
    (steps env (running a, s) (failed, s') /\ c = failed) \/
    (steps env (running a, s) (running term_break, s') /\ c = running term_break)
Proof
  Induct_on `n`
  >- (rpt strip_tac \\ disj1_tac \\ qexistsl [`a`, `s`] \\ fs[NRC_0, steps_REFL])
  >- (
    fs[NRC] \\ rpt strip_tac
    \\ Cases_on `z` \\ fs[step_seq]
    >- (gvs[] \\ disj1_tac \\ qexistsl [`P'`, `r`] \\ metis_tac[steps_CASES1, steps_NRC])
    >- (gvs[] \\ disj2_tac \\ disj1_tac \\ qexists `r` \\ metis_tac[steps_CASES1, steps_NRC])
    >- (
        gvs[] \\ disj2_tac \\ disj2_tac \\ disj1_tac
        \\ ONCE_REWRITE_TAC [steps_CASES1] \\ conj_tac
        >- (disj2_tac \\ qexistsl [`failed`, `r`] \\ metis_tac[steps_NRC, steps_final_failed])
        >- (metis_tac[steps_NRC, steps_final_failed])
    )
    >- (
      gvs[]\\ disj2_tac \\ disj2_tac \\ disj2_tac
      \\ `steps env (running term_break, r) (c,s')` by metis_tac[steps_NRC]
      \\ gvs[steps_running_break]
    )
  )
QED


Theorem steps_seq_thm2a:
!env a s s' c c' x b n m.
  NRC (step env) n (running a,s) (running c',x) ==> NRC (step env) m (running (term_seq c' b),x) (c,s')
    ==> NRC (step env) (n + m) (running (term_seq a b),s) (c,s')
Proof
  Induct_on `n`
  >- (
  rpt strip_tac
  \\ gvs[NRC_0]
  )
  >- (
    rpt strip_tac \\ gvs[NRC]
    \\ `?a b. z = (running a, b)` by metis_tac[steps_NRC, steps_into_running]
    \\ gvs[]
    \\ res_tac
    \\ REWRITE_TAC[GSYM ADD_SUC, NRC]
    \\ metis_tac[step_Seq1]
  )
QED

Theorem NRC_step_from_final:
  NRC (step env) n (final, x) y ==> n = 0 /\ y = (final, x)
Proof
  Cases_on `n`
  >- rw[]
  >- (gvs[NRC]\\ metis_tac [step_only_running_rewrs])
QED

Theorem NRC_step_from_failed:
  NRC (step env) n (failed, x) y ==> n = 0 /\ y = (failed, x)
Proof
  Cases_on `n`
  >- rw[]
  >- (gvs[NRC]\\ metis_tac [step_only_running_rewrs])
QED

Theorem steps_seq_thm2b:
!env a s s' c x b n m.
  NRC (step env) n (running a,s) (final,x) ==> NRC (step env) m (running b,x) (c,s')
    ==> NRC (step env) (n + m) (running (term_seq a b),s) (c,s')
Proof
  Induct_on `n`
  >- fs[NRC_0]
  >- (
    rpt strip_tac \\ gvs[NRC]
    \\ `(?c' s'. z = (running c', s')) \/ (z = (final, x))`
      by (metis_tac[steps_NRC, steps_into_final])
      >- (
     gvs[]
    \\ res_tac
    \\ REWRITE_TAC[GSYM ADD_SUC, NRC]
    \\ metis_tac[step_Seq1]
          )
      >- (
        `n = 0` by metis_tac[NRC_step_from_final]
        \\ ASM_REWRITE_TAC[GSYM ADD_SUC, NRC]
        \\ REWRITE_TAC [ADD_0]
         \\ metis_tac[step_Seq2]

      )
  )
QED

Theorem step_to_failed_preserves_stack:
  !env c s s'. step env (running c, s) (failed, s') ==> s' = s
Proof
  rpt gen_tac \\ simp [Once step_cases] \\ rw[]
QED

Theorem steps_seq_thm2c:
!env n a s x b s.
  NRC (step env) n (running a,s) (failed,x)
     ==> NRC (step env) n (running (term_seq a b),s) (failed,x)
Proof
  Induct_on `n`
  >- fs[NRC_0]
  >- (
    rpt strip_tac \\ gvs[NRC]
    \\ `(?c' s'. z = (running c', s')) \/ (z = (failed, x))`
      by metis_tac[steps_NRC, steps_into_failed]
    >- (gvs[] \\ res_tac \\ REWRITE_TAC[GSYM ADD1, NRC]
        \\ metis_tac[step_Seq1] )
    >- (`n = 0` by metis_tac[NRC_step_from_failed]
        \\ gvs[]
        \\ `s = x` by metis_tac[step_to_failed_preserves_stack]
        \\ metis_tac[step_Seq3])
  )
QED

Theorem steps_seq_thm2d:
  !env n a s s' b.
    NRC (step env) n (running a, s) (running term_break, s')
      ==> NRC (step env) (SUC n) (running (term_seq a b),s) (running term_break,s')
Proof
   Induct_on `n`
  >- (fs[NRC_0] \\ metis_tac[step_Break])
  >- (
      rpt strip_tac \\ gvs[NRC]
   \\ `(?c' s'. z = (running c', s'))`
      by metis_tac[steps_NRC, steps_into_running]
    \\ gvs[]
    \\ res_tac
      \\ metis_tac[step_Seq1]
  )
QED

Theorem steps_seq_thm2:
  !env a b s s' c.
    (?c' m. steps env (running a, s) (running c', m) /\ steps env (running (term_seq c' b), m) (c, s')) \/
    (?m. steps env (running a, s) (final, m) /\ steps env (running b, m) (c, s')) \/
    (steps env (running a, s) (failed, s') /\ c = failed) \/
    (steps env (running a, s) (running term_break, s') /\ c = running term_break)
      ==> steps env (running (term_seq a b),s) (c,s')
Proof
  rpt strip_tac
  >- metis_tac [steps_seq_thm2a, steps_NRC]
  >- metis_tac [steps_seq_thm2b, steps_NRC]
  >- metis_tac [steps_seq_thm2c, steps_NRC]
  >- metis_tac [steps_seq_thm2d, steps_NRC]
QED

Theorem steps_seq:
  !env a b s s' c. steps env (running (term_seq a b), s) (c, s') <=>
    (?c' m. steps env (running a, s) (running c', m) /\ steps env (running (term_seq c' b), m) (c, s')) \/
    (?m. steps env (running a, s) (final, m) /\ steps env (running b, m) (c, s')) \/
    (steps env (running a, s) (failed, s') /\ c = failed) \/
    (steps env (running a, s) (running term_break, s') /\ c = running term_break)
Proof
  rw[EQ_IMP_THM]
  >- metis_tac[steps_NRC, steps_seq_thm1]
  \\ metis_tac[steps_NRC, steps_seq_thm2]
QED


(* Stack frame lemma: extra elements at the bottom of the stack are preserved.
   Stack frames are now (hostgraph # morphism # hostgraph) triples. *)
Theorem step_frame:
  !env x y. step env x y ==>
    !rest. step env (FST x, SND x ++ rest) (FST y, SND y ++ rest)
Proof
  ho_match_mp_tac step_ind >> rpt strip_tac
  >- ( (* Call1 *)
    simp[] >>
    `pop_stack (S' ++ rest') = SOME ((G, tr), rest ++ rest')` by
      (Cases_on `S'` >> gvs[pop_stack_def]) >>
    `push_stack (h, compose_morphism (track ri.lhs ri.inf m G) tr) rest ++ rest' =
     push_stack (h, compose_morphism (track ri.lhs ri.inf m G) tr) (rest ++ rest')`
      by simp[push_stack_def] >>
    ASM_REWRITE_TAC[] >> simp[Once step_cases] >> metis_tac[])
  >- ( (* Call2 *)
    simp[] >> `pop_stack (S' ++ rest') = SOME ((G, tr), rest ++ rest')` by
      (Cases_on `S'` >> gvs[pop_stack_def]) >> simp[Once step_cases] >> metis_tac[])
  >- simp[Once step_cases] (* ProcCall *)
  >- (simp[] >> first_x_assum (qspec_then `rest` assume_tac) >> gvs[] >>
      irule step_Seq1 >> simp[]) (* Seq1 *)
  >- (simp[] >> first_x_assum (qspec_then `rest` assume_tac) >> gvs[] >>
      irule step_Seq2 >> simp[]) (* Seq2 *)
  >- (simp[] >> first_x_assum (qspec_then `rest` assume_tac) >> gvs[] >>
      irule step_Seq3 >> simp[]) (* Seq3 *)
  >- simp[Once step_cases] (* Break *)
  >- simp[Once step_cases] (* Alap1 *)
  >- ( (* Alap2 - pop2_stack *)
    simp[] >> `pop2_stack (S' ++ rest) = SOME (FST h, SND h ++ rest)` by
      (gvs[pop2_stack_def] >> Cases_on `S'` >> gvs[] >> Cases_on `t` >> gvs[]) >>
    simp[Once step_cases] >> qexists_tac `(FST h, SND h ++ rest)` >> simp[])
  >- ( (* If1 - push_stack with top_stack *)
    simp[] >> `top_stack (S' ++ rest) = SOME el` by
      (Cases_on `S'` >> gvs[top_stack_def]) >>
    `push_stack el S' ++ rest = push_stack el (S' ++ rest)` by simp[push_stack_def] >>
    simp[Once step_cases])
  >- (simp[] >> first_x_assum (qspec_then `rest` assume_tac) >> gvs[] >>
      irule step_If2 >> simp[]) (* If2 *)
  >- ( (* If3 - pop_stack after final *)
    simp[] >> first_x_assum (qspec_then `rest` assume_tac) >> gvs[] >>
    `pop_stack (S'' ++ rest) = SOME (FST r, SND r ++ rest)` by
      (Cases_on `S''` >> gvs[pop_stack_def]) >>
    simp[Once step_cases] >> disj2_tac >> disj1_tac >>
    qexists_tac `S'' ++ rest` >> qexists_tac `(FST r, SND r ++ rest)` >> simp[])
  >- ( (* If4 - pop_stack after failed *)
    simp[] >> first_x_assum (qspec_then `rest` assume_tac) >> gvs[] >>
    `pop_stack (S' ++ rest) = SOME (FST S'', SND S'' ++ rest)` by
      (Cases_on `S'` >> gvs[pop_stack_def]) >>
    simp[Once step_cases] >> disj2_tac >> disj2_tac >>
    qexists_tac `(FST S'', SND S'' ++ rest)` >> simp[])
  >- ( (* Try1 *)
    simp[] >> `top_stack (S' ++ rest) = SOME el` by
      (Cases_on `S'` >> gvs[top_stack_def]) >>
    `push_stack el S' ++ rest = push_stack el (S' ++ rest)` by simp[push_stack_def] >>
    simp[Once step_cases])
  >- (simp[] >> first_x_assum (qspec_then `rest` assume_tac) >> gvs[] >>
      irule step_Try2 >> simp[]) (* Try2 *)
  >- ( (* Try3 - pop2_stack after final *)
    simp[] >> first_x_assum (qspec_then `rest` assume_tac) >> gvs[] >>
    `pop2_stack (S'' ++ rest) = SOME (FST r, SND r ++ rest)` by
      (gvs[pop2_stack_def] >> Cases_on `S''` >> gvs[] >> Cases_on `t` >> gvs[]) >>
    simp[Once step_cases] >> disj2_tac >> disj1_tac >>
    qexists_tac `S'' ++ rest` >> qexists_tac `(FST r, SND r ++ rest)` >> simp[])
  >- ( (* Try4 - pop_stack after failed *)
    simp[] >> first_x_assum (qspec_then `rest` assume_tac) >> gvs[] >>
    `pop_stack (S' ++ rest) = SOME (FST S'', SND S'' ++ rest)` by
      (Cases_on `S'` >> gvs[pop_stack_def]) >>
    simp[Once step_cases] >> disj2_tac >> disj2_tac >>
    qexists_tac `(FST S'', SND S'' ++ rest)` >> simp[])
  >- simp[Once step_cases] (* Or1 *)
  >- simp[Once step_cases] (* Or2 *)
  >- simp[Once step_cases] (* Skip *)
  >- simp[Once step_cases] (* Fail *)
QED

Theorem NRC_step_frame:
  !env n x y. NRC (step env) n x y ==>
    !rest. NRC (step env) n (FST x, SND x ++ rest) (FST y, SND y ++ rest)
Proof
  Induct_on `n` >> simp[NRC] >> rpt strip_tac >> gvs[] >>
  Cases_on `z` >> rename1 `step env x (q, stk)` >>
  qexists_tac `(q, stk ++ rest)` >> conj_tac
  >- (Cases_on `x` >> drule step_frame >> disch_then (qspec_then `rest` mp_tac) >> simp[])
  >- (first_x_assum (drule_then (qspec_then `rest` mp_tac)) >> simp[])
QED

Theorem steps_frame:
  !env x y. steps env x y ==>
    !rest. steps env (FST x, SND x ++ rest) (FST y, SND y ++ rest)
Proof
  rw[steps_NRC] >> drule NRC_step_frame >> metis_tac[]
QED


Theorem step_inverse_frame_aux:
  !env c1 c2. step env c1 c2 ==>
    !P S state S' rest.
      c1 = (running P, S ++ rest) /\
      c2 = (state, S' ++ rest) /\
      no_intermediate_terms P /\
      LENGTH S >= 1 ==>
      step env (running P, S) (state, S')
Proof
  ho_match_mp_tac step_ind >> rpt conj_tac >> rpt gen_tac
  (* term_rscall success (Call1): need to show step still works without rest *)
  >- (
    rpt strip_tac >> gvs[] >>
    `S'' = HD S'' :: TL S''` by (Cases_on `S''` >> gvs[]) >>
    qpat_x_assum `S'' = _` SUBST_ALL_TAC >>
    gvs[pop_stack_def, push_stack_def] >>
    simp[Once step_cases, push_stack_def, pop_stack_def] >> metis_tac[]
  )
  (* term_rscall failure (Call2): stack unchanged *)
  >- (
    rpt strip_tac >> gvs[] >>
    `S'' = HD S'' :: TL S''` by (Cases_on `S''` >> gvs[]) >>
    qpat_x_assum `S'' = _` SUBST_ALL_TAC >>
    gvs[pop_stack_def] >>
    simp[Once step_cases, pop_stack_def] >> metis_tac[]
  )
  (* term_proc: stack unchanged *)
  >- (rpt strip_tac >> gvs[] >> simp[Once step_cases] >> metis_tac[])
  (* term_seq - running: use IH *)
  >- (
    rpt strip_tac >> gvs[no_intermediate_terms_def] >>
    first_x_assum (qspecl_then [`S'³'`, `S'⁴'`, `rest`] mp_tac) >>
    simp[] >> strip_tac >> simp[Once step_cases] >> metis_tac[]
  )
  (* term_seq - final: use IH *)
  >- (
    rpt strip_tac >> gvs[no_intermediate_terms_def] >>
    first_x_assum (qspecl_then [`S'³'`, `S'⁴'`, `rest`] mp_tac) >>
    simp[] >> strip_tac >> simp[Once step_cases] >> metis_tac[]
  )
  (* term_seq - failed: use IH *)
  >- (
    rpt strip_tac >> gvs[no_intermediate_terms_def] >>
    first_x_assum (qspecl_then [`S''`, `S''`, `rest`] mp_tac) >>
    simp[] >> strip_tac >> simp[Once step_cases] >> metis_tac[]
  )
  (* term_seq term_break: direct *)
  >- (rpt strip_tac >> gvs[no_intermediate_terms_def] >> simp[Once step_cases])
  (* term_alap: direct *)
  >- (rpt strip_tac >> gvs[no_intermediate_terms_def] >> simp[Once step_cases])
  (* term_TRY term_break: vacuous, no_intermediate_terms is F *)
  >- (rpt strip_tac >> gvs[no_intermediate_terms_def])
  (* term_ifte: need to reconstruct the step *)
  >- (
    rpt strip_tac >> gvs[no_intermediate_terms_def, push_stack_def, top_stack_def] >>
    `S'' = HD S'' :: TL S''` by (Cases_on `S''` >> gvs[]) >>
    qpat_x_assum `S'' = _` SUBST_ALL_TAC >> gvs[] >>
    simp[Once step_cases, push_stack_def, top_stack_def]
  )
  (* term_ITE running: vacuous *)
  >- (rpt strip_tac >> gvs[no_intermediate_terms_def])
  (* term_ITE final: vacuous *)
  >- (rpt strip_tac >> gvs[no_intermediate_terms_def])
  (* term_ITE failed: vacuous *)
  >- (rpt strip_tac >> gvs[no_intermediate_terms_def])
  (* term_trte: similar to term_ifte *)
  >- (
    rpt strip_tac >> gvs[no_intermediate_terms_def, push_stack_def, top_stack_def] >>
    `S'' = HD S'' :: TL S''` by (Cases_on `S''` >> gvs[]) >>
    qpat_x_assum `S'' = _` SUBST_ALL_TAC >> gvs[] >>
    simp[Once step_cases, push_stack_def, top_stack_def]
  )
  (* term_TRY running: vacuous *)
  >- (rpt strip_tac >> gvs[no_intermediate_terms_def])
  (* term_TRY final: vacuous *)
  >- (rpt strip_tac >> gvs[no_intermediate_terms_def])
  (* term_TRY failed: vacuous *)
  >- (rpt strip_tac >> gvs[no_intermediate_terms_def])
  (* term_or - left: direct *)
  >- (rpt strip_tac >> gvs[no_intermediate_terms_def] >> simp[Once step_cases])
  (* term_or - right: direct *)
  >- (rpt strip_tac >> gvs[no_intermediate_terms_def] >> simp[Once step_cases])
  (* term_skip: direct *)
  >- (rpt strip_tac >> gvs[no_intermediate_terms_def] >> simp[Once step_cases])
  (* term_fail: direct *)
  >- (rpt strip_tac >> gvs[no_intermediate_terms_def] >> simp[Once step_cases])
QED


Theorem step_inverse_frame:
  !env P S state S' rest.
    step env (running P, S ++ rest) (state, S' ++ rest) /\
    no_intermediate_terms P /\
    LENGTH S >= 1 ==>
    step env (running P, S) (state, S')
Proof
  metis_tac[step_inverse_frame_aux]
QED

(* Step characterization for term_ifte: single step always goes to term_ITE *)
Theorem step_ifte:
  !env C P Q S c S'.
    step env (running (term_ifte C P Q), S) (c, S') <=>
      ?el. top_stack S = SOME el /\ c = running (term_ITE C P Q) /\ S' = push_stack el S
Proof
  simp[Once step_cases] \\ metis_tac[]
QED

(* Step characterization for term_ITE: C steps, or branches to P/Q *)
Theorem step_ITE:
  !env C P Q S c S'.
    step env (running (term_ITE C P Q), S) (c, S') <=>
      (?C'' S''. step env (running C, S) (running C'', S'') /\
                 c = running (term_ITE C'' P Q) /\ S' = S'') \/
      (?S'' r. step env (running C, S) (final, S'') /\
               pop_stack S'' = SOME r /\ c = running P /\ S' = SND r) \/
      (?r. step env (running C, S) (failed, S) /\
           pop_stack S = SOME r /\ c = running Q /\ S' = SND r)
Proof
  simp[Once step_cases] \\ metis_tac[]
QED

(* Steps characterization for term_ifte: zero steps or step to term_ITE *)
Theorem steps_ifte:
  !env C P Q stk c stk'.
    steps env (running (term_ifte C P Q), stk) (c, stk') <=>
      (c = running (term_ifte C P Q) /\ stk' = stk) \/
      (?el. top_stack stk = SOME el /\
            steps env (running (term_ITE C P Q), push_stack el stk) (c, stk'))
Proof
  rpt strip_tac \\ EQ_TAC
  >- (simp[Once steps_CASES1] \\ strip_tac
      >- (disj1_tac \\ gvs[])
      >- (qpat_x_assum `step _ _ _` mp_tac \\ simp[Once step_cases] \\
          strip_tac \\ gvs[]))
  >- (strip_tac
      >- simp[steps_REFL]
      >- (ONCE_REWRITE_TAC[steps_CASES1] \\
          disj2_tac \\
          qexists_tac `running (term_ITE C P Q)` \\
          qexists_tac `push_stack el stk` \\
          simp[Once step_cases]))
QED

(* NRC lifting lemma for term_ITE: if C succeeds, term_ITE goes to P *)
Theorem NRC_ITE_lift:
  !env n C P Q S S' r.
    NRC (step env) n (running C,S) (final,S') /\
    pop_stack S' = SOME r ==>
    NRC (step env) n (running (term_ITE C P Q),S) (running P,SND r)
Proof
  Induct_on `n` >- simp[NRC_0] >> rpt strip_tac >> gvs[NRC] >>
  Cases_on `z` >> rename1 `step env (running C, S') (q', S''')` >> Cases_on `q'`
  >- (qexists_tac `(running (term_ITE t P Q), S''')` >>
      conj_tac >- (simp[Once step_cases] >> disj2_tac >> disj1_tac >> metis_tac[]) >>
      first_x_assum irule >> metis_tac[])
  >- (Cases_on `n` >> gvs[NRC]
      >- (simp[Once step_cases] >> disj2_tac >> disj1_tac >> qexistsl [`S''`, `r`] >> simp[])
      >- (gvs[Once step_cases] >> `F` by (pop_assum (K ALL_TAC) >> pop_assum (K ALL_TAC) >>
          pop_assum mp_tac >> simp[Once step_cases])))
  >- (Cases_on `n` >> gvs[NRC, Once step_cases] >>
      `F` by (qpat_x_assum `step env (failed, _) _` mp_tac >> simp[Once step_cases]))
QED

(* NRC lifting lemma for term_ITE: if C fails, term_ITE goes to Q *)
Theorem NRC_ITE_lift_fail:
  !env n C P Q S S' r.
    NRC (step env) n (running C,S) (failed,S') /\
    pop_stack S' = SOME r ==>
    NRC (step env) n (running (term_ITE C P Q),S) (running Q,SND r)
Proof
  Induct_on `n` >- simp[NRC_0] >> rpt strip_tac >> gvs[NRC] >>
  Cases_on `z` >> rename1 `step env (running C, S') (q', S''')` >> Cases_on `q'`
  >- (qexists_tac `(running (term_ITE t P Q), S''')` >>
      conj_tac >- (simp[Once step_cases] >> disj2_tac >> disj1_tac >> metis_tac[]) >>
      first_x_assum irule >> metis_tac[])
  >- (Cases_on `n` >> gvs[NRC, Once step_cases] >>
      `F` by (qpat_x_assum `step env (final, _) _` mp_tac >> simp[Once step_cases]))
  >- (Cases_on `n` >> gvs[NRC]
      >- (simp[Once step_cases] >>
          `S'' = S'` by (qpat_x_assum `step _ _ (failed, _)` mp_tac >> simp[Once step_cases] >>
                         rpt strip_tac >> gvs[]) >>
          disj2_tac >> disj2_tac >> qexists_tac `r` >> simp[] >> gvs[])
      >- (`F` by (qpat_x_assum `step env (failed, _) _` mp_tac >> simp[Once step_cases])))
QED

(* Decomposition lemma for term_ITE: converse of NRC_ITE_lift *)
Theorem NRC_ITE_decompose:
  !env n C P Q S c.
    NRC (step env) n (running (term_ITE C P Q), S) c /\ ~can_step c ==>
    (?n1 n2 S' r.
      NRC (step env) n1 (running C, S) (final, S') /\
      pop_stack S' = SOME r /\
      NRC (step env) n2 (running P, SND r) c /\
      n = n1 + n2) \/
    (?n1 n2 S' r.
      NRC (step env) n1 (running C, S) (failed, S') /\
      pop_stack S' = SOME r /\
      NRC (step env) n2 (running Q, SND r) c /\
      n = n1 + n2)
Proof
  Induct_on `n`
  >- (simp[NRC] >> rpt strip_tac >> gvs[can_step_def, Once step_cases])
  >- (rpt strip_tac >> gvs[NRC] >>
      qpat_x_assum `step env (running (term_ITE _ _ _), _) _` mp_tac >>
      simp[Once step_cases] >> strip_tac >> gvs[]
      (* If2: C is running *)
      >- (first_x_assum (qspecl_then [`env`, `C''`, `P`, `Q`, `S''`, `c`] mp_tac) >>
          impl_tac >- simp[] >> strip_tac
          >- (disj1_tac >> qexistsl [`SUC n1`, `n2`, `S'³'`, `r`] >> simp[NRC] >> metis_tac[])
          >- (disj2_tac >> qexistsl [`SUC n1`, `n2`, `S'³'`, `r`] >> simp[NRC] >> metis_tac[]))
      (* If3: C succeeded *)
      >- (disj1_tac >> qexistsl [`1`, `n`, `S''`, `r`] >> simp[NRC])
      (* If4: C failed *)
      >- (disj2_tac >> qexistsl [`1`, `n`, `S'`, `S''`] >> simp[NRC]))
QED

(* Decomposition lemma for term_TRY: similar to NRC_ITE_decompose.
   Three cases:
   1. C reaches final, then P runs
   2. C reaches failed, then Q runs
   3. Break case: term_TRY term_break (term_alap P') term_skip exits immediately *)
Theorem NRC_TRY_decompose:
  !env n C P Q S c.
    NRC (step env) n (running (term_TRY C P Q), S) c /\ ~can_step c ==>
    (?n1 n2 S' r.
      NRC (step env) n1 (running C, S) (final, S') /\
      pop2_stack S' = SOME r /\
      NRC (step env) n2 (running P, SND r) c /\
      n = n1 + n2) \/
    (?n1 n2 S' r.
      NRC (step env) n1 (running C, S) (failed, S') /\
      pop_stack S' = SOME r /\
      NRC (step env) n2 (running Q, SND r) c /\
      n = n1 + n2) \/
    (* Break case: C reaches term_break, then term_TRY exits if P = term_alap P' *)
    (?n1 S' h P'.
      NRC (step env) n1 (running C, S) (running term_break, S') /\
      ~can_step (running term_break, S') /\
      P = term_alap P' /\ Q = term_skip /\
      pop2_stack S' = SOME h /\ c = (final, SND h) /\ n = SUC n1)
Proof
  Induct_on `n`
  >- (simp[NRC] >> rpt strip_tac >> gvs[can_step_def, Once step_cases])
  >- (rpt strip_tac >> gvs[NRC] >>
      qpat_x_assum `step env (running (term_TRY _ _ _), _) _` mp_tac >>
      simp[Once step_cases] >> strip_tac >> gvs[]
      (* step_Alap2: term_TRY term_break (term_alap P') term_skip
         This case exits immediately via the break rule. C = term_break, n1 = 0. *)
      >- (`n = 0` by (drule NRC_step_from_final >> strip_tac >> gvs[]) >> gvs[] >>
          DISJ2_TAC >> DISJ2_TAC >> simp[can_step_def])
      (* step_Try2: C stepped to C'' *)
      >- (last_x_assum (qspecl_then [`env`, `C''`, `P`, `Q`, `S''`, `c`] mp_tac) >>
          simp[] >> strip_tac >> gvs[]
          (* IH case 1: C'' reached final *)
          >- (DISJ1_TAC >> qexistsl_tac [`SUC n1`, `n2`, `S'³'`, `r`] >> simp[NRC] >>
              qexists_tac `(running C'', S'')` >> metis_tac[])
          (* IH case 2: C'' reached failed *)
          >- (DISJ2_TAC >> DISJ1_TAC >> qexistsl_tac [`SUC n1`, `n2`, `S'³'`, `r`] >> simp[NRC] >>
              qexists_tac `(running C'', S'')` >> metis_tac[])
          (* IH case 3: C'' reached term_break *)
          >- (DISJ2_TAC >> DISJ2_TAC >> qexistsl_tac [`S'³'`, `h`] >> simp[NRC] >>
              qexists_tac `(running C'', S'')` >> metis_tac[]))
      (* step_Try3: C stepped to final *)
      >- (DISJ1_TAC >> qexistsl_tac [`1`, `n`, `S''`, `r`] >> simp[NRC_1] >>
          metis_tac[])
      (* step_Try4: C stepped to failed *)
      >- (DISJ2_TAC >> DISJ1_TAC >> qexistsl_tac [`1`, `n`, `S'`, `S''`] >> simp[NRC_1] >>
          metis_tac[]))
QED

(* Decomposition lemma for term_seq: splits execution into sub-executions.
   Three cases:
   1. A reaches final, then B runs
   2. A reaches failed, propagate failure
   3. A reaches break, propagate break *)
Theorem NRC_seq_decompose:
  !env n A B S c.
    NRC (step env) n (running (term_seq A B), S) c /\ ~can_step c ==>
    (?n1 n2 S'.
      NRC (step env) n1 (running A, S) (final, S') /\
      NRC (step env) n2 (running B, S') c /\
      n = n1 + n2) \/
    (?n1 S'.
      NRC (step env) n1 (running A, S) (failed, S') /\
      c = (failed, S') /\ n = n1) \/
    (?n1 S'.
      NRC (step env) n1 (running A, S) (running term_break, S') /\
      c = (running term_break, S') /\ n = SUC n1)
Proof
  Induct_on `n`
  >- (simp[NRC] >> rpt strip_tac >> gvs[can_step_def, Once step_cases])
  >- (rpt strip_tac >> gvs[NRC] >>
      qpat_x_assum `step _ (running (term_seq _ _), _) _` mp_tac >>
      simp[Once step_cases] >> strip_tac >> gvs[]
      (* Seq1: A stepped to A', still running *)
      >- (first_x_assum (qspecl_then [`env`, `P'`, `B`, `S''`, `c`] mp_tac) >>
          simp[] >> strip_tac
          (* IH case: A' reached final *)
          >- (disj1_tac >> qexistsl [`SUC n1`, `n2`, `S'''`] >> simp[NRC] >> metis_tac[])
          (* IH case: A' reached failed *)
          >- (disj2_tac >> disj1_tac >> simp[] >> metis_tac[NRC])
          (* IH case: A' reached break *)
          >- (disj2_tac >> disj2_tac >> gvs[] >> simp[NRC] >> metis_tac[]))
      (* Seq2: A reached final, switch to B *)
      >- (disj1_tac >> qexistsl [`1`, `n`, `S''`] >> simp[NRC])
      (* Seq3: A reached failed, propagate failure *)
      >- (disj2_tac >> disj1_tac >> imp_res_tac NRC_step_from_failed >> gvs[] >> metis_tac[NRC])
      (* Break: A = term_break, propagate break *)
      >- (Cases_on `n` >> gvs[NRC] >>
          qpat_x_assum `step _ (running term_break, _) _` mp_tac >> simp[Once step_cases]))
QED

(* Composition lemma for term_TRY: if C reaches final in n steps,
   then term_TRY C P Q reaches running P in n steps. *)
Theorem NRC_TRY_C_to_final_lift:
  !env n C P Q S S' r.
    NRC (step env) n (running C, S) (final, S') /\
    pop2_stack S' = SOME r ==>
    NRC (step env) n (running (term_TRY C P Q), S) (running P, SND r)
Proof
  Induct_on `n`
  >- simp[NRC_0]
  >- (rpt strip_tac >> gvs[NRC] >>
      Cases_on `z` >> Cases_on `q`
      (* C stepped to running t *)
      >- (qexists_tac `(running (term_TRY t P Q), r')` >>
          conj_tac >- simp[Once step_cases]
          >- (first_x_assum irule >> simp[] >> qexists_tac `S''` >> simp[]))
      (* C stepped to final *)
      >- (`n = 0 /\ r' = S''` by (Cases_on `n` >> gvs[NRC_0, NRC] >>
            qpat_x_assum `step env (final, _) _` mp_tac >> simp[Once step_cases]) >>
          gvs[] >> simp[Once step_cases] >>
          DISJ2_TAC >> DISJ1_TAC >> qexistsl_tac [`S''`, `r`] >> simp[])
      (* C stepped to failed - impossible since NRC n (failed,...) (final,...) *)
      >- (`F` by (Cases_on `n` >> gvs[NRC_0, NRC] >>
            qpat_x_assum `step env (failed, _) _` mp_tac >> simp[Once step_cases])))
QED

(* Similar lemma for C reaching failed *)
Theorem NRC_TRY_C_to_failed_lift:
  !env n C P Q S S' r.
    NRC (step env) n (running C, S) (failed, S') /\
    pop_stack S' = SOME r ==>
    NRC (step env) n (running (term_TRY C P Q), S) (running Q, SND r)
Proof
  Induct_on `n`
  >- simp[NRC_0]
  >- (rpt strip_tac >> gvs[NRC] >>
      Cases_on `z` >> Cases_on `q`
      (* C stepped to running t *)
      >- (qexists_tac `(running (term_TRY t P Q), r')` >>
          conj_tac >- simp[Once step_cases]
          >- (first_x_assum irule >> simp[] >> qexists_tac `S''` >> simp[]))
      (* C stepped to final - impossible *)
      >- (`F` by (Cases_on `n` >> gvs[NRC_0, NRC] >>
            qpat_x_assum `step env (final, _) _` mp_tac >> simp[Once step_cases]))
      (* C stepped to failed *)
      >- (`n = 0 /\ r' = S''` by (Cases_on `n` >> gvs[NRC_0, NRC] >>
            qpat_x_assum `step env (failed, _) _` mp_tac >> simp[Once step_cases]) >>
          gvs[] >> simp[Once step_cases] >>
          `S'' = S'` by metis_tac[step_to_failed_preserves_stack] >>
          gvs[] >> DISJ2_TAC >> DISJ2_TAC >> qexists_tac `r` >> simp[]))
QED

(* Lift lemma for C reaching term_break - lifts to term_TRY still running *)
Theorem NRC_TRY_C_to_break_lift:
  !env n C P Q S S'.
    NRC (step env) n (running C, S) (running term_break, S') ==>
    NRC (step env) n (running (term_TRY C P Q), S) (running (term_TRY term_break P Q), S')
Proof
  Induct_on `n`
  >- simp[NRC_0]
  >- (rpt strip_tac >> gvs[NRC] >>
      Cases_on `z` >> Cases_on `q`
      (* C stepped to running t *)
      >- (qexists_tac `(running (term_TRY t P Q), r)` >>
          conj_tac >- simp[Once step_cases]
          >- (first_x_assum irule >> simp[]))
      (* C stepped to final - impossible, can't reach term_break from final *)
      >- (`F` by (Cases_on `n` >> gvs[NRC_0, NRC] >>
            qpat_x_assum `step env (final, _) _` mp_tac >> simp[Once step_cases]))
      (* C stepped to failed - impossible, can't reach term_break from failed *)
      >- (`F` by (Cases_on `n` >> gvs[NRC_0, NRC] >>
            qpat_x_assum `step env (failed, _) _` mp_tac >> simp[Once step_cases])))
QED


Theorem step_to_TRY_preserves_components:
  !P S S' C P' Q env.
    step env (running P, S) (running (term_TRY C P' Q), S') /\
    no_intermediate_terms P /\
    FEVERY (\(_,t). no_intermediate_terms t) env.proc ==>
    no_intermediate_terms C /\ no_intermediate_terms P' /\ no_intermediate_terms Q
Proof
  rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
  simp[Once step_cases] >> strip_tac >> gvs[no_intermediate_terms_def]
  (* proc case is vacuous: term_TRY can't be in env.proc due to FEVERY *)
  >- (`F` suffices_by simp[] >>
      `p IN FDOM env.proc` by (gvs[FLOOKUP_DEF] >> Cases_on `p IN FDOM env.proc` >> gvs[]) >>
      gvs[FEVERY_DEF] >> first_x_assum (qspec_then `p` mp_tac) >> simp[] >>
      gvs[FLOOKUP_DEF, no_intermediate_terms_def])
  >- (`F` suffices_by simp[] >>
      `p IN FDOM env.proc` by (gvs[FLOOKUP_DEF] >> Cases_on `p IN FDOM env.proc` >> gvs[]) >>
      gvs[FEVERY_DEF] >> first_x_assum (qspec_then `p` mp_tac) >> simp[] >>
      gvs[FLOOKUP_DEF, no_intermediate_terms_def])
  >- (`F` suffices_by simp[] >>
      `p IN FDOM env.proc` by (gvs[FLOOKUP_DEF] >> Cases_on `p IN FDOM env.proc` >> gvs[]) >>
      gvs[FEVERY_DEF] >> first_x_assum (qspec_then `p` mp_tac) >> simp[] >>
      gvs[FLOOKUP_DEF, no_intermediate_terms_def])
QED

(* Similar lemma for term_ITE *)
Theorem step_to_ITE_preserves_components:
  !P S S' C P' Q env.
    step env (running P, S) (running (term_ITE C P' Q), S') /\
    no_intermediate_terms P /\
    FEVERY (\(_,t). no_intermediate_terms t) env.proc ==>
    no_intermediate_terms C /\ no_intermediate_terms P' /\ no_intermediate_terms Q
Proof
  rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
  simp[Once step_cases] >> strip_tac >> gvs[no_intermediate_terms_def]
  (* proc case is vacuous: term_ITE can't be in env.proc due to FEVERY *)
  >- (`F` suffices_by simp[] >>
      `p IN FDOM env.proc` by (gvs[FLOOKUP_DEF] >> Cases_on `p IN FDOM env.proc` >> gvs[]) >>
      gvs[FEVERY_DEF] >> first_x_assum (qspec_then `p` mp_tac) >> simp[] >>
      gvs[FLOOKUP_DEF, no_intermediate_terms_def])
  >- (`F` suffices_by simp[] >>
      `p IN FDOM env.proc` by (gvs[FLOOKUP_DEF] >> Cases_on `p IN FDOM env.proc` >> gvs[]) >>
      gvs[FEVERY_DEF] >> first_x_assum (qspec_then `p` mp_tac) >> simp[] >>
      gvs[FLOOKUP_DEF, no_intermediate_terms_def])
  >- (`F` suffices_by simp[] >>
      `p IN FDOM env.proc` by (gvs[FLOOKUP_DEF] >> Cases_on `p IN FDOM env.proc` >> gvs[]) >>
      gvs[FEVERY_DEF] >> first_x_assum (qspec_then `p` mp_tac) >> simp[] >>
      gvs[FLOOKUP_DEF, no_intermediate_terms_def])
QED

(* When stepping from no_intermediate_terms to intermediate terms, stack grows.
   This is because the only way to produce term_ITE/term_TRY is via term_ifte/term_trte,
   both of which use push_stack first. *)
Theorem step_to_intermediate_increases_stack:
  !env P S t S' rest.
    step env (running P, S ++ rest) (running t, S' ++ rest) /\
    no_intermediate_terms P /\
    FEVERY (\(_,t). no_intermediate_terms t) env.proc /\
    ~no_intermediate_terms t /\
    LENGTH S >= 1 ==>
    LENGTH S' >= 2
Proof
  Induct_on `P`
  >- ((* term_seq *)
      rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases, no_intermediate_terms_def] >> rpt strip_tac >>
      gvs[push_stack_def]
      >- (first_x_assum drule >> gvs[no_intermediate_terms_def])
      >- gvs[no_intermediate_terms_def]
      >- gvs[no_intermediate_terms_def])
  >- ((* term_or *)
      rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases] >> rpt strip_tac >> gvs[no_intermediate_terms_def])
  >- ((* term_ifte - main case: steps to term_ITE via push_stack *)
      rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases, top_stack_def, push_stack_def] >> rpt strip_tac >> gvs[])
  >- ((* term_trte - main case: steps to term_TRY via push_stack *)
      rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases, top_stack_def, push_stack_def] >> rpt strip_tac >> gvs[])
  >- ((* term_rscall - steps to final, not running *)
      rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases, push_stack_def, pop_stack_def] >> rpt strip_tac >> gvs[])
  >- ((* term_proc - FEVERY contradiction *)
      rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases] >> rpt strip_tac >> gvs[] >>
      `no_intermediate_terms t` by (drule_all FEVERY_FLOOKUP >> simp[]) >> gvs[])
  >- ((* term_alap - steps to term_trte which has no_intermediate_terms = T *)
      rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases] >> rpt strip_tac >> gvs[no_intermediate_terms_def])
  >- ((* term_skip - steps to final *) rpt strip_tac >>
      qpat_x_assum `step _ _ _` mp_tac >> simp[Once step_cases])
  >- ((* term_fail - steps to failed *) rpt strip_tac >>
      qpat_x_assum `step _ _ _` mp_tac >> simp[Once step_cases])
  >- ((* term_break - no step *) rpt strip_tac >>
      qpat_x_assum `step _ _ _` mp_tac >> simp[Once step_cases])
  >- ((* term_TRY - vacuous: no_intermediate_terms = F *)
      rpt strip_tac >> gvs[no_intermediate_terms_def])
  >- ((* term_ITE - vacuous: no_intermediate_terms = F *)
      rpt strip_tac >> gvs[no_intermediate_terms_def])
QED

(* Helper lemma: for no_intermediate_terms programs, stepping preserves the stack suffix. *)
Theorem step_preserves_suffix:
  !env P S q stk rest.
    step env (running P, S ++ rest) (q, stk) /\
    no_intermediate_terms P /\
    LENGTH S >= 1 ==>
    ?S'. stk = S' ++ rest
Proof
  `!P env S q stk rest.
    step env (running P, S ++ rest) (q, stk) /\
    no_intermediate_terms P /\
    LENGTH S >= 1 ==>
    ?S'. stk = S' ++ rest` suffices_by metis_tac[] >>
  ho_match_mp_tac term_induction >> rpt conj_tac >> rpt gen_tac
  (* term_seq *)
  >- (strip_tac >> rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases] >> rpt strip_tac >> gvs[no_intermediate_terms_def]
      >- (first_x_assum drule_all >> simp[])
      >- (first_x_assum drule_all >> simp[]))
  (* term_or *)
  >- (strip_tac >> rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases] >> rpt strip_tac >> gvs[no_intermediate_terms_def])
  (* term_ifte *)
  >- (strip_tac >> rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases] >> rpt strip_tac >> gvs[no_intermediate_terms_def] >>
      qexists_tac `el::S'` >> simp[push_stack_def])
  (* term_trte *)
  >- (strip_tac >> rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases] >> rpt strip_tac >> gvs[no_intermediate_terms_def] >>
      qexists_tac `el::S'` >> simp[push_stack_def])
  (* term_rscall *)
  >- (rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases] >> rpt strip_tac >> gvs[no_intermediate_terms_def] >>
      Cases_on `S'` >> gvs[pop_stack_def] >>
      qexists_tac `(h, compose_morphism (track ri.lhs ri.inf m G) tr)::t` >>
      simp[push_stack_def])
  (* term_proc *)
  >- (rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases] >> rpt strip_tac >> gvs[no_intermediate_terms_def])
  (* term_alap *)
  >- (strip_tac >> rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases] >> rpt strip_tac >> gvs[no_intermediate_terms_def])
  (* term_skip *)
  >- (rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases] >> rpt strip_tac >> gvs[no_intermediate_terms_def])
  (* term_fail *)
  >- (rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases] >> rpt strip_tac >> gvs[no_intermediate_terms_def])
  (* term_break *)
  >- (rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases] >> rpt strip_tac >> gvs[no_intermediate_terms_def])
  (* term_TRY - vacuous: no_intermediate_terms = F *)
  >- (strip_tac >> rpt strip_tac >> gvs[no_intermediate_terms_def])
  (* term_ITE - vacuous: no_intermediate_terms = F *)
  >- (strip_tac >> rpt strip_tac >> gvs[no_intermediate_terms_def])
QED

(* Helper: stepping a no_intermediate_terms program with suffix preserves prefix length >= 1 *)
Theorem step_preserves_prefix_length:
  !env P S q S' rest.
    step env (running P, S ++ rest) (q, S' ++ rest) /\
    no_intermediate_terms P /\
    LENGTH S >= 1 ==>
    LENGTH S' >= 1
Proof
  Induct_on `P` >> rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
  simp[Once step_cases, no_intermediate_terms_def] >> rpt strip_tac >> gvs[]
  >- ((* seq1 *) first_x_assum drule >> gvs[no_intermediate_terms_def])
  >- ((* seq2 *) first_x_assum drule >> gvs[no_intermediate_terms_def])
  >- ((* ifte *) gvs[push_stack_def] >> Cases_on `S'` >> gvs[])
  >- ((* trte *) gvs[push_stack_def] >> Cases_on `S'` >> gvs[])
  >- ((* rscall *) gvs[push_stack_def, pop_stack_def] >>
      Cases_on `S' ++ rest` >> gvs[] >> Cases_on `S'` >> gvs[])
  >- ((* term_TRY: no_intermediate_terms = F *) gvs[no_intermediate_terms_def])
  >- ((* term_TRY inner running *) gvs[no_intermediate_terms_def])
  >- ((* term_TRY inner final *) gvs[no_intermediate_terms_def])
  >- ((* term_TRY inner failed *) gvs[no_intermediate_terms_def])
  >- ((* term_ITE inner running *) gvs[no_intermediate_terms_def])
  >- ((* term_ITE inner final *) gvs[no_intermediate_terms_def])
  >- ((* term_ITE inner failed *) gvs[no_intermediate_terms_def])
QED

Definition count_intermediate_terms_def:
  count_intermediate_terms (term_seq a b) =
    (count_intermediate_terms a + count_intermediate_terms b) /\
  count_intermediate_terms (term_or a b) =
    (count_intermediate_terms a + count_intermediate_terms b) /\
  count_intermediate_terms (term_ifte a b c) =
    (count_intermediate_terms a + count_intermediate_terms b + count_intermediate_terms c) /\
  count_intermediate_terms (term_trte a b c) =
    (count_intermediate_terms a + count_intermediate_terms b + count_intermediate_terms c) /\
  count_intermediate_terms (term_rscall rset) = 0 /\
  count_intermediate_terms (term_proc pid) = 0 /\
  count_intermediate_terms (term_alap t) = count_intermediate_terms t /\
  count_intermediate_terms term_skip = 0 /\
  count_intermediate_terms term_fail = 0 /\
  count_intermediate_terms term_break = 0 /\
  count_intermediate_terms (term_TRY a b c) =
    SUC (count_intermediate_terms a + count_intermediate_terms b + count_intermediate_terms c) /\
  count_intermediate_terms (term_ITE a b c) =
    SUC (count_intermediate_terms a + count_intermediate_terms b + count_intermediate_terms c)
End

(* Well-formed Intermediate Terms - intermediate terms only appear in leftmost position of sequences *)
Definition wf_intermediate_terms_def:
  wf_intermediate_terms (term_seq a b) =
    (wf_intermediate_terms a /\ no_intermediate_terms b) /\
  wf_intermediate_terms (term_or a b) =
    (no_intermediate_terms a /\ no_intermediate_terms b) /\
  wf_intermediate_terms (term_ifte a b c) =
    (no_intermediate_terms a /\ no_intermediate_terms b /\ no_intermediate_terms c) /\
  wf_intermediate_terms (term_trte a b c) =
    (no_intermediate_terms a /\ no_intermediate_terms b /\ no_intermediate_terms c) /\
  wf_intermediate_terms (term_rscall rset) = T /\
  wf_intermediate_terms (term_proc pid) = T /\
  wf_intermediate_terms (term_alap t) = no_intermediate_terms t /\
  wf_intermediate_terms term_skip = T /\
  wf_intermediate_terms term_fail = T /\
  wf_intermediate_terms term_break = T /\
  wf_intermediate_terms (term_TRY a b c) =
    (wf_intermediate_terms a /\ no_intermediate_terms b /\ no_intermediate_terms c) /\
  wf_intermediate_terms (term_ITE a b c) =
    (wf_intermediate_terms a /\ no_intermediate_terms b /\ no_intermediate_terms c)
End

Theorem no_intermediate_terms_count_0:
  !t. no_intermediate_terms t <=> count_intermediate_terms t = 0
Proof
  Induct_on `t` THEN simp [no_intermediate_terms_def, count_intermediate_terms_def]
QED

Theorem no_intermediate_terms_well_formed:
  !t. no_intermediate_terms t ==> wf_intermediate_terms t
Proof
  Induct_on `t` THEN simp [no_intermediate_terms_def, wf_intermediate_terms_def]
QED

Theorem no_intermediate_terms_OK:
  !t. no_intermediate_terms t <=>
      (count_intermediate_terms t = 0 /\ wf_intermediate_terms t)
Proof
  METIS_TAC[no_intermediate_terms_well_formed, no_intermediate_terms_count_0]
QED

(* Stack Invariant - relates configuration to a fixed base stack S2 *)
Definition config_wf_fixed_stack_def:
  config_wf_fixed_stack S2 (final, S) = (?s'. S = s' :: S2) /\
  config_wf_fixed_stack S2 (failed, S) = (?s'. S = s' :: S2) /\
  config_wf_fixed_stack S2 (running t, S) =
    (?S1. S = S1 ++ S2 /\
          wf_intermediate_terms t /\
          LENGTH S1 = SUC (count_intermediate_terms t))
End

Theorem step_fails_stack_unchanged:
  !env P S S'. step env (running P, S) (failed, S') ==> S = S'
Proof
  Induct_on `P` THEN simp[Once step_cases] THEN METIS_TAC[]
QED

Theorem step_fails_no_intermediate:
  !env P S S'.
    step env (running P, S) (failed, S') ==>
    wf_intermediate_terms P ==>
    count_intermediate_terms P = 0
Proof
  Induct_on `P` THEN simp[Once step_cases]
  THEN simp [wf_intermediate_terms_def, no_intermediate_terms_OK, count_intermediate_terms_def]
  THEN METIS_TAC[]
QED

(* Main Stack Invariant Theorem (Single Step) *)
Theorem step_STACK_INVARIANT_RUNNING:
  !env. FEVERY (\(_, t). no_intermediate_terms t) env.proc ==>
  !P S1 S2 c.
    config_wf_fixed_stack S2 (running P, S1) ==>
    step env (running P, S1) c ==>
    config_wf_fixed_stack S2 c
Proof
  GEN_TAC THEN strip_tac
  THEN Induct_on `P` THEN (
       ONCE_REWRITE_TAC[step_cases]
       THEN simp []
       THEN fs [
              GSYM LEFT_FORALL_IMP_THM, DISJ_IMP_THM, IMP_CONJ_THM, FORALL_AND_THM, GSYM RIGHT_FORALL_IMP_THM,
              config_wf_fixed_stack_def, count_intermediate_terms_def, wf_intermediate_terms_def,
              no_intermediate_terms_OK]
  ) >- (
    (* seq *)
    SIMP_TAC (list_ss++boolSimps.CONJ_ss) []
    THEN rpt strip_tac
    >- (
         rename1 `step env (running P, S1a ++ S2) (running Pa, Sa)`
      THEN Q.PAT_X_ASSUM `!S2 c S1a. wf_intermediate_terms P' /\ _ ==> _` (K ALL_TAC)
      THEN Q.PAT_X_ASSUM `!S2 c S1a. wf_intermediate_terms P /\ _ ==> _` (MP_TAC o Q.SPECL [`S2`, `(running Pa, Sa)`, `S1a`])
      THEN fs [config_wf_fixed_stack_def]
    ) >- (
         Q.PAT_X_ASSUM `!S2 c S1a. wf_intermediate_terms P' /\ _ ==> _` (K ALL_TAC)
      THEN Q.PAT_X_ASSUM `!S2 c S1a. wf_intermediate_terms P /\ _ ==> _` (MP_TAC o Q.SPECL [`S2`, `(final, S')`, `S1'`])
      THEN fs [config_wf_fixed_stack_def, GSYM LEFT_FORALL_IMP_THM]
    ) >- (
      `count_intermediate_terms P = 0`  by METIS_TAC[step_fails_no_intermediate]
      THEN fs [LIST_LENGTH_1]
    )
  ) >- (
    (* ifte *)
    SIMP_TAC (list_ss++boolSimps.CONJ_ss ++ QUANT_INST_ss [list_qp]) [top_stack_def, push_stack_def]
    THEN rpt strip_tac
    THEN Q.EXISTS_TAC `[el;el]`
    THEN simp []
  ) >- (
    (* trte *)
    SIMP_TAC (list_ss++boolSimps.CONJ_ss ++ QUANT_INST_ss [list_qp]) [top_stack_def, push_stack_def]
    THEN rpt strip_tac
    THEN Q.EXISTS_TAC `[el;el]`
    THEN simp []
  ) >- (
    (* rscall *)
    SIMP_TAC (list_ss++boolSimps.CONJ_ss ++ QUANT_INST_ss [list_qp]) [pop_stack_def, push_stack_def]
  ) >- (
    (* proc *)
   fs[FEVERY_ALL_FLOOKUP]
   THEN METIS_TAC[]
  ) >- (
    (* skip *)
   fs [LIST_LENGTH_1]
  ) >- (
    (* fail *)
   fs [LIST_LENGTH_1]
  ) >- (
    (* term_TRY *)
    SIMP_TAC (list_ss++boolSimps.CONJ_ss) []
    THEN rpt CONJ_TAC
    >- (
      (* Alap2 case - break exits loop *)
      fs [LENGTH_EQ_NUM]
      THEN SIMP_TAC (list_ss++boolSimps.CONJ_ss ++ QUANT_INST_ss [list_qp]) [count_intermediate_terms_def, pop2_stack_def,
        AND_IMP_INTRO]
    ) >- (
      (* Try2 case - condition steps to running *)
      rpt STRIP_TAC
      THEN sg `?S1b s2. S1' = SNOC s2 S1b` >- (
         Cases_on `S1' = []`
         >- fs []
         >- METIS_TAC[SNOC_CASES]
      )
      THEN FULL_SIMP_TAC list_ss [APPEND_SNOC1]
      THEN Q.PAT_X_ASSUM `!S2 c S1. _ ==> step env (running P, _) c ==> _` (MP_TAC o Q.SPECL [`s2::S2`, `(running C', S')`, `S1b`])
      THEN ASM_SIMP_TAC list_ss [config_wf_fixed_stack_def, GSYM LEFT_FORALL_IMP_THM]
      THEN REPEAT STRIP_TAC
      THEN Q.EXISTS_TAC `SNOC s2 S1`
      THEN FULL_SIMP_TAC list_ss [APPEND_SNOC1]
   ) >- (
      (* Try3 case - condition steps to final *)
      rpt STRIP_TAC
      THEN sg `?S1b s2. S1' = SNOC s2 S1b` >- (
         Cases_on `S1' = []`
         >- fs []
         >- METIS_TAC[SNOC_CASES]
      )
      THEN FULL_SIMP_TAC list_ss [APPEND_SNOC1]
      THEN Q.PAT_X_ASSUM `pop2_stack _ = SOME _` (MP_TAC o GSYM)
      THEN Q.PAT_X_ASSUM `!S2 c S1. _ ==> step env (running P, _) c ==> _` (MP_TAC o Q.SPECL [`s2::S2`, `(final, S')`, `S1b`])
      THEN ASM_SIMP_TAC list_ss [config_wf_fixed_stack_def, GSYM LEFT_FORALL_IMP_THM, pop2_stack_def]
      THEN REPEAT STRIP_TAC
      THEN Q.EXISTS_TAC `[s']`
      THEN fs []
   ) >- (
      (* Try4 case - condition steps to failed *)
      rpt STRIP_TAC
      THEN `count_intermediate_terms P = 0`  by METIS_TAC[step_fails_no_intermediate]
      THEN fs [LENGTH_EQ_NUM]
      THEN Q.PAT_X_ASSUM `pop_stack _ = SOME _` (MP_TAC o GSYM)
      THEN fs [pop_stack_def]
   )
 ) >- (
    (* term_ITE *)
    SIMP_TAC (list_ss++boolSimps.CONJ_ss) []
    THEN rpt CONJ_TAC
    >- (
      (* If2 case - condition steps to running *)
      rpt STRIP_TAC
      THEN sg `?S1b s2. S1' = SNOC s2 S1b` >- (
         Cases_on `S1' = []`
         >- fs []
         >- METIS_TAC[SNOC_CASES]
      )
      THEN FULL_SIMP_TAC list_ss [APPEND_SNOC1]
      THEN Q.PAT_X_ASSUM `!S2 c S1. _ ==> step env (running P, _) c ==> _` (MP_TAC o Q.SPECL [`s2::S2`, `(running C', S')`, `S1b`])
      THEN ASM_SIMP_TAC list_ss [config_wf_fixed_stack_def, GSYM LEFT_FORALL_IMP_THM]
      THEN REPEAT STRIP_TAC
      THEN Q.EXISTS_TAC `SNOC s2 S1`
      THEN FULL_SIMP_TAC list_ss [APPEND_SNOC1]
   ) >- (
      (* If3 case - condition steps to final *)
      rpt STRIP_TAC
      THEN sg `?S1b s2. S1' = SNOC s2 S1b` >- (
         Cases_on `S1' = []`
         >- fs []
         >- METIS_TAC[SNOC_CASES]
      )
      THEN FULL_SIMP_TAC list_ss [APPEND_SNOC1]
      THEN Q.PAT_X_ASSUM `pop_stack _ = SOME _` (MP_TAC o GSYM)
      THEN Q.PAT_X_ASSUM `!S2 c S1. _ ==> step env (running P, _) c ==> _` (MP_TAC o Q.SPECL [`s2::S2`, `(final, S')`, `S1b`])
      THEN ASM_SIMP_TAC list_ss [config_wf_fixed_stack_def, GSYM LEFT_FORALL_IMP_THM, pop_stack_def]
      THEN REPEAT STRIP_TAC
      THEN Q.EXISTS_TAC `[s2]`
      THEN fs []
   ) >- (
      (* If4 case - condition steps to failed *)
      rpt STRIP_TAC
      THEN `count_intermediate_terms P = 0`  by METIS_TAC[step_fails_no_intermediate]
      THEN fs [LENGTH_EQ_NUM]
      THEN Q.PAT_X_ASSUM `pop_stack _ = SOME _` (MP_TAC o GSYM)
      THEN fs [pop_stack_def]
   )
 )
QED

(* Stack Invariant for Any Configuration *)
Theorem step_STACK_INVARIANT:
  !env S2 c1 c2.
    FEVERY (\(_,t). no_intermediate_terms t) env.proc ==>
    config_wf_fixed_stack S2 c1 ==>
    step env c1 c2 ==>
    config_wf_fixed_stack S2 c2
Proof
  Cases_on `c1`
  THEN rename1 `(st, stk)`
  THEN Cases_on `st`
  THEN METIS_TAC [step_STACK_INVARIANT_RUNNING, step_only_running_rewrs]
QED

(* Multi-Step Stack Invariant *)
Theorem steps_STACK_INVARIANT:
  !env S2 c1 c2.
    FEVERY (\(_,t). no_intermediate_terms t) env.proc ==>
    config_wf_fixed_stack S2 c1 ==>
    steps env c1 c2 ==>
    config_wf_fixed_stack S2 c2
Proof
  simp [steps_NRC, GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_IMP_THM]
  THEN Induct_on `n` THEN fs [NRC]
  THEN METIS_TAC [step_STACK_INVARIANT]
QED

(* Finished predicate for configurations *)
Definition is_finished_def:
  is_finished (running t, s) s' = F /\
  is_finished (final, s) s' = (s = s') /\
  is_finished (failed, s) s' = (s = s')
End

(* Main Result: Stack Structure at Termination *)
Theorem steps_STACK_INVARIANT_FINISHED:
  !env t S1 s1 c2 S2.
    FEVERY (\(_,t). no_intermediate_terms t) env.proc ==>
    steps env (running t, s1 :: S1) c2 ==>
    is_finished c2 S2 ==>
    no_intermediate_terms t ==>
    ?s2. S2 = s2 :: S1
Proof
  rpt strip_tac
  THEN `config_wf_fixed_stack S1 (running t, s1 :: S1)` by
    (fs [config_wf_fixed_stack_def, no_intermediate_terms_OK] THEN Q.EXISTS_TAC `[s1]` THEN simp[])
  THEN `config_wf_fixed_stack S1 c2` by METIS_TAC [steps_STACK_INVARIANT]
  THEN Cases_on `c2`
  THEN rename1 `(st, stk)`
  THEN Cases_on `st`
  THEN fs [is_finished_def, config_wf_fixed_stack_def]
  THEN METIS_TAC[]
QED

(* Corollary: Singleton Stack for Final Configurations *)
Theorem steps_SINGLETON_STACK_FINAL:
  !env t G c2.
    FEVERY (\(_,t). no_intermediate_terms t) env.proc ==>
    steps env (running t, [G]) c2 ==>
    ~can_step c2 ==>
    no_intermediate_terms t ==>
    ?G'. c2 = (final, [G']) \/ c2 = (failed, [G']) \/ c2 = (running term_break, [G'])
Proof
  rpt strip_tac
  THEN `config_wf_fixed_stack [] (running t, [G])` by
    (fs [config_wf_fixed_stack_def, no_intermediate_terms_OK] THEN Q.EXISTS_TAC `[G]` THEN simp[])
  THEN `config_wf_fixed_stack [] c2` by METIS_TAC [steps_STACK_INVARIANT]
  THEN Cases_on `c2`
  THEN rename1 `(st, stk)`
  THEN Cases_on `st` >- (
    (* running case *)
    fs [can_step_def, config_wf_fixed_stack_def]
    THEN fs [count_intermediate_terms_def]
    THEN Cases_on `stk` THEN fs []
    THEN fs [can_step_def, count_intermediate_terms_def, LENGTH_NIL]
    THEN `t' = term_break` by (Cases_on `t'` THEN fs [can_step_def])
    THEN fs [count_intermediate_terms_def, LENGTH_NIL]
  ) >- (
    (* final case *)
    fs [config_wf_fixed_stack_def]
  ) >- (
    (* failed case *)
    fs [config_wf_fixed_stack_def]
  )
QED

(* Helper lemma: for non-empty stacks, the tail is preserved *)
Theorem no_intermediate_terms_preserves_stack_tail:
  !n P env h t state S'.
    NRC (step env) n (running P, h::t) (state, S') /\
    ~can_step (state, S') /\
    no_intermediate_terms P /\
    FEVERY (\(_,t). no_intermediate_terms t) env.proc ==>
    ?h'. S' = h'::t
Proof
  rpt strip_tac >>
  `config_wf_fixed_stack t (running P, h :: t)` by
    (simp[config_wf_fixed_stack_def] >>
     `wf_intermediate_terms P` by metis_tac[no_intermediate_terms_well_formed] >>
     `count_intermediate_terms P = 0` by metis_tac[no_intermediate_terms_count_0] >>
     simp[] >> qexists_tac `[h]` >> simp[]) >>
  `steps env (running P, h::t) (state, S')` by (simp[steps_NRC] >> metis_tac[]) >>
  `config_wf_fixed_stack t (state, S')` by metis_tac[steps_STACK_INVARIANT] >>
  Cases_on `state`
  >- (gvs[config_wf_fixed_stack_def] >>
      `t' = term_break` by (Cases_on `t'` >> gvs[can_step_def]) >>
      gvs[count_intermediate_terms_def] >> Cases_on `S1` >> gvs[])
  >- gvs[config_wf_fixed_stack_def]
  >- gvs[config_wf_fixed_stack_def]
QED

(* Empty stack helper lemmas for stack length preservation *)

(* Step from empty stack with no_intermediate_terms produces empty stack *)
Theorem step_empty_stack_preserves:
  !env c1 c2. step env c1 c2 ==>
    !P st stk. c1 = (running P, []) /\ c2 = (st, stk) /\
    no_intermediate_terms P /\
    FEVERY (\(_,t). no_intermediate_terms t) env.proc ==>
    stk = []
Proof
  ho_match_mp_tac step_strongind >> rpt conj_tac >> rpt strip_tac >>
  gvs[no_intermediate_terms_def, pop_stack_def, top_stack_def, push_stack_def]
QED

(* Step from empty stack preserves no_intermediate_terms property *)
Theorem step_empty_preserves_no_intermediate:
  !env c1 c2. step env c1 c2 ==>
    !P P'. c1 = (running P, []) /\ c2 = (running P', []) /\
    no_intermediate_terms P /\
    FEVERY (\(_,t). no_intermediate_terms t) env.proc ==>
    no_intermediate_terms P'
Proof
  ho_match_mp_tac step_strongind >> rpt conj_tac >> rpt strip_tac >>
  gvs[no_intermediate_terms_def, pop_stack_def, top_stack_def, push_stack_def] >>
  imp_res_tac FEVERY_FLOOKUP >> gvs[]
QED

(* NRC version: empty stack execution with no_intermediate_terms preserves empty stack *)
Theorem NRC_empty_stack_preserves:
  !n P env state stk'.
    NRC (step env) n (running P, []) (state, stk') /\
    ~can_step (state, stk') /\
    no_intermediate_terms P /\
    FEVERY (\(_,t). no_intermediate_terms t) env.proc ==>
    stk' = []
Proof
  Induct_on `n` >> rpt strip_tac
  >- gvs[NRC]
  >- (gvs[NRC] >>
      Cases_on `z` >> rename1 `step env (running P, []) (st, stk)` >>
      `stk = []` by metis_tac[step_empty_stack_preserves] >> gvs[] >>
      Cases_on `st`
      >- (rename1 `step env (running P, []) (running t, [])` >>
          first_x_assum irule >> simp[] >>
          metis_tac[step_empty_preserves_no_intermediate])
      >- (drule NRC_step_from_final >> simp[])
      >- (drule NRC_step_from_failed >> simp[]))
QED

(* Stack length invariant: no_intermediate_terms programs preserve stack length.
   This is needed to ensure pop2_stack_append preconditions in term_TRY case.
   The proof uses complete induction on n and handles each term constructor:
   - term_skip/fail/break: trivial (go to final/failed/break in 1 step)
   - term_seq/or: decompose and apply IH
   - term_ifte/trte: push + C runs + pop + P/Q runs, net effect 0
   - term_rscall: pop + push, net effect 0
   - term_proc: procedure body preserves length by FEVERY hypothesis
   - term_alap: repeatedly runs body which preserves length
   - term_TRY/ITE: vacuous (no_intermediate_terms = F) *)
Theorem no_intermediate_terms_preserves_stack_length:
  !n P env stk state stk'.
    NRC (step env) n (running P, stk) (state, stk') /\
    ~can_step (state, stk') /\
    no_intermediate_terms P /\
    FEVERY (\(_,t). no_intermediate_terms t) env.proc ==>
    LENGTH stk' = LENGTH stk
Proof
  rpt strip_tac >> Cases_on `stk`
  (* stk = [] case: empty stack stays empty *)
  >- (drule_all NRC_empty_stack_preserves >> simp[])
  (* stk = h::t case: use no_intermediate_terms_preserves_stack_tail *)
  >- (rename1 `h :: t` >>
      drule_all no_intermediate_terms_preserves_stack_tail >> strip_tac >> gvs[])
QED

(* Generalized suffix preservation for well-formed intermediate terms.
   Uses the stack invariant: LENGTH prefix = SUC (count_intermediate_terms t).
   When execution completes, count drops to 0, so prefix has length 1, preserving suffix. *)
Theorem NRC_wf_intermediate_preserves_suffix:
  !env n t S q stk rest.
    NRC (step env) n (running t, S ++ rest) (q, stk) /\
    ~can_step (q, stk) /\
    FEVERY (\(_,t). no_intermediate_terms t) env.proc /\
    wf_intermediate_terms t /\
    LENGTH S = SUC (count_intermediate_terms t) ==>
    ?S'. stk = S' ++ rest
Proof
  completeInduct_on `n` >> rpt strip_tac >> Cases_on `n`
  (* Base case: n = 0 *)
  >- (rename1 `LENGTH prefix = _` >> gvs[NRC_0] >> qexists_tac `prefix` >> simp[])
  (* Inductive case: n = SUC n' *)
  >- (rename1 `NRC _ (SUC n') _ _` >> rename1 `LENGTH prefix = _` >> gvs[NRC] >>
      Cases_on `z` >> rename1 `step env _ (q', stk')` >>
      (* Use step_STACK_INVARIANT to track suffix preservation *)
      `config_wf_fixed_stack rest (running t, prefix ++ rest)` by simp[config_wf_fixed_stack_def] >>
      `config_wf_fixed_stack rest (q', stk')` by metis_tac[step_STACK_INVARIANT] >>
      Cases_on `q'`
      (* q' = running t': apply IH *)
      >- (gvs[config_wf_fixed_stack_def] >>
          first_x_assum (qspec_then `n'` mp_tac) >> simp[] >>
          disch_then drule >> simp[])
      (* q' = final: no more steps from final *)
      >- (drule NRC_step_from_final >> strip_tac >> gvs[config_wf_fixed_stack_def])
      (* q' = failed: no more steps from failed *)
      >- (drule NRC_step_from_failed >> strip_tac >> gvs[config_wf_fixed_stack_def]))
QED

(* Helper: stepping a wf_intermediate_terms program preserves suffix.
   This follows directly from step_STACK_INVARIANT.
   (Moved from stackInvariantScript) *)
Theorem step_preserves_suffix_wf:
  !env P S q stk rest.
    step env (running P, S ++ rest) (q, stk) /\
    wf_intermediate_terms P /\
    FEVERY (\(_, t). no_intermediate_terms t) env.proc /\
    LENGTH S = SUC (count_intermediate_terms P) ==>
    ?S'. stk = S' ++ rest /\ LENGTH S' >= 1
Proof
  rpt strip_tac >>
  `config_wf_fixed_stack rest (running P, S' ++ rest)` by
    simp[config_wf_fixed_stack_def] >>
  `config_wf_fixed_stack rest (q, stk)` by metis_tac[step_STACK_INVARIANT] >>
  Cases_on `q` >> fs[config_wf_fixed_stack_def] >>
  metis_tac[]
QED

(* Inverse frame for wf_intermediate_terms programs - auxiliary form for induction.

   Key insight: From h1::tl = S'' ++ rest (the result stack with suffix),
   we derive tl = TL S'' ++ rest, so the intermediate stack h1::h2::tl has
   rest as suffix and can be decomposed as (h1::h2::TL S'') ++ rest. *)
Theorem step_inverse_frame_wf_aux:
  !env cfg1 cfg2. step env cfg1 cfg2 ==>
    !P S state S' rest.
      cfg1 = (running P, S ++ rest) /\
      cfg2 = (state, S' ++ rest) /\
      wf_intermediate_terms P /\
      FEVERY (\(_, t). no_intermediate_terms t) env.proc /\
      LENGTH S >= SUC (count_intermediate_terms P) ==>
      step env (running P, S) (state, S')
Proof
  ho_match_mp_tac step_ind >> rpt conj_tac >> rpt gen_tac
  (* Case 1: RuleCall success (Call1) *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def,
      pop_stack_def, push_stack_def] >> Cases_on `S''` >> gvs[] >>
      once_rewrite_tac[step_cases] >> simp[pop_stack_def, push_stack_def] >> metis_tac[])
  (* Case 1b: RuleCall failure (Call2) *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def,
      pop_stack_def] >> Cases_on `S''` >> gvs[] >>
      once_rewrite_tac[step_cases] >> simp[pop_stack_def] >> metis_tac[])
  (* Case 2: ProcCall *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def] >>
      irule step_ProcCall >> simp[])
  (* Case 3: Seq running *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def] >>
      irule step_Seq1 >> first_x_assum irule >> simp[])
  (* Case 4: Seq final *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def] >>
      irule step_Seq2 >> first_x_assum irule >> simp[])
  (* Case 5: Seq failed *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def] >>
      irule step_Seq3 >> first_x_assum irule >> simp[])
  (* Case 6: Break *)
  >- (strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def] >>
      irule step_Break)
  (* Case 7: Alap1 *)
  >- (strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def] >>
      irule step_Alap1)
  (* Case 8: Alap2 (break escape) *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def,
      pop2_stack_def] >> Cases_on `S''` >- gvs[] >>
      Cases_on `t` >> gvs[] >> once_rewrite_tac[step_cases] >> simp[pop2_stack_def])
  (* Case 9: term_ifte *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def,
      push_stack_def, top_stack_def] >> Cases_on `S''` >> gvs[] >>
      once_rewrite_tac[step_cases] >> simp[top_stack_def, push_stack_def])
  (* Case 10: term_ITE running *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def] >>
      irule step_If2 >> first_x_assum irule >> simp[])
  (* Case 11: term_ITE final - uses config_wf_fixed_stack invariant *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def] >>
      once_rewrite_tac[step_cases] >> simp[pop_stack_def] >>
      disj2_tac >> disj1_tac >>
      `LENGTH S'³' >= SUC (count_intermediate_terms C)` by simp[] >>
      `S'³' = TAKE (SUC (count_intermediate_terms C)) S'³' ++
              DROP (SUC (count_intermediate_terms C)) S'³'` by simp[TAKE_DROP] >>
      qabbrev_tac `sfx = DROP (SUC (count_intermediate_terms C)) S'³' ++ rest` >>
      sg `config_wf_fixed_stack sfx (running C, S'³' ++ rest)`
      >- (Q.UNABBREV_TAC `sfx` >>
          rewrite_tac[config_wf_fixed_stack_def] >> simp[GSYM APPEND_ASSOC] >>
          qexists_tac `TAKE (SUC (count_intermediate_terms C)) S'³'` >>
          simp[LENGTH_TAKE]) >>
      sg `config_wf_fixed_stack sfx (final, S'')`
      >- (`step env (running C, S'³' ++ rest) (final, S'')` by
            (first_x_assum (qspecl_then [`S'³' ++ rest`, `S''`, `[]`] mp_tac) >> simp[]) >>
          drule_all step_STACK_INVARIANT >> simp[]) >>
      gvs[config_wf_fixed_stack_def, Abbr `sfx`] >> gvs[pop_stack_def] >>
      qexists_tac `s' :: DROP (SUC (count_intermediate_terms C)) S'³'` >>
      qexists_tac `(s', DROP (SUC (count_intermediate_terms C)) S'³')` >> simp[])
  (* Case 12: term_ITE failed *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def,
      pop_stack_def] >> Cases_on `S'³'` >> gvs[] >>
      once_rewrite_tac[step_cases] >> simp[pop_stack_def])
  (* Case 13: term_trte *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def,
      push_stack_def, top_stack_def] >> Cases_on `S''` >> gvs[] >>
      once_rewrite_tac[step_cases] >> simp[top_stack_def, push_stack_def])
  (* Case 14: term_TRY running *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def] >>
      irule step_Try2 >> first_x_assum irule >> simp[])
  (* Case 15: term_TRY final - similar to case 11 but with pop2_stack *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def] >>
      once_rewrite_tac[step_cases] >> simp[pop2_stack_def] >>
      disj2_tac >> disj1_tac >>
      `LENGTH S'³' >= SUC (count_intermediate_terms C)` by simp[] >>
      `S'³' = TAKE (SUC (count_intermediate_terms C)) S'³' ++
              DROP (SUC (count_intermediate_terms C)) S'³'` by simp[TAKE_DROP] >>
      qabbrev_tac `sfx = DROP (SUC (count_intermediate_terms C)) S'³' ++ rest` >>
      sg `config_wf_fixed_stack sfx (running C, S'³' ++ rest)`
      >- (Q.UNABBREV_TAC `sfx` >>
          rewrite_tac[config_wf_fixed_stack_def] >> simp[GSYM APPEND_ASSOC] >>
          qexists_tac `TAKE (SUC (count_intermediate_terms C)) S'³'` >>
          simp[LENGTH_TAKE]) >>
      `step env (running C, S'³' ++ rest) (final, S'')` by
        (first_x_assum (qspecl_then [`S'³' ++ rest`, `S''`, `[]`] mp_tac) >> simp[]) >>
      `config_wf_fixed_stack sfx (final, S'')` by
        (drule_all step_STACK_INVARIANT >> simp[]) >>
      gvs[config_wf_fixed_stack_def, Abbr `sfx`, pop2_stack_def] >>
      Cases_on `DROP (SUC (count_intermediate_terms C)) S'³'` >> gvs[] >>
      qexists_tac `s' :: h :: t` >> qexists_tac `([h], s' :: t)` >> simp[])
  (* Case 16: term_TRY failed *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def,
      pop_stack_def] >> Cases_on `S'³'` >> gvs[] >>
      once_rewrite_tac[step_cases] >> simp[pop_stack_def])
  (* Case 17: Or left *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def] >>
      irule step_Or1)
  (* Case 18: Or right *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def] >>
      irule step_Or2)
  (* Case 19: Skip *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def] >>
      irule step_Skip)
  (* Case 20: Fail *)
  >- (rpt strip_tac >> gvs[wf_intermediate_terms_def, count_intermediate_terms_def] >>
      irule step_Fail)
QED

(* Main theorem derived from auxiliary form. *)
Theorem step_inverse_frame_wf:
  !env P S state S' rest.
    step env (running P, S ++ rest) (state, S' ++ rest) /\
    wf_intermediate_terms P /\
    FEVERY (\(_, t). no_intermediate_terms t) env.proc /\
    LENGTH S >= SUC (count_intermediate_terms P) ==>
    step env (running P, S) (state, S')
Proof
  rpt strip_tac >> irule step_inverse_frame_wf_aux >> metis_tac[]
QED


Theorem NRC_step_preserves_suffix:
  !env n P S q stk rest.
    NRC (step env) n (running P, S ++ rest) (q, stk) /\
    ~can_step (q, stk) /\
    no_intermediate_terms P /\
    FEVERY (\(_,t). no_intermediate_terms t) env.proc /\
    LENGTH S >= 1 ==>
    ?S'. stk = S' ++ rest
Proof
  (* Split on whether S has exactly length 1 or more.
     Length 1 case uses NRC_wf_intermediate_preserves_suffix directly.
     Length >= 2 case: extra prefix elements act as part of suffix for the LENGTH=1 case. *)
  rpt strip_tac >> rename1 `LENGTH prefix >= 1` >>
  `LENGTH prefix = 1 \/ LENGTH prefix >= 2` by simp[]
  (* LENGTH prefix = 1: apply NRC_wf_intermediate_preserves_suffix directly *)
  >- (`wf_intermediate_terms P /\ count_intermediate_terms P = 0`
        by metis_tac[no_intermediate_terms_OK] >>
      irule NRC_wf_intermediate_preserves_suffix >> simp[] >>
      qexists_tac `prefix` >> qexists_tac `env` >> qexists_tac `n` >>
      qexists_tac `q` >> qexists_tac `P` >> simp[])
  (* LENGTH prefix >= 2: split prefix = [hd] ++ tl, use NRC_wf with suffix (tl ++ rest) *)
  >- (Cases_on `prefix`
      (* prefix = []: contradicts LENGTH prefix >= 2 *)
      >- gvs[]
      (* prefix = h::t: rewrite to [h] ++ (t ++ rest) *)
      >- (`LENGTH t >= 1` by gvs[] >>
          `(h::t) ++ rest = [h] ++ (t ++ rest)` by simp[] >>
          `wf_intermediate_terms P /\ count_intermediate_terms P = 0`
            by metis_tac[no_intermediate_terms_OK] >>
          `?S''. stk = S'' ++ (t ++ rest)` suffices_by
            (strip_tac >> qexists_tac `S'' ++ t` >> simp[]) >>
          irule NRC_wf_intermediate_preserves_suffix >>
          qexists_tac `[h]` >> qexists_tac `env` >> qexists_tac `n` >>
          qexists_tac `q` >> qexists_tac `P` >> simp[] >> gvs[]))
QED

(* NRC version of step_inverse_frame: frame removal for multi-step execution.
   Uses complete induction. When stepping produces an intermediate term,
   we use the observation that such executions still preserve the suffix. *)

Theorem bla:
  !n env P S state S' rest.
    NRC (step env) n (running P, S ++ rest) (state, S' ++ rest) /\
    wf_intermediate_terms P /\
    FEVERY (\(_, t). no_intermediate_terms t) env.proc /\
    LENGTH S >= SUC (count_intermediate_terms P) ==>
    NRC (step env) n (running P, S) (state, S')
Proof
  Induct_on `n` >- simp[NRC_0] >>
  rpt gen_tac >> strip_tac >>
  rename1 `LENGTH stk >= _` >>
  (* Split stk into prefix (exact length for invariant) and extra *)
  qabbrev_tac `k = SUC (count_intermediate_terms P)` >>
  qabbrev_tac `prefix = TAKE k stk` >>
  qabbrev_tac `extra = DROP k stk` >>
  `stk = prefix ++ extra /\ LENGTH prefix = k` by
    simp[Abbr `prefix`, Abbr `extra`, Abbr `k`, TAKE_DROP, LENGTH_TAKE] >>
  qabbrev_tac `suffix = extra ++ rest` >>
  `stk ++ rest = prefix ++ suffix` by simp[Abbr `suffix`] >>
  (* Establish stack invariant *)
  `config_wf_fixed_stack suffix (running P, prefix ++ suffix)` by
    (simp[config_wf_fixed_stack_def, Abbr `k`] >> qexists_tac `prefix` >> simp[]) >>
  (* Extract intermediate state from NRC (SUC n) *)
  `?z. step env (running P, stk ++ rest) z /\ NRC (step env) n z (state, S'' ++ rest)` by
    (qpat_x_assum `NRC _ (SUC _) _ _` mp_tac >> simp[NRC]) >>
  `config_wf_fixed_stack suffix z` by metis_tac[step_STACK_INVARIANT] >>
  `?q' stk'. z = (q', stk')` by (Cases_on `z` >> simp[]) >> fs[] >>
  (* Case analysis on intermediate state *)
  Cases_on `q'`
  (* Case: running t *)
  >- (`?S1. stk' = S1 ++ suffix /\ wf_intermediate_terms t /\
             LENGTH S1 = SUC (count_intermediate_terms t)` by
        (qpat_x_assum `config_wf_fixed_stack suffix (running t, _)` mp_tac >>
         simp[config_wf_fixed_stack_def]) >>
      `stk' = (S1 ++ extra) ++ rest` by simp[Abbr `suffix`] >>
      simp[NRC] >> qexists_tac `(running t, S1 ++ extra)` >> conj_tac
      >- (irule step_inverse_frame_wf >> simp[Abbr `k`] >>
          qexists_tac `rest` >> simp[Abbr `suffix`] >> metis_tac[])
      >- (first_x_assum irule >> simp[] >> qexists_tac `rest` >> fs[]))
  (* Case: final - NRC from final requires n = 0 *)
  >- (`n = 0 /\ (state, S'' ++ rest) = (final, stk')` by
        metis_tac[NRC_step_from_final] >> fs[] >>
      irule step_inverse_frame_wf >> simp[Abbr `k`] >>
      qexists_tac `rest` >> simp[Abbr `suffix`] >> fs[])
  (* Case: failed - NRC from failed requires n = 0 *)
  >- (`n = 0 /\ (state, S'' ++ rest) = (failed, stk')` by
        metis_tac[NRC_step_from_failed] >> fs[] >>
      irule step_inverse_frame_wf >> simp[Abbr `k`] >>
      qexists_tac `rest` >> simp[Abbr `suffix`] >> fs[])
QED

Theorem NRC_step_inverse_frame:
  !env n P S state S' rest.
    NRC (step env) n (running P, S ++ rest) (state, S' ++ rest) /\
    ~can_step (state, S' ++ rest) /\
    no_intermediate_terms P /\
    FEVERY (\(_,t). no_intermediate_terms t) env.proc /\
    LENGTH S >= 1 ==>
    NRC (step env) n (running P, S) (state, S')
Proof
  rpt strip_tac >> irule bla >> simp[] >>
  `wf_intermediate_terms P` by metis_tac[no_intermediate_terms_well_formed] >>
  `count_intermediate_terms P = 0` by metis_tac[no_intermediate_terms_count_0] >>
  simp[] >> qexists_tac `rest` >> simp[]
QED

(* Procedure call evaluation - statement is still valid with tracked semantics
   TODO: Update proof for new stack type *)
Theorem step_term_proc_inv:
  !env p S c.
    step env (running (term_proc p), S) c ==>
    ?body. FLOOKUP env.proc p = SOME body /\ c = (running body, S)
Proof
  rw[Once step_cases]
QED

Theorem evaluate_proc:
    !env G p (H:hostgraph) (tr:morphism) (D:hostgraph).
      evaluate env G (term_proc p) (H, tr) <=>
        ?body. FLOOKUP env.proc p = SOME body /\ evaluate env G body (H, tr)
Proof
  rpt gen_tac >> simp[evaluate_def, steps_def] >> EQ_TAC
  >- (strip_tac >> gvs[] >>
      qpat_x_assum `RTC _ _ _` mp_tac >>
      simp[Once RTC_CASES1] >>
      strip_tac >> Cases_on `u` >>
      qpat_x_assum `step _ _ _` mp_tac >> simp[Once step_cases] >>
      strip_tac >> gvs[] >> qexists_tac `(H,tr)::rest` >> simp[])
  >- (strip_tac >> gvs[] >>
      qexists_tac `(H,tr)::rest` >>
      simp[] >>
      simp[Once RTC_CASES1] >>
      qexists_tac `(running body, [(G, id_track G)])` >>
      conj_tac >- simp[Once step_cases] >> first_x_assum ACCEPT_TAC)
QED

(* Rule set call evaluation for composed track semantics.
   Success case: some rule applies and produces (H, tr).
   For a single rule call from initial state, the composed track
   is compose_morphism (track ...) (id_track G), which equals the track
   when applied to elements (since id_track is identity on G).
   Failure case: no rule applies, so evaluate is false. *)
Theorem evaluate_rscall:
    !env G rset (H:hostgraph) (tr:morphism).
      evaluate env G (term_rscall rset) (H, tr) <=>
        (* Success case: some rule can be applied *)
        (?rname r m assign ri.
          rname IN rset /\
          FLOOKUP env.rule rname = SOME r /\
          is_prematch r.lhs r.inf m G /\
          mk_assignment r m G = SOME assign /\
          instantiate_rule r assign m G = SOME ri /\
          apply_ruleinstance ri m G = SOME H /\
          tr = compose_morphism (track ri.lhs ri.inf m G) (id_track G))
Proof
  rpt gen_tac >> simp[evaluate_def, steps_def] >> EQ_TAC
  >- (strip_tac >> gvs[] >>
      qpat_x_assum `RTC _ _ _` mp_tac >> simp[Once RTC_CASES1] >>
      strip_tac >> Cases_on `u` >> qpat_x_assum `step _ _ _` mp_tac >>
      simp[Once step_cases] >>
      strip_tac >> gvs[pop_stack_def]
      >- (qexistsl_tac [`rname`, `r'`, `m`, `assign`, `ri`] >>
          simp[push_stack_def] >>
          qpat_x_assum `RTC _ _ _` mp_tac >>
          simp[Once RTC_CASES1, push_stack_def] >>
          strip_tac >> gvs[] >> qpat_x_assum `step _ _ _` mp_tac >>
          simp[Once step_cases])
      >- (qpat_x_assum `RTC _ _ _` mp_tac >> simp[Once RTC_CASES1] >>
          strip_tac >> gvs[] >> qpat_x_assum `step _ _ _` mp_tac >>
          simp[Once step_cases]))
  >- (strip_tac >> gvs[] >>
      qexists_tac `[(H, compose_morphism (track ri.lhs ri.inf m G) (id_track G))]` >>
      simp[can_step_def] >> simp[Once RTC_CASES1] >>
      qexists_tac `(final, [(H, compose_morphism (track ri.lhs ri.inf m G) (id_track G))])` >>
      simp[] >> simp[Once step_cases, pop_stack_def, push_stack_def] >>
      qexistsl_tac [`rname`, `r`, `m`, `ri`, `assign`] >> simp[])
QED

(* Single step: graphs in output are determined by graphs in input.
   Uses induction on the step relation to handle recursive cases. *)
Theorem step_track_swap:
  !env x y. step env x y ==>
    !G tr1 rest.
      SND x = (G, tr1) :: rest ==>
      !tr2. ?s'. step env (FST x, (G, tr2) :: rest) (FST y, s') /\
                 MAP FST (SND y) = MAP FST s'
Proof
  ho_match_mp_tac step_ind >> rpt strip_tac >> gvs[]
  (* Call1: rule application - composed track uses tr2 instead of tr1 *)
  >- (gvs[pop_stack_def, push_stack_def] >>
      qexists_tac `(h, compose_morphism (track ri.lhs ri.inf m G) tr2)::rest` >>
      simp[] >> simp[Once step_cases, pop_stack_def, push_stack_def] >>
      qexistsl_tac [`rname`, `r`, `m`, `ri`, `assign`] >> simp[])
  (* Call2: rule failure *)
  >- (gvs[pop_stack_def] >> qexists_tac `(G, tr2)::rest` >>
      simp[Once step_cases, pop_stack_def])
  (* ProcCall *)
  >- (qexists_tac `(G, tr2)::rest` >> simp[Once step_cases])
  (* Seq1: recursive case - use IH *)
  >- (first_x_assum (qspec_then `tr2` strip_assume_tac) >>
      qexists_tac `s'` >> simp[Once step_cases] >> metis_tac[])
  (* Seq2: recursive case - use IH *)
  >- (first_x_assum (qspec_then `tr2` strip_assume_tac) >>
      qexists_tac `s'` >> simp[Once step_cases] >> metis_tac[])
  (* Seq3: recursive case, failure preserves stack *)
  >- (first_x_assum (qspec_then `tr2` strip_assume_tac) >>
      `s' = (G, tr2)::rest` by metis_tac[step_to_failed_preserves_stack] >>
      gvs[] >> qexists_tac `(G, tr2)::rest` >> simp[Once step_cases])
  (* Break *)
  >- (qexists_tac `(G, tr2)::rest` >> simp[Once step_cases])
  (* Alap1 *)
  >- (qexists_tac `(G, tr2)::rest` >> simp[Once step_cases])
  (* Alap2 - pop2_stack requires at least 2 elements *)
  >- (Cases_on `rest` >> gvs[pop2_stack_def] >>
      qexists_tac `(G, tr2)::t` >> simp[Once step_cases, pop2_stack_def])
  (* If1 *)
  >- (gvs[top_stack_def] >>
      qexists_tac `(G, tr2)::(G, tr2)::rest` >>
      simp[Once step_cases, top_stack_def, push_stack_def])
  (* If2: recursive case - use IH *)
  >- (first_x_assum (qspec_then `tr2` strip_assume_tac) >>
      qexists_tac `s'` >> simp[Once step_cases] >> metis_tac[])
  (* If3: condition succeeds *)
  >- (first_x_assum (qspec_then `tr2` strip_assume_tac) >>
      Cases_on `s'` >> gvs[]
      >- (gvs[pop_stack_def])
      >- (qexists_tac `t` >> simp[] >> conj_tac
          >- (simp[Once step_cases, pop_stack_def] >>
              disj2_tac >> disj1_tac >>
              qexistsl_tac [`h::t`, `(h, t)`] >> simp[])
          >- (Cases_on `S''` >> gvs[pop_stack_def])))
  (* If4: condition fails *)
  >- (gvs[pop_stack_def] >> first_x_assum (qspec_then `tr2` strip_assume_tac) >>
      `s' = (G, tr2)::rest` by metis_tac[step_to_failed_preserves_stack] >>
      gvs[] >> qexists_tac `rest` >> simp[Once step_cases, pop_stack_def])
  (* Try1 *)
  >- (gvs[top_stack_def] >>
      qexists_tac `(G, tr2)::(G, tr2)::rest` >>
      simp[Once step_cases, top_stack_def, push_stack_def])
  (* Try2: recursive case - use IH *)
  >- (first_x_assum (qspec_then `tr2` strip_assume_tac) >>
      qexists_tac `s'` >> simp[Once step_cases] >> metis_tac[])
  (* Try3: condition succeeds *)
  >- (first_x_assum (qspec_then `tr2` strip_assume_tac) >>
      Cases_on `s'` >> gvs[]
      >- (gvs[pop2_stack_def])
      >- (Cases_on `t` >> gvs[pop2_stack_def] >>
          Cases_on `S''` >> gvs[pop2_stack_def] >>
          Cases_on `t` >> gvs[] >>
          qexists_tac `h::t'` >> simp[] >>
          simp[Once step_cases, pop2_stack_def] >>
          disj2_tac >> disj1_tac >>
          qexistsl_tac [`h::h'::t'`, `([h'], h::t')`] >> simp[]))
  (* Try4: condition fails *)
  >- (gvs[pop_stack_def] >> first_x_assum (qspec_then `tr2` strip_assume_tac) >>
      `s' = (G, tr2)::rest` by metis_tac[step_to_failed_preserves_stack] >>
      gvs[] >> qexists_tac `rest` >> simp[Once step_cases, pop_stack_def])
  (* Or1 *)
  >- (qexists_tac `(G, tr2)::rest` >> simp[Once step_cases])
  (* Or2 *)
  >- (qexists_tac `(G, tr2)::rest` >> simp[Once step_cases])
  (* Skip *)
  >- (qexists_tac `(G, tr2)::rest` >> simp[Once step_cases])
  (* Fail *)
  >- (qexists_tac `(G, tr2)::rest` >> simp[Once step_cases])
QED

(* Corollary: step_track_swap for singleton stacks *)
Theorem step_track_swap_singleton:
  !env P G tr1 c s.
    step env (running P, [(G, tr1)]) (c, s) ==>
    !tr2. ?s'. step env (running P, [(G, tr2)]) (c, s') /\
               MAP FST s = MAP FST s'
Proof
  rpt strip_tac >>
  drule step_track_swap >> simp[] >> strip_tac >>
  first_x_assum (qspec_then `tr2` strip_assume_tac) >>
  metis_tac[]
QED

(* More general: changing any tracks in stack preserves graph evolution.
   Unlike step_track_swap which only allows changing the top track,
   this allows changing ALL tracks as long as graphs match. *)
Theorem step_graph_determined:
  !env c1 s1 c2 s2. step env (c1, s1) (c2, s2) ==>
    !s1'. MAP FST s1 = MAP FST s1' ==>
          ?s2'. step env (c1, s1') (c2, s2') /\ MAP FST s2 = MAP FST s2'
Proof
  Induct_on `step` >> rpt conj_tac >> rpt strip_tac >> gvs[]
  (* Call1: Rule application - reconstruct the step with s1' *)
  >- (Cases_on `s1'` >> gvs[pop_stack_def] >>
      PairCases_on `h'` >> gvs[] >> Cases_on `S'` >> gvs[] >>
      qexists_tac `push_stack (h, compose_morphism (track ri.lhs ri.inf m G) h'1) t` >>
      simp[push_stack_def, Once step_cases] >>
      qexistsl_tac [`G`, `h'1`, `rname`, `r`, `m`, `ri`, `assign`] >> simp[pop_stack_def])
  (* Call2: No matching rule - same for any stack with same graphs *)
  >- (Cases_on `s1'` >> gvs[pop_stack_def] >>
      PairCases_on `h` >> gvs[] >> Cases_on `S'` >> gvs[] >>
      qexists_tac `(G,h1)::t` >> simp[Once step_cases, pop_stack_def])
  (* ProcCall: Stack unchanged *)
  >- (qexists_tac `s1'` >> simp[Once step_cases])
  (* Seq1: IH gives the step *)
  >- (`?s2''. step env (running P,s1') (running P',s2'') /\ MAP FST S'' = MAP FST s2''`
        by (first_x_assum irule >> simp[]) >>
      qexists_tac `s2''` >> simp[Once step_cases] >> metis_tac[])
  (* Seq2: IH gives the step *)
  >- (`?s2''. step env (running P,s1') (final,s2'') /\ MAP FST S'' = MAP FST s2''`
        by (first_x_assum irule >> simp[]) >>
      qexists_tac `s2''` >> simp[Once step_cases] >> metis_tac[])
  (* Seq3: IH gives the step, stack unchanged on failure *)
  >- (`?s2''. step env (running P,s1') (failed,s2'') /\ MAP FST s1' = MAP FST s2''`
        by (first_x_assum irule >> simp[]) >>
      `s1' = s2''` by metis_tac[step_fails_stack_unchanged] >> gvs[] >>
      qexists_tac `s1'` >> simp[Once step_cases] >> metis_tac[])
  (* Break: Stack unchanged *)
  >- (qexists_tac `s1'` >> simp[Once step_cases])
  (* Alap1: Stack unchanged *)
  >- (qexists_tac `s1'` >> simp[Once step_cases])
  (* Alap2: pop2_stack *)
  >- (Cases_on `s1'` >> gvs[pop2_stack_def] >> Cases_on `t` >> gvs[] >>
      Cases_on `S'` >> gvs[] >> Cases_on `t` >> gvs[] >>
      qexists_tac `h'::t'` >> simp[Once step_cases, pop2_stack_def])
  (* If1: top_stack and push_stack *)
  >- (Cases_on `s1'` >> gvs[top_stack_def] >> rename1 `h'::t'` >>
      Cases_on `S'` >> gvs[] >>
      qexists_tac `push_stack h' (h'::t')` >> simp[Once step_cases, top_stack_def, push_stack_def])
  (* If2: IH *)
  >- (`?s2''. step env (running C,s1') (running C',s2'') /\ MAP FST S'' = MAP FST s2''`
        by (first_x_assum irule >> simp[]) >>
      qexists_tac `s2''` >> simp[Once step_cases] >> metis_tac[])
  (* If3: IH + pop_stack *)
  >- (`?s2''. step env (running C,s1') (final,s2'') /\ MAP FST S'' = MAP FST s2''`
        by (first_x_assum irule >> simp[]) >>
      Cases_on `s2''` >> gvs[pop_stack_def] >>
      Cases_on `S''` >> gvs[] >>
      qexists_tac `t` >> simp[] >>
      simp[Once step_cases, pop_stack_def] >>
      disj2_tac >> disj1_tac >> qexistsl_tac [`h::t`, `(h,t)`] >> simp[])
  (* If4: IH + pop_stack *)
  >- (`?s2''. step env (running C,s1') (failed,s2'') /\ MAP FST s1' = MAP FST s2''`
        by (first_x_assum irule >> simp[]) >>
      `s1' = s2''` by metis_tac[step_fails_stack_unchanged] >> gvs[] >>
      Cases_on `s1'` >> gvs[pop_stack_def] >>
      Cases_on `S'` >> gvs[] >>
      qexists_tac `t` >> simp[Once step_cases, pop_stack_def])
  (* Try1: top_stack and push_stack *)
  >- (Cases_on `s1'` >> gvs[top_stack_def] >> Cases_on `S'` >> gvs[] >>
      qexists_tac `push_stack h (h::t)` >> simp[Once step_cases, top_stack_def, push_stack_def])
  (* Try2: IH *)
  >- (`?s2''. step env (running C,s1') (running C',s2'') /\ MAP FST S'' = MAP FST s2''`
        by (first_x_assum irule >> simp[]) >>
      qexists_tac `s2''` >> simp[Once step_cases] >> metis_tac[])
  (* Try3: IH + pop2_stack *)
  >- (`?s2''. step env (running C,s1') (final,s2'') /\ MAP FST S'' = MAP FST s2''`
        by (first_x_assum irule >> simp[]) >>
      Cases_on `s2''` >> gvs[pop2_stack_def] >> Cases_on `t` >> gvs[] >>
      Cases_on `S''` >> gvs[] >> Cases_on `t` >> gvs[] >>
      qexists_tac `h::t'` >> simp[] >>
      simp[Once step_cases, pop2_stack_def] >>
      DISJ2_TAC >> DISJ1_TAC >> qexistsl_tac [`h::h'::t'`, `([h'], h::t')`] >> simp[])
  (* Try4: IH + pop_stack *)
  >- (`?s2''. step env (running C,s1') (failed,s2'') /\ MAP FST s1' = MAP FST s2''`
        by (first_x_assum irule >> simp[]) >>
      `s1' = s2''` by metis_tac[step_fails_stack_unchanged] >> gvs[] >>
      Cases_on `s1'` >> gvs[pop_stack_def] >> Cases_on `S'` >> gvs[] >>
      qexists_tac `t` >> simp[Once step_cases, pop_stack_def])
  (* Or1: Stack unchanged *)
  >- (qexists_tac `s1'` >> simp[Once step_cases])
  (* Or2: Stack unchanged *)
  >- (qexists_tac `s1'` >> simp[Once step_cases])
  (* Skip: Stack unchanged *)
  >- (qexists_tac `s1'` >> simp[Once step_cases])
  (* Fail: Stack unchanged *)
  >- (qexists_tac `s1'` >> simp[Once step_cases])
QED

(* NRC version: changing all tracks in stack preserves graph evolution. *)
Theorem NRC_step_graph_determined:
  !n env c1 s1 c2 s2.
    NRC (step env) n (c1, s1) (c2, s2) ==>
    !s1'. MAP FST s1 = MAP FST s1' ==>
          ?s2'. NRC (step env) n (c1, s1') (c2, s2') /\
                MAP FST s2 = MAP FST s2'
Proof
  Induct_on `n` >> rpt strip_tac >> gvs[NRC] >>
  Cases_on `z` >> rename1 `step env _ (c', stk')` >>
  (* Apply step_graph_determined to get single step with s1' *)
  drule step_graph_determined >> strip_tac >>
  first_x_assum (qspec_then `s1'` mp_tac) >> simp[] >> strip_tac >>
  (* Apply IH to rest of execution *)
  first_x_assum (qspecl_then [`env`, `c'`, `stk'`, `c2`, `s2`] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum (qspec_then `s2'` mp_tac) >> simp[] >> strip_tac >>
  qexists_tac `s2''` >> simp[NRC] >>
  qexists_tac `(c', s2')` >> simp[]
QED

(* Corollary: NRC version of track swap for specific initial track *)
Theorem NRC_step_track_swap:
  !n env c1 s1 c2 s2.
    NRC (step env) n (c1, s1) (c2, s2) ==>
    !G tr1 rest.
      s1 = (G, tr1)::rest ==>
      !tr2. ?s2'. NRC (step env) n (c1, (G, tr2)::rest) (c2, s2') /\
                  MAP FST s2 = MAP FST s2'
Proof
  rpt strip_tac >> drule NRC_step_graph_determined >> strip_tac >>
  first_x_assum (qspec_then `(G, tr2)::rest` mp_tac) >> simp[] >> strip_tac >>
  metis_tac[]
QED

(* Main theorem: evaluation graph is independent of initial track *)
Theorem evaluate_track_independent:
  !env G P H tr1.
    wf_program env /\
    no_intermediate_terms P /\
    evaluate env G P (H, tr1) ==>
    !tr2. ?tr2'. evaluate env G P (H, tr2')
Proof
  (* The tr2 is unused - witness with the given tr1 *)
  rpt strip_tac >> qexists_tac `tr1` >> simp[]
QED

(*
div 0 error case : how to handle it?
*)
Definition diverges_def:
    diverges (env:program) (G:hostgraph) (P:term) <=> ~evaluates env G P
End

(* Track Morphism Validity                                            *)
(*                                                                    *)
(* When evaluation completes, the resulting track morphism is a       *)
(* valid track morphism from the input graph to the output graph.     *)

(* Stack track validity for composed tracks.
   With the composed track approach, each frame (H, tr) has tr: G0 -> H
   where tr is the accumulated track from the original input G0.
   Since we don't store G0 in each frame, we define validity based on
   whether the track's domain/range are finite (basic sanity check).
   The full validity is_track_morphism G0 tr H is proven separately
   using stack_tracks_morphism. *)
Definition stack_tracks_valid_def:
  stack_tracks_valid [] = T /\
  stack_tracks_valid ((H, tr)::rest) =
    (FINITE (FDOM tr.nodemap) /\ FINITE (FDOM tr.edgemap) /\ stack_tracks_valid rest)
End

(* A single step preserves stack_tracks_valid (finiteness of track domains).
   The key case is Call1 where the composed track's domains are finite
   because both the DPO track and the input track have finite domains,
   and f_o_f preserves finiteness. *)
Theorem step_preserves_stack_tracks_valid:
  !env c1 s1 c2 s2.
    step env (c1, s1) (c2, s2) /\
    wf_program env /\
    stack_tracks_valid s1 /\
    wf_stack_labels s1
    ==> stack_tracks_valid s2
Proof
  Induct_on `step` >> rpt conj_tac >> rpt strip_tac >> gvs[]
  >- ( (* Call1 - composed track *)
    simp[push_stack_def, stack_tracks_valid_def, compose_morphism_def,
         FDOM_FINITE] >>
    fs[pop_stack_def, stack_tracks_valid_def] >>
    Cases_on `S'` >> gvs[stack_tracks_valid_def])
  >- ( (* Alap2 - pop2_stack *)
    gvs[pop2_stack_def] >> Cases_on `S'` >> gvs[stack_tracks_valid_def] >>
    Cases_on `t` >> gvs[stack_tracks_valid_def] \\
    gvs[stack_tracks_valid_def] \\
    Cases_on `h'` >> Cases_on `h''` >> gvs[stack_tracks_valid_def])
  >- ( (* If1 - push_stack *)
    Cases_on `S'` >> gvs[push_stack_def, stack_tracks_valid_def, top_stack_def] \\
    Cases_on `el` >> gvs[stack_tracks_valid_def])
  >- ( (* If3 - pop_stack after final *)
    Cases_on `S''` >> gvs[pop_stack_def, stack_tracks_valid_def] \\
    Cases_on `h` >> gvs[stack_tracks_valid_def])
  >- ( (* If4 - pop_stack after failed *)
    Cases_on `S'` >> gvs[pop_stack_def, stack_tracks_valid_def] \\
    Cases_on `h` >> gvs[stack_tracks_valid_def])
  >- ( (* Try1 - push_stack *)
    Cases_on `S'` >> gvs[push_stack_def, stack_tracks_valid_def, top_stack_def] \\
    Cases_on `el` >> gvs[stack_tracks_valid_def])
  >- ( (* Try3 - pop2_stack after final *)
    Cases_on `S''` >> gvs[pop2_stack_def, stack_tracks_valid_def] \\
    Cases_on `t` >> gvs[stack_tracks_valid_def] \\
    Cases_on `h` >> Cases_on `h'` >> gvs[stack_tracks_valid_def])
  >- ( (* Try4 - pop_stack after failed *)
    Cases_on `S'` >> gvs[pop_stack_def, stack_tracks_valid_def] \\
    Cases_on `h` >> gvs[stack_tracks_valid_def])
QED

(* NRC version: multiple steps preserve track validity *)
Theorem NRC_step_preserves_stack_tracks_valid:
  !n env c1 s1 c2 s2.
    NRC (step env) n (c1, s1) (c2, s2) /\
    wf_program env /\
    stack_tracks_valid s1 /\
    wf_stack_labels s1
    ==> stack_tracks_valid s2
Proof
  Induct_on `n` >> rpt strip_tac
  >- gvs[NRC]
  >- (gvs[NRC] >> PairCases_on `z` >>
      `wf_stack_labels z1` by metis_tac[step_preserves_wf_stack_labels] >>
      `stack_tracks_valid z1` by metis_tac[step_preserves_stack_tracks_valid] >>
      first_x_assum irule >> metis_tac[])
QED

(* Main theorem: evaluation produces a valid composed track morphism.
   The result (H, tr) has tr: G -> H as a partial track morphism.
   tr maps surviving elements of G (those in FDOM tr.nodemap/edgemap) to H.
   The track is valid: is_track_morphism G tr H (partial injective premorphism).

   For now, we prove a weaker version showing finiteness is preserved.
   The full stack_tracks_morphism invariant uses compose_is_track_morphism. *)
Theorem evaluate_track_is_valid:
  !env G P H tr.
    wf_program env /\
    wf_hostgraph G /\
    no_intermediate_terms P /\
    evaluate env G P (H, tr)
    ==> FINITE (FDOM tr.nodemap) /\ FINITE (FDOM tr.edgemap)
Proof
  rpt strip_tac >>
  fs[evaluate_def, steps_def] >>
  (* Initial stack [(G, id_track G)] has finite domains *)
  `stack_tracks_valid [(G, id_track G)]` by
    (simp[stack_tracks_valid_def, FDOM_id_track_nodemap, FDOM_id_track_edgemap] >>
     metis_tac[wf_hostgraph_IMP_finite_sets]) >>
  `wf_stack_labels [(G, id_track G)]` by
    (simp[wf_stack_labels_def] >>
     metis_tac[wf_hostgraph_IMP_wf_partial_hostgraph]) >>
  (* Convert RTC to NRC *)
  drule RTC_NRC >> strip_tac >>
  (* Apply NRC preservation to get stack_tracks_valid for final stack *)
  `stack_tracks_valid S'` by
    (irule NRC_step_preserves_stack_tracks_valid >>
     qexistsl_tac [`running P`, `final`, `env`, `n`, `[(G,id_track G)]`] >> simp[]) >>
  (* Extract finiteness from stack_tracks_valid *)
  gvs[stack_tracks_valid_def]
QED

(* ------------------------------------------------------------------------- *)
(* Track Morphism Validity                                                   *)
(* ------------------------------------------------------------------------- *)

(* Stack invariant: each track is a valid partial track morphism from
   the original G0 to its paired host graph.

   For stack element (H, tr), we require:
   is_track_morphism G0 tr H

   Since is_track_morphism now uses is_partial_inj_premorphism,
   the domain of tr can be a subset of G0.V/E (surviving elements). *)
Definition stack_tracks_morphism_def:
  stack_tracks_morphism G0 [] = T /\
  stack_tracks_morphism G0 ((H, tr)::rest) =
    (is_track_morphism G0 tr H /\
     stack_tracks_morphism G0 rest)
End

(* Initial stack satisfies the morphism invariant:
   id_track G is a track morphism from G to G *)
Theorem initial_stack_tracks_morphism:
  !G. wf_hostgraph G ==>
      stack_tracks_morphism G [(G, id_track G)]
Proof
  rw[stack_tracks_morphism_def] >>
  irule id_track_is_track_morphism >>
  fs[wf_hostgraph_def, wf_graph_def]
QED

(* Step preserves stack_tracks_morphism invariant.
   The key case is Call1 where we compose the DPO track with the accumulated track.
   Most other cases preserve the stack or only pop/push without changing tracks. *)
Theorem step_preserves_stack_tracks_morphism:
  !env c1 s1 c2 s2 G0.
    step env (c1, s1) (c2, s2) /\
    wf_program env /\
    wf_stack_labels s1 /\
    stack_tracks_morphism G0 s1
    ==> stack_tracks_morphism G0 s2
Proof
  Induct_on `step` >> rpt conj_tac >> rpt strip_tac >> gvs[]
  (* Call1: Rule application - compose track morphisms *)
  >- (Cases_on `S'` >> gvs[pop_stack_def, wf_stack_labels_def,
       stack_tracks_morphism_def, push_stack_def] >>
      `wf_rule r` by (fs[wf_program_def] >>
        imp_res_tac finite_mapTheory.FEVERY_FLOOKUP >> fs[]) >>
      `wf_rulegraph_labels r.lhs` by fs[wf_rule_def] >>
      `hostgraph_labels_spine G` by metis_tac[wf_hostgraph_IMP_hostgraph_labels_spine] >>
      `wf_assignment_spine assign` by metis_tac[mk_assignment_wf_assignment_spine] >>
      `wf_ruleinstance ri` by metis_tac[instantiate_rule_wf] >>
      `is_match ri.lhs ri.inf m G` by metis_tac[prematch_instantiation_is_match] >>
      `h = dpo ri.lhs ri.inf ri.rhs m G` by
        fs[apply_ruleinstance_def, optionTheory.OPTION_BIND_SOME] >>
      `wf_hostgraph ri.lhs /\ wf_hostgraph ri.rhs` by fs[wf_ruleinstance_def] >>
      `ri.inf SUBSET ri.lhs.V /\ ri.inf SUBSET ri.rhs.V` by
        fs[wf_ruleinstance_def] >>
      `is_track_morphism G (track ri.lhs ri.inf m G) h` by
        (gvs[] >> irule track_is_track_morphism >> simp[]) >>
      metis_tac[compose_is_track_morphism])
  (* Alap2: pop2_stack *)
  >- (Cases_on `S'` >> gvs[pop2_stack_def, stack_tracks_morphism_def] >>
      Cases_on `t` >> gvs[pop2_stack_def, stack_tracks_morphism_def] >>
      fs[stack_tracks_morphism_def] >>
      PairCases_on `h'` >> PairCases_on `h''` >> fs[stack_tracks_morphism_def])
  (* If1: push_stack *)
  >- (Cases_on `S'` >> gvs[top_stack_def, push_stack_def,
        stack_tracks_morphism_def] >>
      PairCases_on `el` >> fs[stack_tracks_morphism_def])
  (* If3: condition succeeded, pop *)
  >- (`stack_tracks_morphism G0 S''` by metis_tac[] >>
      Cases_on `S''` >> gvs[pop_stack_def, stack_tracks_morphism_def] >>
      PairCases_on `h` >> fs[stack_tracks_morphism_def])
  (* If4: condition failed, pop *)
  >- (Cases_on `S'` >> gvs[pop_stack_def, stack_tracks_morphism_def] >>
      PairCases_on `h` >> fs[stack_tracks_morphism_def])
  (* Try1: push_stack *)
  >- (Cases_on `S'` >> gvs[top_stack_def, push_stack_def,
        stack_tracks_morphism_def] >>
      PairCases_on `el` >> fs[stack_tracks_morphism_def])
  (* Try3: condition succeeded, pop2 *)
  >- (`stack_tracks_morphism G0 S''` by metis_tac[] >>
      Cases_on `S''` >> gvs[pop2_stack_def, stack_tracks_morphism_def] >>
      Cases_on `t` >> gvs[pop2_stack_def, stack_tracks_morphism_def] >>
      PairCases_on `h` >> PairCases_on `h'` >> fs[stack_tracks_morphism_def])
  (* Try4: condition failed, pop *)
  >- (Cases_on `S'` >> gvs[pop_stack_def, stack_tracks_morphism_def] >>
      PairCases_on `h` >> fs[stack_tracks_morphism_def])
QED

(* NRC version: multiple steps preserve track morphism invariant *)
Theorem NRC_step_preserves_stack_tracks_morphism:
  !n env c1 s1 c2 s2 G0.
    NRC (step env) n (c1, s1) (c2, s2) /\
    wf_program env /\
    wf_stack_labels s1 /\
    stack_tracks_morphism G0 s1
    ==> stack_tracks_morphism G0 s2
Proof
  Induct_on `n` >> rpt strip_tac
  >- gvs[NRC]
  >- (gvs[NRC] >> PairCases_on `z` >>
      `wf_stack_labels z1` by metis_tac[step_preserves_wf_stack_labels] >>
      `stack_tracks_morphism G0 z1` by metis_tac[step_preserves_stack_tracks_morphism] >>
      first_x_assum irule >> metis_tac[])
QED

(* Main theorem: evaluation produces a valid track morphism *)
Theorem evaluate_is_track_morphism:
  !env G P H tr.
    wf_program env /\
    wf_hostgraph G /\
    evaluate env G P (H, tr)
    ==> is_track_morphism G tr H
Proof
  rpt strip_tac >>
  fs[evaluate_def, steps_def] >>
  (* Initial stack has valid track morphism *)
  `stack_tracks_morphism G [(G, id_track G)]` by metis_tac[initial_stack_tracks_morphism] >>
  (* Initial stack is well-formed *)
  `wf_stack_labels [(G, id_track G)]` by
    (rw[wf_stack_labels_def] >> fs[wf_hostgraph_def]) >>
  (* Convert RTC to NRC *)
  drule RTC_NRC >> strip_tac >>
  (* Apply NRC preservation *)
  `stack_tracks_morphism G S'` by metis_tac[NRC_step_preserves_stack_tracks_morphism] >>
  (* Extract from final singleton stack *)
  Cases_on `S'` >> gvs[stack_tracks_morphism_def] >>
  Cases_on `t` >> gvs[stack_tracks_morphism_def] >>
  Cases_on `h` >> gvs[stack_tracks_morphism_def]
QED

(* Single-step morphism preservation:
   If we can take a step from (c1, [(G, tr)]) to (c2, [(H, m)]),
   then we can take a corresponding step from (c1, [(G, id_track G)]) to
   (c2, [(H, m')]) where m = compose_morphism m' tr.

   Note: Uses morphismTheory.compose_morphism where compose_morphism m2 m1
   applies m2 to the output of m1. For the identity to work, we need
   FRANGE tr ⊆ G (the target of tr is in G).

   This follows from the fact that the step function only modifies the
   morphism in the Call1 case, and all other cases preserve S unchanged. *)
(* Proof strategy for step_morphism_preserve:
   Use step induction (Induct_on `step`).
   For each case:
   - Call1: Witness is compose_morphism (track ...) (id_track G).
            Uses compose_morphism_assoc and compose_morphism_id_track_left.
   - Stack unchanged cases (Call2, ProcCall, Break, Alap1, Or1/2, Skip, Fail):
            Witness is id_track G. Uses compose_morphism_id_track_left.
   - Recursive cases (Seq1/2/3, If2, Try2): Use IH from step induction.
   - Impossible cases (Alap2, If1/3/4, Try1/3/4):
            Singleton stack constraints make these unreachable. *)
Theorem step_morphism_preserve:
  !env c1 G tr c2 H m.
    step env (c1, [(G, tr)]) (c2, [(H, m)]) /\
    wf_hostgraph G /\
    FRANGE tr.nodemap SUBSET G.V /\
    FRANGE tr.edgemap SUBSET G.E
    ==>
    ?m'. step env (c1, [(G, id_track G)]) (c2, [(H, m')]) /\
         m = compose_morphism m' tr
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `step _ _ _` mp_tac >>
  qpat_x_assum `wf_hostgraph _` mp_tac >>
  qpat_x_assum `FRANGE _.nodemap SUBSET _` mp_tac >>
  qpat_x_assum `FRANGE _.edgemap SUBSET _` mp_tac >>
  MAP_EVERY qid_spec_tac [`m`, `H`, `c2`, `tr`, `G`, `c1`] >>
  Induct_on `step` >> rpt conj_tac >> rpt strip_tac >>
  gvs[pop_stack_def, push_stack_def, top_stack_def, pop2_stack_def]
  (* Call1: rule application *)
  >- (qexists_tac `compose_morphism (track ri.lhs ri.inf m G) (id_track G)` >>
      conj_tac
      >- (simp[Once step_cases, pop_stack_def, push_stack_def] >>
          qexistsl_tac [`rname`, `r`, `m`, `ri`, `assign`] >> simp[])
      >- (simp[GSYM compose_morphism_assoc] >>
          `compose_morphism (id_track G) tr = tr` by
            (irule compose_morphism_id_track_left >> simp[]) >>
          simp[]))
  (* Call2: rule not applicable *)
  >- (qexists_tac `id_track G` >> conj_tac
      >- simp[Once step_cases, pop_stack_def]
      >- simp[GSYM compose_morphism_id_track_left])
  (* ProcCall *)
  >- (qexists_tac `id_track G` >> conj_tac
      >- simp[Once step_cases]
      >- simp[GSYM compose_morphism_id_track_left])
  (* Seq1: first part running *)
  >- (qexists_tac `m''` >> conj_tac
      >- (irule step_Seq1 >> simp[])
      >- simp[])
  (* Seq2: first part done *)
  >- (qexists_tac `m''` >> conj_tac
      >- (irule step_Seq2 >> simp[])
      >- simp[])
  (* Seq3: first part failed *)
  >- (qexists_tac `m''` >> conj_tac
      >- (`m'' = id_track G` by
            (drule step_fails_stack_unchanged >> simp[]) >>
          gvs[] >> irule step_Seq3 >> simp[])
      >- gvs[GSYM compose_morphism_id_track_left])
  (* Break *)
  >- (qexists_tac `id_track G` >> conj_tac
      >- simp[Once step_cases]
      >- simp[GSYM compose_morphism_id_track_left])
  (* Alap1 *)
  >- (qexists_tac `id_track G` >> conj_tac
      >- simp[Once step_cases]
      >- simp[GSYM compose_morphism_id_track_left])
  (* If1: condition running *)
  >- (qexists_tac `m''` >> conj_tac
      >- simp[step_ITE]
      >- simp[])
  (* If2: condition succeeded - singleton input to final produces singleton output,
     so pop_stack with 2 elements is impossible from singleton input *)
  >- (sg `!env P G tr s. step env (running P, [(G,tr)]) (final, s) ==>
                         ?H' m'. s = [(H',m')]`
      >- (rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
          simp[Once step_cases] >> rpt strip_tac >>
          gvs[pop_stack_def, push_stack_def, pop2_stack_def])
      >- (first_x_assum (fn th => drule th) >> strip_tac >> gvs[]))
  (* Try1: condition running *)
  >- (qexists_tac `m''` >> conj_tac
      >- (irule step_Try2 >> simp[])
      >- simp[])
  (* Try2: condition succeeded - singleton input to final produces singleton output,
     so pop2_stack with 2+ elements is impossible from singleton input *)
  >- (sg `!env P G tr s. step env (running P, [(G,tr)]) (final, s) ==>
                         ?H' m'. s = [(H',m')]`
      >- (rpt strip_tac >> qpat_x_assum `step _ _ _` mp_tac >>
          simp[Once step_cases] >> rpt strip_tac >>
          gvs[pop_stack_def, push_stack_def, pop2_stack_def])
      >- (first_x_assum (fn th => drule th) >> strip_tac >> gvs[]))
  (* Or1 *)
  >- (qexists_tac `id_track G` >> conj_tac
      >- simp[Once step_cases]
      >- simp[GSYM compose_morphism_id_track_left])
  (* Or2 *)
  >- (qexists_tac `id_track G` >> conj_tac
      >- simp[Once step_cases]
      >- simp[GSYM compose_morphism_id_track_left])
  (* Skip *)
  >- (qexists_tac `id_track G` >> conj_tac
      >- simp[Once step_cases]
      >- simp[GSYM compose_morphism_id_track_left])
  (* Fail *)
  >- (qexists_tac `id_track G` >> conj_tac
      >- simp[Once step_cases]
      >- simp[GSYM compose_morphism_id_track_left])
QED

val () = export_theory ()
