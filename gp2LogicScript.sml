open HolKernel boolLib bossLib
open arithmeticTheory programTheory stackTheory semTheory semPropsTheory hostgraphTheory morphismTheory
open finite_mapTheory pred_setTheory trackTheory graphTheory
(* Note: Do NOT open categoryTheoryExtTheory as it shadows morphismTheory.compose_morphism *)
(* Use categoryTheoryExtTheory.compose_morphism_assoc where needed *)

val () = new_theory "gp2Logic"

(* A predicate is iso-invariant if it's preserved under bijective morphisms *)
Definition iso_invariant_def:
  iso_invariant (P: hostgraph -> bool) <=>
    !G H m. is_bij_morphism G m H ==> (P G <=> P H)
End

(* Lift a graph predicate to ignore the morphism component.
   Used for intermediate predicates in sequential composition and loops. *)
Definition lift_def:
  lift (P: hostgraph -> bool) = \(G:hostgraph) (m:morphism). P G
End

(* WSPEC - Weakest Specification for GP2 programs.
   Requires:
   - Well-formed program (wf_program ensures procedures have no intermediate terms)
   - Well-formed rule labels (implied by wf_program via wf_rule)
   - The term itself has no intermediate terms (source program)

   This ensures stack invariants are maintained during execution,
   enabling compositional reasoning.

   NOTE: iso_invariant requirements removed - developer responsibility.
   NOTE: Updated for composed track semantics - stack elements are (hostgraph # morphism) pairs.
   NOTE: Postcondition Q has type hostgraph -> morphism -> bool, allowing access to
         the composed tracking morphism tr: G -> og from the initial graph G to the final graph og.
   NOTE: Uses steps to cover ALL terminal states, ensuring t always succeeds from P. *)
Definition WSPEC_def:
    WSPEC (env: program) (P:hostgraph -> bool) t (Q:hostgraph -> morphism -> bool) <=>
      wf_program env /\
      no_intermediate_terms t /\
      !G c. wf_hostgraph G /\ P G /\
            steps env (running t, [(G, id_track G)]) c /\ ~can_step c
        ==> ?og om. c = (final, [(og, om)]) /\ Q og om
End

Theorem WSPEC_wf_program:
  !env P t Q. WSPEC env P t Q ==> wf_program env
Proof
  rw[WSPEC_def]
QED

Theorem WSPEC_wf_program_rule_labels:
  !env P t Q. WSPEC env P t Q ==> wf_program_rule_labels env
Proof
  rw[WSPEC_def] >> metis_tac[wf_program_IMP_wf_program_rule_labels]
QED

Theorem WSPEC_no_intermediate:
  !env P t Q. WSPEC env P t Q ==> no_intermediate_terms t
Proof
  rw[WSPEC_def]
QED

Theorem wf_program_FEVERY:
  !env. wf_program env ==> FEVERY (\(_,t). no_intermediate_terms t) env.proc
Proof
  rw[wf_program_def] >>
  fs[finite_mapTheory.FEVERY_DEF] >> rpt strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[]
QED

Theorem WSPEC_consequence:
  !env P P' Q Q' t.
    (!s. P' s ==> P s) /\ (* Strengthen precondition *)
    (!s m. Q s m ==> Q' s m) /\ (* Weaken postcondition *)
    WSPEC env P t Q
    ==> WSPEC env P' t Q'
Proof
  rpt strip_tac >> fs[WSPEC_def] >> rpt strip_tac >>
  `P G` by metis_tac[] >>
  first_x_assum drule_all >> rpt strip_tac >> metis_tac[]
QED

Theorem WSPEC_skip:
  !env P.
    wf_program env ==>
    WSPEC env P term_skip (lift P)
Proof
  rw[WSPEC_def, no_intermediate_terms_def, lift_def] >> rpt strip_tac >>
  Cases_on `c` >> fs[steps_skip, can_step_def] >>
  gvs[can_step_def] >>
  qexists_tac `G` >> qexists_tac `id_track G` >> qexists_tac `G` >> gvs[]
QED


(* WSPEC_fail: term_fail always reaches failed state, never final.
   So WSPEC env P term_fail Q is FALSE when P is satisfiable. *)
Theorem WSPEC_fail:
  !env P Q.
    wf_program env /\
    (?s. wf_hostgraph s /\ P s) ==> ~WSPEC env P term_fail Q
Proof
  rpt strip_tac >> fs[WSPEC_def, no_intermediate_terms_def] >>
  first_x_assum (qspecl_then [`s`, `(failed, [(s, id_track s)])`] mp_tac) >>
  simp[steps_fail, can_step_def]
QED

(* Helper lemma: For terminated term_seq executions, the "running" intermediate
   case is eliminated. Either a reaches final (then b runs), or a fails/breaks. *)
Theorem steps_seq_terminal:
  !env n a b s c s'.
    NRC (step env) n (running (term_seq a b), s) (c, s') /\ ~can_step (c, s') ==>
    (?m. steps env (running a, s) (final, m) /\ steps env (running b, m) (c, s')) \/
    (steps env (running a, s) (failed, s') /\ c = failed) \/
    (steps env (running a, s) (running term_break, s') /\ c = running term_break)
Proof
  Induct_on `n` >> rpt strip_tac
  >- (gvs[arithmeticTheory.NRC] >> fs[can_step_def])
  >- (
    gvs[arithmeticTheory.NRC] >> fs[step_seq] >>
    qpat_x_assum `step env (running (term_seq a b), s) z` mp_tac >>
    simp[Once step_cases] >>
    strip_tac >> gvs[]
    >- (
      first_x_assum (qspecl_then [`env`, `P'`, `b`, `S'`, `c`, `s'`] mp_tac) >>
      simp[] >> strip_tac >> gvs[]
      >- (disj1_tac >> qexists_tac `m` >> simp[] >> metis_tac[steps_CASES1])
      >- (disj2_tac >> metis_tac[steps_CASES1])
      >- (disj2_tac >> metis_tac[steps_CASES1]))
    >- (
      disj1_tac >> qexists_tac `S'` >> conj_tac
      >- (irule steps_SINGLE >> simp[])
      >- (fs[steps_NRC] >> qexists_tac `n` >> simp[]))
    >- (
      drule NRC_step_from_failed >> strip_tac >> gvs[] >>
      disj2_tac >> irule steps_SINGLE >> simp[])
    >- (
      `c = running term_break /\ s' = s /\ n = 0` by (
        Cases_on `n` >> gvs[arithmeticTheory.NRC] >>
        `~step env (running term_break, s) z` by
          metis_tac[step_only_running, can_step_def]) >> gvs[] >>
      disj2_tac >> simp[steps_REFL]))
QED

(* can_step depends only on the state, not the stack *)
Theorem can_step_state_only:
  !c s s'. can_step (c, s) = can_step (c, s')
Proof
  Cases_on `c` >> TRY (Cases_on `t`) >> simp[can_step_def]
QED

(* Sequential composition rule for WSPEC.
   Uses evaluate_preserves_wf_hostgraph to show wf_hostgraph is preserved
   between t1 and t2, making the rule compositional.
   NOTE: All predicates (Q and R) are hostgraph -> bool, lifted for postconditions.
   The morphism tracking happens implicitly in the semantics. *)
Theorem WSPEC_seq:
  !env P Q R t1 t2.
    WSPEC env P t1 (lift Q) /\
    WSPEC env Q t2 (lift R)
    ==> WSPEC env P (term_seq t1 t2) (lift R)
Proof
  rpt strip_tac >>
  `wf_program env` by metis_tac[WSPEC_wf_program] >>
  rw[WSPEC_def, no_intermediate_terms_def, lift_def]
  >- metis_tac[WSPEC_no_intermediate]
  >- metis_tac[WSPEC_no_intermediate]
  >- (
    Cases_on `c` >> rename1 `steps _ _ (st, stk)` >>
    (* Convert steps to NRC form and apply steps_seq_terminal *)
    `?n. NRC (step env) n (running (term_seq t1 t2), [(G, id_track G)]) (st, stk)` by
      metis_tac[steps_NRC] >>
    drule steps_seq_terminal >> simp[can_step_def] >> strip_tac
    (* Case 1: final - t1 completes to final, then t2 runs *)
    >- (
      `FEVERY (\(_,t). no_intermediate_terms t) env.proc` by metis_tac[wf_program_FEVERY] >>
      `no_intermediate_terms t1` by metis_tac[WSPEC_no_intermediate] >>
      `?el. m = [el]` by (
        imp_res_tac steps_SINGLETON_STACK_FINAL >>
        fs[can_step_def]) >>
      gvs[] >>
      fs[WSPEC_def, lift_def] >>
      qpat_x_assum `!G' c. _ /\ P _ /\ steps _ _ c /\ _ ==> _`
        (qspecl_then [`G`, `(final, [el])`] mp_tac) >>
      simp[can_step_def] >> strip_tac >>
      (* Show evaluate env G t1 (FST el, SND el) to use preservation theorems *)
      `evaluate env G t1 (FST el, SND el)` by (
        fs[evaluate_def, can_step_def] >>
        qexists_tac `[el]` >> simp[] >>
        qexists_tac `[]` >> simp[]) >>
      (* Use evaluate_preserves_wf_hostgraph to show el is well-formed *)
      `wf_hostgraph (FST el)` by metis_tac[evaluate_preserves_wf_hostgraph] >>
      (* Use evaluate_preserves_hostgraph_labels_spine to show labels are well-formed *)
      `hostgraph_labels_spine (FST el)` by metis_tac[evaluate_preserves_hostgraph_labels_spine] >>
      (* Need to convert t2's execution to start from id_track *)
      qpat_x_assum `steps _ (running t2, _) _` mp_tac >>
      simp[steps_NRC] >> strip_tac >>
      drule NRC_step_graph_determined >> strip_tac >>
      pop_assum (qspec_then `[(FST el, id_track (FST el))]` mp_tac) >> simp[] >>
      strip_tac >>
      qpat_x_assum `!G' c. _ /\ Q _ /\ _ ==> _`
        (qspecl_then [`FST el`, `(st, s2')`] mp_tac) >>
      simp[can_step_state_only, steps_NRC] >>
      impl_tac
      >- (rpt conj_tac >> gvs[] >> TRY (qexists_tac `n'` >> simp[]) >>
          metis_tac[can_step_state_only])
      >> strip_tac >> gvs[] >>
      qexistsl_tac [`FST x0`, `SND x0`] >> simp[])
    (* Case 2: failed - contradicts WSPEC for t1 *)
    >- (
      fs[WSPEC_def, lift_def] >>
      qpat_x_assum `!G' c. _ /\ P _ /\ _ ==> _`
        (qspecl_then [`G`, `(failed, stk)`] mp_tac) >>
      simp[can_step_def])
    (* Case 3: break - contradicts WSPEC for t1 *)
    >- (
      fs[WSPEC_def, lift_def] >>
      qpat_x_assum `!G' c. _ /\ P _ /\ _ ==> _`
        (qspecl_then [`G`, `(running term_break, stk)`] mp_tac) >>
      simp[can_step_def]))
QED

Theorem WSPEC_or:
  !env P Q a b.
    WSPEC env P a Q /\
    WSPEC env P b Q
    ==> WSPEC env P (term_or a b) Q
Proof
  rw[WSPEC_def, no_intermediate_terms_def] >> rpt strip_tac >>
  Cases_on `c` >> fs[steps_or, can_step_def] >> gvs[can_step_def]
  >- (qpat_x_assum `!G c. _ /\ _ /\ steps _ (running a, _) _ /\ _ ==> _`
        (qspecl_then [`G`, `(q, r)`] mp_tac) >> simp[] >> metis_tac[])
  >- (qpat_x_assum `!G c. _ /\ _ /\ steps _ (running b, _) _ /\ _ ==> _`
        (qspecl_then [`G`, `(q, r)`] mp_tac) >> simp[] >> metis_tac[])
QED

Theorem WSPEC_proc:
  !env p P Q body.
    FLOOKUP env.proc p = SOME body /\
    WSPEC env P body Q
    ==> WSPEC env P (term_proc p) Q
Proof
  rw[WSPEC_def, no_intermediate_terms_def] >> rpt strip_tac >>
  qpat_x_assum `steps _ (running (term_proc _), _) _` mp_tac >>
  simp[steps_NRC] >> strip_tac >>
  Cases_on `n`
  >- gvs[arithmeticTheory.NRC, can_step_def]
  >- (
    fs[arithmeticTheory.NRC] >>
    qpat_x_assum `step env (running (term_proc p), _) z` mp_tac >>
    simp[Once step_cases] >> strip_tac >> gvs[] >>
    qpat_x_assum `!G c. _ /\ _ /\ steps _ _ c /\ _ ==> _`
      (qspecl_then [`G`, `c`] mp_tac) >>
    simp[steps_NRC] >> strip_tac >>
    qpat_x_assum `_ ==> ?og om. _` mp_tac >> impl_tac
    >- (qexists_tac `n'` >> simp[])
    >> simp[])
QED

(* WSPEC for rule set call - requires that some rule is always applicable
   when precondition holds (total correctness).
   With the new semantics, term_rscall can fail if no rule applies,
   so we need the applicability precondition to guarantee success.
   NOTE: Uses lift Q since we abstract over morphism tracking details. *)
Theorem WSPEC_rscall:
  !env rset P Q.
    wf_program env /\
    (* Postcondition: if a rule applies, Q holds on result graph *)
    (!s rname r m h.
      wf_hostgraph s /\ P s /\
      rname IN rset /\
      FLOOKUP env.rule rname = SOME r /\
      is_prematch r.lhs r.inf m s /\
      apply_rule r m s = SOME h
      ==> Q h) /\
    (* Applicability: precondition implies some rule can apply *)
    (!s. wf_hostgraph s /\ P s ==>
         ?rname r m h. rname IN rset /\ FLOOKUP env.rule rname = SOME r /\
                       is_prematch r.lhs r.inf m s /\ apply_rule r m s = SOME h)
    ==> WSPEC env P (term_rscall rset) (lift Q)
Proof
  rw[WSPEC_def, no_intermediate_terms_def, lift_def] >> rpt strip_tac >> fs[steps_NRC] >>
  Cases_on `n`
  >- gvs[arithmeticTheory.NRC, can_step_def]
  >- (
    gvs[arithmeticTheory.NRC] >>
    qpat_x_assum `step env (running (term_rscall rset), _) z` mp_tac >>
    simp[Once step_cases, pop_stack_def] >> strip_tac >> gvs[]
    >- (
      gvs[push_stack_def] >>
      Cases_on `n'`
      >- (
        gvs[arithmeticTheory.NRC] >>
        `apply_rule r m G = SOME h` by
          (simp[apply_rule_def] >> qexistsl_tac [`assign`, `ri`] >> simp[]) >>
        first_x_assum irule >> simp[] >>
        qexists_tac `m` >> qexists_tac `r` >> qexists_tac `rname` >> simp[] >>
        qexists_tac `G` >> simp[])
      >- (
        gvs[arithmeticTheory.NRC, can_step_def] >> fs[step_only_running_rewrs]))
    >- (
      first_x_assum (qspec_then `G` mp_tac) >> simp[] >> strip_tac >> metis_tac[]))
QED

Theorem WSPEC_conj_post:
  !env P Q1 Q2 t.
    WSPEC env P t Q1 /\
    WSPEC env P t Q2
    ==> WSPEC env P t (\g m. Q1 g m /\ Q2 g m)
Proof
  rw[WSPEC_def] >> rpt strip_tac >>
  `?og om. c = (final, [(og, om)]) /\ Q1 og om` by metis_tac[] >>
  `?og' om'. c = (final, [(og', om')]) /\ Q2 og' om'` by metis_tac[] >>
  gvs[] >> qexists_tac `og` >> qexists_tac `om` >> simp[]
QED

Theorem WSPEC_disj_pre:
  !env P1 P2 Q t.
    WSPEC env P1 t Q /\
    WSPEC env P2 t Q
    ==> WSPEC env (\s. P1 s \/ P2 s) t Q
Proof
  rw[WSPEC_def] >> rpt strip_tac >> metis_tac[]
QED

(* If-then-else rule for WSPEC.
   GP2's ifte semantics: run C, then restore the original state.
   - If C succeeds: run then-branch from original state
   - If C fails: run else-branch from original state
   Both branches run from the same precondition P since C's effect is discarded. *)
Theorem WSPEC_ifte:
  !env P R C t1 t2.
    no_intermediate_terms C /\
    WSPEC env P t1 R /\
    WSPEC env P t2 R
    ==> WSPEC env P (term_ifte C t1 t2) R
Proof
  rw[WSPEC_def, no_intermediate_terms_def] >> rpt strip_tac >>
  `FEVERY (\(_,t). no_intermediate_terms t) env.proc` by
    metis_tac[wf_program_FEVERY] >>
  qpat_x_assum `steps env (running (term_ifte _ _ _), _) _` mp_tac >>
  simp[steps_ifte] >> strip_tac >> gvs[can_step_def] >>
  fs[steps_ifte, top_stack_def] >> fs[steps_NRC] >>
  Cases_on `n`
  >- gvs[arithmeticTheory.NRC, can_step_def]
  >- (
    gvs[arithmeticTheory.NRC] >>
    qpat_x_assum `step env (running (term_ifte _ _ _), _) _` mp_tac >>
    simp[Once step_cases, top_stack_def] >> strip_tac >> gvs[] >>
    gvs[push_stack_def] >>
    drule_all NRC_ITE_decompose >> strip_tac
    (* Case 1: C succeeds, t1 runs from original state *)
    >- (
      subgoal `?h'. S' = h' :: [(G, id_track G)]`
      >- (drule no_intermediate_terms_preserves_stack_tail >> simp[can_step_def])
      >- (gvs[pop_stack_def] >> metis_tac[]))
    (* Case 2: C fails, t2 runs from original state *)
    >- (
      subgoal `?h'. S' = h' :: [(G, id_track G)]`
      >- (drule no_intermediate_terms_preserves_stack_tail >> simp[can_step_def])
      >- (gvs[pop_stack_def] >> metis_tac[])))
QED

(* Helper lemma for WSPEC_alap: complete induction on step count.
   Proves that for any n-step execution of term_alap P from [G],
   if Q G holds and P preserves Q, then the result satisfies Q.
   The hypothesis covers ALL terminal states - this is crucial for handling
   the term_break case, where we derive a contradiction since the hypothesis
   requires final state but term_break gives running term_break state.

   Proof approach (documented for future completion):
   1. Use completeInduct_on 'n' for complete induction
   2. n=0 case: contradiction via can_step_def (term_alap always steps)
   3. n>0 case:
      a. First step: term_alap P → term_trte P (term_alap P) term_skip (via step_Alap1)
      b. Second step: term_trte → term_TRY with pushed stack (via step_Try1)
      c. Use NRC_TRY_decompose to split into 3 cases:
         - P succeeds: Apply hypothesis to get Q on new graph, then use IH on remaining alap
           Key lemma: NRC_step_graph_determined handles track mismatch [(G',tr)] vs [(G',id_track G')]
         - P fails: term_skip executes, Q preserved on original graph
         - P breaks: NRC_TRY_decompose gives c = (final, SND h) directly
      d. Use NRC_step_preserves_suffix, NRC_step_inverse_frame for stack reasoning
      e. Use NRC_step_preserves_wf_stack_labels for wf_hostgraph/hostgraph_labels_spine preservation
*)
Theorem WSPEC_alap_helper:
  !n env P Q (G:hostgraph) c.
    wf_program env /\
    no_intermediate_terms P /\
    (* Key: hypothesis covers ALL terminal states, allowing contradiction for term_break *)
    (!G c. wf_hostgraph G /\ Q G /\
           steps env (running P,[(G,id_track G)]) c /\ ~can_step c ==>
           ?el. c = (final,[el]) /\ Q (FST el)) /\
    wf_hostgraph G /\ Q G /\
    NRC (step env) n (running (term_alap P),[(G, id_track G)]) c /\
    ~can_step c
    ==> ?el. c = (final,[el]) /\ Q (FST el)
Proof
  completeInduct_on `n` >> rpt strip_tac >> Cases_on `n` >>
  gvs[can_step_def] >> qabbrev_tac `S0 = [(G, id_track G)]` >>
  `step env (running (term_alap P), S0) (running (term_trte P (term_alap P) term_skip), S0)`
    by simp[step_rules] >>
  `step env (running (term_trte P (term_alap P) term_skip), S0)
            (running (term_TRY P (term_alap P) term_skip), push_stack (G, id_track G) S0)`
    by simp[step_rules, Abbr `S0`, top_stack_def] >>
  drule_at (Pos last) (iffLR (cj 2 NRC)) >> strip_tac >>
  `z = (running (term_trte P (term_alap P) term_skip), S0)`
    by (qpat_x_assum `step _ _ z` mp_tac >> simp[Once step_cases]) >> gvs[] >>
  Cases_on `n'` >> gvs[can_step_def] >>
  drule_at (Pos last) (iffLR (cj 2 NRC)) >> strip_tac >>
  `z = (running (term_TRY P (term_alap P) term_skip), push_stack (G, id_track G) S0)`
    by (qpat_x_assum `step _ (running (term_trte _ _ _), _) z` mp_tac >>
        simp[Once step_cases, Abbr `S0`, top_stack_def]) >> gvs[] >>
  qabbrev_tac `S1 = push_stack (G, id_track G) S0` >>
  drule_at (Pos last) NRC_TRY_decompose >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`env`, `n`, `P`, `term_alap P`, `term_skip`, `S1`] mp_tac) >>
  simp[] >> strip_tac >> gvs[]
  (* Case 1: P succeeds, continue with term_alap P *)
  >- (
    `FEVERY (λ(_0,t). no_intermediate_terms t) env.proc` by (irule wf_program_FEVERY >> simp[]) >>
    `S1 = [(G, id_track G); (G, id_track G)]` by simp[Abbr `S1`, Abbr `S0`, push_stack_def] >>
    `LENGTH S' = LENGTH S1`
      by (qspecl_then [`n1`, `P`, `env`, `S1`, `final`, `S'`] mp_tac
            no_intermediate_terms_preserves_stack_length >> simp[can_step_def]) >>
    Cases_on `S'` >- gvs[] >> Cases_on `t` >> gvs[] >>
    `t' = []` by (Cases_on `t'` >> gvs[Abbr `S0`]) >> gvs[pop2_stack_def] >>
    `h' = (G, id_track G)`
      by (qspecl_then [`n1`, `P`, `env`, `(G, id_track G)`, `S0`, `final`, `[h; h']`] mp_tac
            no_intermediate_terms_preserves_stack_tail >> simp[can_step_def, Abbr `S0`]) >> gvs[] >>
    `NRC (step env) n1 (running P,[(G,id_track G)]) (final,[h])`
      by (qspecl_then [`env`, `n1`, `P`, `[(G, id_track G)]`, `final`, `[h]`, `S0`] mp_tac
            NRC_step_inverse_frame >> simp[can_step_def, Abbr `S0`]) >>
    `Q (FST h)`
      by (qpat_assum `!G c. _ ==> ?el. c = (final, [el]) /\ Q (FST el)`
            (qspecl_then [`G`, `(final, [h])`] mp_tac) >>
          simp[can_step_def, steps_def] >>
          impl_tac >- (irule arithmeticTheory.NRC_RTC >> qexists `n1` >> simp[Abbr `S0`]) >>
          strip_tac >> gvs[]) >>
    `wf_stack_labels [(G, id_track G)]`
      by simp[wf_stack_labels_def, wf_hostgraph_IMP_wf_partial_hostgraph] >>
    `wf_stack_labels [h]` by (drule_all NRC_step_preserves_wf_stack_labels >> simp[]) >>
    qabbrev_tac `H = FST h` >>
    `wf_hostgraph H` by (gvs[wf_stack_labels_def, Abbr `H`] >> PairCases_on `h` >> gvs[]) >>
    `hostgraph_labels_spine H` by metis_tac[wf_hostgraph_IMP_hostgraph_labels_spine] >>
    `MAP FST [h] = MAP FST [(H, id_track H)]` by simp[Abbr `H`] >>
    `?s2'. NRC (step env) n2 (running (term_alap P), [(H, id_track H)]) (FST c, s2') /\
           MAP FST (SND c) = MAP FST s2'`
      by (qspecl_then [`n2`, `env`, `running (term_alap P)`, `[h]`, `FST c`, `SND c`] mp_tac
            NRC_step_graph_determined >> simp[] >>
          disch_then (qspec_then `[(H, id_track H)]` mp_tac) >> simp[Abbr `H`]) >>
    `~can_step (FST c, s2')`
      by (Cases_on `c` >> gvs[] >> Cases_on `q` >> gvs[can_step_def] >>
          Cases_on `t` >> gvs[can_step_def]) >>
    first_x_assum (qspec_then `n2` mp_tac) >> simp[] >>
    disch_then (qspecl_then [`env`, `P`, `Q`, `H`, `(FST c, s2')`] mp_tac) >> simp[] >>
    impl_tac >- first_assum ACCEPT_TAC >>
    strip_tac >> gvs[] >> qexists `x0` >> simp[] >> Cases_on `c` >> gvs[])
  (* Case 2: P fails, term_skip runs *)
  >- (
    `FEVERY (λ(_0,t). no_intermediate_terms t) env.proc` by (irule wf_program_FEVERY >> simp[]) >>
    `S1 = [(G, id_track G); (G, id_track G)]` by simp[Abbr `S1`, Abbr `S0`, push_stack_def] >>
    `LENGTH S' = LENGTH S1`
      by (qspecl_then [`n1`, `P`, `env`, `S1`, `failed`, `S'`] mp_tac
            no_intermediate_terms_preserves_stack_length >> simp[can_step_def]) >>
    Cases_on `S'` >- gvs[] >> Cases_on `t` >> gvs[] >>
    `t' = []` by (Cases_on `t'` >> gvs[Abbr `S0`]) >> gvs[pop_stack_def] >>
    `h' = (G, id_track G)`
      by (qspecl_then [`n1`, `P`, `env`, `(G, id_track G)`, `S0`, `failed`, `[h; h']`] mp_tac
            no_intermediate_terms_preserves_stack_tail >> simp[can_step_def, Abbr `S0`]) >> gvs[] >>
    Cases_on `n2` >- gvs[can_step_def] >>
    drule_at (Pos last) (iffLR (cj 2 NRC)) >> strip_tac >>
    `z = (final, S0)` by (qpat_x_assum `step _ _ z` mp_tac >> simp[Once step_cases]) >> gvs[] >>
    drule_all NRC_step_from_final >> strip_tac >> gvs[] >>
    qexists `(G, id_track G)` >> simp[Abbr `S0`])
  (* Case 3: P breaks - contradiction via WSPEC *)
  >- (
    `FEVERY (λ(_0,t). no_intermediate_terms t) env.proc` by (irule wf_program_FEVERY >> simp[]) >>
    `S1 = [(G, id_track G); (G, id_track G)]` by simp[Abbr `S1`, Abbr `S0`, push_stack_def] >>
    `LENGTH S' = LENGTH S1`
      by (qspecl_then [`n1`, `P`, `env`, `S1`, `running term_break`, `S'`] mp_tac
            no_intermediate_terms_preserves_stack_length >> simp[can_step_def]) >>
    Cases_on `S'` >- gvs[] >> Cases_on `t` >> gvs[] >>
    `t' = []` by (Cases_on `t'` >> gvs[Abbr `S0`]) >> gvs[pop2_stack_def] >>
    `h'' = (G, id_track G)`
      by (qspecl_then [`n1`, `P`, `env`, `(G, id_track G)`, `S0`, `running term_break`, `[h'; h'']`]
            mp_tac no_intermediate_terms_preserves_stack_tail >> simp[can_step_def, Abbr `S0`]) >> gvs[] >>
    `NRC (step env) n1 (running P,[(G,id_track G)]) (running term_break,[h'])`
      by (qspecl_then [`env`, `n1`, `P`, `[(G, id_track G)]`, `running term_break`, `[h']`, `S0`]
            mp_tac NRC_step_inverse_frame >> simp[can_step_def, Abbr `S0`]) >>
    qpat_assum `!G c. _ ==> ?el. c = (final, [el]) /\ Q (FST el)`
      (qspecl_then [`G`, `(running term_break, [h'])`] mp_tac) >> simp[can_step_def] >>
    `steps env (running P,S0) (running term_break,[h'])`
      by (simp[steps_def, Abbr `S0`] >> irule arithmeticTheory.NRC_RTC >> qexists `n1` >> simp[]) >> simp[])
QED

(* As-long-as-possible rule for WSPEC.
   ALAP(P) runs P repeatedly until P fails.
   If Q is both a pre and post condition for P, then Q is also
   a post condition for ALAP(P). The key insight is that P preserves Q,
   so after any number of successful iterations, Q still holds.
   When P eventually fails, the state before failure still satisfies Q.
   NOTE: Uses lift Q for postcondition since Q is a pure graph predicate.
   NOTE: This can also be derived from WSPEC_alap_tracked - see WSPEC_alap'. *)
Theorem WSPEC_alap:
  !env P Q.
    WSPEC env Q P (lift Q)
    ==> WSPEC env Q (term_alap P) (lift Q)
Proof
  rw[WSPEC_def, lift_def] >> rpt strip_tac
  >- simp[programTheory.no_intermediate_terms_def]
  >- (
    `?n. NRC (step env) n (running (term_alap P), [(G, id_track G)]) c`
      by metis_tac[steps_NRC] >>
    (* Convert the hypothesis to the form expected by WSPEC_alap_helper *)
    `!G' c'. wf_hostgraph G' /\ Q G' /\
           steps env (running P,[(G',id_track G')]) c' /\ ~can_step c' ==>
           ?el. c' = (final,[el]) /\ Q (FST el)` by (
      rpt strip_tac >>
      first_x_assum (qspecl_then [`G'`, `c'`] mp_tac) >> simp[] >> strip_tac >>
      qexists_tac `(og, om)` >> simp[]) >>
    `?el. c = (final,[el]) /\ Q (FST el)` by (
      irule WSPEC_alap_helper >> simp[] >> metis_tac[]) >>
    fs[] >> qexistsl_tac [`FST el`, `SND el`] >> simp[])
QED

(* Tracked ALAP: preserves morphism-aware invariants                  *)

(* Note: f_o_f_identity and compose_morphism_id_track_left are in trackTheory.
         step_morphism_preserve is in semPropsTheory. *)

(* ==================================================================
   Stack compose related - relating stacks where morphisms are composed
   ==================================================================

   This is key for the alternative proof approach that doesn't require
   NRC_step_morphism_compose for arbitrary executions.

   stack_compose_related tr s1 s2 means:
   - s1 and s2 have the same length and graphs
   - For each position, m1_i = compose_morphism m2_i tr
*)

Definition stack_compose_related_def:
  (stack_compose_related tr [] [] <=> T) /\
  (stack_compose_related tr [] (v0::v1) <=> F) /\
  (stack_compose_related tr (v2::v3) [] <=> F) /\
  (stack_compose_related tr ((G1,m1)::s1) ((G2,m2)::s2) <=>
     G1 = G2 /\ m1 = compose_morphism m2 tr /\ stack_compose_related tr s1 s2)
End

(* Helper lemma: pop_stack preserves stack_compose_related *)
Theorem scr_pop:
  !tr S' s1' G m rest.
    pop_stack S' = SOME ((G,m),rest) /\ stack_compose_related tr S' s1' ==>
    ?m' rest'. pop_stack s1' = SOME ((G,m'),rest') /\
               m = compose_morphism m' tr /\ stack_compose_related tr rest rest'
Proof
  Cases_on `S'` >> Cases_on `s1'` >>
  rw[stackTheory.pop_stack_def, stack_compose_related_def] >> gvs[] >>
  PairCases_on `h'` >> gvs[stack_compose_related_def]
QED

(* Helper lemma: top_stack preserves stack_compose_related *)
Theorem scr_top:
  !tr S' s1' G m.
    top_stack S' = SOME (G,m) /\ stack_compose_related tr S' s1' ==>
    ?m'. top_stack s1' = SOME (G,m') /\ m = compose_morphism m' tr
Proof
  Cases_on `S'` >> Cases_on `s1'` >>
  rw[stackTheory.top_stack_def, stack_compose_related_def] >> gvs[] >>
  PairCases_on `h'` >> gvs[stack_compose_related_def]
QED

(* Helper lemma: pop2_stack preserves stack_compose_related *)
Theorem scr_pop2:
  !tr S' s1' fst snd.
    pop2_stack S' = SOME (fst,snd) /\ stack_compose_related tr S' s1' ==>
    ?fst' snd'. pop2_stack s1' = SOME (fst',snd') /\
                stack_compose_related tr fst fst' /\ stack_compose_related tr snd snd'
Proof
  rpt gen_tac >> strip_tac >>
  `?a b c. S' = a::b::c` by
    (Cases_on `S'` >> gvs[stackTheory.pop2_stack_def] >>
     Cases_on `t` >> gvs[stackTheory.pop2_stack_def]) >>
  gvs[stackTheory.pop2_stack_def] >>
  Cases_on `s1'` >> gvs[stack_compose_related_def] >>
  Cases_on `t` >> gvs[stack_compose_related_def] >>
  PairCases_on `a` >> PairCases_on `b` >> PairCases_on `h` >>
  fs[stack_compose_related_def] >>
  Cases_on `h'` >> fs[stack_compose_related_def, stackTheory.pop2_stack_def]
QED

(* step preserves stack_compose_related: given a step from s1 to s2
   and stack_compose_related tr s1 s1', we can step from s1' to s2'
   with stack_compose_related tr s2 s2' *)
Theorem step_stack_compose_related:
  !env c1 s1 c2 s2.
    step env (c1, s1) (c2, s2) ==>
    !s1' tr. stack_compose_related tr s1 s1' ==>
      ?s2'. step env (c1, s1') (c2, s2') /\ stack_compose_related tr s2 s2'
Proof
  Induct_on `step` >> rpt strip_tac >> gvs[]
  (* Case 1: Call1 - rule application succeeds *)
  >- (imp_res_tac scr_pop >>
      Q.EXISTS_TAC `push_stack (h, compose_morphism (track ri.lhs ri.inf m G) m') rest'` >>
      conj_tac
      >- (irule (el 1 (CONJUNCTS semTheory.step_rules)) >>
          rpt conj_tac >> gvs[] >>
          Q.EXISTS_TAC `assign` >> Q.EXISTS_TAC `r` >> Q.EXISTS_TAC `rname` >> gvs[])
      >- (simp[stackTheory.push_stack_def, stack_compose_related_def] >>
          `m' = m'' /\ rest' = rest''` by gvs[] >>
          gvs[morphismTheory.compose_morphism_assoc]))
  (* Case 2: Call2 - rule application fails *)
  >- (imp_res_tac scr_pop >> Q.EXISTS_TAC `s1'` >>
      conj_tac
      >- (irule (el 2 (CONJUNCTS semTheory.step_rules)) >> gvs[] >>
          rpt strip_tac >> first_x_assum drule >> simp[])
      >- gvs[])
  (* Case 3: Proc - stack unchanged *)
  >- (Q.EXISTS_TAC `s1'` >> simp[semTheory.step_rules])
  (* Case 4: Seq step *)
  >- (first_x_assum drule >> rpt strip_tac >> Q.EXISTS_TAC `s2''` >>
      simp[semTheory.step_rules])
  (* Case 5: Seq done *)
  >- (first_x_assum drule >> rpt strip_tac >> Q.EXISTS_TAC `s2''` >>
      simp[semTheory.step_rules])
  (* Case 6: Seq fail *)
  >- (first_x_assum drule >> rpt strip_tac >> Q.EXISTS_TAC `s2''` >>
      simp[semTheory.step_rules] >>
      imp_res_tac semPropsTheory.step_fails_stack_unchanged >>
      gvs[semTheory.step_rules])
  (* Case 7: Seq break - stack unchanged *)
  >- (Q.EXISTS_TAC `s1'` >> simp[semTheory.step_rules])
  (* Case 8: ALAP - stack unchanged *)
  >- (Q.EXISTS_TAC `s1'` >> simp[semTheory.step_rules])
  (* Case 9: TRY break (ALAP) *)
  >- (imp_res_tac scr_pop2 >>
      Cases_on `h` >> first_x_assum drule >> rpt strip_tac >>
      Q.EXISTS_TAC `snd'` >> simp[semTheory.step_rules] >>
      `snd' = SND (fst', snd')` by simp[] >> pop_assum SUBST1_TAC >>
      simp[semTheory.step_rules])
  (* Case 10: IFTE push *)
  >- (imp_res_tac scr_top >>
      Cases_on `el` >> first_x_assum drule >> rpt strip_tac >>
      Q.EXISTS_TAC `push_stack (q, m') s1'` >>
      conj_tac >- simp[semTheory.step_rules] >>
      simp[stackTheory.push_stack_def, stack_compose_related_def])
  (* Case 11: ITE step *)
  >- (first_x_assum drule >> rpt strip_tac >> Q.EXISTS_TAC `s2''` >>
      simp[semTheory.step_rules])
  (* Case 12: ITE done *)
  >- (first_x_assum drule >> rpt strip_tac >> imp_res_tac scr_pop >>
      Cases_on `r` >> PairCases_on `q` >> first_x_assum drule >> rpt strip_tac >>
      simp[] >> Q.EXISTS_TAC `rest'` >> simp[] >>
      Q.SUBGOAL_THEN `step env (running (term_ITE C P Q),s1') (running P, SND ((q0,m'),rest'))` ASSUME_TAC
      >- (irule (el 12 (CONJUNCTS semTheory.step_rules)) >>
          Q.EXISTS_TAC `s2''` >> gvs[])
      >- gvs[])
  (* Case 13: ITE fail *)
  >- (first_x_assum drule >> rpt strip_tac >>
      imp_res_tac semPropsTheory.step_fails_stack_unchanged >> gvs[] >>
      imp_res_tac scr_pop >> Cases_on `S''` >> PairCases_on `q` >>
      first_x_assum drule >> rpt strip_tac >>
      simp[] >> Q.EXISTS_TAC `rest'` >> simp[] >>
      Q.SUBGOAL_THEN `step env (running (term_ITE C P Q),s1') (running Q, SND ((q0,m'),rest'))` ASSUME_TAC
      >- (irule (el 13 (CONJUNCTS semTheory.step_rules)) >> gvs[])
      >- gvs[])
  (* Case 14: TRTE push *)
  >- (imp_res_tac scr_top >> Cases_on `el` >> first_x_assum drule >> rpt strip_tac >>
      Q.EXISTS_TAC `push_stack (q, m') s1'` >>
      conj_tac >- simp[semTheory.step_rules] >>
      simp[stackTheory.push_stack_def, stack_compose_related_def])
  (* Case 15: TRY step *)
  >- (first_x_assum drule >> rpt strip_tac >> Q.EXISTS_TAC `s2''` >>
      simp[semTheory.step_rules])
  (* Case 16: TRY done *)
  >- (first_x_assum drule >> rpt strip_tac >> imp_res_tac scr_pop2 >>
      Cases_on `r` >> first_x_assum drule >> rpt strip_tac >>
      simp[] >> Q.EXISTS_TAC `snd'` >> simp[] >>
      Q.SUBGOAL_THEN `step env (running (term_TRY C P Q),s1') (running P, SND (fst',snd'))` ASSUME_TAC
      >- (irule (el 16 (CONJUNCTS semTheory.step_rules)) >>
          Q.EXISTS_TAC `s2''` >> gvs[])
      >- gvs[])
  (* Case 17: TRY fail *)
  >- (first_x_assum drule >> rpt strip_tac >>
      imp_res_tac semPropsTheory.step_fails_stack_unchanged >> gvs[] >>
      imp_res_tac scr_pop >> Cases_on `S''` >> PairCases_on `q` >>
      first_x_assum drule >> rpt strip_tac >> simp[] >>
      Q.EXISTS_TAC `rest'` >> simp[] >>
      Q.SUBGOAL_THEN `step env (running (term_TRY C P Q),s1') (running Q, SND ((q0,m'),rest'))` ASSUME_TAC
      >- (irule (el 17 (CONJUNCTS semTheory.step_rules)) >> gvs[])
      >- gvs[])
  (* Case 18-21: Or L, Or R, Skip, Fail - stack unchanged *)
  >- (Q.EXISTS_TAC `s1'` >> simp[semTheory.step_rules])
  >- (Q.EXISTS_TAC `s1'` >> simp[semTheory.step_rules])
  >- (Q.EXISTS_TAC `s1'` >> simp[semTheory.step_rules])
  >- (Q.EXISTS_TAC `s1'` >> simp[semTheory.step_rules])
QED

(* NRC (n-step execution) preserves stack_compose_related *)
Theorem NRC_step_stack_compose_related:
  !n env c1 s1 c2 s2 s1' tr.
    NRC (step env) n (c1, s1) (c2, s2) /\
    stack_compose_related tr s1 s1' ==>
    ?s2'. NRC (step env) n (c1, s1') (c2, s2') /\ stack_compose_related tr s2 s2'
Proof
  Induct
  (* Base case: n=0, configurations are equal *)
  >- (rpt strip_tac >> gvs[NRC] >> Q.EXISTS_TAC `s1'` >> simp[])
  (* Inductive case: use step_stack_compose_related for first step, then IH *)
  >- (rpt strip_tac >> gvs[NRC] >>
      PairCases_on `z` >> gvs[] >>
      `?sm. step env (c1, s1') (z0, sm) /\ stack_compose_related tr z1 sm`
        by metis_tac[step_stack_compose_related] >>
      first_x_assum (drule_then strip_assume_tac) >>
      first_x_assum (drule_then strip_assume_tac) >>
      Q.EXISTS_TAC `s2'` >> simp[] >>
      Q.EXISTS_TAC `(z0, sm)` >> simp[])
QED

(* ==================================================================
   WSPEC_alap_tracked_helper subtheorems for individual cases
   ==================================================================

   After NRC_TRY_decompose, we get 3 cases:
   1. P succeeds (final): Use IH on remaining alap, compose morphisms
   2. P fails (failed): term_skip runs, left identity gives result
   3. P breaks (running term_break): Contradiction - body preservation
      says P must reach (final,...) but we have (running term_break,...)
*)

(* Case 1: P succeeds, continue with term_alap P.

   Key: After one successful iteration of P:
   1. Extract (H1, mH1) from P execution
   2. Body preservation gives Q H1 (compose_morphism mH1 m0)
   3. Use NRC_step_graph_determined to get execution from [(H1, id_track H1)]
   4. Apply IH with starting morphism (compose_morphism mH1 m0)
   5. IH gives Q H (compose_morphism mH' (compose_morphism mH1 m0))
   6. Use NRC_step_morphism_compose to get: mH = compose_morphism mH' mH1
   7. By associativity: compose_morphism mH' (compose_morphism mH1 m0)
                      = compose_morphism (compose_morphism mH' mH1) m0
                      = compose_morphism mH m0

   DEPENDS ON: NRC_step_morphism_compose (currently cheated) *)
Theorem WSPEC_alap_tracked_helper_case1:
  !n1 n2 env P Q G m0 S' h h' S0 c.
    (* From main theorem assumptions *)
    wf_program env /\
    no_intermediate_terms P /\
    (* Body preserves Q with morphism composition *)
    (!G' m' c'. wf_hostgraph G' /\ Q G' m' /\
                steps env (running P,[(G',id_track G')]) c' /\ ~can_step c' ==>
                ?H mH. c' = (final,[(H,mH)]) /\ Q H (compose_morphism mH m')) /\
    (* Q implies morphism well-formedness *)
    (!G m. Q G m ==> FRANGE m.nodemap SUBSET G.V /\ FRANGE m.edgemap SUBSET G.E) /\
    wf_hostgraph G /\ Q G m0 /\
    (* IH for smaller n *)
    (!m. m < n1 + n2 + 1 ==>
      !env P Q G m0 c.
        wf_program env /\ no_intermediate_terms P /\
        (!G' m' c'. wf_hostgraph G' /\ Q G' m' /\
                    steps env (running P,[(G',id_track G')]) c' /\ ~can_step c' ==>
                    ?H mH. c' = (final,[(H,mH)]) /\ Q H (compose_morphism mH m')) /\
        (!G m. Q G m ==> FRANGE m.nodemap SUBSET G.V /\ FRANGE m.edgemap SUBSET G.E) /\
        wf_hostgraph G /\ Q G m0 /\
        NRC (step env) m (running (term_alap P),[(G,id_track G)]) c /\
        ~can_step c ==>
        ?H mH. c = (final,[(H,mH)]) /\ Q H (compose_morphism mH m0)) /\
    (* From NRC_TRY_decompose case 1 *)
    S0 = [(G, id_track G)] /\
    NRC (step env) n1 (running P, push_stack (G, id_track G) S0) (final, S') /\
    S' = [h; h'] /\ h' = (G, id_track G) /\
    NRC (step env) n2 (running (term_alap P), [h]) c /\
    ~can_step c
    ==>
    ?H mH. c = (final,[(H,mH)]) /\ Q H (compose_morphism mH m0)
Proof
  (* Proof strategy (alternative approach - does NOT use NRC_step_morphism_compose):
     1. Extract frameless P execution using NRC_step_inverse_frame
     2. Body preservation gives Q H1 (compose_morphism mH1 m0)
     3. Establish wf_hostgraph H1 via NRC_step_preserves_wf_stack
     4. Establish is_track_morphism via NRC_step_preserves_stack_tracks_morphism
     5. Use NRC_step_stack_compose_related to CONSTRUCT execution from id_track
     6. Use can_step_state_only to transfer ~can_step
     7. Apply IH to the CONSTRUCTED execution
     8. Use compose_morphism_assoc to connect morphisms *)
  rpt strip_tac >> fs[stackTheory.push_stack_def] >> Cases_on `h` >>
  (* Step 1: Extract frameless execution *)
  sg `NRC (step env) n1 (running P, [(G, id_track G)]) (final, [(q, r)])`
  >- (irule semPropsTheory.NRC_step_inverse_frame >>
      rpt conj_tac >- fs[] >- simp[] >- metis_tac[wf_program_FEVERY] >>
      qexists_tac `[(G, id_track G)]` >>
      simp[semTheory.can_step_def, semTheory.step_cases] >> rfs[]) >>
  (* Step 2: Apply body preservation *)
  sg `Q q (compose_morphism r m0)`
  >- (first_x_assum (qspecl_then [`G`, `m0`, `(final, [(q,r)])`] mp_tac) >>
      impl_tac
      >- (rpt conj_tac >- fs[] >- fs[]
          >- (fs[semTheory.steps_def] >> irule NRC_RTC >> metis_tac[])
          >- fs[semTheory.can_step_def, semTheory.step_cases])
      >- (rpt strip_tac >> fs[])) >>
  (* Step 3: Establish wf_hostgraph q *)
  sg `wf_hostgraph q`
  >- (`wf_stack [(q, r)]` suffices_by fs[semTheory.wf_stack_def] >>
      irule semPropsTheory.NRC_step_preserves_wf_stack >>
      qexistsl_tac [`running P`, `final`, `env`, `n1`, `[(G, id_track G)]`] >>
      fs[semTheory.wf_stack_labels_def]) >>
  (* Step 4: Establish is_track_morphism G r q *)
  sg `is_track_morphism G r q`
  >- (`stack_tracks_morphism G [(q, r)]`
        suffices_by fs[semPropsTheory.stack_tracks_morphism_def] >>
      irule semPropsTheory.NRC_step_preserves_stack_tracks_morphism >>
      qexistsl_tac [`running P`, `final`, `env`, `n1`, `[(G, id_track G)]`] >>
      fs[semTheory.wf_stack_labels_def, semPropsTheory.stack_tracks_morphism_def] >>
      irule trackTheory.id_track_is_track_morphism >>
      fs[hostgraphTheory.wf_hostgraph_def, graphTheory.wf_graph_def]) >>
  (* Extract morphism range conditions *)
  `FRANGE r.nodemap SUBSET q.V /\ FRANGE r.edgemap SUBSET q.E`
    by fs[trackTheory.is_track_morphism_def, morphismTheory.partial_dom_ran_def] >>
  (* Establish stack_compose_related *)
  `stack_compose_related r [(q,r)] [(q, id_track q)]`
    by (fs[stack_compose_related_def] >>
        irule (GSYM compose_morphism_id_track_left) >> fs[]) >>
  (* Step 5: Use NRC_step_stack_compose_related to construct execution from id_track *)
  `?s2'. NRC (step env) n2 (running (term_alap P), [(q, id_track q)]) (FST c, s2') /\
         stack_compose_related r (SND c) s2'`
    by (Cases_on `c` >> fs[] >> irule NRC_step_stack_compose_related >> metis_tac[]) >>
  (* Step 6: Transfer ~can_step using can_step_state_only *)
  sg `~can_step (FST c, s2')`
  >- (Cases_on `c` >> fs[can_step_state_only] >> metis_tac[can_step_state_only]) >>
  (* Step 7: Apply IH *)
  first_x_assum (qspec_then `n2` mp_tac) >> impl_tac >- simp[] >>
  disch_then (qspecl_then [`env`, `P`, `Q`, `q`, `compose_morphism r m0`, `(FST c, s2')`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> fs[]) >>
  (* Step 8: Extract conclusion using stack_compose_related and associativity *)
  rpt strip_tac >> fs[] >>
  Cases_on `SND c` >- fs[stack_compose_related_def] >>
  Cases_on `h` >> fs[stack_compose_related_def] >>
  fs[stack_compose_related_def] >>
  Cases_on `t` >> fs[stack_compose_related_def] >>
  qexistsl_tac [`H`, `compose_morphism mH r`] >>
  conj_tac >- (Cases_on `c` >> fs[]) >>
  fs[morphismTheory.compose_morphism_assoc]
QED

(* Case 2: P fails, term_skip runs.
   Key: When P fails, we stay on the original graph G.
   The result is (final, [(G, id_track G)]).
   Use compose_morphism_id_track_left: compose (id_track G) m0 = m0. *)
Theorem WSPEC_alap_tracked_helper_case2:
  !n1 n2 env P Q G m0 S' h h' S0 c.
    (* From main theorem assumptions *)
    wf_program env /\
    no_intermediate_terms P /\
    (* Q implies morphism well-formedness *)
    (!G m. Q G m ==> FRANGE m.nodemap SUBSET G.V /\ FRANGE m.edgemap SUBSET G.E) /\
    wf_hostgraph G /\ Q G m0 /\
    (* From NRC_TRY_decompose case 2 *)
    S0 = [(G, id_track G)] /\
    NRC (step env) n1 (running P, push_stack (G, id_track G) S0) (failed, S') /\
    S' = [h; h'] /\ h' = (G, id_track G) /\
    NRC (step env) n2 (running term_skip, [h']) c /\
    ~can_step c
    ==>
    ?H mH. c = (final,[(H,mH)]) /\ Q H (compose_morphism mH m0)
Proof
  rpt strip_tac >> gvs[push_stack_def] >>
  (* Derive FRANGE from Q *)
  `FRANGE m0.nodemap SUBSET G.V /\ FRANGE m0.edgemap SUBSET G.E` by metis_tac[] >>
  (* term_skip from [(G, id_track G)] takes one step to (final, [(G, id_track G)]) *)
  Cases_on `n2` >- gvs[can_step_def] >>
  drule_at (Pos last) (iffLR (cj 2 NRC)) >> strip_tac >>
  sg `z = (final, [(G, id_track G)])`
  >- (qpat_x_assum `step _ _ z` mp_tac >> simp[Once step_cases])
  >- (
    gvs[] >>
    drule_all NRC_step_from_final >> strip_tac >> gvs[] >>
    (* After NRC_step_from_final and gvs, the goal becomes Q G (compose id_track m0) *)
    (* Use left identity: compose_morphism (id_track G) m0 = m0 *)
    `compose_morphism (id_track G) m0 = m0`
      by (irule compose_morphism_id_track_left >> simp[]) >>
    simp[])
QED

(* Case 3: P breaks - this is a contradiction.
   Key: The body preservation hypothesis says that when P terminates,
   the result is (final, [(H, mH)]). But in this case, P terminated with
   (running term_break, ...) which contradicts this. *)
Theorem WSPEC_alap_tracked_helper_case3:
  !n1 n2 env P Q G m0 S' h' S0 c.
    (* From main theorem assumptions *)
    wf_program env /\
    no_intermediate_terms P /\
    (* Body preserves Q with morphism composition - crucially, result is (final,...) *)
    (!G' m' c'. wf_hostgraph G' /\ Q G' m' /\
                steps env (running P,[(G',id_track G')]) c' /\ ~can_step c' ==>
                ?H mH. c' = (final,[(H,mH)]) /\ Q H (compose_morphism mH m')) /\
    (* Q implies morphism well-formedness *)
    (!G m. Q G m ==> FRANGE m.nodemap SUBSET G.V /\ FRANGE m.edgemap SUBSET G.E) /\
    wf_hostgraph G /\ Q G m0 /\
    (* From NRC_TRY_decompose case 3 *)
    S0 = [(G, id_track G)] /\
    NRC (step env) n1 (running P, push_stack (G, id_track G) S0) (running term_break, S') /\
    LENGTH S' = 2 /\ h' = LAST S' /\ h' = (G, id_track G) /\
    NRC (step env) n2 (running (term_alap P), [HD S']) c /\
    ~can_step c
    ==>
    ?H mH. c = (final,[(H,mH)]) /\ Q H (compose_morphism mH m0)
Proof
  rpt strip_tac >> gvs[push_stack_def] >>
  (* Extract the singleton execution from LENGTH S' = 2 *)
  Cases_on `S'` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  (* Now S' = [h; (G, id_track G)] *)
  (* Get singleton execution via NRC_step_inverse_frame *)
  sg `NRC (step env) n1 (running P,[(G,id_track G)]) (running term_break,[h])`
  >- (qspecl_then [`env`, `n1`, `P`, `[(G, id_track G)]`, `running term_break`, `[h]`,
                   `[(G, id_track G)]`] mp_tac NRC_step_inverse_frame >>
      simp[can_step_def] >> rpt strip_tac >> gvs[wf_program_def, FEVERY_DEF])
  >- (
    (* Body preservation says c' = (final, ...) but we have c' = (running term_break, ...) *)
    qpat_assum `!G' m' c'. _ ==> ?H mH. c' = (final,[(H,mH)]) /\ _`
      (qspecl_then [`G`, `m0`, `(running term_break, [h])`] mp_tac) >>
    simp[can_step_def] >>
    (* Show steps from singleton *)
    sg `steps env (running P,[(G,id_track G)]) (running term_break,[h])`
    >- (simp[steps_def] >> irule arithmeticTheory.NRC_RTC >> qexists `n1` >> simp[])
    >- simp[])
QED

(* Helper for WSPEC_alap_tracked.
   Similar to WSPEC_alap_helper but tracks morphism composition.

   Key insight: the operational semantics already compose morphisms at each
   rule application. We track a logical morphism m0 through the induction,
   showing that Q is preserved with the composition of operational and
   logical morphisms.

   The associativity of compose_morphism is crucial:
     compose_morphism mH' (compose_morphism m1 m0)
   = compose_morphism (compose_morphism mH' m1) m0

   This lets us relate the IH result to the final composed morphism. *)
Theorem WSPEC_alap_tracked_helper:
  !n env P Q (G:hostgraph) m0 c.
    wf_program env /\
    no_intermediate_terms P /\
    (* Body preserves Q with morphism composition *)
    (!G' m' c'. wf_hostgraph G' /\ Q G' m' /\
                steps env (running P,[(G',id_track G')]) c' /\ ~can_step c' ==>
                ?H mH. c' = (final,[(H,mH)]) /\ Q H (compose_morphism mH m')) /\
    (* Q implies morphism well-formedness *)
    (!G m. Q G m ==> FRANGE m.nodemap SUBSET G.V /\ FRANGE m.edgemap SUBSET G.E) /\
    wf_hostgraph G /\ Q G m0 /\
    NRC (step env) n (running (term_alap P), [(G, id_track G)]) c /\
    ~can_step c
    ==> ?H mH. c = (final,[(H,mH)]) /\ Q H (compose_morphism mH m0)
Proof
  completeInduct_on `n` >> rpt strip_tac >> Cases_on `n` >>
  gvs[can_step_def] >> qabbrev_tac `S0 = [(G, id_track G)]` >>
  `step env (running (term_alap P), S0) (running (term_trte P (term_alap P) term_skip), S0)`
    by simp[step_rules] >>
  `step env (running (term_trte P (term_alap P) term_skip), S0)
            (running (term_TRY P (term_alap P) term_skip), push_stack (G, id_track G) S0)`
    by simp[step_rules, Abbr `S0`, top_stack_def] >>
  drule_at (Pos last) (iffLR (cj 2 NRC)) >> strip_tac >>
  `z = (running (term_trte P (term_alap P) term_skip), S0)`
    by (qpat_x_assum `step _ _ z` mp_tac >> simp[Once step_cases]) >> gvs[] >>
  Cases_on `n'` >> gvs[can_step_def] >>
  drule_at (Pos last) (iffLR (cj 2 NRC)) >> strip_tac >>
  `z = (running (term_TRY P (term_alap P) term_skip), push_stack (G, id_track G) S0)`
    by (qpat_x_assum `step _ (running (term_trte _ _ _), _) z` mp_tac >>
        simp[Once step_cases, Abbr `S0`, top_stack_def]) >>
  gvs[] >> qabbrev_tac `S1 = push_stack (G, id_track G) S0` >>
  drule_at (Pos last) NRC_TRY_decompose >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`env`, `n`, `P`, `term_alap P`, `term_skip`, `S1`] mp_tac) >>
  simp[] >> strip_tac >> gvs[]
  (* Case 1: P succeeds, continue with term_alap P *)
  >- (
    `FEVERY (λ(_0,t). no_intermediate_terms t) env.proc` by (irule wf_program_FEVERY >> simp[]) >>
    `S1 = [(G, id_track G); (G, id_track G)]` by simp[Abbr `S1`, Abbr `S0`, push_stack_def] >>
    `LENGTH S' = LENGTH S1`
      by (qspecl_then [`n1`, `P`, `env`, `S1`, `final`, `S'`] mp_tac
            no_intermediate_terms_preserves_stack_length >> simp[can_step_def]) >>
    Cases_on `S'` >- gvs[] >> Cases_on `t` >> gvs[] >>
    `t' = []` by (Cases_on `t'` >> gvs[Abbr `S0`]) >> gvs[pop2_stack_def] >>
    `h' = (G, id_track G)`
      by (qspecl_then [`n1`, `P`, `env`, `(G, id_track G)`, `S0`, `final`, `[h; h']`] mp_tac
            no_intermediate_terms_preserves_stack_tail >> simp[can_step_def, Abbr `S0`]) >> gvs[] >>
    irule WSPEC_alap_tracked_helper_case1 >> simp[push_stack_def] >>
    qexistsl_tac [`G`, `P`, `env`, `h`, `n1`, `n2`] >> simp[] >>
    conj_tac
    >- (rpt strip_tac >> first_x_assum (qspec_then `m` mp_tac) >> impl_tac >- simp[] >> metis_tac[])
    >- (first_assum ACCEPT_TAC))
  (* Case 2: P fails, term_skip runs *)
  >- (
    `FEVERY (λ(_0,t). no_intermediate_terms t) env.proc` by (irule wf_program_FEVERY >> simp[]) >>
    `S1 = [(G, id_track G); (G, id_track G)]` by simp[Abbr `S1`, Abbr `S0`, push_stack_def] >>
    `LENGTH S' = LENGTH S1`
      by (qspecl_then [`n1`, `P`, `env`, `S1`, `failed`, `S'`] mp_tac
            no_intermediate_terms_preserves_stack_length >> simp[can_step_def]) >>
    Cases_on `S'` >- gvs[] >> Cases_on `t` >> gvs[] >>
    `t' = []` by (Cases_on `t'` >> gvs[Abbr `S0`]) >> gvs[pop_stack_def] >>
    `h' = (G, id_track G)`
      by (qspecl_then [`n1`, `P`, `env`, `(G, id_track G)`, `S0`, `failed`, `[h; h']`] mp_tac
            no_intermediate_terms_preserves_stack_tail >> simp[can_step_def, Abbr `S0`]) >> gvs[] >>
    irule WSPEC_alap_tracked_helper_case2 >> simp[push_stack_def] >>
    qexistsl_tac [`G`, `P`, `env`, `h`, `n1`, `n2`] >> gvs[])
  (* Case 3: P breaks - contradiction *)
  >- (
    `FEVERY (λ(_0,t). no_intermediate_terms t) env.proc` by (irule wf_program_FEVERY >> simp[]) >>
    `S1 = [(G, id_track G); (G, id_track G)]` by simp[Abbr `S1`, Abbr `S0`, push_stack_def] >>
    `LENGTH S' = LENGTH S1`
      by (qspecl_then [`n1`, `P`, `env`, `S1`, `running term_break`, `S'`] mp_tac
            no_intermediate_terms_preserves_stack_length >> simp[can_step_def]) >>
    Cases_on `S'` >- gvs[] >> Cases_on `t` >> gvs[] >>
    `t' = []` by (Cases_on `t'` >> gvs[Abbr `S0`]) >> gvs[pop2_stack_def] >>
    `h'' = (G, id_track G)`
      by (qspecl_then [`n1`, `P`, `env`, `(G, id_track G)`, `S0`, `running term_break`, `[h'; h'']`]
            mp_tac no_intermediate_terms_preserves_stack_tail >> simp[can_step_def, Abbr `S0`]) >> gvs[] >>
    sg `NRC (step env) n1 (running P,[(G,id_track G)]) (running term_break,[h'])`
    >- (qspecl_then [`env`, `n1`, `P`, `[(G, id_track G)]`, `running term_break`, `[h']`,
                     `[(G, id_track G)]`] mp_tac NRC_step_inverse_frame >>
        simp[can_step_def] >> rpt strip_tac >> gvs[wf_program_def, FEVERY_DEF])
    >- (
      qpat_assum `!G' m' c'. _ ==> ?H mH. c' = (final,[(H,mH)]) /\ _`
        (qspecl_then [`G`, `m0`, `(running term_break, [h'])`] mp_tac) >>
      simp[can_step_def] >>
      sg `steps env (running P,S0) (running term_break,[h'])`
      >- (simp[steps_def, Abbr `S0`] >> irule arithmeticTheory.NRC_RTC >> qexists `n1` >> simp[])
      >- simp[]))
QED

(* Tracked as-long-as-possible rule for WSPEC.

   This is the morphism-aware version of WSPEC_alap. Instead of using
   (lift Q) which ignores the morphism, this version:
   - Takes an invariant Q : hostgraph -> morphism -> bool
   - Requires the body to preserve Q with morphism composition
   - Produces Q with the fully composed morphism in the postcondition

   The universal quantification over m0 allows entering the loop with
   any accumulated morphism from prior execution, not just id_track.
   This is the general Hoare-style rule for tracked loops.

   Composition order: compose_morphism m m0 means m0 first, then m.
   So if m0 : G0 -> G (prior) and m : G -> H (loop), result is G0 -> H.

   Q must imply morphism well-formedness (FRANGE conditions). This is
   natural: any sensible invariant tracking morphisms should imply that
   the morphism's range is contained in the target graph. *)
Theorem WSPEC_alap_tracked:
  !env P Q.
    (* Body: preserves Q with morphism composition *)
    (!G m. WSPEC env
             (\H. H = G /\ Q G m)
             P
             (\H' m'. Q H' (compose_morphism m' m))) /\
    (* Q implies morphism well-formedness *)
    (!G m. Q G m ==> FRANGE m.nodemap SUBSET G.V /\ FRANGE m.edgemap SUBSET G.E)
    ==>
    (* For any starting morphism m0, loop composes on top *)
    !m0. WSPEC env
           (\G. Q G m0)
           (term_alap P)
           (\H m. Q H (compose_morphism m m0))
Proof
  rw[WSPEC_def] >> rpt strip_tac
  (* no_intermediate_terms (term_alap P) *)
  >- (first_x_assum (qspecl_then [`ARB`, `ARB`] strip_assume_tac) >>
      gvs[programTheory.no_intermediate_terms_def])
  (* Main case: show postcondition *)
  >- (
    `?n. NRC (step env) n (running (term_alap P), [(G, id_track G)]) c`
      by metis_tac[steps_NRC] >>
    `wf_program env /\ no_intermediate_terms P` by
      (first_x_assum (qspecl_then [`ARB`, `ARB`] strip_assume_tac) >> simp[]) >>
    sg `!G' m' c'. wf_hostgraph G' /\ Q G' m' /\
                   steps env (running P,[(G',id_track G')]) c' /\ ~can_step c' ==>
                   ?H mH. c' = (final,[(H,mH)]) /\ Q H (compose_morphism mH m')`
    >- (rpt strip_tac >>
        qpat_assum `!G m. wf_program _ /\ _ /\ _` (qspecl_then [`G'`, `m'`] mp_tac) >>
        simp[])
    >- (irule WSPEC_alap_tracked_helper >> simp[] >>
        qexistsl_tac [`G`, `P`, `env`, `n`] >> simp[] >> metis_tac[]))
QED

(* Note: WSPEC_alap is a special case of WSPEC_alap_tracked where the
   predicate ignores the morphism (Q' = λG m. Q G). The non-tracked version
   uses WSPEC_alap_helper, which has a simpler proof structure. Both
   approaches work; the tracked version is more general and allows
   reasoning about morphism composition through loop iterations. *)

(* WSPEC_alap_with_termination: ALAP with body failure handling       *)

(* This version handles the case where the body can fail, providing a
   termination condition R in addition to the loop invariant Q.

   ALAP semantics: term_alap P runs P repeatedly until P fails.
   - While P succeeds: Q is preserved (loop invariant)
   - When P fails: R holds on the final graph (termination condition)
   - Result: Q ∧ R (invariant maintained AND termination achieved)

   This is more general than WSPEC_alap_tracked which requires P to
   always succeed when Q holds.

   Key use case: Transitive closure where:
   - Q = tc_loop_invariant (graph minimally extends G0)
   - R = ¬link_can_apply (link rule can't match)
   - When link fails, graph is transitive
*)

(* Helper for Case 2 with termination condition R *)
Theorem WSPEC_alap_termination_helper_case2:
  !n1 n2 env P Q R G m0 S' h h' S0 c.
    wf_program env /\
    no_intermediate_terms P /\
    (* Q implies morphism well-formedness *)
    (!G m. Q G m ==> FRANGE m.nodemap SUBSET G.V /\ FRANGE m.edgemap SUBSET G.E) /\
    (* Body spec: P either succeeds with Q or fails atomically *)
    (!G' m' c'. wf_hostgraph G' /\ Q G' m' /\
                steps env (running P,[(G',id_track G')]) c' /\ ~can_step c' ==>
                (?H mH. c' = (final,[(H,mH)]) /\ Q H (compose_morphism mH m')) \/
                (c' = (failed, [(G', id_track G')]))) /\
    (* When body fails, R holds *)
    (!G' m'. wf_hostgraph G' /\ Q G' m' /\
             steps env (running P, [(G', id_track G')]) (failed, [(G', id_track G')]) ==>
             R G' m') /\
    wf_hostgraph G /\ Q G m0 /\
    (* From NRC_TRY_decompose case 2 *)
    S0 = [(G, id_track G)] /\
    NRC (step env) n1 (running P, push_stack (G, id_track G) S0) (failed, S') /\
    S' = [h; h'] /\ h' = (G, id_track G) /\
    NRC (step env) n2 (running term_skip, [h']) c /\
    ~can_step c
    ==>
    ?H mH. c = (final,[(H,mH)]) /\ Q H (compose_morphism mH m0) /\ R H (compose_morphism mH m0)
Proof
  rpt strip_tac >> gvs[push_stack_def] >>
  `FRANGE m0.nodemap SUBSET G.V /\ FRANGE m0.edgemap SUBSET G.E` by metis_tac[] >>
  `FEVERY (λ(_0,t). no_intermediate_terms t) env.proc` by fs[wf_program_def, FEVERY_DEF, pairTheory.FORALL_PROD] >>
  Cases_on `n2` >- gvs[can_step_def] >>
  drule_at (Pos last) (iffLR (cj 2 NRC)) >> strip_tac >>
  sg `z = (final, [(G, id_track G)])`
  >- (qpat_x_assum `step _ _ z` mp_tac >> simp[Once step_cases])
  >- (
    gvs[] >>
    drule_all NRC_step_from_final >> strip_tac >> gvs[] >>
    `compose_morphism (id_track G) m0 = m0`
      by (irule compose_morphism_id_track_left >> simp[] >> metis_tac[]) >>
    simp[] >>
    (* Prove R G m0 from failure condition *)
    last_x_assum irule >> simp[] >>
    (* Extract frameless P execution *)
    sg `NRC (step env) n1 (running P, [(G, id_track G)]) (failed, [h])`
    >- (irule NRC_step_inverse_frame >> simp[] >>
        qexists_tac `[(G, id_track G)]` >> simp[can_step_def])
    >- (
      (* Convert NRC to steps *)
      `steps env (running P, [(G, id_track G)]) (failed, [h])`
        by (simp[steps_def] >> irule NRC_RTC >> qexists_tac `n1` >> simp[]) >>
      (* Use body spec to show (failed, [h]) = (failed, [(G, id_track G)]) *)
      `(failed, [h]) = (failed, [(G, id_track G)])`
        by (first_x_assum (qspecl_then [`G`, `m0`, `(failed, [h])`] mp_tac) >>
            simp[can_step_def]) >>
      gvs[]))
QED

(* Main helper theorem with termination condition *)
Theorem WSPEC_alap_with_termination_helper:
  !n env P Q R (G:hostgraph) m0 c.
    wf_program env /\
    no_intermediate_terms P /\
    (* Body preserves Q when it succeeds *)
    (!G' m' c'. wf_hostgraph G' /\ Q G' m' /\
                steps env (running P,[(G',id_track G')]) c' /\ ~can_step c' ==>
                (?H mH. c' = (final,[(H,mH)]) /\ Q H (compose_morphism mH m')) \/
                (c' = (failed, [(G', id_track G')]))) /\
    (* When body fails, R holds *)
    (!G' m'. wf_hostgraph G' /\ Q G' m' /\
             steps env (running P, [(G', id_track G')]) (failed, [(G', id_track G')]) ==>
             R G' m') /\
    (* Q implies morphism well-formedness *)
    (!G m. Q G m ==> FRANGE m.nodemap SUBSET G.V /\ FRANGE m.edgemap SUBSET G.E) /\
    wf_hostgraph G /\ Q G m0 /\
    NRC (step env) n (running (term_alap P), [(G, id_track G)]) c /\
    ~can_step c
    ==> ?H mH. c = (final,[(H,mH)]) /\ Q H (compose_morphism mH m0) /\ R H (compose_morphism mH m0)
Proof
  completeInduct_on `n` >> rpt strip_tac >> Cases_on `n` >>
  gvs[can_step_def] >> qabbrev_tac `S0 = [(G, id_track G)]` >>
  `step env (running (term_alap P), S0) (running (term_trte P (term_alap P) term_skip), S0)`
    by simp[step_rules] >>
  `step env (running (term_trte P (term_alap P) term_skip), S0)
            (running (term_TRY P (term_alap P) term_skip), push_stack (G, id_track G) S0)`
    by simp[step_rules, Abbr `S0`, top_stack_def] >>
  drule_at (Pos last) (iffLR (cj 2 NRC)) >> strip_tac >>
  `z = (running (term_trte P (term_alap P) term_skip), S0)`
    by (qpat_x_assum `step _ _ z` mp_tac >> simp[Once step_cases]) >> gvs[] >>
  Cases_on `n'` >> gvs[can_step_def] >>
  drule_at (Pos last) (iffLR (cj 2 NRC)) >> strip_tac >>
  `z = (running (term_TRY P (term_alap P) term_skip), push_stack (G, id_track G) S0)`
    by (qpat_x_assum `step _ (running (term_trte _ _ _), _) z` mp_tac >>
        simp[Once step_cases, Abbr `S0`, top_stack_def]) >>
  gvs[] >> qabbrev_tac `S1 = push_stack (G, id_track G) S0` >>
  drule_at (Pos last) NRC_TRY_decompose >> simp[] >> strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`env`, `n`, `P`, `term_alap P`, `term_skip`, `S1`] mp_tac) >>
  simp[] >> strip_tac >> gvs[]
  (* Case 1: P succeeds, continue with term_alap P *)
  >- (gvs[Abbr `S1`, Abbr `S0`, push_stack_def] >>
      sg `?S''. S' = S'' ++ [(G, id_track G)]`
      >- (irule NRC_step_preserves_suffix >> simp[can_step_def] >>
          qexistsl_tac [`P`, `[(G, id_track G)]`, `env`, `n1`, `final`] >> simp[] >>
          simp[can_step_def] >> drule wf_program_FEVERY >> simp[])
      >- (sg `NRC (step env) n1 (running P, [(G, id_track G)]) (final, S'')`
          >- (match_mp_tac NRC_step_inverse_frame >> simp[can_step_def] >>
              drule wf_program_FEVERY >> strip_tac >>
              qexists_tac `[(G, id_track G)]` >> simp[] >> gvs[])
          >- (`steps env (running P, [(G, id_track G)]) (final, S'')` by
                (simp[steps_def] >> irule NRC_RTC >> qexists_tac `n1` >> simp[]) >>
              `(?H mH. (final, S'') = (final,[(H,mH)]) /\ Q H (compose_morphism mH m0)) \/
               (final, S'') = (failed,[(G,id_track G)])` by
                (first_x_assum (qspecl_then [`G`, `m0`, `(final, S'')`] mp_tac) >>
                 simp[can_step_def])
              >- (gvs[] >>
                  sg `wf_hostgraph H`
                  >- (`wf_stack [(H, mH)]` suffices_by fs[wf_stack_def] >>
                      irule NRC_step_preserves_wf_stack >>
                      qexistsl_tac [`running P`, `final`, `env`, `n1`, `[(G, id_track G)]`] >>
                      simp[wf_stack_labels_def])
                  >- (sg `is_track_morphism G mH H`
                      >- (`stack_tracks_morphism G [(H, mH)]` suffices_by
                            fs[stack_tracks_morphism_def] >>
                          irule NRC_step_preserves_stack_tracks_morphism >>
                          qexistsl_tac [`running P`, `final`, `env`, `n1`, `[(G, id_track G)]`] >>
                          rpt conj_tac >- fs[] >- simp[wf_stack_labels_def]
                          >- (fs[stack_tracks_morphism_def] >>
                              irule trackTheory.id_track_is_track_morphism >>
                              fs[wf_hostgraph_def] >>
                              fs[wf_hostgraph_def, graphTheory.wf_graph_def])
                          >- fs[])
                      >- (`FRANGE mH.nodemap SUBSET H.V /\ FRANGE mH.edgemap SUBSET H.E` by
                            fs[trackTheory.is_track_morphism_def, morphismTheory.partial_dom_ran_def] >>
                          `stack_compose_related mH [(H, mH)] [(H, id_track H)]` by
                            (fs[stack_compose_related_def] >>
                             irule (GSYM trackTheory.compose_morphism_id_track_left) >> fs[]) >>
                          gvs[stackTheory.pop2_stack_def] >>
                          `?s2'. NRC (step env) n2 (running (term_alap P), [(H, id_track H)]) (FST c, s2') /\
                                 stack_compose_related mH (SND c) s2'` by
                            (Cases_on `c` >> fs[] >>
                             irule NRC_step_stack_compose_related >> metis_tac[]) >>
                          sg `~can_step (FST c, s2')`
                          >- (Cases_on `c` >> fs[can_step_state_only] >>
                              metis_tac[can_step_state_only])
                          >- (first_x_assum (qspec_then `n2` mp_tac) >> impl_tac >- simp[] >>
                              disch_then (qspecl_then [`env`, `P`, `Q`, `R`, `H`,
                                `compose_morphism mH m0`, `(FST c, s2')`] mp_tac) >>
                              impl_tac >- (rpt conj_tac >> fs[]) >>
                              rpt strip_tac >> gvs[] >>
                              Cases_on `SND c` >- fs[stack_compose_related_def] >>
                              Cases_on `h` >> fs[stack_compose_related_def] >>
                              Cases_on `t` >> fs[stack_compose_related_def] >>
                              qexistsl_tac [`H'`, `compose_morphism mH' mH`] >>
                              rpt conj_tac >- (Cases_on `c` >> fs[]) >>
                              fs[morphismTheory.compose_morphism_assoc]))))
              >- fs[])))
  (* Case 2: P fails, term_skip runs - use helper *)
  >- (gvs[Abbr `S1`, Abbr `S0`, push_stack_def] >>
      irule WSPEC_alap_termination_helper_case2 >> simp[] >>
      qexists_tac `G` >> qexists_tac `P` >> qexists_tac `env` >>
      sg `?S''. S' = S'' ++ [(G, id_track G)]`
      >- (irule NRC_step_preserves_suffix >> simp[can_step_def] >>
          qexistsl_tac [`P`, `[(G, id_track G)]`, `env`, `n1`, `failed`] >>
          simp[push_stack_def, can_step_def] >> drule wf_program_FEVERY >> simp[])
      >- (sg `NRC (step env) n1 (running P, [(G, id_track G)]) (failed, S'')`
          >- (match_mp_tac NRC_step_inverse_frame >> simp[can_step_def] >>
              drule wf_program_FEVERY >> strip_tac >>
              qexists_tac `[(G, id_track G)]` >> simp[push_stack_def] >> gvs[])
          >- (`steps env (running P, [(G, id_track G)]) (failed, S'')` by
                (simp[steps_def] >> irule NRC_RTC >> qexists_tac `n1` >> simp[]) >>
              `(?H mH. (failed, S'') = (final,[(H,mH)]) /\ Q H (compose_morphism mH m0)) \/
               (failed, S'') = (failed,[(G,id_track G)])` by
                (first_x_assum (qspecl_then [`G`, `m0`, `(failed, S'')`] mp_tac) >>
                 simp[can_step_def])
              >- gvs[]
              >- (gvs[push_stack_def, stackTheory.pop_stack_def] >>
                  qexistsl_tac [`(G, id_track G)`, `n1`, `n2`] >> simp[]))))
  (* Case 3: P breaks - contradictory since body spec doesn't allow break *)
  >- (gvs[Abbr `S1`, Abbr `S0`, push_stack_def, stackTheory.pop2_stack_def] >>
      Cases_on `S'` >> gvs[stackTheory.pop2_stack_def] >>
      Cases_on `t` >> gvs[stackTheory.pop2_stack_def] >> fs[] >>
      sg `LENGTH (h'::h''::t') = LENGTH [(G,id_track G); (G,id_track G)]`
      >- (irule no_intermediate_terms_preserves_stack_length >>
          qexistsl_tac [`P`, `env`, `n1`, `running term_break`] >> simp[] >>
          drule wf_program_FEVERY >> simp[])
      >- (gvs[] >>
          sg `h'' = (G, id_track G)`
          >- (drule_at (Pat `NRC _ _`) no_intermediate_terms_preserves_stack_tail >>
              simp[] >> drule wf_program_FEVERY >> simp[])
          >- (gvs[] >>
              sg `NRC (step env) n1 (running P, [(G,id_track G)]) (running term_break, [h'])`
              >- (match_mp_tac NRC_step_inverse_frame >> simp[can_step_def] >>
                  drule wf_program_FEVERY >> strip_tac >>
                  qexists_tac `[(G,id_track G)]` >> simp[])
              >- (sg `~can_step (running term_break, [h'])`
                  >- simp[can_step_state_only, can_step_def]
                  >- (`steps env (running P, [(G,id_track G)]) (running term_break, [h'])` by
                        (simp[steps_def] >> irule NRC_RTC >> qexists_tac `n1` >> simp[]) >>
                      `(?H mH. (running term_break, [h']) = (final,[(H,mH)]) /\
                               Q H (compose_morphism mH m0)) \/
                       (running term_break, [h']) = (failed,[(G,id_track G)])` by
                        (first_x_assum (qspecl_then [`G`, `m0`, `(running term_break, [h'])`]
                           mp_tac) >> simp[])
                      >- gvs[]
                      >- gvs[])))))
QED

(* Main theorem: WSPEC for ALAP with termination condition *)
Theorem WSPEC_alap_with_termination:
  !env P Q R.
    (* Body preserves Q when it succeeds, or fails cleanly *)
    (!G m. WSPEC env
             (\H. H = G /\ Q G m)
             P
             (\H' m'. Q H' (compose_morphism m' m))) /\
    (* When body fails, R holds on the current graph *)
    (!G m. wf_hostgraph G /\ Q G m /\
           steps env (running P, [(G, id_track G)]) (failed, [(G, id_track G)]) ==>
           R G m) /\
    (* Q implies morphism well-formedness *)
    (!G m. Q G m ==> FRANGE m.nodemap SUBSET G.V /\ FRANGE m.edgemap SUBSET G.E)
    ==>
    !m0. WSPEC env
           (\G. Q G m0)
           (term_alap P)
           (\H m. Q H (compose_morphism m m0) /\ R H (compose_morphism m m0))
Proof
  rw[WSPEC_def] >> rpt strip_tac
  >- (first_x_assum (qspecl_then [`ARB`, `ARB`] strip_assume_tac) >>
      gvs[no_intermediate_terms_def])
  >- (
    `?n. NRC (step env) n (running (term_alap P), [(G, id_track G)]) c`
      by metis_tac[steps_NRC] >>
    `wf_program env /\ no_intermediate_terms P` by
      (first_x_assum (qspecl_then [`ARB`, `ARB`] strip_assume_tac) >> simp[]) >>
    (* Body either succeeds with Q preserved, or fails *)
    sg `!G' m' c'. wf_hostgraph G' /\ Q G' m' /\
                   steps env (running P,[(G',id_track G')]) c' /\ ~can_step c' ==>
                   (?H mH. c' = (final,[(H,mH)]) /\ Q H (compose_morphism mH m')) \/
                   (c' = (failed, [(G', id_track G')]))`
    >- (rpt strip_tac >>
        qpat_x_assum `!G m. wf_program env /\ no_intermediate_terms P /\ _`
          (qspecl_then [`G'`, `m'`] mp_tac) >>
        strip_tac >>
        Cases_on `c'` >> Cases_on `q`
        (* running case - contradiction via can_step *)
        >- (Cases_on `t` >> gvs[can_step_def])
        (* final case - use WSPEC assumption *)
        >- (first_x_assum (qspec_then `(final, r)` mp_tac) >> simp[can_step_def])
        (* failed case - contradiction via WSPEC assumption which says P always succeeds *)
        >- (first_x_assum (qspec_then `(failed, r)` mp_tac) >> simp[can_step_def]))
    >- (irule WSPEC_alap_with_termination_helper >> simp[] >> metis_tac[]))
QED

(* WSPEC for ALAP where body can fail.
   Unlike WSPEC_alap_with_termination which requires WSPEC for the body
   (implying body always succeeds), this version allows the body to fail.

   The first premise is a disjunction: body either succeeds (final with Q)
   or fails atomically. This is weaker than WSPEC which requires only success.

   When the body fails, the loop terminates and R must hold.
   The postcondition is Q ∧ R, giving both invariant preservation and
   the termination property. *)
Theorem WSPEC_alap_allowing_failure:
  !env P Q R.
    wf_program env /\
    no_intermediate_terms P /\
    (* Body either succeeds with Q, or fails atomically *)
    (!G m c. wf_hostgraph G /\ Q G m /\
             steps env (running P, [(G, id_track G)]) c /\ ~can_step c ==>
             (?H mH. c = (final, [(H, mH)]) /\ Q H (compose_morphism mH m)) \/
             (c = (failed, [(G, id_track G)]))) /\
    (* When body fails, R holds on current graph *)
    (!G m. wf_hostgraph G /\ Q G m /\
           steps env (running P, [(G, id_track G)]) (failed, [(G, id_track G)]) ==>
           R G m) /\
    (* Q implies morphism well-formedness *)
    (!G m. Q G m ==> FRANGE m.nodemap SUBSET G.V /\ FRANGE m.edgemap SUBSET G.E)
    ==>
    !m0. WSPEC env
           (\G. Q G m0)
           (term_alap P)
           (\H m. Q H (compose_morphism m m0) /\ R H (compose_morphism m m0))
Proof
  rw[WSPEC_def] >> rpt strip_tac
  >- simp[no_intermediate_terms_def]
  >- (
    `?n. NRC (step env) n (running (term_alap P), [(G, id_track G)]) c`
      by metis_tac[steps_NRC] >>
    irule WSPEC_alap_with_termination_helper >> simp[] >>
    qexistsl_tac [`G`, `P`, `env`, `n`] >> simp[] >> metis_tac[])
QED

val () = export_theory ()
