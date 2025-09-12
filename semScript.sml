open HolKernel boolLib bossLib alistTheory listTheory finite_mapTheory
open programTheory graphTheory hostgraphTheory stackTheory dpoTheory rulegraphTheory taggingTheory
open ruleTheory morphismTheory trackTheory
open relationTheory arithmeticTheory rich_listTheory
open quantHeuristicsTheory quantHeuristicsLib

val () = new_theory "sem"

Definition agree_on_common_keys_def:
  agree_on_common_keys f1 f2 <=> !x. x IN (FDOM f1 INTER FDOM f2) ==> FLOOKUP f1 x = FLOOKUP f2 x
End


Type assignment = ``:varname |-> hostgraph$label``;


(* Label semantics *)

monadsyntax.enable_monadsyntax();
monadsyntax.enable_monad "option";

Inductive eval_label:
[~ConstInt:]
  !a m G i.
    eval_label (a:assignment, m:morphism, G:hostgraph, rulegraph$label_integer i) ((label_integer i):hostgraph$label)

[~ConstString:]
  !a m G s.
    eval_label (a, m, G, rulegraph$label_string s) (label_string s)

[~ConstChar:]
  !a m G c.
    eval_label (a, m, G, rulegraph$label_char c) (label_char c)

[~Nil:]
  !a m G.
    eval_label (a, m, G, rulegraph$label_nil) label_nil

[~VarBound:]
  !a m G v l.
    FLOOKUP a v = SOME l ==>
      eval_label (a, m, G, rulegraph$label_variable v) l

[~Outdeg:]
  !a m G n hn deg.
    FLOOKUP m.nodemap n = SOME hn /\
    count_outgoing_edges G hn = SOME deg ==>
    eval_label (a, m, G, rulegraph$label_outdeg n) (label_integer (int_of_num deg))

[~Indeg:]
  !a m G n hn deg.
    FLOOKUP m.nodemap n = SOME hn /\
    count_incoming_edges G hn = SOME deg ==>
    eval_label (a, m, G, rulegraph$label_indeg n) (label_integer (int_of_num deg))

[~LengthInt:]
  !a m G v i.
    FLOOKUP a v = SOME (label_integer i) ==>
    eval_label (a, m, G, rulegraph$label_length v) (label_integer 1)

[~LengthString:]
  !a m G v s.
    FLOOKUP a v = SOME (label_string s) ==>
    eval_label (a, m, G, rulegraph$label_length v) (label_integer (int_of_num (LENGTH s)))

[~LengthChar:]
  !a m G v c.
    FLOOKUP a v = SOME (label_char c) ==>
    eval_label (a, m, G, rulegraph$label_length v) (label_integer 1)

(* Arithmetic Operations *)
[~Add:]
  !a m G l1 l2 i1 i2.
    eval_label (a, m, G, l1) (label_integer i1) /\
    eval_label (a, m, G, l2) (label_integer i2) ==>
    eval_label (a, m, G, rulegraph$label_add l1 l2) (label_integer (i1 + i2))

[~Sub:]
  !a m G l1 l2 i1 i2.
    eval_label (a, m, G, l1) (label_integer i1) /\
    eval_label (a, m, G, l2) (label_integer i2) ==>
    eval_label (a, m, G, rulegraph$label_sub l1 l2) (label_integer (i1 - i2))

[~Mult:]
  !a m G l1 l2 i1 i2.
    eval_label (a, m, G, l1) (label_integer i1) /\
    eval_label (a, m, G, l2) (label_integer i2) ==>
    eval_label (a, m, G, rulegraph$label_mult l1 l2) (label_integer (i1 * i2))

[~Div:]
  !a m G l1 l2 i1 i2.
    i2 <> 0 ∧
    eval_label (a, m, G, l1) (label_integer i1) /\
    eval_label (a, m, G, l2) (label_integer i2) ==>
    eval_label (a, m, G, rulegraph$label_div l1 l2) (label_integer (i1 / i2))

[~Negate:]
  !a m G l i.
    eval_label (a, m, G, l) (label_integer i) ==>
    eval_label (a, m, G, rulegraph$label_negate l) (label_integer (~i))

[~Concat:]
  !a m G l1 l2 s1 s2.
    eval_label (a, m, G, l1) (label_string s1) /\
    eval_label (a, m, G, l2) (label_string s2) ==>
    eval_label (a, m, G, rulegraph$label_concat l1 l2) (label_string (s1 ++ s2))

[~Empty:]
  !a m G.
    eval_label (a, m, G, rulegraph$label_nil) label_nil

(* Use label_append to splice list values instead of wrapping *)
[~Cons:]
  !a m G l1 l2 v1 v2.
    eval_label (a, m, G, l1) v1 /\
    eval_label (a, m, G, l2) v2 ==>
    eval_label (a, m, G, rulegraph$label_cons l1 l2) (label_append v1 v2)
End

Theorem eval_label_rewrites:
 (!a m G i. eval_label (a,m,G,label_integer i) expr <=> expr = label_integer i) /\
 (!a m G s. eval_label (a,m,G,label_string s) expr <=> expr = label_string s) /\
 (!a m G c. eval_label (a,m,G,label_char c) expr <=> expr = label_char c) /\
 (!a m G. eval_label (a,m,G,label_nil) expr <=> expr = label_nil) /\
 (!a m G v. eval_label (a,m,G,label_variable v) expr <=> FLOOKUP a v = SOME expr) /\
 (!a m G n. eval_label (a,m,G,label_outdeg n) expr <=> SOME expr = do
  hn <- FLOOKUP m.nodemap n;
  deg <- count_outgoing_edges G hn;
  return (label_integer (int_of_num deg))
  od) /\
(!a m G n. eval_label (a,m,G,label_indeg n) expr <=> SOME expr = do
  hn <- FLOOKUP m.nodemap n;
  deg <- count_incoming_edges G hn;
  return (label_integer (int_of_num deg))
  od)
Proof
  rpt conj_tac
  \\ CONV_TAC (STRIP_QUANT_CONV $ LHS_CONV (ONCE_REWRITE_CONV [eval_label_cases]))
  \\ gvs[count_outgoing_edges_def]
  \\ metis_tac[]
QED

(* Arithmetic on labels. Operates on bare atoms as intermediate values. *)
Definition eval_arith_def:
  eval_arith (f: int -> int -> int option) (hostgraph$label_integer a) (hostgraph$label_integer b) =
    OPTION_MAP hostgraph$label_integer (f a b) /\
  eval_arith f a b = NONE
End

(* String concatenation on bare atom intermediate values. *)
Definition eval_string_concat_def:
  eval_string_concat (hostgraph$label_string a) (hostgraph$label_string b) =
    SOME (hostgraph$label_string (a ++ b)) /\
  eval_string_concat a b = NONE
End

(* Evaluate rule labels to host labels.
   Atomic expressions produce bare atoms as INTERMEDIATE values.
   The label_cons case uses label_append which wraps atoms to produce spine-form results.
   Parser-produced rule labels always have outer label_cons, so final results are spines. *)
Definition eval_label_fun_def:
  eval_label_fun a m G (rulegraph$label_integer i) = SOME (hostgraph$label_integer i) /\
  eval_label_fun a m G (rulegraph$label_string s) = SOME (label_string s) /\
  eval_label_fun a m G (rulegraph$label_char c) = SOME (label_char c) /\
  eval_label_fun a m G rulegraph$label_nil = SOME label_nil /\
  eval_label_fun a m G (rulegraph$label_variable v) = FLOOKUP a v /\
  eval_label_fun a m G (rulegraph$label_outdeg n) =
    do
      hn <- FLOOKUP m.nodemap n;
      deg <- count_outgoing_edges G hn;
      return (label_integer (int_of_num deg))
    od /\

  eval_label_fun a m G (rulegraph$label_indeg n) =
    do
      hn <- FLOOKUP m.nodemap n;
      deg <- count_incoming_edges G hn;
      return (label_integer (int_of_num deg))
    od /\

  eval_label_fun a m G (rulegraph$label_length v) =
    (case FLOOKUP a v of
       SOME (label_integer i) => SOME (label_integer 1)
     | SOME (label_string s) => SOME (label_integer (int_of_num (LENGTH s)))
     | SOME (label_char c) => SOME (label_integer 1)
     | _ => NONE) /\

  eval_label_fun a m G (rulegraph$label_add l1 l2) =
    do
      i1 <- eval_label_fun a m G l1;
      i2 <- eval_label_fun a m G l2;
      eval_arith (\a b. SOME (a + b)) i1 i2
    od /\

  eval_label_fun a m G (rulegraph$label_sub l1 l2) =
    do
      i1 <- eval_label_fun a m G l1;
      i2 <- eval_label_fun a m G l2;
      eval_arith (\a b. SOME (a - b)) i1 i2
    od /\

  eval_label_fun a m G (rulegraph$label_mult l1 l2) =
    do
      i1 <- eval_label_fun a m G l1;
      i2 <- eval_label_fun a m G l2;
      eval_arith (\a b. SOME (a * b)) i1 i2
    od /\

  eval_label_fun a m G (rulegraph$label_div l1 l2) =
    do
      i1 <- eval_label_fun a m G l1;
      i2 <- eval_label_fun a m G l2;
      eval_arith (\a b. if b = 0 then NONE else SOME (a / b)) i1 i2
    od /\

  eval_label_fun a m G (rulegraph$label_negate l) =
    do
      i <- eval_label_fun a m G l;
      eval_arith (\a b. SOME (a * b)) i (hostgraph$label_integer $ -1)
    od /\

  eval_label_fun a m G (rulegraph$label_concat l1 l2) =
    do
      s1 <- eval_label_fun a m G l1;
      s2 <- eval_label_fun a m G l2;
      eval_string_concat s1 s2
    od /\

  (* Use label_append to splice list values instead of wrapping them.
     This ensures list-typed variables are properly spliced into the result. *)
  eval_label_fun a m G (rulegraph$label_cons l1 l2) =
    do
      v1 <- eval_label_fun a m G l1;
      v2 <- eval_label_fun a m G l2;
      return (label_append v1 v2)
    od
End

Theorem eval_label_fun_sem_labels_equiv:
  !a m G l v. eval_label_fun a m G l = SOME v <=> eval_label (a, m, G, l) v
Proof
  Induct_on `l`
  (* Constants: integer, string, char, nil *)
  >- (rpt strip_tac \\ fs[eval_label_fun_def, eval_label_rewrites] \\ metis_tac[])
  >- (rpt strip_tac \\ fs[eval_label_fun_def, eval_label_rewrites] \\ metis_tac[])
  >- (rpt strip_tac \\ fs[eval_label_fun_def, eval_label_rewrites] \\ metis_tac[])
  >- (rpt strip_tac \\ fs[eval_label_fun_def, eval_label_rewrites] \\ metis_tac[])
  (* label_cons *)
  >- (rpt strip_tac \\ fs[eval_label_fun_def] \\ EQ_TAC
      >- (rw[] \\ irule eval_label_Cons \\ metis_tac[])
      >- (rw[Once eval_label_cases] \\ metis_tac[]))
  (* label_variable *)
  >- (rpt strip_tac \\ fs[eval_label_fun_def, eval_label_rewrites])
  (* label_indeg *)
  >- (rpt strip_tac \\ fs[eval_label_fun_def, eval_label_rewrites] \\ metis_tac[])
  (* label_outdeg *)
  >- (rpt strip_tac \\ fs[eval_label_fun_def, eval_label_rewrites] \\ metis_tac[])
  (* label_length *)
  >- (rpt strip_tac \\ fs[eval_label_fun_def] \\ EQ_TAC
      >- (Cases_on `FLOOKUP a v` \\ fs[] \\ Cases_on `x` \\ fs[] \\ rw[]
          \\ simp[Once eval_label_cases])
      >- (simp[Once eval_label_cases] \\ rpt strip_tac \\ gvs[]))
  (* label_add *)
  >- (rpt strip_tac \\ fs[eval_label_fun_def, eval_arith_def] \\ EQ_TAC
      >- (rpt strip_tac \\ Cases_on `i1` \\ Cases_on `i2` \\ gvs[eval_arith_def]
          \\ irule eval_label_Add \\ metis_tac[])
      >- (simp[Once eval_label_cases] \\ rpt strip_tac \\ gvs[eval_arith_def]
          \\ qexists_tac `label_integer i1` \\ simp[]
          \\ qexists_tac `label_integer i2` \\ simp[eval_arith_def]))
  (* label_sub *)
  >- (rpt strip_tac \\ fs[eval_label_fun_def, eval_arith_def] \\ EQ_TAC
      >- (rpt strip_tac \\ Cases_on `i1` \\ Cases_on `i2` \\ gvs[eval_arith_def]
          \\ irule eval_label_Sub \\ metis_tac[])
      >- (simp[Once eval_label_cases] \\ rpt strip_tac \\ gvs[eval_arith_def]
          \\ qexists_tac `label_integer i1` \\ simp[]
          \\ qexists_tac `label_integer i2` \\ simp[eval_arith_def]))
  (* label_mult *)
  >- (rpt strip_tac \\ fs[eval_label_fun_def, eval_arith_def] \\ EQ_TAC
      >- (rpt strip_tac \\ Cases_on `i1` \\ Cases_on `i2` \\ gvs[eval_arith_def]
          \\ irule eval_label_Mult \\ metis_tac[])
      >- (simp[Once eval_label_cases] \\ rpt strip_tac \\ gvs[eval_arith_def]
          \\ qexists_tac `label_integer i1` \\ simp[]
          \\ qexists_tac `label_integer i2` \\ simp[eval_arith_def]))
  (* label_div *)
  >- (rpt strip_tac \\ fs[eval_label_fun_def, eval_arith_def] \\ EQ_TAC
      >- (rpt strip_tac \\ Cases_on `i1` \\ Cases_on `i2`
          \\ gvs[eval_arith_def, AllCaseEqs()]
          \\ irule eval_label_Div \\ metis_tac[])
      >- (simp[Once eval_label_cases] \\ rpt strip_tac \\ gvs[eval_arith_def]
          \\ qexists_tac `label_integer i1` \\ simp[]
          \\ qexists_tac `label_integer i2` \\ simp[eval_arith_def]))
  (* label_concat *)
  >- (rpt strip_tac \\ fs[eval_label_fun_def, eval_string_concat_def] \\ EQ_TAC
      >- (rpt strip_tac \\ Cases_on `s1` \\ Cases_on `s2`
          \\ gvs[eval_string_concat_def]
          \\ irule eval_label_Concat \\ metis_tac[])
      >- (simp[Once eval_label_cases] \\ rpt strip_tac \\ gvs[eval_string_concat_def]
          \\ qexists_tac `label_string s1` \\ simp[]
          \\ qexists_tac `label_string s2` \\ simp[eval_string_concat_def]))
  (* label_negate *)
  >- (rpt strip_tac \\ fs[eval_label_fun_def, eval_arith_def] \\ EQ_TAC
      >- (rpt strip_tac \\ Cases_on `i` \\ gvs[eval_arith_def]
          \\ simp[Once integerTheory.INT_MUL_COMM, GSYM integerTheory.INT_NEG_MINUS1]
          \\ irule eval_label_Negate \\ metis_tac[])
      >- (simp[Once eval_label_cases] \\ rpt strip_tac \\ gvs[eval_arith_def]
          \\ qexists_tac `label_integer i` \\ simp[eval_arith_def]
          \\ simp[Once integerTheory.INT_MUL_COMM, GSYM integerTheory.INT_NEG_MINUS1]))
QED

(* Condition semantics *)

Definition eval_comparison_def:
  eval_comparison (f: int -> int -> bool) (hostgraph$label_integer a) (hostgraph$label_integer b) = SOME (f a b) /\
  eval_comparison f a b = NONE
End

Definition edgemark_matches_def:
  edgemark_matches (hm:hostgraph$edgemark option) (rm:rulegraph$edgemark option) <=>
    case rm of
      NONE => hm = NONE |
      SOME m => case m of
        edgemark_any => T |
        edgemark_red => hm = SOME hostgraph$edgemark_red |
        edgemark_green => hm = SOME hostgraph$edgemark_green |
        edgemark_blue => hm = SOME hostgraph$edgemark_blue |
        edgemark_dashed => hm = SOME hostgraph$edgemark_dashed
End

Inductive eval_condition:
[~edgeTest:]
  !assign pre G s t r.
    (r <=> ?e.
      e IN G.E /\
      FLOOKUP G.s e = FLOOKUP pre.nodemap s /\
      FLOOKUP G.t e = FLOOKUP pre.nodemap t)
     ==> eval_condition (assign:assignment, pre, G, condEdgeTest s t NONE) r

[~edgeTestLabel:]
  !assign pre G s t l m r.
    (r <=> ?e l' gl gm.
      e IN G.E /\
      FLOOKUP G.s e = FLOOKUP pre.nodemap s /\
      FLOOKUP G.t e = FLOOKUP pre.nodemap t /\
      eval_label (assign,pre,G,l) l' /\
      FLOOKUP G.m e = SOME (gl, gm) /\
      l' = gl /\
      edgemark_matches gm m)
     ==> eval_condition (assign:assignment, pre, G, condEdgeTest s t (SOME (l,m))) r

[~subType:]
  !assign pre G ty var r.
    (r <=> ?l ty'. FLOOKUP assign var = SOME l /\
           hostgraph$label_typeof l = ty' /\
           is_subtype_of ty' ty) ==>
    eval_condition (assign, pre, G, condSubtype ty var) r

[~condLabelEq:]
  !assign pre G la lb la' lb'.
    eval_label (assign, pre, G, la:rulegraph$label) (la':hostgraph$label) /\
    eval_label (assign, pre, G, lb:rulegraph$label) (lb':hostgraph$label) ==>
    eval_condition (assign:assignment, pre, G, condLabelEq la lb) (la' = lb')

[~condLabelNeq:]
  !assign pre G la lb la' lb'.
    eval_label (assign, pre, G, la:rulegraph$label) (la':hostgraph$label) /\
    eval_label (assign, pre, G, lb:rulegraph$label) (lb':hostgraph$label) ==>
    eval_condition (assign, pre, G, condLabelNeq la lb) (la' <> lb')

[~condLabelGt:]
  !assign pre G la lb la' lb' v1 v2.
    eval_label (assign, pre, G, la:rulegraph$label) (la':hostgraph$label) /\
    eval_label (assign, pre, G, lb:rulegraph$label) (lb':hostgraph$label) /\
    hostgraph$label_typeof la' = tyInt /\
    hostgraph$label_typeof lb' = tyInt /\
    la' = hostgraph$label_integer v1 /\
    lb' = hostgraph$label_integer v2 ==>
    eval_condition (assign, pre, G, condGt la lb) (v1 > v2)

[~condLabelGteq:]
  !assign pre G la lb la' lb' v1 v2.
    eval_label (assign, pre, G, la:rulegraph$label) (la':hostgraph$label) /\
    eval_label (assign, pre, G, lb:rulegraph$label) (lb':hostgraph$label) /\
    hostgraph$label_typeof la' = tyInt /\
    hostgraph$label_typeof lb' = tyInt /\
    la' = hostgraph$label_integer v1 /\
    lb' = hostgraph$label_integer v2 ==>
    eval_condition (assign, pre, G, condGteq la lb) (v1 >= v2)

[~condLabelLt:]
  !assign pre G la lb la' lb' v1 v2.
    eval_label (assign, pre, G, la:rulegraph$label) (la':hostgraph$label) /\
    eval_label (assign, pre, G, lb:rulegraph$label) (lb':hostgraph$label) /\
    hostgraph$label_typeof la' = tyInt /\
    hostgraph$label_typeof lb' = tyInt /\
    la' = hostgraph$label_integer v1 /\
    lb' = hostgraph$label_integer v2 ==>
    eval_condition (assign, pre, G, condLt la lb) (v1 < v2)

[~condLabelLteq:]
  !assign pre G la lb la' lb' v1 v2.
    eval_label (assign, pre, G, la:rulegraph$label) (la':hostgraph$label) /\
    eval_label (assign, pre, G, lb:rulegraph$label) (lb':hostgraph$label) /\
    hostgraph$label_typeof la' = tyInt /\
    hostgraph$label_typeof lb' = tyInt /\
    la' = hostgraph$label_integer v1 /\
    lb' = hostgraph$label_integer v2 ==>
    eval_condition (assign, pre, G, condLteq la lb) (v1 <= v2)

[~condAnd:]
  !assign pre G ca cb ra rb.
    eval_condition (assign, pre, G, ca) ra /\
    eval_condition (assign, pre, G, cb) rb ==>
    eval_condition (assign, pre, G, condAnd ca cb) (ra /\ rb)

[~condOr:]
  !assign pre G ca cb ra rb.
    eval_condition (assign, pre, G, ca) ra /\
    eval_condition (assign, pre, G, cb) rb ==>
    eval_condition (assign, pre, G, condOr ca cb) (ra \/ rb)

[~condNot:]
  !assign pre G c t.
    eval_condition (assign, pre, G, c) t ==>
    eval_condition (assign, pre, G, condNot c) (~t)
End


Definition eval_condition_fun_def:
  eval_condition_fun (assign:assignment) (m: morphism) (G:hostgraph) (condEdgeTest s t opt) =
    SOME (case opt of
       NONE =>
         EXISTS (\e.
           FLOOKUP G.s e = FLOOKUP m.nodemap s /\
           FLOOKUP G.t e = FLOOKUP m.nodemap t) (SET_TO_LIST G.E)
     | SOME (l, mark) =>
         EXISTS (\e.
           FLOOKUP G.s e = FLOOKUP m.nodemap s /\
           FLOOKUP G.t e = FLOOKUP m.nodemap t /\
           (case (eval_label_fun assign m G l, FLOOKUP G.m e) of
              (SOME l', SOME (gl, gm)) => l' = gl /\ edgemark_matches gm mark
            | _ => F)) (SET_TO_LIST G.E)) /\

  eval_condition_fun (assign:assignment) (m: morphism) (G:hostgraph) (condSubtype ty var) =
    SOME (case FLOOKUP assign var of
      NONE => F |
      SOME l => is_subtype_of (hostgraph$label_typeof l) ty) /\

  eval_condition_fun (assign:assignment) (m: morphism) (G:hostgraph) (condLabelEq la lb) =
    do
      la' <- eval_label_fun assign m G la;
      lb' <- eval_label_fun assign m G lb;
      return (la' = lb')
    od /\

  eval_condition_fun (assign:assignment) (m: morphism) (G:hostgraph) (condLabelNeq la lb) =
    do
      la' <- eval_label_fun assign m G la;
      lb' <- eval_label_fun assign m G lb;
      return (la' <> lb')
    od /\

  eval_condition_fun (assign:assignment) (m: morphism) (G:hostgraph) (condGt la lb) =
    do
      la' <- eval_label_fun assign m G la;
      lb' <- eval_label_fun assign m G lb;
      eval_comparison (>) la' lb'
    od /\

  eval_condition_fun (assign:assignment) (m: morphism) (G:hostgraph) (condGteq la lb) =
    do
      la' <- eval_label_fun assign m G la;
      lb' <- eval_label_fun assign m G lb;
      eval_comparison (>=) la' lb'
    od /\

  eval_condition_fun (assign:assignment) (m: morphism) (G:hostgraph) (condLt la lb) =
    do
      la' <- eval_label_fun assign m G la;
      lb' <- eval_label_fun assign m G lb;
      eval_comparison (<) la' lb'
    od /\

  eval_condition_fun (assign:assignment) (m: morphism) (G:hostgraph) (condLteq la lb) =
    do
      la' <- eval_label_fun assign m G la;
      lb' <- eval_label_fun assign m G lb;
      eval_comparison (<=) la' lb'
    od /\

eval_condition_fun (assign:assignment) (m: morphism) (G:hostgraph) (condAnd ca cb) =
  do
    ra <- eval_condition_fun assign m G ca;
    rb <- eval_condition_fun assign m G cb;
    return (ra /\ rb)
  od /\

eval_condition_fun (assign:assignment) (m: morphism) (G:hostgraph) (condOr ca cb) =
  do
    ra <- eval_condition_fun assign m G ca;
    rb <- eval_condition_fun assign m G cb;
    return (ra \/ rb)
  od /\

eval_condition_fun (assign:assignment) (m: morphism) (G:hostgraph) (condNot c) =
  do
    r <- eval_condition_fun assign m G c;
    return (~r)
  od
End

Theorem eval_condition_fun_equiv:
  !assign m G c r.
    wf_hostgraph G ==>
    (eval_condition_fun (assign:assignment) (m:morphism) (G:hostgraph) (c:cond) = SOME r <=>
    eval_condition (assign,m,G,c) r)
Proof
  Induct_on `c` >> rpt strip_tac
  >- ((* condEdgeTest *)
      Cases_on `o'` >> simp[eval_condition_fun_def, Once eval_condition_cases] >>
      `FINITE G.E` by fs[wf_hostgraph_def, wf_graph_def] >>
      simp[EXISTS_MEM, MEM_SET_TO_LIST]
      >- metis_tac[]
      >- (Cases_on `x` >> simp[GSYM eval_label_fun_sem_labels_equiv] >>
          eq_tac >> rpt strip_tac >> gvs[]
          >- (eq_tac >> rpt strip_tac >> gvs[AllCaseEqs()]
              >- (qpat_x_assum `case _ of _ => _` mp_tac >>
                  Cases_on `eval_label_fun assign m G q` >> simp[] >>
                  Cases_on `FLOOKUP G.m e` >> simp[] >>
                  Cases_on `x'` >> simp[] >> strip_tac >>
                  qexistsl_tac [`e`, `r`] >> simp[])
              >- (qexists_tac `e` >> simp[]))
          >- (Cases_on `eval_label_fun assign m G q`
              >- simp[]
              >- (simp[] >> eq_tac >> rpt strip_tac >> gvs[AllCaseEqs()]
                  >- (qpat_x_assum `case _ of _ => _` mp_tac >>
                      Cases_on `FLOOKUP G.m e` >> simp[] >>
                      Cases_on `x'` >> simp[] >> strip_tac >>
                      qexistsl_tac [`e`, `r`] >> simp[])
                  >- (qexists_tac `e` >> simp[])))))
  >- ((* condSubtype *)
      simp[eval_condition_fun_def, Once eval_condition_cases] >>
      Cases_on `FLOOKUP assign v` >> simp[] >> metis_tac[])
  >- ((* condLabelEq *)
      simp[eval_condition_fun_def, Once eval_condition_cases,
           GSYM eval_label_fun_sem_labels_equiv] >> metis_tac[])
  >- ((* condLabelNeq *)
      simp[eval_condition_fun_def, Once eval_condition_cases,
           GSYM eval_label_fun_sem_labels_equiv] >> metis_tac[])
  >- ((* condGt *)
      simp[eval_condition_fun_def, Once eval_condition_cases,
           GSYM eval_label_fun_sem_labels_equiv, eval_comparison_def] >>
      eq_tac >> rpt strip_tac >>
      gvs[AllCaseEqs(), eval_comparison_def, hostgraphTheory.label_typeof_def] >>
      Cases_on `la'` >> Cases_on `lb'` >> gvs[eval_comparison_def])
  >- ((* condGteq *)
      simp[eval_condition_fun_def, Once eval_condition_cases,
           GSYM eval_label_fun_sem_labels_equiv, eval_comparison_def] >>
      eq_tac >> rpt strip_tac >>
      gvs[AllCaseEqs(), eval_comparison_def, hostgraphTheory.label_typeof_def] >>
      Cases_on `la'` >> Cases_on `lb'` >> gvs[eval_comparison_def])
  >- ((* condLt *)
      simp[eval_condition_fun_def, Once eval_condition_cases,
           GSYM eval_label_fun_sem_labels_equiv, eval_comparison_def] >>
      eq_tac >> rpt strip_tac >>
      gvs[AllCaseEqs(), eval_comparison_def, hostgraphTheory.label_typeof_def] >>
      Cases_on `la'` >> Cases_on `lb'` >> gvs[eval_comparison_def])
  >- ((* condLteq *)
      simp[eval_condition_fun_def, Once eval_condition_cases,
           GSYM eval_label_fun_sem_labels_equiv, eval_comparison_def] >>
      eq_tac >> rpt strip_tac >>
      gvs[AllCaseEqs(), eval_comparison_def, hostgraphTheory.label_typeof_def] >>
      Cases_on `la'` >> Cases_on `lb'` >> gvs[eval_comparison_def])
  >- ((* condAnd *)
      simp[SimpLHS, Once eval_condition_fun_def] >>
      first_assum (qspecl_then [`assign`, `m`, `G`] (fn th => simp[th])) >>
      last_assum (qspecl_then [`assign`, `m`, `G`] (fn th => simp[th])) >>
      eq_tac
      >- (strip_tac >> simp[Once eval_condition_cases] >> metis_tac[])
      >- (strip_tac >> gvs[Once eval_condition_cases] >>
          pop_assum mp_tac >> simp[Once eval_condition_cases] >>
          strip_tac >> gvs[] >> metis_tac[]))
  >- ((* condOr *)
      simp[SimpLHS, Once eval_condition_fun_def] >>
      first_assum (qspecl_then [`assign`, `m`, `G`] (fn th => simp[th])) >>
      last_assum (qspecl_then [`assign`, `m`, `G`] (fn th => simp[th])) >>
      eq_tac >> strip_tac
      >- (simp[Once eval_condition_cases] >> metis_tac[])
      >- (pop_assum mp_tac >> simp[Once eval_condition_cases] >>
          strip_tac >> gvs[] >> metis_tac[]))
  >- ((* condNot *)
      simp[SimpLHS, Once eval_condition_fun_def] >>
      first_assum (qspecl_then [`assign`, `m`, `G`] (fn th => simp[th])) >>
      eq_tac
      >- (rpt strip_tac >> gvs[] >> simp[Once eval_condition_cases] >>
          qexists_tac `r'` >> simp[])
      >- (strip_tac >> pop_assum mp_tac >> simp[Once eval_condition_cases] >>
          strip_tac >> qexists_tac `t` >> simp[]))
QED

(* Program semantics *)

Datatype:
  state = running term | final | failed
End

Type stack[pp] = ``:hostgraph stack``
Type config[pp] = ``:state # stack``

(*
  is_final checks if the execution finished successfully. This implies
  that the resulting stack contains *a single* element.
*)
Definition is_final_def:
  is_final (running t, s) = F /\
  is_final (final, s) = is_singleton_stack s /\
  is_final (failed, s) = F
End


Definition is_failed_def:
  is_failed (running t, s) = F /\
  is_failed (final, s) = F /\
  is_failed (failed, s) = T
End


Definition can_step_def:
  can_step (running term_break, s) = F /\
  can_step (running t, s) = T /\
  can_step (final, s) = F /\
  can_step (failed, s) = F
End


Type RuleAppFn = ``:rule set -> hostgraph -> hostgraph option``


Datatype:
  ruleinstance = <| lhs: hostgraph; inf: nodeid set; rhs: hostgraph |>
End


Definition wf_ruleinstance_def:
  wf_ruleinstance ri <=>
    wf_hostgraph ri.lhs /\
    wf_hostgraph ri.rhs /\
    ri.inf SUBSET ri.lhs.V /\
    ri.inf SUBSET ri.rhs.V
End

Definition fmap_option_values_def:
  fmap_option_values f m =
    FOLDR (\(k,v) macc.
      case macc of
        NONE => NONE |
        SOME acc => case f k v of
          NONE => NONE |
          SOME v' => SOME (acc |+ (k,v')))
      (SOME FEMPTY)
      (fmap_to_alist m)
End


Definition eval_nodemark_def:
  eval_nodemark (hm:hostgraph$nodemark option) (rm:rulegraph$nodemark option): (hostgraph$nodemark option) option =
    case (rm, hm) of
      (NONE, NONE) => return NONE |
      (SOME nodemark_any, hm) => return hm |  (* "any" preserves host mark including NONE *)
      (SOME nodemark_red, SOME nodemark_red) => return (SOME nodemark_red) |
      (SOME nodemark_green, SOME nodemark_green) => return (SOME nodemark_green) |
      (SOME nodemark_blue, SOME nodemark_blue) => return (SOME nodemark_blue) |
      (SOME nodemark_grey, SOME nodemark_grey) => return (SOME nodemark_grey) |
      _ => fail
End

(* Helper: eval_nodemark preserves the host mark *)
Theorem eval_nodemark_preserves_hostmark:
  !hm rm res. eval_nodemark hm rm = SOME res ==> res = hm
Proof
  rpt strip_tac >> fs[eval_nodemark_def, AllCaseEqs()]
QED

(* Convert rule mark to host mark for NEW nodes (not matched from host graph).
   For new nodes, there's no host mark to look up, so we use the rule's mark directly.
   nodemark_any is not valid for new nodes since we can't infer a concrete mark. *)
Definition rule_to_host_nodemark_def:
  rule_to_host_nodemark (rm: rulegraph$nodemark option): (hostgraph$nodemark option) option =
    case rm of
      NONE => return NONE
    | SOME nodemark_red => return (SOME nodemark_red)
    | SOME nodemark_green => return (SOME nodemark_green)
    | SOME nodemark_blue => return (SOME nodemark_blue)
    | SOME nodemark_grey => return (SOME nodemark_grey)
    | SOME nodemark_any => fail  (* Can't create node with "any" mark *)
End

(* Instantiate a node's attributes from a rulegraph.
   For nodes in the morphism (matched nodes): combine host mark with rule mark.
   For new nodes (not in morphism): use rule mark directly. *)
Definition instantiate_nodeattr_def:
  instantiate_nodeattr (r:rulegraph) (assign: assignment) (m: morphism) (G:hostgraph) (nid:nodeid): hostgraph$nodeattr option = do
    (rl, rm) <- FLOOKUP r.l nid;
    l <- eval_label_fun assign m G rl;
    case FLOOKUP (G.l f_o_f m.nodemap) nid of
      SOME (_, hm) => do  (* Matched node: combine host mark with rule mark *)
        m <- eval_nodemark hm rm;
        return (l, m)
      od
    | NONE => do  (* New node: convert rule mark to host mark *)
        m <- rule_to_host_nodemark rm;
        return (l, m)
      od
  od
End

Definition eval_edgemark_def:
  eval_edgemark (hm:hostgraph$edgemark option) (rm:rulegraph$edgemark option): (hostgraph$edgemark option) option =
    case (rm, hm) of
      (NONE, NONE) => return NONE |
      (SOME edgemark_any, hm) => return hm |  (* "any" preserves host mark including NONE *)
      (SOME edgemark_red, SOME edgemark_red) => return (SOME edgemark_red) |
      (SOME edgemark_green, SOME edgemark_green) => return (SOME edgemark_green) |
      (SOME edgemark_blue, SOME edgemark_blue) => return (SOME edgemark_blue) |
      (SOME edgemark_dashed, SOME edgemark_dashed) => return (SOME edgemark_dashed) |
      _ => fail
End

(* Helper: eval_edgemark preserves the host mark *)
Theorem eval_edgemark_preserves_hostmark:
  !hm rm res. eval_edgemark hm rm = SOME res ==> res = hm
Proof
  rpt strip_tac >> fs[eval_edgemark_def, AllCaseEqs()]
QED

(* Convert rule mark to host mark for NEW edges (not matched from host graph).
   For new edges, there's no host mark to look up, so we use the rule's mark directly.
   edgemark_any is not valid for new edges since we can't infer a concrete mark. *)
Definition rule_to_host_edgemark_def:
  rule_to_host_edgemark (rm: rulegraph$edgemark option): (hostgraph$edgemark option) option =
    case rm of
      NONE => return NONE
    | SOME edgemark_red => return (SOME edgemark_red)
    | SOME edgemark_green => return (SOME edgemark_green)
    | SOME edgemark_blue => return (SOME edgemark_blue)
    | SOME edgemark_dashed => return (SOME edgemark_dashed)
    | SOME edgemark_any => fail  (* Can't create edge with "any" mark *)
End

(* Instantiate an edge's attributes from a rulegraph.
   For edges in the morphism (matched edges): combine host mark with rule mark.
   For new edges (not in morphism): use rule mark directly. *)
Definition instantiate_edgeattr_def:
  instantiate_edgeattr (r:rulegraph) (assign: assignment) (m: morphism) (G:hostgraph) (eid:edgeid): hostgraph$edgeattr option = do
    (rl, rm) <- FLOOKUP r.m eid;
    l <- eval_label_fun assign m G rl;
    case FLOOKUP (G.m f_o_f m.edgemap) eid of
      SOME (_, hm) => do  (* Matched edge: combine host mark with rule mark *)
        m <- eval_edgemark hm rm;
        return (l, m)
      od
    | NONE => do  (* New edge: convert rule mark to host mark *)
        m <- rule_to_host_edgemark rm;
        return (l, m)
      od
  od
End

Definition fmap_buildM_def:
  fmap_buildM (f: 'a -> 'b option) (ks: 'a set): ('a |-> 'b) option =
    FOLDR
      (\k acc.
         case acc of
           NONE => NONE
         | SOME acc' =>
             case f k of
               NONE => NONE
             | SOME v => SOME (acc' |+ (k, v)))
      (SOME FEMPTY)
      (SET_TO_LIST ks)
End

Theorem fmap_buildM_FDOM_helper:
  !f lst fm.
    FOLDR (\k acc. case acc of
             NONE => NONE
           | SOME acc' => case f k of
               NONE => NONE
             | SOME v => SOME (acc' |+ (k, v)))
          (SOME FEMPTY) lst = SOME fm
    ==> FDOM fm = set lst
Proof
  Induct_on `lst` >> rw[FOLDR] >> rpt strip_tac >>
  Cases_on `FOLDR (\k acc. case acc of
                     NONE => NONE
                   | SOME acc' => case f k of
                       NONE => NONE
                     | SOME v => SOME (acc' |+ (k, v)))
                  (SOME FEMPTY) lst` >> fs[] >>
  Cases_on `f h` >> fs[] >>
  `FDOM x = set lst` by metis_tac[] >>
  gvs[FDOM_FUPDATE]
QED

(* Key lemma: fmap_buildM produces maps with domain = input set. *)
Theorem fmap_buildM_FDOM:
  !f ks fm. FINITE ks /\ fmap_buildM f ks = SOME fm ==> FDOM fm = ks
Proof
  rw[fmap_buildM_def] >>
  drule fmap_buildM_FDOM_helper >>
  simp[SET_TO_LIST_INV]
QED

(* Helper: fmap_buildM gives FLOOKUP = f for each key in the input list *)
Theorem fmap_buildM_FLOOKUP_helper:
  !f l fm k.
    FOLDR (\k acc. case acc of NONE => NONE | SOME acc' =>
             case f k of NONE => NONE | SOME v => SOME (acc' |+ (k,v)))
           (SOME FEMPTY) l = SOME fm /\ MEM k l ==>
    FLOOKUP fm k = f k
Proof
  Induct_on `l` >- simp[] >>
  rpt gen_tac >> simp[FOLDR] >> strip_tac
  >- gvs[AllCaseEqs(), FLOOKUP_UPDATE]
  >- (gvs[AllCaseEqs()] >> Cases_on `k = h`
      >- gvs[FLOOKUP_UPDATE]
      >- (simp[FLOOKUP_UPDATE] >>
          first_x_assum (qspecl_then [`f`, `acc'`, `k`] mp_tac) >> simp[]))
QED

(* fmap_buildM: FLOOKUP fm k = f k for each k in the input set *)
Theorem fmap_buildM_FLOOKUP:
  !f ks fm k. FINITE ks /\ fmap_buildM f ks = SOME fm /\ k IN ks ==>
    FLOOKUP fm k = f k
Proof
  rw[fmap_buildM_def] >>
  `MEM k (SET_TO_LIST ks)` by simp[SET_TO_LIST_INV] >>
  drule_all fmap_buildM_FLOOKUP_helper >> simp[]
QED

(* fmap_buildM succeeds when all element functions succeed *)
Theorem fmap_buildM_succeeds_helper:
  !f l. (!k. MEM k l ==> ?v. f k = SOME v) ==>
    ?fm. FOLDR (\k acc. case acc of NONE => NONE | SOME acc' =>
             case f k of NONE => NONE | SOME v => SOME (acc' |+ (k,v)))
           (SOME FEMPTY) l = SOME fm
Proof
  Induct_on `l` >> rw[FOLDR] >>
  `?v. f h = SOME v` by (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  `?fm. FOLDR (\k acc. case acc of NONE => NONE | SOME acc' =>
           case f k of NONE => NONE | SOME v => SOME (acc' |+ (k,v)))
         (SOME FEMPTY) l = SOME fm` by (first_x_assum irule >> simp[]) >>
  qexists_tac `fm |+ (h, v)` >> simp[]
QED

Theorem fmap_buildM_succeeds:
  !f ks. FINITE ks /\ (!k. k IN ks ==> ?v. f k = SOME v) ==>
    ?fm. fmap_buildM f ks = SOME fm
Proof
  rw[fmap_buildM_def] >>
  irule fmap_buildM_succeeds_helper >>
  rw[MEM_SET_TO_LIST]
QED

Definition instantiate_rulegraph_def:
    instantiate_rulegraph (r:rulegraph) (assign: assignment) (pre:morphism) (G:hostgraph): hostgraph option = do
      l <- fmap_buildM (instantiate_nodeattr r assign pre G) (FDOM r.l);
      m <- fmap_buildM (instantiate_edgeattr r assign pre G) (FDOM r.m);
      res <<- <| V := r.V; E := r.E; s := r.s; t := r.t; l := l; m := m; p := r.p|>;
      return res
    od
End


Definition eval_rule_condition_def:
  eval_rule_condition (r:rule) (assign:assignment) (pre:morphism) (G:hostgraph) =
    case r.cond of
      NONE => SOME T |
      SOME c => eval_condition_fun assign pre G c
End

Definition instantiate_rule_def:
  instantiate_rule (r:rule) (assign:assignment) (pre:morphism) (G:hostgraph) = do
      cond_result <- eval_rule_condition r assign pre G;
      assert cond_result;

      lhs' <- instantiate_rulegraph r.lhs assign pre G;
      rhs' <- instantiate_rulegraph r.rhs assign pre G;
      ri <<- (<| lhs := lhs'; inf := r.inf; rhs := rhs' |>):ruleinstance;
      return ri
    od
End


Definition nodemark_matches_def:
  nodemark_matches (hm:hostgraph$nodemark option) (rm:rulegraph$nodemark option) <=>
    case rm of
      NONE => hm = NONE |
      SOME m => case m of
        nodemark_any => T |
        nodemark_red => hm = SOME hostgraph$nodemark_red |
        nodemark_green => hm = SOME hostgraph$nodemark_green |
        nodemark_blue => hm = SOME hostgraph$nodemark_blue |
        nodemark_grey => hm = SOME hostgraph$nodemark_grey
End

Definition extend_assignment_def:
  extend_assignment (typing: varname |-> ty) (name: varname) (hl:hostgraph$label): assignment option = do
    ty <- FLOOKUP typing name;
    if is_subtype_of (label_typeof hl) ty
    then return (FEMPTY |+ (name, hl))
    else fail
  od
End

(* This should be valid, see simple expressions, in particular:
- is_simple_label1_def

TODO: Question: How to match `concat`?

*)
Definition unify_constant_labels_def:
  unify_constant_labels (x: 'a) (y: 'a): assignment option =
    if x = y then return FEMPTY else NONE
End

Definition merge_assignment_def:
  merge_assignment (a:assignment) (b: assignment): assignment option =
    if agree_on_common_keys a b
    then SOME (FUNION a b)
    else NONE
End

(* Helper: When maps agree on common keys, the right map is a submap of their FUNION.
   This is because FUNION prefers left values on overlap, but if they agree, the value
   at any overlapping key is the same as the right map's value. *)
Theorem SUBMAP_FUNION_agree_right:
  !f g. agree_on_common_keys f g ==> g SUBMAP FUNION f g
Proof
  rw[SUBMAP_DEF, FUNION_DEF, agree_on_common_keys_def] >>
  Cases_on `x IN FDOM f` >> simp[] >>
  `FLOOKUP f x = FLOOKUP g x` by (first_x_assum irule >> simp[]) >>
  gvs[FLOOKUP_DEF]
QED

Definition unify_label_def:
  unify_label (typing: varname |-> ty) (rl:rulegraph$label) (hl:hostgraph$label): assignment option =
    case (rl, hl) of

      (label_variable v, h) => extend_assignment typing v h |

      (label_nil, label_nil) => return FEMPTY |

      (label_cons r1 r2, label_cons h1 h2) =>
        (case r1 of

          (* Special case: list-typed variable in head position *)
          label_variable v =>
            do
              ty <- FLOOKUP typing v;
              if ty = tyList
              then
                do
                  r2len <<- count_labels r2;
                  hostlen <<- count_labels (label_cons h1 h2);
                  prefix_len <<- hostlen - r2len;
                  (prefix, suffix) <- split_label_list prefix_len (label_cons h1 h2);

                  a1 <- extend_assignment typing v prefix;
                  a2 <- unify_label typing r2 suffix;
                  merge_assignment a1 a2
                od
              else
                (* Fallback: variable not list-typed, treat as normal cons *)
                do
                  a1 <- unify_label typing r1 h1;
                  a2 <- unify_label typing r2 h2;
                  merge_assignment a1 a2
                od
            od |

          (* Normal case: recursive unify *)
          _ =>
            do
              a1 <- unify_label typing r1 h1;
              a2 <- unify_label typing r2 h2;
              merge_assignment a1 a2
            od
        ) |

    (* Constants *)
    (label_integer i1, label_integer i2) => unify_constant_labels i1 i2 |
    (label_char c1, label_char c2) => unify_constant_labels c1 c2 |
    (label_string s1, label_string s2) => unify_constant_labels s1 s2 |

    (* label_negate l1 evaluates to -(eval l1), so for it to equal h,
       we need eval l1 = -h. Thus we unify l1 with the negated h. *)
    (label_negate l1, label_integer i) => unify_label typing l1 (label_integer (~i)) |

    (* Case: rule has cons with list variable but host is empty.
       Per GP2 semantics (thesis Section on label matching), a list variable
       can match the empty list. E.g., pattern "x:nil" matches "nil" with x=nil. *)
    (label_cons (label_variable v) r2, label_nil) =>
      do
        ty <- FLOOKUP typing v;
        if ty = tyList
        then
          do
            a1 <- extend_assignment typing v label_nil;
            a2 <- unify_label typing r2 label_nil;
            merge_assignment a1 a2
          od
        else
          NONE
      od |

    _ => NONE
End

Definition unify_nodeattr_def:
  unify_nodeattr (typing: varname |-> ty) ((rl, rm):rulegraph$nodeattr) ((hl, hm):hostgraph$nodeattr): assignment option = do
    assert (nodemark_matches hm rm);
    unify_label typing rl hl
  od
End

Definition unify_edgeattr_def:
  unify_edgeattr (typing: varname |-> ty) ((rl, rm):rulegraph$edgeattr) ((hl, hm):hostgraph$edgeattr): assignment option = do
    assert (edgemark_matches hm rm);
    unify_label typing rl hl
  od
End

(* Helper: eval_label_fun is preserved under FUNION when evaluation succeeds on left side *)
Theorem eval_label_fun_FUNION_left:
  !rl a1 a2 m G hl.
    agree_on_common_keys a1 a2 /\
    eval_label_fun a1 m G rl = SOME hl ==>
    eval_label_fun (FUNION a1 a2) m G rl = SOME hl
Proof
  Induct_on `rl` >> rpt strip_tac >>
  gvs[eval_label_fun_def, FLOOKUP_FUNION, AllCaseEqs()]
  (* label_cons case - need to show label_append v1 v2 is preserved *)
  >- (first_x_assum (qspecl_then [`a1`, `a2`, `m`, `G`] mp_tac) >> simp[] >>
      strip_tac >>
      last_x_assum (qspecl_then [`a1`, `a2`, `m`, `G`] mp_tac) >> simp[])
  >> metis_tac[]
QED

(* Helper: eval_label_fun is preserved under FUNION when evaluation succeeds on right side *)
Theorem eval_label_fun_FUNION_right:
  !rl a1 a2 m G hl.
    agree_on_common_keys a1 a2 /\
    eval_label_fun a2 m G rl = SOME hl ==>
    eval_label_fun (FUNION a1 a2) m G rl = SOME hl
Proof
  Induct_on `rl` >> rpt strip_tac >>
  gvs[eval_label_fun_def, FLOOKUP_FUNION, AllCaseEqs()]
  (* label_cons case - need to show label_append v1 v2 is preserved - comes FIRST after gvs *)
  >- (first_x_assum (qspecl_then [`a1`, `a2`, `m`, `G`] mp_tac) >> simp[] >>
      strip_tac >>
      last_x_assum (qspecl_then [`a1`, `a2`, `m`, `G`] mp_tac) >> simp[])
  (* label_variable case *)
  >- (Cases_on `FLOOKUP a1 v` >> gvs[] >>
      fs[agree_on_common_keys_def] >>
      first_x_assum (qspec_then `v` mp_tac) >> gvs[IN_DEF, FLOOKUP_DEF])
  (* label_length cases *)
  >- (Cases_on `FLOOKUP a1 v` >> gvs[] >>
      fs[agree_on_common_keys_def, FLOOKUP_DEF] >>
      first_x_assum (qspec_then `v` mp_tac) >> simp[IN_DEF] >>
      gvs[] >> strip_tac >> `a1 ' v = label_integer i` by metis_tac[IN_DEF] >> gvs[])
  >- (Cases_on `FLOOKUP a1 v` >> gvs[] >>
      fs[agree_on_common_keys_def, FLOOKUP_DEF] >>
      first_x_assum (qspec_then `v` mp_tac) >> simp[IN_DEF] >> gvs[])
  >- (Cases_on `FLOOKUP a1 v` >> gvs[] >>
      fs[agree_on_common_keys_def, FLOOKUP_DEF] >>
      first_x_assum (qspec_then `v` mp_tac) >> simp[IN_DEF] >> gvs[])
  >> metis_tac[]
QED

(* Helper: SUBMAP implies agree_on_common_keys *)
Theorem SUBMAP_agree_on_common_keys:
  !a1 a2. a1 SUBMAP a2 ==> agree_on_common_keys a1 a2
Proof
  rpt strip_tac >> simp[agree_on_common_keys_def] >>
  rpt strip_tac >> fs[SUBMAP_DEF, FLOOKUP_DEF]
QED

(* Helper: eval_label_fun is preserved under SUBMAP.
   If a SUBMAP b and evaluation succeeds with a, it succeeds with b. *)
Theorem eval_label_fun_SUBMAP:
  !rl a b m G hl.
    a SUBMAP b /\ eval_label_fun a m G rl = SOME hl ==>
    eval_label_fun b m G rl = SOME hl
Proof
  Induct_on `rl`
  (* label_integer, label_string, label_char, label_nil - independent of assignment *)
  >- simp[eval_label_fun_def]
  >- simp[eval_label_fun_def]
  >- simp[eval_label_fun_def]
  >- simp[eval_label_fun_def]
  (* label_cons - uses IH for both parts *)
  >- (rpt strip_tac >> gvs[eval_label_fun_def] >> metis_tac[])
  (* label_variable - key case using FLOOKUP_SUBMAP *)
  >- (rpt strip_tac >> gvs[eval_label_fun_def] >> metis_tac[FLOOKUP_SUBMAP])
  (* label_indeg - independent of assignment, depends on morphism *)
  >- simp[eval_label_fun_def]
  (* label_outdeg - independent of assignment, depends on morphism *)
  >- simp[eval_label_fun_def]
  (* label_length - uses FLOOKUP_SUBMAP *)
  >- (rpt strip_tac >> gvs[eval_label_fun_def, AllCaseEqs()] >>
      imp_res_tac FLOOKUP_SUBMAP >> simp[])
  (* label_add - uses IH for both parts *)
  >- (rpt strip_tac >> gvs[eval_label_fun_def] >> metis_tac[])
  (* label_sub - uses IH for both parts *)
  >- (rpt strip_tac >> gvs[eval_label_fun_def] >> metis_tac[])
  (* label_mult - uses IH for both parts *)
  >- (rpt strip_tac >> gvs[eval_label_fun_def] >> metis_tac[])
  (* label_div - uses IH for both parts *)
  >- (rpt strip_tac >> gvs[eval_label_fun_def] >> metis_tac[])
  (* label_concat - uses IH for both parts *)
  >- (rpt strip_tac >> gvs[eval_label_fun_def] >> metis_tac[])
  (* label_negate - uses IH *)
  >- (rpt strip_tac >> gvs[eval_label_fun_def] >> metis_tac[])
QED

(* An assignment is well-formed if all its values are is_hostlabel_spine *)
Definition wf_assignment_labels_def:
  wf_assignment_labels a <=> FEVERY (is_hostlabel_spine o SND) a
End

(* Assignment values are in spine form - used for spine preservation proofs *)
Definition wf_assignment_spine_def:
  wf_assignment_spine a <=> FEVERY ((λl. is_host_atom l \/ is_hostlabel_spine l) o SND) a
End

(* Helper: label_append of (spine or atom) with spine produces spine *)
Theorem label_append_spine_or_atom:
  !l1 l2. (is_hostlabel_spine l1 \/ is_host_atom l1) /\ is_hostlabel_spine l2 ==>
          is_hostlabel_spine (label_append l1 l2)
Proof
  rpt strip_tac >> gvs[] >- metis_tac[label_append_spine] >>
  Cases_on `l1` >> gvs[is_host_atom_def, label_append_def, is_hostlabel_spine_def]
QED

(* Helper: eval of rule atom gives spine or host atom *)
Theorem eval_rule_atom_spine_or_atom:
  !rl a m G hl.
    is_rule_atom rl /\
    wf_assignment_spine a /\
    eval_label_fun a m G rl = SOME hl ==>
    is_hostlabel_spine hl \/ is_host_atom hl
Proof
  Cases_on `rl` >> gvs[is_rule_atom_def] >> rpt strip_tac >>
  gvs[eval_label_fun_def, is_host_atom_def, AllCaseEqs()] >>
  TRY (gvs[wf_assignment_spine_def] >> drule_all FEVERY_FLOOKUP >> simp[] >> metis_tac[] >> NO_TAC) >>
  TRY (Cases_on `i1` >> Cases_on `i2` >> gvs[eval_arith_def, is_host_atom_def, AllCaseEqs()] >> NO_TAC) >>
  TRY (Cases_on `s1` >> Cases_on `s2` >> gvs[eval_string_concat_def, is_host_atom_def, AllCaseEqs()] >> NO_TAC) >>
  TRY (Cases_on `i` >> gvs[eval_arith_def, is_host_atom_def, AllCaseEqs()] >> NO_TAC)
QED

(* Key theorem: eval_label_fun produces spine labels when given spine assignment
   and spine-form rule label. This is essential for showing instantiate_rulegraph
   preserves hostgraph_labels_spine. *)
Theorem eval_label_fun_spine:
  !rl a m G hl.
    is_rulelabel_spine rl /\
    wf_assignment_spine a /\
    eval_label_fun a m G rl = SOME hl ==>
    is_hostlabel_spine hl
Proof
  Induct_on `rl` >> rpt strip_tac >>
  gvs[is_rulelabel_spine_def, eval_label_fun_def, is_hostlabel_spine_def] >>
  (* Only label_cons case remains after gvs eliminates non-spine cases *)
  sg `is_hostlabel_spine v2` >-
  (first_x_assum (qspecl_then [`a`, `m`, `G`, `v2`] mp_tac) >> simp[]) >>
  irule label_append_spine_or_atom >> simp[] >>
  irule eval_rule_atom_spine_or_atom >> metis_tac[]
QED

(* extend_assignment preserves wf_assignment_spine when extended with spine or atom value *)
Theorem extend_assignment_wf_assignment_spine:
  !typing v hl a.
    (is_hostlabel_spine hl \/ is_host_atom hl) /\
    extend_assignment typing v hl = SOME a ==>
    wf_assignment_spine a
Proof
  rw[extend_assignment_def, wf_assignment_spine_def, AllCaseEqs()] >>
  simp[FEVERY_FUPDATE, FEVERY_FEMPTY, DRESTRICT_DEF]
QED

(* merge_assignment preserves wf_assignment_spine *)
Theorem merge_assignment_wf_assignment_spine:
  !a b c.
    wf_assignment_spine a /\ wf_assignment_spine b /\
    merge_assignment a b = SOME c ==>
    wf_assignment_spine c
Proof
  rw[merge_assignment_def, wf_assignment_spine_def] >>
  irule fevery_funion >> simp[]
QED

(* Helper lemmas for unify_label_wf_assignment_spine proof *)

(* Base case: empty assignment satisfies wf_assignment_spine *)
Theorem wf_assignment_spine_FEMPTY:
  wf_assignment_spine FEMPTY
Proof
  simp[wf_assignment_spine_def, FEVERY_FEMPTY]
QED

(* Negate case helper: label_integer is always a host atom *)
Theorem is_host_atom_integer:
  !i. is_host_atom (label_integer i)
Proof
  simp[is_host_atom_def]
QED

(* Spine cons elimination: decompose a spine cons into atom head and spine tail *)
Theorem is_hostlabel_spine_cons_elim:
  !h t. is_hostlabel_spine (label_cons h t) ==>
        is_host_atom h /\ is_hostlabel_spine t
Proof
  simp[is_hostlabel_spine_def]
QED

(* Nil is a spine label *)
Theorem is_hostlabel_spine_nil:
  is_hostlabel_spine label_nil
Proof
  simp[is_hostlabel_spine_def]
QED

(* Case lemma: variable case *)
Theorem unify_label_wf_assignment_spine_var:
  !typing v hl a.
    (is_hostlabel_spine hl \/ is_host_atom hl) /\
    unify_label typing (label_variable v) hl = SOME a ==>
    wf_assignment_spine a
Proof
  rpt strip_tac >>
  fs[unify_label_def] >>
  irule extend_assignment_wf_assignment_spine >>
  metis_tac[]
QED

(* Case lemma: constant matching - integer *)
Theorem unify_label_wf_assignment_spine_int:
  !typing i1 i2 a.
    unify_label typing (label_integer i1) (label_integer i2) = SOME a ==>
    wf_assignment_spine a
Proof
  rpt strip_tac >>
  fs[unify_label_def, unify_constant_labels_def] >>
  simp[wf_assignment_spine_FEMPTY]
QED

(* Case lemma: constant matching - char *)
Theorem unify_label_wf_assignment_spine_char:
  !typing c1 c2 a.
    unify_label typing (label_char c1) (label_char c2) = SOME a ==>
    wf_assignment_spine a
Proof
  rpt strip_tac >>
  fs[unify_label_def, unify_constant_labels_def] >>
  simp[wf_assignment_spine_FEMPTY]
QED

(* Case lemma: constant matching - string *)
Theorem unify_label_wf_assignment_spine_string:
  !typing s1 s2 a.
    unify_label typing (label_string s1) (label_string s2) = SOME a ==>
    wf_assignment_spine a
Proof
  rpt strip_tac >>
  fs[unify_label_def, unify_constant_labels_def] >>
  simp[wf_assignment_spine_FEMPTY]
QED

(* Case lemma: nil-nil matching *)
Theorem unify_label_wf_assignment_spine_nil:
  !typing a.
    unify_label typing label_nil label_nil = SOME a ==>
    wf_assignment_spine a
Proof
  rpt strip_tac >>
  fs[unify_label_def] >>
  simp[wf_assignment_spine_FEMPTY]
QED

(* Key lemma: unify_label produces wf_assignment_spine when given spine label.
   Values extracted from a spine-form or atom host label are also spine-form or atom.
   The strengthened precondition (atoms OR spines) is needed because the negate case
   recurses on label_integer(-i) which is an atom, not a spine.

   Proof approach:
   1. Use structural induction on rl (Induct_on 'rl')
   2. For each case of rl, do case analysis on hl (Cases_on 'hl')
   3. Most cases are trivially false because unify_label returns NONE
   4. Base cases (int-int, char-char, string-string, nil-nil) return FEMPTY
   5. Variable case uses extend_assignment_wf_assignment_spine
   6. Cons-cons case uses IH and merge_assignment_wf_assignment_spine
   7. Cons-nil case (list variable) uses extend + IH + merge
   8. Negate case uses IH with is_host_atom (label_integer (-i))

   The case-specific lemmas above (unify_label_wf_assignment_spine_var etc.)
   cover the base cases. The full proof requires careful handling of the
   cons-cons and cons-nil recursive cases with the induction hypothesis. *)
Theorem unify_label_wf_assignment_spine:
  !typing rl hl a.
    (is_hostlabel_spine hl \/ is_host_atom hl) /\
    unify_label typing rl hl = SOME a ==>
    wf_assignment_spine a
Proof
  Induct_on `rl`
  (* Base cases: integer, string, char, nil *)
  >- (rw[unify_label_def, unify_constant_labels_def,
         wf_assignment_spine_FEMPTY, AllCaseEqs()] >> rw[])
  >- (rw[unify_label_def, unify_constant_labels_def,
         wf_assignment_spine_FEMPTY, AllCaseEqs()] >> rw[])
  >- (rw[unify_label_def, unify_constant_labels_def,
         wf_assignment_spine_FEMPTY, AllCaseEqs()] >> rw[])
  >- (rw[unify_label_def, unify_constant_labels_def,
         wf_assignment_spine_FEMPTY, AllCaseEqs()] >> rw[])
  (* Cons case - most complex *)
  >- (rpt strip_tac >> Cases_on `hl` >> fs[is_hostlabel_spine_rws, is_host_atom_rws]
      (* hl = label_nil: cons-nil subcase *)
      >- (simp[Once unify_label_def, AllCaseEqs()] \\
          Cases_on `rl`
          (* Only variable with tyList succeeds; others return NONE *)
          >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def])
          >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def])
          >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def])
          >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def])
          >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def])
          (* Variable case: only succeeds for tyList *)
          >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >>
              simp[Once unify_label_def, AllCaseEqs()] \\
              strip_tac >> irule merge_assignment_wf_assignment_spine >>
              qexistsl_tac [`a1`, `a2`] >> rpt conj_tac
              >- (irule extend_assignment_wf_assignment_spine >> qexists_tac `label_nil` >>
                  simp[is_hostlabel_spine_rws] \\ qexistsl_tac [`typing`, `v`] >> simp[])
              >- (first_x_assum (qspecl_then [`typing`, `label_nil`, `a2`] mp_tac) >>
                  simp[is_hostlabel_spine_rws])
              >- simp[])
          >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def])
          >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def])
          >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def])
          >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def])
          >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def])
          >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def])
          >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def])
          >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def])
          >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def]))
      (* hl = label_cons l l0: cons-cons subcase *)
      >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >>
          simp[Once unify_label_def, AllCaseEqs()] >> strip_tac >> gvs[]
          (* For each head constructor, use merge + IHs *)
          >- (irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >>
              rpt conj_tac >- (last_x_assum irule >> simp[] >> qexistsl_tac [`l`, `typing`] >> simp[])
              >- (first_x_assum irule >> qexistsl_tac [`l0`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[])
          >- (irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >>
              rpt conj_tac >- (last_x_assum irule >> simp[] >> qexistsl_tac [`l`, `typing`] >> simp[])
              >- (first_x_assum irule >> qexistsl_tac [`l0`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[])
          >- (irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >>
              rpt conj_tac >- (last_x_assum irule >> simp[] >> qexistsl_tac [`l`, `typing`] >> simp[])
              >- (first_x_assum irule >> qexistsl_tac [`l0`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[])
          >- (irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >>
              rpt conj_tac >- (last_x_assum irule >> simp[] >> qexistsl_tac [`l`, `typing`] >> simp[])
              >- (first_x_assum irule >> qexistsl_tac [`l0`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[])
          >- (irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >>
              rpt conj_tac >- (last_x_assum irule >> simp[] >> qexistsl_tac [`l`, `typing`] >> simp[])
              >- (first_x_assum irule >> qexistsl_tac [`l0`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[])
          (* Variable with tyList: split_label_list case *)
          >- (Cases_on `x` >> gvs[] \\
              irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >> rpt conj_tac
              >- (irule extend_assignment_wf_assignment_spine >> qexists_tac `q` \\
                  qexistsl_tac [`typing`, `v`] >> conj_tac >- simp[] \\
                  DISJ1_TAC >> `is_hostlabel_spine (label_cons l l0)` by simp[is_hostlabel_spine_rws] >>
                  imp_res_tac split_label_list_spine >> simp[])
              >- (`is_hostlabel_spine (label_cons l l0)` by simp[is_hostlabel_spine_rws] >>
                  imp_res_tac split_label_list_spine >>
                  first_x_assum irule >> qexistsl_tac [`r`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[])
          (* Variable with ty != tyList: use normal head-tail matching *)
          >- (irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >>
              rpt conj_tac >- (last_x_assum irule >> simp[] >> qexistsl_tac [`l`, `typing`] >> simp[])
              >- (first_x_assum irule >> qexistsl_tac [`l0`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[])
          (* Remaining head constructors: indeg, outdeg, length, add, sub, mult, div, concat, negate *)
          >- (irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >>
              rpt conj_tac >- (last_x_assum irule >> simp[] >> qexistsl_tac [`l`, `typing`] >> simp[])
              >- (first_x_assum irule >> qexistsl_tac [`l0`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[])
          >- (irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >>
              rpt conj_tac >- (last_x_assum irule >> simp[] >> qexistsl_tac [`l`, `typing`] >> simp[])
              >- (first_x_assum irule >> qexistsl_tac [`l0`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[])
          >- (irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >>
              rpt conj_tac >- (last_x_assum irule >> simp[] >> qexistsl_tac [`l`, `typing`] >> simp[])
              >- (first_x_assum irule >> qexistsl_tac [`l0`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[])
          >- (irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >>
              rpt conj_tac >- (last_x_assum irule >> simp[] >> qexistsl_tac [`l`, `typing`] >> simp[])
              >- (first_x_assum irule >> qexistsl_tac [`l0`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[])
          >- (irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >>
              rpt conj_tac >- (last_x_assum irule >> simp[] >> qexistsl_tac [`l`, `typing`] >> simp[])
              >- (first_x_assum irule >> qexistsl_tac [`l0`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[])
          >- (irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >>
              rpt conj_tac >- (last_x_assum irule >> simp[] >> qexistsl_tac [`l`, `typing`] >> simp[])
              >- (first_x_assum irule >> qexistsl_tac [`l0`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[])
          >- (irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >>
              rpt conj_tac >- (last_x_assum irule >> simp[] >> qexistsl_tac [`l`, `typing`] >> simp[])
              >- (first_x_assum irule >> qexistsl_tac [`l0`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[])
          >- (irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >>
              rpt conj_tac >- (last_x_assum irule >> simp[] >> qexistsl_tac [`l`, `typing`] >> simp[])
              >- (first_x_assum irule >> qexistsl_tac [`l0`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[])
          >- (irule merge_assignment_wf_assignment_spine >> qexistsl_tac [`a1`, `a2`] >>
              rpt conj_tac >- (last_x_assum irule >> simp[] >> qexistsl_tac [`l`, `typing`] >> simp[])
              >- (first_x_assum irule >> qexistsl_tac [`l0`] >> simp[] >> qexists_tac `typing` >> simp[])
              >- simp[]))
      (* hl = atom cases: cons pattern vs atoms all return NONE *)
      >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def])
      >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def])
      >- (qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >> simp[Once unify_label_def]))
  (* Variable case: use extend_assignment_wf_assignment_spine *)
  >- (rpt strip_tac >> gvs[unify_label_def] >>
      irule extend_assignment_wf_assignment_spine >> qexists_tac `hl` >> simp[]
      >- (qexistsl_tac [`typing`, `v`] >> simp[])
      >- (qexistsl_tac [`typing`, `v`] >> simp[]))
  (* indeg, outdeg, length: always return NONE *)
  >- (rpt strip_tac >> gvs[unify_label_def])
  >- (rpt strip_tac >> gvs[unify_label_def])
  >- (rpt strip_tac >> gvs[unify_label_def])
  (* Binary operators: always return NONE *)
  >- (rpt strip_tac >> fs[Once unify_label_def])
  >- (rpt strip_tac >> fs[Once unify_label_def])
  >- (rpt strip_tac >> fs[Once unify_label_def])
  >- (rpt strip_tac >> fs[Once unify_label_def])
  >- (rpt strip_tac >> fs[Once unify_label_def])
  (* Negate case: only succeeds for label_integer *)
  >- (rpt strip_tac >> qpat_x_assum `unify_label _ _ _ = SOME _` mp_tac >>
      simp[Once unify_label_def, AllCaseEqs()] >> strip_tac >> gvs[]
      >- fs[is_hostlabel_spine_rws]
      >- (first_x_assum irule >> qexists_tac `label_integer (-i)` >>
          simp[is_host_atom_rws] \\ qexists_tac `typing` >> simp[]))
QED

(* extend_assignment preserves wf_assignment_labels when extended with is_hostlabel_spine value *)
Theorem extend_assignment_wf_assignment_labels:
  !typing v hl a.
    is_hostlabel_spine hl /\
    extend_assignment typing v hl = SOME a ==>
    wf_assignment_labels a
Proof
  rw[extend_assignment_def, wf_assignment_labels_def, AllCaseEqs()] >>
  simp[FEVERY_FUPDATE, FEVERY_FEMPTY, DRESTRICT_DEF]
QED

(* merge_assignment preserves wf_assignment_labels *)
Theorem merge_assignment_wf_assignment_labels:
  !a b c.
    wf_assignment_labels a /\ wf_assignment_labels b /\
    merge_assignment a b = SOME c ==>
    wf_assignment_labels c
Proof
  rw[merge_assignment_def, wf_assignment_labels_def] >>
  irule fevery_funion >> simp[]
QED

(* unify_nodeattr produces wf_assignment_spine when given spine label *)
Theorem unify_nodeattr_wf_assignment_spine:
  !typing rl rm hl hm a.
    is_hostlabel_spine hl /\
    unify_nodeattr typing (rl,rm) (hl,hm) = SOME a ==>
    wf_assignment_spine a
Proof
  rpt strip_tac >> gvs[unify_nodeattr_def] >>
  irule unify_label_wf_assignment_spine >> metis_tac[]
QED

(* unify_edgeattr produces wf_assignment_spine when given spine label *)
Theorem unify_edgeattr_wf_assignment_spine:
  !typing rl rm hl hm a.
    is_hostlabel_spine hl /\
    unify_edgeattr typing (rl,rm) (hl,hm) = SOME a ==>
    wf_assignment_spine a
Proof
  rpt strip_tac >> gvs[unify_edgeattr_def] >>
  irule unify_label_wf_assignment_spine >> metis_tac[]
QED

(* Helper: FOLDR merge produces a result where each input is a SUBMAP.
   When the FOLDR successfully merges all partial assignments, each
   individual assignment is a SUBMAP of the final result. *)
Theorem foldr_merge_SUBMAP:
  !f l total x.
    FOLDR (\nid acc. case (f nid, acc) of
             (NONE, _) => NONE
           | (SOME a, NONE) => NONE
           | (SOME a, SOME acc') => merge_assignment acc' a)
          (SOME FEMPTY) l = SOME total /\ MEM x l ==>
    ?a_x. f x = SOME a_x /\ a_x SUBMAP total
Proof
  Induct_on `l` >> simp[] >>
  rpt gen_tac >> simp[FOLDR] >> strip_tac
  (* x = h case *)
  >- (gvs[AllCaseEqs(), merge_assignment_def] >>
      simp[SUBMAP_DEF, FUNION_DEF, FLOOKUP_DEF, agree_on_common_keys_def] >>
      rpt strip_tac >> Cases_on `x IN FDOM acc'` >> simp[] >>
      gvs[agree_on_common_keys_def, FLOOKUP_DEF])
  (* MEM x l case *)
  >- (gvs[AllCaseEqs(), merge_assignment_def] >>
      first_x_assum (qspecl_then [`f`, `acc'`, `x`] mp_tac) >> simp[] >>
      strip_tac >> qexists_tac `a_x` >> simp[] >>
      metis_tac[SUBMAP_TRANS, SUBMAP_FUNION_ID])
QED

(* Helper: label_append for atoms equals label_cons *)
Theorem label_append_atom:
  (!i rest. label_append (label_integer i) rest = label_cons (label_integer i) rest) /\
  (!s rest. label_append (label_string s) rest = label_cons (label_string s) rest) /\
  (!c rest. label_append (label_char c) rest = label_cons (label_char c) rest) /\
  (!rest. label_append label_nil rest = rest)
Proof
  simp[label_append_def]
QED

(* Helper lemma: unify_label against an integer implies eval returns that integer.
   This handles the case where the host label is an atom (integer), which doesn't
   satisfy is_hostlabel_spine. Used for nested negate in the main lemma. *)
Theorem unify_label_eval_label_fun_integer:
  !m G typing rl i assign.
    wf_rulelabel rl /\
    unify_label typing rl (label_integer i) = SOME assign ==>
    eval_label_fun assign m G rl = SOME (label_integer i)
Proof
  Induct_on `rl`
  (* Base cases *)
  >- rw[unify_label_def, unify_constant_labels_def, AllCaseEqs(), eval_label_fun_def]
  >- rw[unify_label_def]
  >- rw[unify_label_def]
  >- rw[unify_label_def]
  >- rw[unify_label_def]
  >- (rw[unify_label_def, eval_label_fun_def, extend_assignment_def, AllCaseEqs()] >> simp[FLOOKUP_UPDATE])
  (* Vacuous cases *)
  >- rw[unify_label_def]
  >- rw[unify_label_def]
  >- rw[unify_label_def]
  >- rw[unify_label_def]
  >- rw[unify_label_def]
  >- rw[unify_label_def]
  >- rw[unify_label_def]
  >- rw[unify_label_def]
  (* label_negate case - uses IH *)
  >- (rpt strip_tac >> simp[Once eval_label_fun_def] >>
      qexists_tac `label_integer (-i)` >> CONJ_TAC
      >- (first_x_assum (qspecl_then [`m`, `G`, `typing`, `-i`, `assign`] mp_tac) >>
          impl_tac
          >- (CONJ_TAC >- fs[wf_rulelabel_def] >>
              qpat_x_assum `unify_label _ (label_negate _) _ = _` mp_tac >>
              simp[Once unify_label_def])
          >- simp[])
      >- simp[eval_arith_def, integerTheory.INT_MUL_RNEG, integerTheory.INT_NEG_NEG])
QED

(* Key lemma: if unify_label succeeds, then eval_label_fun returns the host label.
   This connects the unification process to label evaluation.

   IMPORTANT: m and G must be quantified at the outer level to avoid type polymorphism
   issues in the induction. The original form `!typing rl hl assign. ... ==> !m G. ...`
   causes the IH to have different type variables for G than the conclusion, making
   it impossible to use the FUNION lemmas correctly.

   The wf_rulelabel and is_hostlabel_spine preconditions ensure labels are proper lists
   with atoms in head positions (no label_nil or label_cons in head of cons).
   This is enforced by the parser/translation - these predicates are for proofs only. *)
(* TODO: Update proof for new empty-list-matching case in unify_label *)
Theorem unify_label_eval_label_fun:
  !m G typing rl hl assign.
    wf_rulelabel rl /\ is_hostlabel_spine hl /\
    unify_label typing rl hl = SOME assign ==>
    eval_label_fun assign m G rl = SOME hl
Proof
  Induct_on `rl`
  (* Base cases: label_integer, label_string, label_char, label_nil *)
  >- rw[unify_label_def, eval_label_fun_def, unify_constant_labels_def, AllCaseEqs()]
  >- rw[unify_label_def, eval_label_fun_def, unify_constant_labels_def, AllCaseEqs()]
  >- rw[unify_label_def, eval_label_fun_def, unify_constant_labels_def, AllCaseEqs()]
  >- rw[unify_label_def, eval_label_fun_def, AllCaseEqs()]
  (* label_cons case *)
  >- (
    rpt strip_tac >> Cases_on `rl' = label_nil`
    (* rl' = label_nil: singleton list pattern *)
    >- (
      gvs[] >> fs[Once unify_label_def] >> simp[Once eval_label_fun_def] >>
      Cases_on `hl`
      >- gvs[]
      >- gvs[]
      >- gvs[]
      (* hl = label_nil *)
      >- (gvs[AllCaseEqs()] >>
          qexists_tac `label_nil` >> CONJ_TAC
          >- (simp[eval_label_fun_def] >>
              fs[extend_assignment_def, merge_assignment_def, AllCaseEqs()] >>
              gvs[FLOOKUP_FUNION, FLOOKUP_UPDATE])
          >- (qexists_tac `label_nil` >> simp[eval_label_fun_def, label_append_def]))
      (* hl = label_cons l l0 *)
      >- (gvs[AllCaseEqs()]
          (* Constant cases *)
          >- (fs[unify_label_def, AllCaseEqs(), unify_constant_labels_def] >>
              simp[eval_label_fun_def, label_append_def])
          >- (fs[unify_label_def, AllCaseEqs(), unify_constant_labels_def] >>
              simp[eval_label_fun_def, label_append_def])
          >- (fs[unify_label_def, AllCaseEqs(), unify_constant_labels_def] >>
              simp[eval_label_fun_def, label_append_def])
          >- fs[wf_rulelabel_def, is_rule_atom_def]
          >- fs[wf_rulelabel_def, is_rule_atom_def]
          (* label_variable with tyList *)
          >- (PairCases_on `x` >> gvs[] >>
              fs[AllCaseEqs()] >>
              gvs[merge_assignment_def, AllCaseEqs(), FUNION_FEMPTY_2] >>
              qexists_tac `x0` >> CONJ_TAC
              >- (first_x_assum (qspecl_then [`m`, `G`, `typing`, `x0`, `a1`] mp_tac) >>
                  impl_tac
                  >- (fs[wf_rulelabel_def] >>
                      drule split_label_list_spine >> simp[is_hostlabel_spine_def] >>
                      disch_then (qspecl_then [`count_labels (label_cons l l0) - count_labels label_nil`, `x0`, `x1`] mp_tac) >> simp[])
                  >- (strip_tac >> irule eval_label_fun_FUNION_left >> simp[]))
              >- (qexists_tac `label_nil` >>
                  simp[eval_label_fun_def] >>
                  `x1 = label_nil` by (qpat_x_assum `unify_label _ label_nil _ = _` mp_tac >>
                                       simp[Once unify_label_def, AllCaseEqs()]) >>
                  gvs[] >> drule split_label_list_append >> simp[]))
          (* label_variable with ty ≠ tyList *)
          >- (fs[unify_label_def, AllCaseEqs()] >>
              gvs[merge_assignment_def, AllCaseEqs(), FUNION_FEMPTY_2] >>
              qexists_tac `l` >>
              simp[eval_label_fun_def] >> fs[extend_assignment_def, AllCaseEqs()] >> gvs[FLOOKUP_UPDATE] >>
              Cases_on `l` >> gvs[label_append_def, is_hostlabel_spine_def, is_host_atom_def])
          (* Vacuous cases: label_indeg, label_outdeg, etc. *)
          >- fs[unify_label_def]
          >- REPEAT (TRY (fs[unify_label_def] >> NO_TAC))
          >- rpt (fs[unify_label_def])
          >- fs[unify_label_def]
          >- fs[unify_label_def]
          >- fs[unify_label_def]
          >- fs[unify_label_def]
          >- fs[unify_label_def]
          (* label_negate case *)
          >- (qpat_x_assum `unify_label _ (label_negate _) _ = _` mp_tac >>
              simp[Once unify_label_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
              qpat_x_assum `unify_label _ label_nil _ = _` mp_tac >>
              simp[Once unify_label_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
              gvs[merge_assignment_def, AllCaseEqs(), FUNION_FEMPTY_2] >>
              qexists_tac `label_integer i` >> CONJ_TAC
              >- (simp[Once eval_label_fun_def] >>
                  qexists_tac `label_integer (-i)` >> CONJ_TAC
                  >- (irule unify_label_eval_label_fun_integer >>
                      CONJ_TAC >- fs[wf_rulelabel_def] >>
                      qexists_tac `typing` >> simp[])
                  >- simp[eval_arith_def, integerTheory.INT_MUL_RNEG, integerTheory.INT_NEG_NEG])
              >- (qexists_tac `label_nil` >> simp[eval_label_fun_def, label_append_def]))))
    (* rl' ≠ label_nil: proper cons matching *)
    >- (simp[Once eval_label_fun_def] >>
        Cases_on `hl`
        >- (qpat_x_assum `unify_label _ _ _ = _` mp_tac >> simp[Once unify_label_def, AllCaseEqs()])
        >- (qpat_x_assum `unify_label _ _ _ = _` mp_tac >> simp[Once unify_label_def, AllCaseEqs()])
        >- (qpat_x_assum `unify_label _ _ _ = _` mp_tac >> simp[Once unify_label_def, AllCaseEqs()])
        (* hl = label_nil with tyList variable *)
        >- (qpat_x_assum `unify_label _ _ _ = _` mp_tac >> simp[Once unify_label_def, AllCaseEqs()] >>
            strip_tac >> gvs[] >>
            qexists_tac `label_nil` >>
            CONJ_TAC
            >- (simp[eval_label_fun_def] >> fs[extend_assignment_def, merge_assignment_def, AllCaseEqs()] >>
                gvs[FLOOKUP_FUNION, FLOOKUP_UPDATE])
            >- (qexists_tac `label_nil` >> simp[label_append_def] >>
                first_x_assum (qspecl_then [`m`, `G`, `typing`, `label_nil`, `a2`] mp_tac) >>
                impl_tac >- (simp[is_hostlabel_spine_def] >> fs[wf_rulelabel_def, is_rule_atom_def]) >> strip_tac >>
                fs[merge_assignment_def, AllCaseEqs()] >> gvs[] >> irule eval_label_fun_FUNION_right >> simp[]))
        (* hl = label_cons l l0 - 16 subcases based on head constructor *)
        >- (qpat_x_assum `unify_label _ _ _ = _` mp_tac >> simp[Once unify_label_def, AllCaseEqs()] >>
            strip_tac >> gvs[]
            (* label_integer *)
            >- (qpat_x_assum `unify_label _ (label_integer _) _ = _` mp_tac >>
                simp[Once unify_label_def, AllCaseEqs(), unify_constant_labels_def] >>
                strip_tac >> qexists_tac `label_integer v21` >> CONJ_TAC >- simp[eval_label_fun_def] >>
                qexists_tac `l0` >> CONJ_TAC
                >- (gvs[merge_assignment_def, AllCaseEqs(), FUNION_FEMPTY_1] >>
                    first_x_assum (qspecl_then [`m`, `G`, `typing`, `l0`, `a2`] mp_tac) >>
                    impl_tac >- fs[wf_rulelabel_def, is_hostlabel_spine_def] >> simp[])
                >- simp[label_append_def])
            (* label_string *)
            >- (qpat_x_assum `unify_label _ (label_string _) _ = _` mp_tac >>
                simp[Once unify_label_def, AllCaseEqs(), unify_constant_labels_def] >>
                strip_tac >> qexists_tac `label_string v22` >> CONJ_TAC >- simp[eval_label_fun_def] >>
                qexists_tac `l0` >> CONJ_TAC
                >- (gvs[merge_assignment_def, AllCaseEqs(), FUNION_FEMPTY_1] >>
                    first_x_assum (qspecl_then [`m`, `G`, `typing`, `l0`, `a2`] mp_tac) >>
                    impl_tac >- fs[wf_rulelabel_def, is_hostlabel_spine_def] >> simp[])
                >- simp[label_append_def])
            (* label_char *)
            >- (qpat_x_assum `unify_label _ (label_char _) _ = _` mp_tac >>
                simp[Once unify_label_def, AllCaseEqs(), unify_constant_labels_def] >>
                strip_tac >> qexists_tac `label_char v23` >> CONJ_TAC >- simp[eval_label_fun_def] >>
                qexists_tac `l0` >> CONJ_TAC
                >- (gvs[merge_assignment_def, AllCaseEqs(), FUNION_FEMPTY_1] >>
                    first_x_assum (qspecl_then [`m`, `G`, `typing`, `l0`, `a2`] mp_tac) >>
                    impl_tac >- fs[wf_rulelabel_def, is_hostlabel_spine_def] >> simp[])
                >- simp[label_append_def])
            (* label_nil - vacuous since not a host atom *)
            >- (qpat_x_assum `unify_label _ label_nil _ = _` mp_tac >>
                simp[Once unify_label_def, AllCaseEqs()] >> strip_tac >>
                gvs[is_hostlabel_spine_def, is_host_atom_def])
            (* label_cons v24 v25 - vacuous since nested cons is not rule atom *)
            >- fs[wf_rulelabel_def, is_rule_atom_def]
            (* label_variable with tyList *)
            >- (PairCases_on `x` >> gvs[] >> qexists_tac `x0` >> CONJ_TAC
                >- (simp[eval_label_fun_def] >> fs[extend_assignment_def, AllCaseEqs()] >>
                    gvs[merge_assignment_def, AllCaseEqs()] >> simp[FLOOKUP_FUNION, FLOOKUP_UPDATE])
                >- (qexists_tac `x1` >> CONJ_TAC
                    >- (first_x_assum (qspecl_then [`m`, `G`, `typing`, `x1`, `a2`] mp_tac) >>
                        impl_tac
                        >- (fs[wf_rulelabel_def] >> drule split_label_list_spine >>
                            disch_then (qspecl_then [`count_labels (label_cons l l0) - count_labels rl'`, `x0`, `x1`] mp_tac) >>
                            simp[is_hostlabel_spine_def])
                        >- (fs[merge_assignment_def, AllCaseEqs(), extend_assignment_def] >> gvs[] >>
                            strip_tac >> irule eval_label_fun_FUNION_right >> simp[]))
                    >- (drule split_label_list_append >> simp[])))
            (* label_variable with ty ≠ tyList *)
            >- (qpat_x_assum `unify_label _ (label_variable _) _ = _` mp_tac >>
                simp[Once unify_label_def, AllCaseEqs()] >> strip_tac >>
                qexists_tac `l` >> CONJ_TAC
                >- (simp[eval_label_fun_def] >> fs[extend_assignment_def, AllCaseEqs()] >>
                    gvs[merge_assignment_def, AllCaseEqs()] >> simp[FLOOKUP_FUNION, FLOOKUP_UPDATE])
                >- (qexists_tac `l0` >> CONJ_TAC
                    >- (first_x_assum (qspecl_then [`m`, `G`, `typing`, `l0`, `a2`] mp_tac) >>
                        impl_tac >- fs[wf_rulelabel_def, is_hostlabel_spine_def] >> strip_tac >>
                        fs[merge_assignment_def, extend_assignment_def, AllCaseEqs()] >> gvs[] >>
                        irule eval_label_fun_FUNION_right >> simp[])
                    >- (Cases_on `l` >> simp[label_append_def, is_hostlabel_spine_def, is_host_atom_def]
                        >- fs[is_hostlabel_spine_def, is_host_atom_def]
                        >- fs[is_hostlabel_spine_def, is_host_atom_def])))
            (* label_indeg - vacuous *)
            >- (fs[wf_rulelabel_def, is_rule_atom_def] >>
                qpat_x_assum `unify_label _ (label_indeg _) _ = _` mp_tac >> simp[Once unify_label_def])
            (* label_outdeg - vacuous *)
            >- (qpat_x_assum `unify_label _ (label_outdeg _) _ = _` mp_tac >> simp[Once unify_label_def])
            (* label_length - vacuous *)
            >- (qpat_x_assum `unify_label _ (label_length _) _ = _` mp_tac >> simp[Once unify_label_def])
            (* label_add - vacuous *)
            >- (qpat_x_assum `unify_label _ (label_add _ _) _ = _` mp_tac >> simp[Once unify_label_def])
            (* label_sub - vacuous *)
            >- (qpat_x_assum `unify_label _ (label_sub _ _) _ = _` mp_tac >> simp[Once unify_label_def])
            (* label_mult - vacuous *)
            >- (qpat_x_assum `unify_label _ (label_mult _ _) _ = _` mp_tac >> simp[Once unify_label_def])
            (* label_div - vacuous *)
            >- (qpat_x_assum `unify_label _ (label_div _ _) _ = _` mp_tac >> simp[Once unify_label_def])
            (* label_concat - vacuous *)
            >- (qpat_x_assum `unify_label _ (label_concat _ _) _ = _` mp_tac >> simp[Once unify_label_def])
            (* label_negate *)
            >- (qpat_x_assum `unify_label _ (label_negate _) _ = _` mp_tac >>
                simp[Once unify_label_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
                qexists_tac `label_integer i` >> CONJ_TAC
                >- (simp[Once eval_label_fun_def] >>
                    qexists_tac `label_integer (-i)` >> CONJ_TAC
                    >- (first_x_assum (qspecl_then [`m`, `G`, `typing`, `l0`, `a2`] mp_tac) >>
                        impl_tac >- fs[wf_rulelabel_def, is_hostlabel_spine_def] >> strip_tac >>
                        fs[merge_assignment_def, AllCaseEqs()] >> gvs[] >>
                        irule eval_label_fun_FUNION_left >> simp[] >>
                        irule unify_label_eval_label_fun_integer >>
                        CONJ_TAC >- fs[wf_rulelabel_def] >> qexists_tac `typing` >> simp[])
                    >- simp[eval_arith_def, integerTheory.INT_MUL_RNEG, integerTheory.INT_NEG_NEG])
                >- (qexists_tac `l0` >> CONJ_TAC
                    >- (first_x_assum (qspecl_then [`m`, `G`, `typing`, `l0`, `a2`] mp_tac) >>
                        impl_tac >- fs[wf_rulelabel_def, is_hostlabel_spine_def] >> strip_tac >>
                        fs[merge_assignment_def, AllCaseEqs()] >> gvs[] >>
                        irule eval_label_fun_FUNION_right >> simp[])
                    >- simp[label_append_def])))))
  (* label_variable case *)
  >- (rw[unify_label_def, eval_label_fun_def, extend_assignment_def, AllCaseEqs()] >> simp[FLOOKUP_UPDATE])
  (* Vacuous cases: label_indeg, label_outdeg, label_length *)
  >- rw[unify_label_def, eval_label_fun_def]
  >- rw[unify_label_def, eval_label_fun_def]
  >- rw[unify_label_def, eval_label_fun_def]
  (* Vacuous cases: label_add, label_sub, label_mult, label_div, label_concat *)
  >- rw[unify_label_def, eval_label_fun_def]
  >- rw[unify_label_def, eval_label_fun_def]
  >- rw[unify_label_def, eval_label_fun_def]
  >- rw[unify_label_def, eval_label_fun_def]
  >- rw[unify_label_def, eval_label_fun_def]
  (* label_negate at top level - vacuous since is_hostlabel_spine is false for atoms *)
  >- (rpt strip_tac >> Cases_on `hl`
      >- (simp[Once unify_label_def] >> fs[AllCaseEqs()] >> fs[is_hostlabel_spine_def])
      >- fs[unify_label_def, AllCaseEqs()]
      >- fs[unify_label_def, AllCaseEqs()]
      >- fs[unify_label_def, AllCaseEqs()]
      >- fs[unify_label_def, AllCaseEqs()])
QED

Definition mk_assignment_node_def:
  mk_assignment_node (r:rule) (pre:morphism) (G:hostgraph) (v:nodeid): assignment option = do
    l1 <- FLOOKUP r.lhs.l v;
    v' <- FLOOKUP pre.nodemap v;
    l2 <- FLOOKUP G.l v';
    unify_nodeattr r.vars l1 l2
  od
End

Definition mk_assignment_nodes_def:
  mk_assignment_nodes (r:rule) (pre:morphism) (G:hostgraph): assignment option =
    FOLDR (\nid acc.
      case (mk_assignment_node r pre G nid, acc) of
        (SOME a, SOME acc') => merge_assignment acc' a |
        _ => NONE
    ) (SOME FEMPTY) (SET_TO_LIST r.lhs.V)
End

Definition mk_assignment_edge_def:
  mk_assignment_edge (r:rule) (pre:morphism) (G:hostgraph) (e:edgeid): assignment option = do
    m1 <- FLOOKUP r.lhs.m e;
    e' <- FLOOKUP pre.edgemap e;
    m2 <- FLOOKUP G.m e';
    unify_edgeattr r.vars m1 m2
  od
End

Definition mk_assignment_edges_def:
  mk_assignment_edges (r:rule) (pre:morphism) (G:hostgraph):assignment option =
    FOLDR (\eid acc.
      case (mk_assignment_edge r pre G eid, acc) of
        (SOME a, SOME acc') => merge_assignment acc' a |
        _ => NONE
    ) (SOME FEMPTY) (SET_TO_LIST r.lhs.E)
End

Definition mk_assignment_def:
  mk_assignment (r:rule) (pre:morphism) (G:hostgraph): assignment option = do
    nassign <- mk_assignment_nodes r pre G;
    eassign <- mk_assignment_edges r pre G;
    merge_assignment nassign eassign
  od
End

(* mk_assignment_node produces wf_assignment_spine when host graph has spine labels *)
Theorem mk_assignment_node_wf_assignment_spine:
  !r m G nid a.
    hostgraph_labels_spine G /\
    mk_assignment_node r m G nid = SOME a ==>
    wf_assignment_spine a
Proof
  rpt strip_tac >> gvs[mk_assignment_node_def] >>
  fs[hostgraph_labels_spine_def] >>
  drule_all FEVERY_FLOOKUP >> simp[] >> strip_tac >>
  irule unify_nodeattr_wf_assignment_spine >>
  qexistsl_tac [`FST l2`, `SND l2`, `FST l1`, `SND l1`, `r.vars`] >> simp[]
QED

(* mk_assignment_edge produces wf_assignment_spine when host graph has spine labels *)
Theorem mk_assignment_edge_wf_assignment_spine:
  !r m G eid a.
    hostgraph_labels_spine G /\
    mk_assignment_edge r m G eid = SOME a ==>
    wf_assignment_spine a
Proof
  rpt strip_tac >> gvs[mk_assignment_edge_def] >>
  fs[hostgraph_labels_spine_def] >>
  drule_all FEVERY_FLOOKUP >> simp[] >> strip_tac >>
  irule unify_edgeattr_wf_assignment_spine >>
  qexistsl_tac [`FST m2`, `SND m2`, `FST m1`, `SND m1`, `r.vars`] >> simp[]
QED

(* mk_assignment_nodes produces wf_assignment_spine when host graph has spine labels *)
Theorem mk_assignment_nodes_wf_assignment_spine:
  !r m G result.
    hostgraph_labels_spine G /\
    mk_assignment_nodes r m G = SOME result ==>
    wf_assignment_spine result
Proof
  rpt strip_tac >> gvs[mk_assignment_nodes_def] >>
  `!l r m G result. hostgraph_labels_spine G /\
     FOLDR (\nid acc. case mk_assignment_node r m G nid of
              NONE => NONE | SOME a =>
              case acc of NONE => NONE | SOME acc' => merge_assignment acc' a)
           (SOME FEMPTY) l = SOME result ==>
     wf_assignment_spine result` suffices_by metis_tac[] >>
  Induct_on `l`
  >- simp[wf_assignment_spine_def, FEVERY_FEMPTY]
  >- (simp[] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
      irule merge_assignment_wf_assignment_spine >>
      qexistsl_tac [`acc'`, `a`] >> simp[] >> conj_tac
      >- (first_x_assum irule >> simp[] >> metis_tac[])
      >- (irule mk_assignment_node_wf_assignment_spine >> metis_tac[]))
QED

(* mk_assignment_edges produces wf_assignment_spine when host graph has spine labels *)
Theorem mk_assignment_edges_wf_assignment_spine:
  !r m G result.
    hostgraph_labels_spine G /\
    mk_assignment_edges r m G = SOME result ==>
    wf_assignment_spine result
Proof
  rpt strip_tac >> gvs[mk_assignment_edges_def] >>
  `!l r m G result. hostgraph_labels_spine G /\
     FOLDR (\eid acc. case mk_assignment_edge r m G eid of
              NONE => NONE | SOME a =>
              case acc of NONE => NONE | SOME acc' => merge_assignment acc' a)
           (SOME FEMPTY) l = SOME result ==>
     wf_assignment_spine result` suffices_by metis_tac[] >>
  Induct_on `l`
  >- simp[wf_assignment_spine_def, FEVERY_FEMPTY]
  >- (simp[] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
      irule merge_assignment_wf_assignment_spine >>
      qexistsl_tac [`acc'`, `a`] >> simp[] >> conj_tac
      >- (first_x_assum irule >> simp[] >> metis_tac[])
      >- (irule mk_assignment_edge_wf_assignment_spine >> metis_tac[]))
QED

(* Main lemma: mk_assignment produces wf_assignment_spine when host graph has spine labels *)
Theorem mk_assignment_wf_assignment_spine:
  !r m G result.
    hostgraph_labels_spine G /\
    mk_assignment r m G = SOME result ==>
    wf_assignment_spine result
Proof
  rpt strip_tac >> gvs[mk_assignment_def] >>
  irule merge_assignment_wf_assignment_spine >>
  qexistsl_tac [`nassign`, `eassign`] >> rpt conj_tac
  >- (irule mk_assignment_nodes_wf_assignment_spine >> metis_tac[])
  >- (irule mk_assignment_edges_wf_assignment_spine >> metis_tac[])
  >- simp[]
QED

(* DPO Application: Uses the categorical DPO construction from dpoTheory.
   Given a rule instance r, morphism m, and host graph G,
   construct the result graph H via deletion then gluing. *)
open pred_setTheory

Definition apply_ruleinstance_def:
  apply_ruleinstance (r:ruleinstance) (m:morphism) (G:hostgraph): hostgraph option =
    SOME (dpo r.lhs r.inf r.rhs m G)
End


Definition wf_assignment_def:
  wf_assignment (a:assignment) (r:rule) (pre:morphism) (G:hostgraph) <=>
    IS_SOME $ instantiate_rule r a pre G
End

Definition mk_assignment_spec_def:
  mk_assignment_spec (r:rule) (pre:morphism) (G:hostgraph) <=>
    if ?a. wf_assignment a r pre G then SOME (@a. wf_assignment a r pre G) else NONE
End


Definition apply_rule_def:
  apply_rule (r:rule) (pre:morphism) (G:hostgraph) = do
    assign <- mk_assignment r pre G;
    instance <- instantiate_rule r assign pre G;
    apply_ruleinstance instance pre G
  od
End

(* A prematch is an injective premorphism that satisfies the dangling condition.
   This is the condition needed for rule application in GP2:
   - Injective: the match must be an isomorphism to a subgraph
   - Dangling condition: no edges outside the match are incident to deleted nodes

   This differs from is_match (in dpoTheory) which requires full label preservation.
   For rulegraphs (with parametric labels), we use is_prematch since we cannot check
   label preservation until after instantiation.

   The key property we need:
   is_prematch r.lhs r.inf m G /\ instantiate_rule r assign m G = SOME ri
   ==> is_match ri.lhs ri.inf m G *)
Definition is_prematch_def:
  is_prematch (L:rulegraph) (Kv:nodeid set) (m:morphism) (G:hostgraph) <=>
    is_inj_premorphism L m G /\
    satisfy_dangling_condition L Kv m G
End

(* Relation to is_match: is_prematch on the rulegraph structure is equivalent
   to checking the structural parts of is_match, since:
   - is_inj_premorphism checks structure + injectivity
   - satisfy_dangling_condition only depends on structure (V, E, s, t)
   The label part of is_match is handled by successful instantiation. *)

(* All elements of a stack are well-formed hostgraphs.
   Stack frames are (hostgraph, track morphism) pairs:
   - H: the current hostgraph (fully wf_hostgraph)
   - tr: the composed track morphism from G0 to H *)
Definition wf_stack_def:
  wf_stack s <=> EVERY (\(H,tr). wf_hostgraph H) s
End

(* Extended wellformedness including label structure.
   For practical GP2 execution, labels must be structurally well-formed
   (list heads must be atoms). Note: hostgraph_labels_spine is implied by
   wf_hostgraph, so we don't need to state it separately. *)
Definition wf_stack_labels_def:
  wf_stack_labels s <=> EVERY (\(H,tr). wf_hostgraph H) s
End

(* Backward compatibility: wf_stack_labels implies hostgraph_labels_spine for all elements *)
Theorem wf_stack_labels_IMP_hostgraph_labels_spine:
  !s H tr. wf_stack_labels s /\ MEM (H, tr) s ==> hostgraph_labels_spine H
Proof
  rw[wf_stack_labels_def, EVERY_MEM] >>
  first_x_assum drule >> rw[] >>
  metis_tac[wf_hostgraph_IMP_hostgraph_labels_spine]
QED

Definition wf_program_rule_labels_def:
  wf_program_rule_labels (p:program) <=>
    FEVERY (\(_, r). wf_rulegraph_labels r.lhs /\ wf_rulegraph_labels r.rhs) p.rule
End

(* wf_program now implies wf_program_rule_labels since wf_rule includes wf_rulegraph_labels *)
Theorem wf_program_IMP_wf_program_rule_labels:
  !p. wf_program p ==> wf_program_rule_labels p
Proof
  rw[wf_program_def, wf_program_rule_labels_def] >>
  fs[FEVERY_DEF] >> rpt strip_tac >>
  first_x_assum drule >> rw[wf_rule_def]
QED

(* Helper: instantiate_rulegraph preserves node/edge sets *)
Theorem instantiate_rulegraph_preserves_structure:
  !r assign m G hg.
    instantiate_rulegraph r assign m G = SOME hg ==>
    hg.V = r.V /\ hg.E = r.E /\ hg.s = r.s /\ hg.t = r.t /\ hg.p = r.p
Proof
  rw[instantiate_rulegraph_def, optionTheory.OPTION_BIND_SOME] >>
  gvs[fetch "-" "ruleinstance_component_equality"]
QED

(* Helper: instantiate_nodeattr produces spine labels.
   The label comes from eval_label_fun which preserves spine property. *)
Theorem instantiate_nodeattr_spine:
  !r assign m G nid lab mark.
    wf_assignment_spine assign /\
    is_rulelabel_spine (FST (THE (FLOOKUP r.l nid))) /\
    instantiate_nodeattr r assign m G nid = SOME (lab, mark) ==>
    is_hostlabel_spine lab
Proof
  rpt strip_tac >>
  fs[instantiate_nodeattr_def] >>
  Cases_on `FLOOKUP r.l nid` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  Cases_on `eval_label_fun assign m G x0` >> gvs[] >>
  (Cases_on `FLOOKUP (G.l f_o_f m.nodemap) nid` >> gvs[] >>
   TRY (Cases_on `x` >> gvs[]) >>
   TRY (Cases_on `eval_nodemark r' x1` >> gvs[]) >>
   TRY (Cases_on `rule_to_host_nodemark x1` >> gvs[])) >>
  drule_all eval_label_fun_spine >> simp[]
QED

(* Helper: instantiate_edgeattr produces spine labels.
   The label comes from eval_label_fun which preserves spine property. *)
Theorem instantiate_edgeattr_spine:
  !r assign m G eid lab mark.
    wf_assignment_spine assign /\
    is_rulelabel_spine (FST (THE (FLOOKUP r.m eid))) /\
    instantiate_edgeattr r assign m G eid = SOME (lab, mark) ==>
    is_hostlabel_spine lab
Proof
  rpt strip_tac >>
  fs[instantiate_edgeattr_def] >>
  Cases_on `FLOOKUP r.m eid` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  Cases_on `eval_label_fun assign m G x0` >> gvs[] >>
  (Cases_on `FLOOKUP (G.m f_o_f m.edgemap) eid` >> gvs[] >>
   TRY (Cases_on `x` >> gvs[]) >>
   TRY (Cases_on `eval_edgemark r' x1` >> gvs[]) >>
   TRY (Cases_on `rule_to_host_edgemark x1` >> gvs[])) >>
  drule_all eval_label_fun_spine >> simp[]
QED

Theorem instantiate_rulegraph_wf:
  !r assign m G hg.
    totally_labelled_rulegraph r /\
    wf_assignment_spine assign /\
    instantiate_rulegraph r assign m G = SOME hg ==>
    wf_hostgraph hg
Proof
  rpt strip_tac >>
  gvs[instantiate_rulegraph_def, totally_labelled_rulegraph_def] >>
  `FDOM l = r.V` by (irule fmap_buildM_FDOM >> fs[wf_rulegraph_def, wf_graph_def] >> metis_tac[]) >>
  `FDOM m' = r.E` by (irule fmap_buildM_FDOM >> fs[wf_rulegraph_def, wf_graph_def] >> metis_tac[]) >>
  simp[wf_hostgraph_def, wf_graph_def, item_uniqueness_def] >>
  fs[wf_rulegraph_def, wf_graph_def, item_uniqueness_def] >>
  (* hostgraph_labels_spine: eval_label_fun produces spine labels *)
  simp[hostgraph_labels_spine_def] >> conj_tac
  (* Node labels *)
  >- (simp[FEVERY_DEF] >> rpt strip_tac >>
      `x IN FDOM r.l` by gvs[] >>
      `FINITE (FDOM r.l)` by simp[FDOM_FINITE] >>
      `FLOOKUP l x = instantiate_nodeattr r assign m G x` by
        (drule_then drule fmap_buildM_FLOOKUP >> simp[]) >>
      `x IN FDOM l` by gvs[] >>
      `FLOOKUP l x = SOME (l ' x)` by fs[FLOOKUP_DEF] >>
      `?lab mark. l ' x = (lab, mark)` by metis_tac[pairTheory.pair_CASES] >>
      `instantiate_nodeattr r assign m G x = SOME (lab, mark)` by gvs[] >>
      `is_rulelabel_spine (FST (THE (FLOOKUP r.l x)))` by
        (fs[rulegraph_labels_spine_def, FEVERY_DEF] >>
         first_x_assum (qspec_then `x` mp_tac) >> simp[FLOOKUP_DEF]) >>
      `is_hostlabel_spine lab` by metis_tac[instantiate_nodeattr_spine] >>
      gvs[])
  (* Edge labels *)
  >- (simp[FEVERY_DEF] >> rpt strip_tac >>
      `x IN FDOM r.m` by gvs[] >>
      `FINITE (FDOM r.m)` by simp[FDOM_FINITE] >>
      `FLOOKUP m' x = instantiate_edgeattr r assign m G x` by
        (drule_then drule fmap_buildM_FLOOKUP >> simp[]) >>
      `x IN FDOM m'` by gvs[] >>
      `FLOOKUP m' x = SOME (m' ' x)` by fs[FLOOKUP_DEF] >>
      `?lab mark. m' ' x = (lab, mark)` by metis_tac[pairTheory.pair_CASES] >>
      `instantiate_edgeattr r assign m G x = SOME (lab, mark)` by gvs[] >>
      `is_rulelabel_spine (FST (THE (FLOOKUP r.m x)))` by
        (fs[rulegraph_labels_spine_def, FEVERY_DEF] >>
         first_x_assum (qspec_then `x` mp_tac) >> simp[FLOOKUP_DEF]) >>
      `is_hostlabel_spine lab` by metis_tac[instantiate_edgeattr_spine] >>
      gvs[])
QED

(* Helper: instantiate_rulegraph preserves V component *)
Theorem instantiate_rulegraph_preserves_V:
  !r assign m G hg.
    instantiate_rulegraph r assign m G = SOME hg ==> hg.V = r.V
Proof
  rpt strip_tac >> gvs[instantiate_rulegraph_def]
QED

(* Helper: instantiate_nodeattr preserves unmarked when rule mark is NONE *)
Theorem instantiate_nodeattr_unmarked:
  !r assign m G nid l mk.
    FLOOKUP r.l nid = SOME (l, NONE) /\
    unmarked_hostgraph G /\
    instantiate_nodeattr r assign m G nid = SOME (l', mk) ==>
    mk = NONE
Proof
  rw[instantiate_nodeattr_def, unmarked_hostgraph_def] >>
  gvs[AllCaseEqs(), rule_to_host_nodemark_def, eval_nodemark_def]
QED

(* Helper: instantiate_edgeattr preserves unmarked when rule mark is NONE *)
Theorem instantiate_edgeattr_unmarked:
  !r assign m G eid l mk.
    FLOOKUP r.m eid = SOME (l, NONE) /\
    unmarked_hostgraph G /\
    instantiate_edgeattr r assign m G eid = SOME (l', mk) ==>
    mk = NONE
Proof
  rw[instantiate_edgeattr_def, unmarked_hostgraph_def] >>
  gvs[AllCaseEqs(), rule_to_host_edgemark_def, eval_edgemark_def]
QED

(* Main theorem: instantiate_rulegraph preserves unmarked property *)
Theorem instantiate_rulegraph_unmarked:
  !r assign m G hg.
    FEVERY (\(x,(l,mk)). mk = NONE) r.l /\
    FEVERY (\(x,(l,mk)). mk = NONE) r.m /\
    unmarked_hostgraph G /\
    instantiate_rulegraph r assign m G = SOME hg ==>
    FEVERY (IS_NONE o SND o SND) hg.l /\ FEVERY (IS_NONE o SND o SND) hg.m
Proof
  rw[instantiate_rulegraph_def] >> gvs[AllCaseEqs()]
  >- ((* Node labels *)
      simp[FEVERY_DEF] >> rpt strip_tac >>
      `FINITE (FDOM r.l)` by simp[FDOM_FINITE] >>
      `FDOM l = FDOM r.l` by metis_tac[fmap_buildM_FDOM] >>
      `x IN FDOM r.l` by gvs[] >>
      `FLOOKUP l x = instantiate_nodeattr r assign m G x` by
        metis_tac[fmap_buildM_FLOOKUP] >>
      `?nl. FLOOKUP r.l x = SOME (nl, NONE)` by
        (fs[FEVERY_DEF, FLOOKUP_DEF] >> res_tac >> Cases_on `r.l ' x` >> gvs[]) >>
      `instantiate_nodeattr r assign m G x = SOME (l ' x)` by gvs[FLOOKUP_DEF] >>
      Cases_on `l ' x` >> simp[] >>
      irule instantiate_nodeattr_unmarked >> simp[] >> metis_tac[])
  >- ((* Edge marks *)
      simp[FEVERY_DEF] >> rpt strip_tac >>
      `FINITE (FDOM r.m)` by simp[FDOM_FINITE] >>
      `FDOM m' = FDOM r.m` by metis_tac[fmap_buildM_FDOM] >>
      `x IN FDOM r.m` by gvs[] >>
      `FLOOKUP m' x = instantiate_edgeattr r assign m G x` by
        metis_tac[fmap_buildM_FLOOKUP] >>
      `?el. FLOOKUP r.m x = SOME (el, NONE)` by
        (fs[FEVERY_DEF, FLOOKUP_DEF] >> res_tac >> Cases_on `r.m ' x` >> gvs[]) >>
      `instantiate_edgeattr r assign m G x = SOME (m' ' x)` by gvs[FLOOKUP_DEF] >>
      Cases_on `m' ' x` >> simp[] >>
      irule instantiate_edgeattr_unmarked >> simp[] >> metis_tac[])
QED

(* Theorem: instantiate_rulegraph preserves unrooted property.
   Since instantiate_rulegraph copies r.p directly to hg.p and r.V to hg.V,
   the unrootedness property transfers directly from the rulegraph. *)
Theorem instantiate_rulegraph_unrooted:
  !r assign m G hg.
    FDOM r.p = r.V /\
    (!n. n IN r.V ==> (r.p ' n <=> F)) /\
    instantiate_rulegraph r assign m G = SOME hg ==>
    unrooted_hostgraph hg
Proof
  rw[instantiate_rulegraph_def, unrooted_hostgraph_def] >> gvs[AllCaseEqs()]
QED

(* Theorem: instantiate_rule produces a well-formed ruleinstance.
   wf_rule now implies totally_labelled_rulegraph for both LHS and RHS,
   which gives us the FDOM equalities needed for instantiate_rulegraph_wf.
   Depends on: instantiate_rulegraph_wf, instantiate_rulegraph_preserves_V *)
Theorem instantiate_rule_wf:
  !(r:rule) assign m G ri.
    wf_rule r /\
    wf_assignment_spine assign /\
    instantiate_rule r assign m G = SOME ri ==>
    wf_ruleinstance ri
Proof
  rw[instantiate_rule_def] >> rpt strip_tac >>
  simp[wf_ruleinstance_def] >>
  rpt conj_tac
  >- (irule instantiate_rulegraph_wf >> fs[wf_rule_def] >> metis_tac[])
  >- (irule instantiate_rulegraph_wf >> fs[wf_rule_def] >> metis_tac[])
  >- (`lhs'.V = r.lhs.V` by gvs[instantiate_rulegraph_def] >>
      fs[wf_rule_def, wf_interface_def, totally_labelled_rulegraph_def])
  >- (`rhs'.V = r.rhs.V` by gvs[instantiate_rulegraph_def] >>
      fs[wf_rule_def, wf_interface_def, totally_labelled_rulegraph_def])
QED

(* Theorem: apply_ruleinstance preserves well-formedness using wf_dpo.
   This is the key theorem that connects ruleinstance application to DPO.

   The proof uses wf_dpo from dpoTheory:
   wf_hostgraph L /\ wf_hostgraph R /\ wf_hostgraph G /\
   K SUBSET L.V /\ is_match L K m G ==> wf_hostgraph (dpo L K R m G)

   After unfolding apply_ruleinstance_def:
   h = dpo ri.lhs ri.inf ri.rhs m G
   So we need wf_hostgraph (dpo ri.lhs ri.inf ri.rhs m G)
   which follows from wf_dpo with L=ri.lhs, K=ri.inf, R=ri.rhs

   The proof uses irule wf_dpo and wf_ruleinstance_def. *)
Theorem apply_ruleinstance_preserves_wf:
  !(ri:ruleinstance) m G h.
    wf_ruleinstance ri /\
    wf_hostgraph G /\
    is_match ri.lhs ri.inf m G /\
    apply_ruleinstance ri m G = SOME h ==>
    wf_hostgraph h
Proof
  rpt strip_tac >>
  gvs[apply_ruleinstance_def] >>
  irule wf_dpo >>
  fs[wf_ruleinstance_def]
QED

(* Rule application preserves well-formedness (explicit version).
   This theorem uses wf_dpo from dpoTheory via apply_ruleinstance_preserves_wf.

   The key requirement is that is_match holds on the instantiated LHS.
   In the GP2 semantics, a rule application only succeeds when:
   1. A valid injective morphism (match) from LHS to G exists
   2. The dangling condition is satisfied
   3. The condition (if any) evaluates to true

   NOTE: This theorem requires is_match on the instantiated hostgraph.
   For the step relation (Call1), we use is_prematch on the rulegraph,
   and prematch_instantiation_is_match bridges the gap.

   The proof structure:
   1. Use instantiate_rule_wf to show the ruleinstance is well-formed
   2. Apply apply_ruleinstance_preserves_wf (which uses wf_dpo) *)
Theorem apply_rule_preserves_wf_hostgraph:
  !(r:rule) m G h assign ri.
    wf_rule r /\
    wf_hostgraph G /\
    apply_rule r m G = SOME h /\
    (* The instantiated ruleinstance *)
    mk_assignment r m G = SOME assign /\
    instantiate_rule r assign m G = SOME ri /\
    (* Match condition on instantiated graph *)
    is_match ri.lhs ri.inf m G
    ==> wf_hostgraph h
Proof
  rpt strip_tac >>
  `apply_ruleinstance ri m G = SOME h` by gvs[apply_rule_def] >>
  (* mk_assignment produces spine assignment since host graph has spine labels *)
  `hostgraph_labels_spine G` by fs[wf_hostgraph_def] >>
  `wf_assignment_spine assign` by metis_tac[mk_assignment_wf_assignment_spine] >>
  `wf_ruleinstance ri` by (irule instantiate_rule_wf >> metis_tac[]) >>
  irule apply_ruleinstance_preserves_wf >>
  metis_tac[]
QED

(* Helper: mk_assignment_node produces an assignment that correctly evaluates the label.
   This is the key lemma that connects unify_label to eval_label_fun. *)
Theorem mk_assignment_node_eval_label:
  !r m G nid a.
    wf_rulegraph r.lhs /\ wf_rulegraph_labels r.lhs /\
    wf_hostgraph G /\
    mk_assignment_node r m G nid = SOME a ==>
    ?rl rm hl hm.
      FLOOKUP r.lhs.l nid = SOME (rl, rm) /\
      FLOOKUP (G.l f_o_f m.nodemap) nid = SOME (hl, hm) /\
      eval_label_fun a m G rl = SOME hl
Proof
  rpt strip_tac >> gvs[mk_assignment_node_def, unify_nodeattr_def] >>
  Cases_on `l1` >> Cases_on `l2` >> gvs[unify_nodeattr_def] >>
  qexistsl [`q'`, `r''`] >> conj_tac >- fs[f_o_f_DEF, FLOOKUP_DEF] >>
  `hostgraph_labels_spine G` by metis_tac[wf_hostgraph_IMP_hostgraph_labels_spine] >>
  irule unify_label_eval_label_fun >> rpt (first_x_assum $ irule_at Any) >>
  conj_tac
  >- (fs[hostgraph_labels_spine_def] >> drule_all FEVERY_FLOOKUP >> simp[])
  >- (fs[wf_rulegraph_labels_def] >> drule_all FEVERY_FLOOKUP >> simp[])
QED

(* mk_assignment_node implies nodemark_matches for the node's marks *)
Theorem mk_assignment_node_nodemark_matches:
  !r m G nid a.
    mk_assignment_node r m G nid = SOME a ==>
    ?rl rm hl hm.
      FLOOKUP r.lhs.l nid = SOME (rl, rm) /\
      FLOOKUP (G.l f_o_f m.nodemap) nid = SOME (hl, hm) /\
      nodemark_matches hm rm
Proof
  rpt strip_tac >>
  fs[mk_assignment_node_def] >>
  (* At this point: l1 from FLOOKUP r.lhs.l, v' from FLOOKUP m.nodemap,
     l2 from FLOOKUP G.l v', and unify_nodeattr succeeds *)
  PairCases_on `l1` >> PairCases_on `l2` >>
  fs[unify_nodeattr_def] >>
  (* unify_nodeattr expands to: do assert (nodemark_matches l21 l11); ... od = SOME a
     The OPTION_BIND only returns SOME when assert returns SOME () *)
  `nodemark_matches l21 l11` by (
    qpat_x_assum `_ = SOME a` mp_tac >>
    simp[optionTheory.OPTION_GUARD_EQ_THM, AllCaseEqs()]) >>
  qexistsl_tac [`l20`, `l21`] >>
  simp[f_o_f_DEF, FLOOKUP_DEF] >>
  gvs[FLOOKUP_DEF]
QED

(* NOTE: mk_assignment_*_wf_assignment_labels theorems were removed.
   The property wf_assignment_labels (requiring all values to be spines)
   is FALSE for unify_label results because variables typed as atoms
   can match atom heads of spine labels, producing non-spine values.

   Counterexample: typing = {x ↦ tyInt}, rl = x:nil, hl = 1:nil
   Result: {x ↦ label_integer 1} where label_integer 1 is NOT a spine.

   Use wf_assignment_spine instead (allows spines OR atoms). *)

(* Helper: Domain of f_o_f composition for morphism.
   When morphism domain/range are compatible with graph labeling domains,
   the composed map has the same domain as the source graph's labels. *)
Theorem f_o_f_morphism_FDOM:
  !G m L.
    wf_hostgraph G /\
    FDOM m.nodemap = L.V /\
    FRANGE m.nodemap SUBSET G.V /\
    totally_labelled_rulegraph L ==>
    FDOM (G.l f_o_f m.nodemap) = L.V
Proof
  rpt strip_tac >> simp[f_o_f_DEF, EXTENSION] >>
  rpt strip_tac >> EQ_TAC >> strip_tac >> simp[] >>
  gvs[wf_hostgraph_def] >>
  `m.nodemap ' x IN FRANGE m.nodemap`
    by (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
  gvs[SUBSET_DEF]
QED

(* Helper: Per-node assignment is SUBMAP of full assignment.
   mk_assignment merges node and edge assignments. For each node,
   the per-node assignment is a SUBMAP of the node-merged assignment,
   which is a SUBMAP of the full merged assignment. *)
Theorem mk_assignment_node_SUBMAP:
  !r m G assign nid.
    FINITE r.lhs.V /\
    mk_assignment r m G = SOME assign /\
    nid IN r.lhs.V ==>
    ?a_nid. mk_assignment_node r m G nid = SOME a_nid /\ a_nid SUBMAP assign
Proof
  rpt strip_tac >> gvs[mk_assignment_def, merge_assignment_def, AllCaseEqs()] >>
  `MEM nid (SET_TO_LIST r.lhs.V)` by simp[MEM_SET_TO_LIST] >>
  drule_at (Pos last) foldr_merge_SUBMAP >>
  disch_then (qspecl_then [`mk_assignment_node r m G`, `nassign`] mp_tac) >>
  simp[GSYM mk_assignment_nodes_def] >>
  strip_tac >> qexists_tac `a_x` >> simp[] >>
  irule SUBMAP_TRANS >> first_x_assum $ irule_at Any >>
  simp[SUBMAP_FUNION_ID]
QED

(* Edge version: Per-edge assignment is SUBMAP of full assignment *)
Theorem mk_assignment_edge_SUBMAP:
  !r m G assign eid.
    FINITE r.lhs.E /\
    mk_assignment r m G = SOME assign /\
    eid IN r.lhs.E ==>
    ?a_eid. mk_assignment_edge r m G eid = SOME a_eid /\ a_eid SUBMAP assign
Proof
  rpt strip_tac >> gvs[mk_assignment_def, merge_assignment_def, AllCaseEqs()] >>
  `MEM eid (SET_TO_LIST r.lhs.E)` by simp[MEM_SET_TO_LIST] >>
  drule_at (Pos last) foldr_merge_SUBMAP >>
  disch_then (qspecl_then [`mk_assignment_edge r m G`, `eassign`] mp_tac) >>
  simp[GSYM mk_assignment_edges_def] >>
  strip_tac >> qexists_tac `a_x` >> simp[] >>
  irule SUBMAP_TRANS >> first_x_assum $ irule_at Any >>
  (* eassign is right component of FUNION, use agree_on_common_keys *)
  irule SUBMAP_FUNION_agree_right >> simp[]
QED

(* Edge version: mk_assignment_edge produces an assignment that evaluates the rulegraph
   label back to the hostgraph label *)
Theorem mk_assignment_edge_eval_label:
  !r m G eid a.
    wf_rulegraph r.lhs /\ wf_rulegraph_labels r.lhs /\
    wf_hostgraph G /\
    mk_assignment_edge r m G eid = SOME a ==>
    ?rl rm hl hm.
      FLOOKUP r.lhs.m eid = SOME (rl, rm) /\
      FLOOKUP (G.m f_o_f m.edgemap) eid = SOME (hl, hm) /\
      eval_label_fun a m G rl = SOME hl
Proof
  rpt strip_tac >> gvs[mk_assignment_edge_def, unify_edgeattr_def] >>
  Cases_on `m1` >> Cases_on `m2` >> gvs[unify_edgeattr_def] >>
  qexistsl [`q'`, `r''`] >> conj_tac >- fs[f_o_f_DEF, FLOOKUP_DEF] >>
  `hostgraph_labels_spine G` by metis_tac[wf_hostgraph_IMP_hostgraph_labels_spine] >>
  irule unify_label_eval_label_fun >> rpt (first_x_assum $ irule_at Any) >>
  conj_tac
  >- (fs[hostgraph_labels_spine_def] >> drule_all FEVERY_FLOOKUP >> simp[])
  >- (fs[wf_rulegraph_labels_def] >> drule_all FEVERY_FLOOKUP >> simp[])
QED

(* mk_assignment_edge implies edgemark_matches for the edge's marks *)
Theorem mk_assignment_edge_edgemark_matches:
  !r m G eid a.
    mk_assignment_edge r m G eid = SOME a ==>
    ?rl rm hl hm.
      FLOOKUP r.lhs.m eid = SOME (rl, rm) /\
      FLOOKUP (G.m f_o_f m.edgemap) eid = SOME (hl, hm) /\
      edgemark_matches hm rm
Proof
  rpt strip_tac >>
  fs[mk_assignment_edge_def] >>
  PairCases_on `m1` >> PairCases_on `m2` >>
  fs[unify_edgeattr_def] >>
  `edgemark_matches m21 m11` by (
    qpat_x_assum `_ = SOME a` mp_tac >>
    simp[optionTheory.OPTION_GUARD_EQ_THM, AllCaseEqs()]) >>
  qexistsl_tac [`m20`, `m21`] >>
  simp[f_o_f_DEF, FLOOKUP_DEF] >>
  gvs[FLOOKUP_DEF]
QED

(* Edge version of f_o_f_morphism_FDOM *)
Theorem f_o_f_morphism_FDOM_edge:
  !G m L.
    wf_hostgraph G /\
    FDOM m.edgemap = L.E /\
    FRANGE m.edgemap SUBSET G.E /\
    totally_labelled_rulegraph L ==>
    FDOM (G.m f_o_f m.edgemap) = L.E
Proof
  rpt strip_tac >> simp[f_o_f_DEF, EXTENSION] >>
  rpt strip_tac >> EQ_TAC >> strip_tac >> simp[] >>
  gvs[wf_hostgraph_def] >>
  `m.edgemap ' x IN FRANGE m.edgemap`
    by (simp[FRANGE_DEF] >> qexists_tac `x` >> simp[]) >>
  gvs[SUBSET_DEF]
QED

(* Label preservation: mk_assignment creates an assignment such that
   instantiate_rulegraph produces a hostgraph whose labels match the original.

   The proof relies on:
   - mk_assignment_node calls unify_nodeattr which calls unify_label
   - unify_label creates an assignment mapping variables to host values
   - instantiate_nodeattr calls eval_label_fun with this assignment
   - By unify_label_eval_label_fun, evaluation returns the original host label

   The key property is that merge_assignment preserves the evaluation property
   because variables from the same rule pattern unify to consistent values.

   TODO: Complete proof using mk_assignment_node_eval_label and showing that
   the merged assignment preserves eval_label_fun via eval_label_fun_FUNION_left. *)
Theorem mk_assignment_preserves_nodelabels:
  !r assign m G lhs'.
    wf_rule r /\
    wf_hostgraph G /\
    wf_rulegraph_labels r.lhs /\
    is_prematch r.lhs r.inf m G /\
    mk_assignment r m G = SOME assign /\
    instantiate_rulegraph r.lhs assign m G = SOME lhs' ==>
    preserve_nodelabels lhs' m G
Proof
  rpt strip_tac >>
  (* Derive hostgraph_labels_spine from wf_hostgraph *)
  `hostgraph_labels_spine G` by metis_tac[wf_hostgraph_IMP_hostgraph_labels_spine] >>
  `wf_assignment_spine assign` by metis_tac[mk_assignment_wf_assignment_spine] >>
  simp[preserve_nodelabels_def, Once $ GSYM fmap_EQ_THM] >>
  rpt strip_tac
  (* Goal 1: Domain equality *)
  >- (
    `FDOM lhs'.l = r.lhs.V` by (
      imp_res_tac instantiate_rulegraph_wf >>
      imp_res_tac instantiate_rulegraph_preserves_V >>
      gvs[wf_rule_def, wf_hostgraph_def]) >>
    `FDOM (G.l f_o_f m.nodemap) = r.lhs.V` by (
      irule f_o_f_morphism_FDOM >> simp[] >>
      gvs[wf_rule_def, is_prematch_def, is_inj_premorphism_def,
          is_premorphism_def, morphism_dom_ran_def]) >>
    simp[])
  (* Goal 2: Per-element equality *)
  >- (
    `x IN r.lhs.V` by (
      imp_res_tac instantiate_rulegraph_wf >>
      imp_res_tac instantiate_rulegraph_preserves_V >>
      gvs[wf_rule_def, wf_hostgraph_def]) >>
    `FINITE r.lhs.V` by
      gvs[wf_rule_def, totally_labelled_rulegraph_def,
          wf_rulegraph_def, wf_graph_def] >>
    (* Get per-node assignment *)
    `?a_x. mk_assignment_node r m G x = SOME a_x /\ a_x SUBMAP assign` by (
      irule mk_assignment_node_SUBMAP >> simp[]) >>
    (* Get label evaluation via mk_assignment_node_eval_label *)
    `?rl rm hl hm. FLOOKUP r.lhs.l x = SOME (rl, rm) /\
       FLOOKUP (G.l f_o_f m.nodemap) x = SOME (hl, hm) /\
       eval_label_fun a_x m G rl = SOME hl` by (
      irule mk_assignment_node_eval_label >> simp[] >>
      gvs[wf_rule_def, totally_labelled_rulegraph_def]) >>
    (* Extend to full assignment via SUBMAP *)
    `eval_label_fun assign m G rl = SOME hl` by (
      irule eval_label_fun_SUBMAP >> metis_tac[]) >>
    (* Expand instantiate_rulegraph *)
    gvs[instantiate_rulegraph_def] >>
    `x IN FDOM r.lhs.l` by gvs[wf_rule_def, totally_labelled_rulegraph_def] >>
    `FINITE (FDOM r.lhs.l)` by simp[FDOM_FINITE] >>
    (* Connect fmap_buildM to instantiate_nodeattr *)
    `FLOOKUP l x = instantiate_nodeattr r.lhs assign m G x` by (
      drule_then drule fmap_buildM_FLOOKUP >> simp[]) >>
    (* Show eval_nodemark succeeds from mk_assignment_node *)
    (* Use mk_assignment_node_nodemark_matches to get nodemark_matches *)
    `nodemark_matches hm rm` by (
      drule mk_assignment_node_nodemark_matches >> strip_tac >> gvs[]) >>
    `eval_nodemark hm rm = SOME hm` by (
      Cases_on `rm` >> gvs[nodemark_matches_def, eval_nodemark_def] >>
      Cases_on `x'` >> gvs[nodemark_matches_def, eval_nodemark_def]) >>
    (* x is in domain of (G.l f_o_f m.nodemap) because FLOOKUP returned SOME *)
    `x IN FDOM (G.l f_o_f m.nodemap)` by gvs[FLOOKUP_DEF] >>
    (* Expand instantiate_nodeattr and resolve the matched case *)
    `instantiate_nodeattr r.lhs assign m G x = SOME (hl, hm)` by
      (simp[instantiate_nodeattr_def] >> gvs[]) >>
    gvs[FLOOKUP_DEF])
QED

(* Edge label preservation - analogous to node labels *)
Theorem mk_assignment_preserves_edgelabels:
  !r assign m G lhs'.
    wf_rule r /\
    wf_hostgraph G /\
    wf_rulegraph_labels r.lhs /\
    is_prematch r.lhs r.inf m G /\
    mk_assignment r m G = SOME assign /\
    instantiate_rulegraph r.lhs assign m G = SOME lhs' ==>
    preserve_edgelabels lhs' m G
Proof
  rpt strip_tac >>
  (* Derive hostgraph_labels_spine from wf_hostgraph *)
  `hostgraph_labels_spine G` by metis_tac[wf_hostgraph_IMP_hostgraph_labels_spine] >>
  `wf_assignment_spine assign` by metis_tac[mk_assignment_wf_assignment_spine] >>
  simp[preserve_edgelabels_def, Once $ GSYM fmap_EQ_THM] >>
  rpt strip_tac
  (* Goal 1: Domain equality *)
  >- (
    `FDOM lhs'.m = r.lhs.E` by (
      imp_res_tac instantiate_rulegraph_wf >>
      imp_res_tac instantiate_rulegraph_preserves_structure >>
      gvs[wf_rule_def, wf_hostgraph_def]) >>
    `FDOM (G.m f_o_f m.edgemap) = r.lhs.E` by (
      irule f_o_f_morphism_FDOM_edge >> simp[] >>
      gvs[wf_rule_def, is_prematch_def, is_inj_premorphism_def,
          is_premorphism_def, morphism_dom_ran_def]) >>
    simp[])
  (* Goal 2: Per-element equality *)
  >- (
    `x IN r.lhs.E` by (
      imp_res_tac instantiate_rulegraph_wf >>
      imp_res_tac instantiate_rulegraph_preserves_structure >>
      gvs[wf_rule_def, wf_hostgraph_def]) >>
    `FINITE r.lhs.E` by
      gvs[wf_rule_def, totally_labelled_rulegraph_def,
          wf_rulegraph_def, wf_graph_def] >>
    (* Get per-edge assignment *)
    `?a_x. mk_assignment_edge r m G x = SOME a_x /\ a_x SUBMAP assign` by (
      irule mk_assignment_edge_SUBMAP >> simp[]) >>
    (* Get label evaluation via mk_assignment_edge_eval_label *)
    `?rl rm hl hm. FLOOKUP r.lhs.m x = SOME (rl, rm) /\
       FLOOKUP (G.m f_o_f m.edgemap) x = SOME (hl, hm) /\
       eval_label_fun a_x m G rl = SOME hl` by (
      irule mk_assignment_edge_eval_label >> simp[] >>
      gvs[wf_rule_def, totally_labelled_rulegraph_def]) >>
    (* Extend to full assignment via SUBMAP *)
    `eval_label_fun assign m G rl = SOME hl` by (
      irule eval_label_fun_SUBMAP >> metis_tac[]) >>
    (* Expand instantiate_rulegraph *)
    gvs[instantiate_rulegraph_def] >>
    `x IN FDOM r.lhs.m` by gvs[wf_rule_def, totally_labelled_rulegraph_def, wf_rulegraph_def] >>
    `FINITE (FDOM r.lhs.m)` by simp[FDOM_FINITE] >>
    (* Connect fmap_buildM to instantiate_edgeattr *)
    `FLOOKUP m' x = instantiate_edgeattr r.lhs assign m G x` by (
      drule_then drule fmap_buildM_FLOOKUP >> simp[]) >>
    (* Use mk_assignment_edge_edgemark_matches to get edgemark_matches *)
    `edgemark_matches hm rm` by (
      drule mk_assignment_edge_edgemark_matches >> strip_tac >> gvs[]) >>
    `eval_edgemark hm rm = SOME hm` by (
      Cases_on `rm` >> gvs[edgemark_matches_def, eval_edgemark_def] >>
      Cases_on `x'` >> gvs[edgemark_matches_def, eval_edgemark_def]) >>
    (* x is in domain of (G.m f_o_f m.edgemap) because FLOOKUP returned SOME *)
    `x IN FDOM (G.m f_o_f m.edgemap)` by gvs[FLOOKUP_DEF] >>
    (* Expand instantiate_edgeattr and resolve the matched case *)
    `instantiate_edgeattr r.lhs assign m G x = SOME (hl, hm)` by
      (simp[instantiate_edgeattr_def] >> gvs[]) >>
    gvs[FLOOKUP_DEF])
QED

(* Key lemma: is_prematch on rulegraph implies is_match on instantiated hostgraph.

   The proof relies on:
   1. Structure preservation: instantiate_rulegraph preserves V, E, s, t, p
   2. Injectivity preservation: same morphism m, same domain/range structure
   3. Dangling condition preservation: depends only on structure
   4. Label preservation: instantiation produces matching labels (from mk_assignment)

   Since instantiate_rulegraph preserves the graph structure exactly,
   and is_prematch ensures injectivity + dangling condition on that structure,
   these properties transfer directly to the instantiated hostgraph.
   The label part of is_inj_morphism is satisfied because mk_assignment
   unifies the parametric labels with the host graph labels. *)
Theorem prematch_instantiation_is_match:
  !r assign m G ri.
    wf_rule r /\
    wf_hostgraph G /\
    wf_rulegraph_labels r.lhs /\
    is_prematch r.lhs r.inf m G /\
    mk_assignment r m G = SOME assign /\
    instantiate_rule r assign m G = SOME ri ==>
    is_match ri.lhs ri.inf m G
Proof
  rpt strip_tac >> fs[is_match_def, is_prematch_def, instantiate_rule_def] >>
  gvs[] >> conj_tac >> simp[is_inj_morphism_def, is_morphism_def]
  >- (
    `lhs'.V = r.lhs.V /\ lhs'.E = r.lhs.E /\ lhs'.s = r.lhs.s /\
     lhs'.t = r.lhs.t /\ lhs'.p = r.lhs.p`
      by (imp_res_tac instantiate_rulegraph_preserves_structure >> fs[]) >>
    fs[is_inj_premorphism_def] >>
    rpt conj_tac
    >- fs[is_premorphism_def, morphism_dom_ran_def, preserve_source_def,
          preserve_target_def, preserve_defined_rootedness_def]
    >- (`is_prematch r.lhs r.inf m G` by fs[is_prematch_def, is_inj_premorphism_def] >>
        drule_all mk_assignment_preserves_edgelabels >> simp[])
    >- (`is_prematch r.lhs r.inf m G` by fs[is_prematch_def, is_inj_premorphism_def] >>
        drule_all mk_assignment_preserves_nodelabels >> simp[]))
  >- (
    fs[is_inj_premorphism_def, satisfy_dangling_condition_def] >>
    rpt strip_tac
    >- (
      `lhs'.V = r.lhs.V /\ lhs'.E = r.lhs.E`
        by (imp_res_tac instantiate_rulegraph_preserves_structure >> fs[]) >>
      gvs[] >> metis_tac[])
    >- (
      `lhs'.V = r.lhs.V /\ lhs'.E = r.lhs.E`
        by (imp_res_tac instantiate_rulegraph_preserves_structure >> fs[]) >>
      gvs[] >> metis_tac[]))
QED

(* apply_rule preserves wf_hostgraph when the rule is well-formed and
   we have a valid prematch (injective + dangling condition).

   This is the key theorem needed for step_preserves_wf_stack.
   With is_prematch as the premise (matching the Call1 rule), the proof is:
   1. prematch_instantiation_is_match gives is_match on instantiated graph
   2. instantiate_rule_wf shows the ruleinstance is well-formed
   3. apply_ruleinstance_preserves_wf (via wf_dpo) gives the result *)
Theorem apply_rule_preserves_wf_simple:
  !r m G h.
    wf_rule r /\
    wf_hostgraph G /\
    wf_rulegraph_labels r.lhs /\
    is_prematch r.lhs r.inf m G /\
    apply_rule r m G = SOME h ==>
    wf_hostgraph h
Proof
  rpt strip_tac >>
  gvs[apply_rule_def] >>
  (* Derive hostgraph_labels_spine from wf_hostgraph *)
  `hostgraph_labels_spine G` by metis_tac[wf_hostgraph_IMP_hostgraph_labels_spine] >>
  `wf_assignment_spine assign` by metis_tac[mk_assignment_wf_assignment_spine] >>
  `is_match instance.lhs instance.inf m G`
    by (irule prematch_instantiation_is_match >> metis_tac[]) >>
  (* FDOM properties now derivable from wf_rule via totally_labelled_rulegraph *)
  `wf_ruleinstance instance` by (irule instantiate_rule_wf >> metis_tac[]) >>
  irule apply_ruleinstance_preserves_wf >> metis_tac[]
QED

(* apply_rule preserves hostgraph_labels_spine.
   Key insight: the result graph's labels come from:
   1. The instantiated RHS (which has hostgraph_labels_spine via instantiate_rulegraph_wf)
   2. The preserved parts of G via deletion (which have hostgraph_labels_spine since G does)

   The proof establishes:
   - wf_assignment_spine assign (via mk_assignment properties)
   - hostgraph_labels_spine instance.rhs and instance.lhs (via instantiate_rulegraph_wf)
   - hostgraph_labels_spine for deletion result (deletion preserves labels via DRESTRICT)

   KNOWN ISSUE: The final step (gluing preserves hostgraph_labels_spine) requires fixing
   gluing_l_def and gluing_m_def in dpoScript.sml. Currently these definitions:
   1. Use tagged keys to look up in maps with untagged keys
   2. Have H and R swapped (left-tagged from H.V should use H.l, not R.l)

   The correct definitions should use untag_nodeid:
     if is_left_tagged_nodeid nid
       then (nid, H.l ' (untag_nodeid nid))   (* left-tagged from H *)
       else (nid, R.l ' (untag_nodeid nid))   (* right-tagged from R *)

   Once dpoScript.sml is fixed, this proof can be completed by showing:
   - For left-tagged nid: untag_nodeid nid IN FDOM H.l, so H.l lookup is valid
   - For right-tagged nid: untag_nodeid nid IN FDOM R.l, so R.l lookup is valid
   - Both H.l and R.l satisfy FEVERY (is_hostlabel_spine o FST o SND) *)
Theorem apply_rule_preserves_hostgraph_labels_spine:
  !r m G h.
    wf_rule r /\
    wf_hostgraph G /\
    wf_rulegraph_labels r.lhs /\
    wf_rulegraph_labels r.rhs /\
    is_prematch r.lhs r.inf m G /\
    apply_rule r m G = SOME h ==>
    hostgraph_labels_spine h
Proof
  rpt strip_tac >> gvs[apply_rule_def] >>
  fs[apply_ruleinstance_def] >>
  `hostgraph_labels_spine G` by metis_tac[wf_hostgraph_IMP_hostgraph_labels_spine] >>
  `wf_assignment_spine assign` by (irule mk_assignment_wf_assignment_spine >> metis_tac[]) >>
  `wf_ruleinstance instance` by (irule instantiate_rule_wf >> metis_tac[]) >>
  `is_match instance.lhs instance.inf m G` by (irule prematch_instantiation_is_match >> metis_tac[]) >>
  `wf_hostgraph instance.lhs /\ wf_hostgraph instance.rhs /\
   instance.inf SUBSET instance.lhs.V /\ instance.inf SUBSET instance.rhs.V` by fs[wf_ruleinstance_def] >>
  `wf_hostgraph (dpo instance.lhs instance.inf instance.rhs m G)` by (irule wf_dpo >> metis_tac[]) >>
  metis_tac[wf_hostgraph_IMP_hostgraph_labels_spine]
QED

(* TRACKED SEMANTICS                                                  *)
(*                                                                    *)
(* Extends the step relation to thread track morphisms through        *)
(* execution. The track morphism witnesses how the initial graph      *)
(* embeds into the current graph through the derivation.              *)

(* Step relation with composed track morphism threading.
   Stack elements are (H, tr) pairs where:
   - H is the current hostgraph
   - tr is the COMPOSED track morphism from G0 (original input) to H
   The track is composed at each rule application, so after a derivation
   G0 -> G1 -> ... -> H, we have a direct track tr: G0 -> H.
   Domain of tr shrinks as elements get deleted through the derivation. *)
Inductive step:
(* Rule application: compose new DPO track with accumulated track *)
[~Call1:]
  !env rset S G tr rest rname (r:rule) m h ri assign.
    pop_stack S = SOME ((G, tr), rest) /\
    rname IN rset /\
    FLOOKUP env.rule rname = SOME r /\
    is_prematch r.lhs r.inf m G /\
    mk_assignment r m G = SOME assign /\
    instantiate_rule r assign m G = SOME ri /\
    apply_ruleinstance ri m G = SOME h
    ==>
    step env
      (running (term_rscall rset), S)
      (final, push_stack (h,
                          compose_morphism (track ri.lhs ri.inf m G) tr) rest)

(* Rule failure: no track change *)
[~Call2:]
  !env rset S G tr rest.
    pop_stack S = SOME ((G, tr), rest) /\
    ~(?rname r m h. rname IN rset /\ FLOOKUP env.rule rname = SOME r /\
                    is_prematch r.lhs r.inf m G /\ apply_rule r m G = SOME h)
    ==>
    step env (running (term_rscall rset), S) (failed, S)

(* Procedure call: no track change *)
[~ProcCall:]
  !env p S.
    FLOOKUP env.proc p = SOME cont ==>
    step env (running (term_proc p), S) (running cont, S)

(* Sequence: track propagates through subterm execution *)
[~Seq1:]
  !env P S P' S' Q.
    step env (running P, S) (running P', S') ==>
    step env (running (term_seq P Q), S) (running (term_seq P' Q), S')

[~Seq2:]
  !env P S S' Q.
    step env (running P, S) (final, S') ==>
    step env (running (term_seq P Q), S) (running Q, S')

[~Seq3:]
  !env P S Q.
    step env (running P, S) (failed, S) ==>
    step env (running (term_seq P Q), S) (failed, S)

[~Break:]
  !env P S.
    step env (running (term_seq term_break P), S) (running term_break, S)

(* ALAP loop *)
[~Alap1:]
  !env P S.
    step env (running (term_alap P), S) (running (term_trte P (term_alap P) term_skip), S)

[~Alap2:]
  !env S h P.
    pop2_stack S = SOME h ==>
    step env (running (term_TRY term_break (term_alap P) term_skip), S) (final, SND h)

(* If-then-else: push saved state, condition discarded on success *)
[~If1:]
  !env S el C P Q.
    top_stack S = SOME el ==>
    step env (running (term_ifte C P Q), S) (running (term_ITE C P Q), push_stack el S)

[~If2:]
  !env C S C' S' P Q.
    step env (running C, S) (running C', S') ==>
    step env (running (term_ITE C P Q), S) (running (term_ITE C' P Q), S')

(* If condition succeeds: DISCARD condition's track, restore saved *)
[~If3:]
  !env C P S S' r Q.
    step env (running C, S) (final, S') /\
    pop_stack S' = SOME r ==>
    step env (running (term_ITE C P Q), S) (running P, SND r)

(* If condition fails: restore saved state *)
[~If4:]
  !env C S S' P Q.
    step env (running C, S) (failed, S) /\
    pop_stack S = SOME S' ==>
    step env (running (term_ITE C P Q), S) (running Q, SND S')

(* Try-then-else: push saved state, condition KEPT on success *)
[~Try1:]
  !env S el C P Q.
    top_stack S = SOME el ==>
    step env (running (term_trte C P Q), S) (running (term_TRY C P Q), push_stack el S)

[~Try2:]
  !env C S C' S' P Q.
    step env (running C, S) (running C', S') ==>
    step env (running (term_TRY C P Q), S) (running (term_TRY C' P Q), S')

(* Try condition succeeds: KEEP condition's result and track *)
[~Try3:]
  !env C P S S' r Q.
    step env (running C, S) (final, S') /\
    pop2_stack S' = SOME r ==>
    step env (running (term_TRY C P Q), S) (running P, SND r)

(* Try condition fails: restore saved state *)
[~Try4:]
  !env C S S' P Q.
    step env (running C, S) (failed, S) /\
    pop_stack S = SOME S' ==>
    step env (running (term_TRY C P Q), S) (running Q, SND S')

(* Non-deterministic choice: track follows chosen branch *)
[~Or1:]
  !env P Q S.
    step env (running (term_or P Q), S) (running P, S)

[~Or2:]
  !env P Q S.
    step env (running (term_or P Q), S) (running Q, S)

(* Skip and Fail: no track change *)
[~Skip:]
  !env S.
    step env (running term_skip, S) (final, S)

[~Fail:]
  !env S.
    step env (running term_fail, S) (failed, S)
End

(* Step only from running states (not final/failed/break) *)
Theorem step_only_running:
  !env P Q. step env P Q ==> can_step P
Proof
 rpt strip_tac
\\ Cases_on `P`
\\ rename1 `can_step (t, s)`
\\ Cases_on `t`
>- ( Cases_on `t'` \\ rw[can_step_def]
     \\ fs[Once step_cases]
   )
\\ rw[can_step_def]
\\ fs[Once step_cases]
QED

Theorem step_only_running_rewrs:
    ~(step env (failed, s) res) /\ ~(step env (final, s) res)
Proof
  metis_tac [step_only_running, can_step_def]
QED

(* Multi-step execution *)
Definition steps_def:
  steps (env:program) = RTC (step env)
End

Theorem steps_NRC:
  steps env c c' <=> ?n. NRC (step env) n c c'
Proof
  simp [steps_def, arithmeticTheory.RTC_eq_NRC]
QED

(* Evaluation: returns final graph and composed track morphism.
   The initial stack element is (G, id_track G) - identity track on G.
   The final result (H, tr) has tr: G -> H (composed through derivation).
   tr maps surviving elements of G to their positions in H. *)
Definition evaluate_def:
  evaluate (env:program) (G:hostgraph) (P:term) (H:hostgraph, tr:morphism) <=>
    ?S. steps env (running P, [(G, id_track G)]) (final, S) /\
        ~can_step (final, S) /\
        ?rest. S = (H, tr) :: rest
End

Definition evaluates_def:
  evaluates (env:program) (G:hostgraph) (P:term) <=>
    ?H tr. evaluate env G P (H, tr)
End

val () = export_theory ()
