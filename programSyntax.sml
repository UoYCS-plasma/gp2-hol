structure programSyntax :> programSyntax =
struct

open HolKernel boolLib

val ERR = Feedback.mk_HOL_ERR "programSyntax"

local open programTheory ruleTheory rulegraphTheory hostgraphSyntax rulegraphSyntax Parsetree in end;

structure P = Parsetree;
val _ = Meta.fakeload "P";

fun mk_const_tm n = prim_mk_const{Name=n, Thy="program"};
fun rule_const_tm n = prim_mk_const{Name=n, Thy="rule"};
fun fns1 n = HolKernel.syntax_fns1 "program" n
fun fns2 n = HolKernel.syntax_fns2 "program" n
fun fns3 n = HolKernel.syntax_fns3 "program" n
fun rule_fns1 n = HolKernel.syntax_fns1 "rule" n

(* Basic types *)
val procid_ty = ``:procid``
val ruleid_ty = ``:ruleid``
val term_ty = ``:term``
val rule_ty = ``:rule``
val program_ty = ``:program``

(* Term constructors *)
val (term_seq_tm, mk_term_seq, dest_term_seq, is_term_seq) = fns2 "term_seq"
val (term_or_tm, mk_term_or, dest_term_or, is_term_or) = fns2 "term_or"
val (term_ifte_tm, mk_term_ifte, dest_term_ifte, is_term_ifte) = fns3 "term_ifte"
val (term_trte_tm, mk_term_trte, dest_term_trte, is_term_trte) = fns3 "term_trte"
val (term_rscall_tm, mk_term_rscall, dest_term_rscall, is_term_rscall) = fns1 "term_rscall"
val (term_proc_tm, mk_term_proc, dest_term_proc, is_term_proc) = fns1 "term_proc"
val (term_alap_tm, mk_term_alap, dest_term_alap, is_term_alap) = fns1 "term_alap"

val term_skip_tm = mk_const_tm "term_skip"
val term_fail_tm = mk_const_tm "term_fail"
val term_break_tm = mk_const_tm "term_break"

(* Rule ID constructor *)
val (ruleid_tm, mk_ruleid, dest_ruleid, is_ruleid) = rule_fns1 "ruleid"

(* Well-formedness *)
val (wf_program_tm, mk_wf_program, dest_wf_program, is_wf_program) = fns1 "wf_program"

(* Helper functions *)
fun MK_procid s = stringSyntax.fromMLstring s
fun MK_ruleid s = mk_ruleid (stringSyntax.fromMLstring s)

(* Translation functions *)
fun mk_term_from_parsetree (term: P.term) =
    case term of
        P.term_seq terms =>
        let fun fold_seq [] = term_skip_tm
              | fold_seq [t] = mk_term_from_parsetree t
              | fold_seq (t::ts) = mk_term_seq (mk_term_from_parsetree t, fold_seq ts)
        in fold_seq terms
        end
      | P.term_or (t1, t2) => mk_term_or (mk_term_from_parsetree t1, mk_term_from_parsetree t2)
      | P.term_ifte (cond, then_opt, else_opt) =>
        let val cond_tm = mk_term_from_parsetree cond
            val then_tm = case then_opt of SOME t => mk_term_from_parsetree t | NONE => term_skip_tm
            val else_tm = case else_opt of SOME t => mk_term_from_parsetree t | NONE => term_skip_tm
        in mk_term_ifte (cond_tm, then_tm, else_tm)
        end
      | P.term_trte (cond, then_opt, else_opt) =>
        let val cond_tm = mk_term_from_parsetree cond
            val then_tm = case then_opt of SOME t => mk_term_from_parsetree t | NONE => term_skip_tm
            val else_tm = case else_opt of SOME t => mk_term_from_parsetree t | NONE => term_skip_tm
        in mk_term_trte (cond_tm, then_tm, else_tm)
        end
      | P.term_rscall rids =>
        let val rid_terms = map MK_ruleid rids
            val rid_set = if null rid_terms
                         then pred_setSyntax.mk_empty ruleid_ty
                         else pred_setSyntax.prim_mk_set (rid_terms, ruleid_ty)
        in mk_term_rscall rid_set
        end
      | P.term_rule rid => mk_term_rscall (pred_setSyntax.prim_mk_set ([MK_ruleid rid], ruleid_ty))
      | P.term_proc pid => mk_term_proc (MK_procid pid)
      | P.term_alap t => mk_term_alap (mk_term_from_parsetree t)
      | P.term_skip => term_skip_tm
      | P.term_fail => term_fail_tm
      | P.term_break => term_break_tm

fun mk_cond_from_parsetree (cond: P.cond) =
    let fun rule_const n = prim_mk_const{Name=n, Thy="rule"}
        val mk_condSubtype = HolKernel.syntax_fns2 "rule" "condSubtype" |> #2
        val mk_condEdgeTest = HolKernel.syntax_fns3 "rule" "condEdgeTest" |> #2
        val mk_condLabelEq = HolKernel.syntax_fns2 "rule" "condLabelEq" |> #2
        val mk_condLabelNeq = HolKernel.syntax_fns2 "rule" "condLabelNeq" |> #2
        val mk_condGt = HolKernel.syntax_fns2 "rule" "condGt" |> #2
        val mk_condGteq = HolKernel.syntax_fns2 "rule" "condGteq" |> #2
        val mk_condLt = HolKernel.syntax_fns2 "rule" "condLt" |> #2
        val mk_condLteq = HolKernel.syntax_fns2 "rule" "condLteq" |> #2
        val mk_condAnd = HolKernel.syntax_fns2 "rule" "condAnd" |> #2
        val mk_condOr = HolKernel.syntax_fns2 "rule" "condOr" |> #2
        val mk_condNot = HolKernel.syntax_fns1 "rule" "condNot" |> #2

        fun mk_ty_term ty = case ty of
            P.int_ty => prim_mk_const{Name="tyInt", Thy="typing"}
          | P.char_ty => prim_mk_const{Name="tyChar", Thy="typing"}
          | P.string_ty => prim_mk_const{Name="tyString", Thy="typing"}
          | P.atom_ty => prim_mk_const{Name="tyAtom", Thy="typing"}
          | P.list_ty => prim_mk_const{Name="tyList", Thy="typing"}

        fun mk_nodeid_term s =
            let val (_, mk_fn, _, _) = HolKernel.syntax_fns1 "graph" "nodeid"
            in mk_fn (stringSyntax.fromMLstring s)
            end
        fun mk_varname_term s =
            let val (_, mk_fn, _, _) = HolKernel.syntax_fns1 "rulegraph" "varname"
            in mk_fn (stringSyntax.fromMLstring s)
            end

    in case cond of
        P.cond_issubtype (ty, var) =>
        mk_condSubtype (mk_ty_term ty, mk_varname_term var)
      | P.cond_edgetest (n1, n2, lbl_opt) =>
        let val n1_tm = mk_nodeid_term n1
            val n2_tm = mk_nodeid_term n2
            val lbl_tm = case lbl_opt of
                SOME lbl => optionSyntax.mk_some (rulegraphSyntax.mk_rule_edge_attr lbl)
              | NONE => optionSyntax.mk_none (``:rulegraph$edgeattr``)
        in mk_condEdgeTest (n1_tm, n2_tm, lbl_tm)
        end
      | P.cond_eq (l1, l2) =>
        mk_condLabelEq (rulegraphSyntax.mk_rule_label_list l1, rulegraphSyntax.mk_rule_label_list l2)
      | P.cond_neq (l1, l2) =>
        mk_condLabelNeq (rulegraphSyntax.mk_rule_label_list l1, rulegraphSyntax.mk_rule_label_list l2)
      | P.cond_expr_gt (e1, e2) =>
        mk_condGt (rulegraphSyntax.mk_rule_label_from_expr e1, rulegraphSyntax.mk_rule_label_from_expr e2)
      | P.cond_expr_gteq (e1, e2) =>
        mk_condGteq (rulegraphSyntax.mk_rule_label_from_expr e1, rulegraphSyntax.mk_rule_label_from_expr e2)
      | P.cond_expr_lt (e1, e2) =>
        mk_condLt (rulegraphSyntax.mk_rule_label_from_expr e1, rulegraphSyntax.mk_rule_label_from_expr e2)
      | P.cond_expr_lteq (e1, e2) =>
        mk_condLteq (rulegraphSyntax.mk_rule_label_from_expr e1, rulegraphSyntax.mk_rule_label_from_expr e2)
      | P.cond_and (c1, c2) =>
        mk_condAnd (mk_cond_from_parsetree c1, mk_cond_from_parsetree c2)
      | P.cond_or (c1, c2) =>
        mk_condOr (mk_cond_from_parsetree c1, mk_cond_from_parsetree c2)
      | P.cond_not c =>
        mk_condNot (mk_cond_from_parsetree c)
    end

fun mk_ruledecl_from_parsetree (ruledecl: P.ruledecl) =
    let val {rid, vars, lhs, rhs, interf, cond} = ruledecl

        (* Create variable type map *)
        fun mk_var_map vardecls =
            let val ty_ty = ``:ty``
                val varname_ty = ``:varname``
                val empty_tm = finite_mapSyntax.mk_fempty (varname_ty, ty_ty)

                fun mk_ty_term ty = case ty of
                    P.int_ty => prim_mk_const{Name="tyInt", Thy="typing"}
                  | P.char_ty => prim_mk_const{Name="tyChar", Thy="typing"}
                  | P.string_ty => prim_mk_const{Name="tyString", Thy="typing"}
                  | P.atom_ty => prim_mk_const{Name="tyAtom", Thy="typing"}
                  | P.list_ty => prim_mk_const{Name="tyList", Thy="typing"}

                fun expand_vardecl {vars, ty} =
                    map (fn v => pairSyntax.mk_pair (rulegraphSyntax.MK_varname v, mk_ty_term ty)) vars

                val all_pairs = List.concat (map expand_vardecl vardecls)
                val pair_ty = pairSyntax.mk_prod (varname_ty, ty_ty)
                val list_tm = listSyntax.mk_list (all_pairs, pair_ty)
            in finite_mapSyntax.mk_fupdate_list (empty_tm, list_tm)
            end

        (* Create interface nodeid set *)
        fun mk_interface_set nodeids =
            let val nodeid_ty = ``:nodeid``
                fun mk_nodeid_from_string n =
                    let val (_, mk_fn, _, _) = HolKernel.syntax_fns1 "graph" "nodeid"
                    in mk_fn (stringSyntax.fromMLstring n)
                    end
                val nodeid_terms = map mk_nodeid_from_string nodeids
            in if null nodeid_terms
               then pred_setSyntax.mk_empty nodeid_ty
               else pred_setSyntax.prim_mk_set (nodeid_terms, nodeid_ty)
            end

        val vars_tm = mk_var_map vars
        val lhs_tm = rulegraphSyntax.mk_rulegraph_tm lhs
        val rhs_tm = rulegraphSyntax.mk_rulegraph_tm rhs
        val inf_tm = mk_interface_set interf
        val cond_tm = case cond of
            SOME c => optionSyntax.mk_some (mk_cond_from_parsetree c)
          | NONE => optionSyntax.mk_none (``:cond``)

        val components = [("vars", vars_tm), ("lhs", lhs_tm), ("rhs", rhs_tm), ("inf", inf_tm), ("cond", cond_tm)]
    in TypeBase.mk_record (rule_ty, components)
    end

(* Expand bidirectional edges: for k bidir edges in a rule, produce 2^k
   copies each picking one orientation per edge. *)
fun expand_bidir_rules (prog : P.program) : P.program =
    let
        (* Collect bidirectional edge IDs from a rulegraph *)
        fun bidir_eids (g : P.rulegraph) =
            List.mapPartial (fn (e : P.ruleedge) =>
                if #bidirectional e then SOME (#eid e) else NONE) (#edges g)

        (* Generate all 2^k boolean lists *)
        fun all_orientations 0 = [[]]
          | all_orientations k =
            let val rest = all_orientations (k - 1)
            in map (fn l => false :: l) rest @ map (fn l => true :: l) rest
            end

        (* Apply orientation to a graph: swap src/trg for edges in swap_set,
           set all bidirectional=false *)
        fun apply_orientation swap_set (g : P.rulegraph) : P.rulegraph =
            let fun member x xs = List.exists (fn y => y = x) xs
                fun rewrite_edge (e : P.ruleedge) =
                    let val swap = member (#eid e) swap_set
                    in {eid = #eid e, bidirectional = false,
                        src = if swap then #trg e else #src e,
                        trg = if swap then #src e else #trg e,
                        label = #label e}
                    end
            in {nodes = #nodes g,
                edges = map rewrite_edge (#edges g),
                position = #position g}
            end

        (* Expand one rule declaration into 1 or 2^k variants *)
        fun expand_one_rule (rd : P.ruledecl) : P.ruledecl list =
            let val lhs_bids = bidir_eids (#lhs rd)
                val rhs_bids = bidir_eids (#rhs rd)
                fun member x xs = List.exists (fn y => y = x) xs
                val all_bids = lhs_bids @
                    List.filter (fn e => not (member e lhs_bids)) rhs_bids
                val k = length all_bids
            in if k = 0 then [rd]
               else
                let val orients = all_orientations k
                    fun mk_variant (i, orient) =
                        let val swap_set = List.mapPartial
                                (fn (eid, sw) => if sw then SOME eid else NONE)
                                (ListPair.zip (all_bids, orient))
                        in {rid = #rid rd ^ "_" ^ Int.toString (i + 1),
                            vars = #vars rd,
                            lhs = apply_orientation swap_set (#lhs rd),
                            rhs = apply_orientation swap_set (#rhs rd),
                            interf = #interf rd,
                            cond = #cond rd}
                        end
                in List.tabulate (length orients,
                        fn i => mk_variant (i, List.nth (orients, i)))
                end
            end

        (* Phase 1: Expand all decl_rule entries, build rid mapping *)
        fun expand_decls (decls : P.decl list)
                : P.decl list * (string * string list) list =
            let fun process (decl, (acc_d, acc_m)) =
                    case decl of
                        P.decl_rule rd =>
                        let val variants = expand_one_rule rd
                            val new_rids = map #rid variants
                        in (acc_d @ map P.decl_rule variants,
                            (#rid rd, new_rids) :: acc_m)
                        end
                      | P.decl_proc (pdecl, local_decls) =>
                        let val (exp_locals, local_m) = expand_decls local_decls
                        in (acc_d @ [P.decl_proc (pdecl, exp_locals)],
                            acc_m @ local_m)
                        end
            in List.foldl process ([], []) decls
            end

        (* Phase 2: Rewrite terms referencing expanded rules *)
        fun lookup_rid mapping rid =
            case List.find (fn (old, _) => old = rid) mapping of
                SOME (_, new_rids) => SOME new_rids
              | NONE => NONE

        fun rewrite_term mapping (t : P.term) : P.term =
            case t of
                P.term_rule rid =>
                (case lookup_rid mapping rid of
                    SOME [single] => P.term_rule single
                  | SOME new_rids => P.term_rscall new_rids
                  | NONE => t)
              | P.term_rscall rids =>
                let val new_rids = List.concat
                        (map (fn r => case lookup_rid mapping r of
                                          SOME rs => rs | NONE => [r]) rids)
                in P.term_rscall new_rids
                end
              | P.term_seq ts =>
                P.term_seq (map (rewrite_term mapping) ts)
              | P.term_or (t1, t2) =>
                P.term_or (rewrite_term mapping t1, rewrite_term mapping t2)
              | P.term_ifte (c, t1, t2) =>
                P.term_ifte (rewrite_term mapping c,
                             Option.map (rewrite_term mapping) t1,
                             Option.map (rewrite_term mapping) t2)
              | P.term_trte (c, t1, t2) =>
                P.term_trte (rewrite_term mapping c,
                             Option.map (rewrite_term mapping) t1,
                             Option.map (rewrite_term mapping) t2)
              | P.term_alap t1 =>
                P.term_alap (rewrite_term mapping t1)
              | _ => t

        fun rewrite_decls mapping (decls : P.decl list) : P.decl list =
            map (fn decl => case decl of
                P.decl_rule _ => decl
              | P.decl_proc ({pid, cmds}, local_decls) =>
                P.decl_proc ({pid = pid,
                              cmds = map (rewrite_term mapping) cmds},
                             rewrite_decls mapping local_decls)
            ) decls

        val (expanded, mapping) = expand_decls prog
    in rewrite_decls mapping expanded
    end

fun mk_program_tm (program: P.program) =
    let fun collect_decls (decls: P.decl list) =
            let fun process_decl (decl, (proc_acc, rule_acc)) = case decl of
                    P.decl_rule rdecl =>
                    let val rule_tm = mk_ruledecl_from_parsetree rdecl
                        val rid_tm = MK_ruleid (#rid rdecl)
                    in (proc_acc, (rid_tm, rule_tm) :: rule_acc)
                    end
                  | P.decl_proc ({pid, cmds}, local_decls) =>
                    let val term_tm = mk_term_from_parsetree (P.term_seq cmds)
                        val pid_tm = MK_procid pid
                        val (local_procs, local_rules) = collect_decls local_decls
                    in ((pid_tm, term_tm) :: (proc_acc @ local_procs), rule_acc @ local_rules)
                    end
            in List.foldr process_decl ([], []) decls
            end

        val (procs, rules) = collect_decls program

        (* Create procedure map *)
        val proc_map =
            let val empty_tm = finite_mapSyntax.mk_fempty (procid_ty, term_ty)
                val pairs = map (fn (pid, term) => pairSyntax.mk_pair (pid, term)) procs
                val pair_ty = pairSyntax.mk_prod (procid_ty, term_ty)
                val list_tm = listSyntax.mk_list (pairs, pair_ty)
            in finite_mapSyntax.mk_fupdate_list (empty_tm, list_tm)
            end

        (* Create rule map *)
        val rule_map =
            let val empty_tm = finite_mapSyntax.mk_fempty (ruleid_ty, rule_ty)
                val pairs = map (fn (rid, rule) => pairSyntax.mk_pair (rid, rule)) rules
                val pair_ty = pairSyntax.mk_prod (ruleid_ty, rule_ty)
                val list_tm = listSyntax.mk_list (pairs, pair_ty)
            in finite_mapSyntax.mk_fupdate_list (empty_tm, list_tm)
            end

        val components = [("proc", proc_map), ("rule", rule_map)]
    in TypeBase.mk_record (program_ty, components)
    end

end
