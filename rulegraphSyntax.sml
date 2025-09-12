structure rulegraphSyntax :> rulegraphSyntax =
struct

open HolKernel boolLib

val ERR = Feedback.mk_HOL_ERR "rulegraphSyntax"

local open rulegraphTheory graphTheory Parsetree in end;

structure P = Parsetree;
val _ = Meta.fakeload "P";

fun mk_const_tm n = prim_mk_const{Name=n, Thy="rulegraph"};
fun fns1 n = HolKernel.syntax_fns1 "rulegraph" n
fun fns2 n = HolKernel.syntax_fns2 "rulegraph" n

val nodeid_ty = ``:nodeid``
val edgeid_ty = ``:edgeid``
val varname_ty = ``:varname``
val rulegraph_ty = ``:rulegraph``
val nodemark_ty = ``:rulegraph$nodemark``
val edgemark_ty = ``:rulegraph$edgemark``

(* Mark constructors *)
val nodemark_red_tm = mk_const_tm "nodemark_red"
val nodemark_green_tm = mk_const_tm "nodemark_green"
val nodemark_blue_tm = mk_const_tm "nodemark_blue"
val nodemark_grey_tm = mk_const_tm "nodemark_grey"
val nodemark_any_tm = mk_const_tm "nodemark_any"

val edgemark_red_tm = mk_const_tm "edgemark_red"
val edgemark_green_tm = mk_const_tm "edgemark_green"
val edgemark_blue_tm = mk_const_tm "edgemark_blue"
val edgemark_dashed_tm = mk_const_tm "edgemark_dashed"
val edgemark_any_tm = mk_const_tm "edgemark_any"

(* Label constructors - basic *)
val (label_integer_tm, mk_label_integer, dest_label_integer, is_label_integer) = fns1 "label_integer"
val (label_string_tm, mk_label_string, dest_label_string, is_label_string) = fns1 "label_string"
val (label_char_tm, mk_label_char, dest_label_char, is_label_char) = fns1 "label_char"
val label_nil_tm = mk_const_tm "label_nil"
val (label_cons_tm, mk_label_cons, dest_label_cons, is_label_cons) = fns2 "label_cons"

(* Label constructors - rule-specific *)
val (label_variable_tm, mk_label_variable, dest_label_variable, is_label_variable) = fns1 "label_variable"
val (label_indeg_tm, mk_label_indeg, dest_label_indeg, is_label_indeg) = fns1 "label_indeg"
val (label_outdeg_tm, mk_label_outdeg, dest_label_outdeg, is_label_outdeg) = fns1 "label_outdeg"
val (label_length_tm, mk_label_length, dest_label_length, is_label_length) = fns1 "label_length"
val (label_add_tm, mk_label_add, dest_label_add, is_label_add) = fns2 "label_add"
val (label_sub_tm, mk_label_sub, dest_label_sub, is_label_sub) = fns2 "label_sub"
val (label_mult_tm, mk_label_mult, dest_label_mult, is_label_mult) = fns2 "label_mult"
val (label_div_tm, mk_label_div, dest_label_div, is_label_div) = fns2 "label_div"
val (label_concat_tm, mk_label_concat, dest_label_concat, is_label_concat) = fns2 "label_concat"
val (label_negate_tm, mk_label_negate, dest_label_negate, is_label_negate) = fns1 "label_negate"

(* Varname constructor *)
val (varname_tm, mk_varname, dest_varname, is_varname) = fns1 "varname"

(* Well-formedness *)
val (wf_rulegraph_tm, mk_wf_rulegraph, dest_wf_rulegraph, is_wf_rulegraph) = fns1 "wf_rulegraph"

(* Helper functions *)
fun MK_label_integer i = mk_label_integer (intSyntax.term_of_int (Arbint.fromInt i))
fun MK_label_string s = mk_label_string (stringSyntax.fromMLstring s)
fun MK_label_char c = mk_label_char (stringSyntax.fromMLchar c)
fun MK_varname s = mk_varname (stringSyntax.fromMLstring s)

(* Node/Edge ID constructors *)
val (nodeid_constructor, mk_nodeid_term, dest_nodeid_term, is_nodeid_term) =
    HolKernel.syntax_fns1 "graph" "nodeid"
val (edgeid_constructor, mk_edgeid_term, dest_edgeid_term, is_edgeid_term) =
    HolKernel.syntax_fns1 "graph" "edgeid"

fun MK_nodeid s = mk_nodeid_term (stringSyntax.fromMLstring s)
fun MK_edgeid s = mk_edgeid_term (stringSyntax.fromMLstring s)

(* Translation functions *)
(* In GP2, unspecified mark in a rule pattern means "match unmarked only".
   Per Brian's thesis: 'any' matches red/green/blue/grey but NOT lack of mark.
   So NONE in rule means host must be unmarked (NONE). *)
fun mk_rule_node_mark (m: P.mark option) =
    case m of
        SOME P.red_mark => optionSyntax.mk_some nodemark_red_tm
      | SOME P.green_mark => optionSyntax.mk_some nodemark_green_tm
      | SOME P.blue_mark => optionSyntax.mk_some nodemark_blue_tm
      | SOME P.grey_mark => optionSyntax.mk_some nodemark_grey_tm
      | SOME P.any_mark => optionSyntax.mk_some nodemark_any_tm
      | NONE => optionSyntax.mk_none nodemark_ty  (* unspecified = must be unmarked *)
      | _ => raise ERR "mk_rule_node_mark" "Invalid mark for rule node"

fun mk_rule_edge_mark (m: P.mark option) =
    case m of
        SOME P.red_mark => optionSyntax.mk_some edgemark_red_tm
      | SOME P.green_mark => optionSyntax.mk_some edgemark_green_tm
      | SOME P.blue_mark => optionSyntax.mk_some edgemark_blue_tm
      | SOME P.dashed_mark => optionSyntax.mk_some edgemark_dashed_tm
      | SOME P.any_mark => optionSyntax.mk_some edgemark_any_tm
      | NONE => optionSyntax.mk_none edgemark_ty  (* unspecified = must be unmarked *)
      | _ => raise ERR "mk_rule_edge_mark" "Invalid mark for rule edge"

fun mk_rule_label_from_expr (expr: P.ruleexpr) =
    case expr of
        P.ruleexpr_num i => MK_label_integer i
      | P.ruleexpr_str s => if size s = 1
                           then MK_label_char (String.sub (s,0))
                           else MK_label_string s
      | P.ruleexpr_var v => mk_label_variable (MK_varname v)
      | P.ruleexpr_indeg n => mk_label_indeg (MK_nodeid n)
      | P.ruleexpr_outdeg n => mk_label_outdeg (MK_nodeid n)
      | P.ruleexpr_length v => mk_label_length (MK_varname v)
      | P.ruleexpr_add (a, b) => mk_label_add (mk_rule_label_from_expr a, mk_rule_label_from_expr b)
      | P.ruleexpr_sub (a, b) => mk_label_sub (mk_rule_label_from_expr a, mk_rule_label_from_expr b)
      | P.ruleexpr_mult (a, b) => mk_label_mult (mk_rule_label_from_expr a, mk_rule_label_from_expr b)
      | P.ruleexpr_div (a, b) => mk_label_div (mk_rule_label_from_expr a, mk_rule_label_from_expr b)
      | P.ruleexpr_concat (a, b) => mk_label_concat (mk_rule_label_from_expr a, mk_rule_label_from_expr b)
      | P.ruleexpr_negate e => mk_label_negate (mk_rule_label_from_expr e)

fun mk_rule_label_list (exprs: P.ruleexpr list) =
    let fun build_list [] = label_nil_tm
          | build_list (e::es) = mk_label_cons (mk_rule_label_from_expr e, build_list es)
    (* Parser produces reversed list due to left-associativity of COLON.
       We reverse to get the correct order: "1:2:3" -> 1:(2:(3:nil)) *)
    in build_list (List.rev exprs)
    end

fun mk_rule_node_attr (label: P.rulelabel) =
    let val label_tm = mk_rule_label_list (#list label)
        val mark_tm = mk_rule_node_mark (#mark label)
    in pairSyntax.mk_pair (label_tm, mark_tm)
    end

fun mk_rule_edge_attr (label: P.rulelabel) =
    let val label_tm = mk_rule_label_list (#list label)
        val mark_tm = mk_rule_edge_mark (#mark label)
    in pairSyntax.mk_pair (label_tm, mark_tm)
    end

(* Helper functions for finite maps *)
fun mk_srctrg_map (f: P.ruleedge -> string, edges: P.ruleedge list) =
    let val empty_tm = finite_mapSyntax.mk_fempty (edgeid_ty, nodeid_ty)
        val pairs = map (fn e => pairSyntax.mk_pair (MK_edgeid (#eid e), MK_nodeid (f e))) edges
        val pair_ty = pairSyntax.mk_prod (edgeid_ty, nodeid_ty)
        val list_tm = listSyntax.mk_list (pairs, pair_ty)
    in finite_mapSyntax.mk_fupdate_list (empty_tm, list_tm)
    end

fun mk_rooted_map nodes =
    let val empty_tm = finite_mapSyntax.mk_fempty (nodeid_ty, ``:bool``)
        val pairs = map (fn n => pairSyntax.mk_pair (MK_nodeid (#nid n),
                                                    boolSyntax.lift_bool ``:bool`` (#rooted n))) nodes
        val pair_ty = pairSyntax.mk_prod (nodeid_ty, ``:bool``)
        val list_tm = listSyntax.mk_list (pairs, pair_ty)
    in finite_mapSyntax.mk_fupdate_list (empty_tm, list_tm)
    end

fun mk_rule_node_attr_map (nodes: P.rulenode list) =
    let val rule_nodeattr_ty = ``:rulegraph$nodeattr``
        val empty_tm = finite_mapSyntax.mk_fempty (nodeid_ty, rule_nodeattr_ty)
        val pairs = map (fn n => pairSyntax.mk_pair (MK_nodeid (#nid n),
                                                    mk_rule_node_attr (#label n))) nodes
        val pair_ty = pairSyntax.mk_prod (nodeid_ty, rule_nodeattr_ty)
        val list_tm = listSyntax.mk_list (pairs, pair_ty)
    in finite_mapSyntax.mk_fupdate_list (empty_tm, list_tm)
    end

fun mk_rule_edge_attr_map (edges: P.ruleedge list) =
    let val rule_edgeattr_ty = ``:rulegraph$edgeattr``
        val empty_tm = finite_mapSyntax.mk_fempty (edgeid_ty, rule_edgeattr_ty)
        val pairs = map (fn e => pairSyntax.mk_pair (MK_edgeid (#eid e),
                                                    mk_rule_edge_attr (#label e))) edges
        val pair_ty = pairSyntax.mk_prod (edgeid_ty, rule_edgeattr_ty)
        val list_tm = listSyntax.mk_list (pairs, pair_ty)
    in finite_mapSyntax.mk_fupdate_list (empty_tm, list_tm)
    end

(* Helper for handling bidirectional edges *)
fun expand_bidirectional_edges (edges: P.ruleedge list) =
    let fun process_edge (e: P.ruleedge) =
            if #bidirectional e
            then let val reverse_e = {eid = (#eid e) ^ "_rev",
                                     bidirectional = false,
                                     src = #trg e,
                                     trg = #src e,
                                     label = #label e}
                 in [e, reverse_e]
                 end
            else [e]
    in List.concat (map process_edge edges)
    end

(* Main rulegraph construction function *)
fun mk_rulegraph_tm (graph: P.rulegraph) =
    let val {nodes, edges, ...} = graph
        val expanded_edges = expand_bidirectional_edges edges
        val V = if null nodes
                then pred_setSyntax.mk_empty nodeid_ty
                else pred_setSyntax.prim_mk_set (map (MK_nodeid o #nid) nodes, nodeid_ty)
        val E = if null expanded_edges
                then pred_setSyntax.mk_empty edgeid_ty
                else pred_setSyntax.prim_mk_set (map (MK_edgeid o #eid) expanded_edges, edgeid_ty)
        val s = mk_srctrg_map ((#src: P.ruleedge -> string), expanded_edges)
        val t = mk_srctrg_map ((#trg: P.ruleedge -> string), expanded_edges)
        val l = mk_rule_node_attr_map nodes
        val m = mk_rule_edge_attr_map expanded_edges
        val p = mk_rooted_map nodes
        val components = [("V", V), ("E", E), ("s", s), ("t", t), ("l", l), ("m", m), ("p", p)]
    in TypeBase.mk_record (rulegraph_ty, components)
    end

end
