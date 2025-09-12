structure hostgraphSyntax :> hostgraphSyntax =
struct

open HolKernel boolLib

val ERR = Feedback.mk_HOL_ERR "hostgraphSyntax"

local open hostgraphTheory graphTheory Parsetree in end;

structure P = Parsetree;
val _ = Meta.fakeload "P";

fun mk_const_tm n = prim_mk_const{Name=n, Thy="hostgraph"};
fun fns1 n = HolKernel.syntax_fns1 "hostgraph" n
fun fns2 n = HolKernel.syntax_fns2 "hostgraph" n

val nodeid_ty = ``:nodeid``
val edgeid_ty = ``:edgeid``
val hostgraph_ty = ``:hostgraph``
val nodemark_ty = ``:hostgraph$nodemark``
val edgemark_ty = ``:hostgraph$edgemark``

(* Mark constructors *)
val nodemark_red_tm = mk_const_tm "nodemark_red"
val nodemark_green_tm = mk_const_tm "nodemark_green"
val nodemark_blue_tm = mk_const_tm "nodemark_blue"
val nodemark_grey_tm = mk_const_tm "nodemark_grey"

val edgemark_red_tm = mk_const_tm "edgemark_red"
val edgemark_green_tm = mk_const_tm "edgemark_green"
val edgemark_blue_tm = mk_const_tm "edgemark_blue"
val edgemark_dashed_tm = mk_const_tm "edgemark_dashed"

(* Label constructors *)
val (label_integer_tm, mk_label_integer, dest_label_integer, is_label_integer) = fns1 "label_integer"

val (label_string_tm, mk_label_string, dest_label_string, is_label_string) = fns1 "label_string"
val (label_char_tm, mk_label_char, dest_label_char, is_label_char) = fns1 "label_char"
val label_nil_tm = mk_const_tm "label_nil"
val (label_cons_tm, mk_label_cons, dest_label_cons, is_label_cons) = fns2 "label_cons"

(* Well-formedness *)
val (wf_hostgraph_tm, mk_wf_hostgraph, dest_wf_hostgraph, is_wf_hostgraph) = fns1 "wf_hostgraph"

(* Helper functions *)
fun MK_label_integer i = mk_label_integer (intSyntax.term_of_int (Arbint.fromInt i))
fun MK_label_string s = mk_label_string (stringSyntax.fromMLstring s)
fun MK_label_char c = mk_label_char (stringSyntax.fromMLchar c)

(* Node/Edge ID constructors *)
val (nodeid_constructor, mk_nodeid_term, dest_nodeid_term, is_nodeid_term) =
    HolKernel.syntax_fns1 "graph" "nodeid"
val (edgeid_constructor, mk_edgeid_term, dest_edgeid_term, is_edgeid_term) =
    HolKernel.syntax_fns1 "graph" "edgeid"

fun MK_nodeid s = mk_nodeid_term (stringSyntax.fromMLstring s)
fun MK_edgeid s = mk_edgeid_term (stringSyntax.fromMLstring s)

(* Translation functions *)
fun mk_host_node_mark (m: P.mark option) =
    case m of
        SOME P.red_mark => optionSyntax.mk_some nodemark_red_tm
      | SOME P.green_mark => optionSyntax.mk_some nodemark_green_tm
      | SOME P.blue_mark => optionSyntax.mk_some nodemark_blue_tm
      | SOME P.grey_mark => optionSyntax.mk_some nodemark_grey_tm
      | NONE => optionSyntax.mk_none nodemark_ty
      | _ => raise ERR "mk_host_node_mark" "Invalid mark for host node"

fun mk_host_edge_mark (m: P.mark option) =
    case m of
        SOME P.red_mark => optionSyntax.mk_some edgemark_red_tm
      | SOME P.green_mark => optionSyntax.mk_some edgemark_green_tm
      | SOME P.blue_mark => optionSyntax.mk_some edgemark_blue_tm
      | SOME P.dashed_mark => optionSyntax.mk_some edgemark_dashed_tm
      | NONE => optionSyntax.mk_none edgemark_ty
      | _ => raise ERR "mk_host_edge_mark" "Invalid mark for host edge"

fun mk_host_label_from_expr (expr: P.hostexpr) =
    case expr of
        P.hostexpr_num i => MK_label_integer i
      | P.hostexpr_str s => if size s = 1
                           then MK_label_char (String.sub (s,0))
                           else MK_label_string s

fun mk_host_label_list (exprs: P.hostexpr list) =
    let fun build_list [] = label_nil_tm
          | build_list (e::es) = mk_label_cons (mk_host_label_from_expr e, build_list es)
    (* Parser produces reversed list due to left-associativity of COLON.
       We reverse to get the correct order: "1:2:3" -> 1:(2:(3:nil)) *)
    in build_list (List.rev exprs)
    end

fun mk_host_node_attr (label: P.hostlabel) =
    let val label_tm = mk_host_label_list (#list label)
        val mark_tm = mk_host_node_mark (#mark label)
    in pairSyntax.mk_pair (label_tm, mark_tm)
    end

fun mk_host_edge_attr (label: P.hostlabel) =
    let val label_tm = mk_host_label_list (#list label)
        val mark_tm = mk_host_edge_mark (#mark label)
    in pairSyntax.mk_pair (label_tm, mark_tm)
    end

(* Helper functions for finite maps *)
fun mk_srctrg_map (f: P.hostedge -> string, edges: P.hostedge list) =
    let val empty_tm = finite_mapSyntax.mk_fempty (edgeid_ty, nodeid_ty)
        val pairs = map (fn e => pairSyntax.mk_pair (MK_edgeid (f e), MK_nodeid (f e))) edges
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

fun mk_node_attr_map (nodes: P.hostnode list) =
    let val host_nodeattr_ty = ``:hostgraph$nodeattr``
        val empty_tm = finite_mapSyntax.mk_fempty (nodeid_ty, host_nodeattr_ty)
        val pairs = map (fn n => pairSyntax.mk_pair (MK_nodeid (#nid n),
                                                    mk_host_node_attr (#label n))) nodes
        val pair_ty = pairSyntax.mk_prod (nodeid_ty, host_nodeattr_ty)
        val list_tm = listSyntax.mk_list (pairs, pair_ty)
    in finite_mapSyntax.mk_fupdate_list (empty_tm, list_tm)
    end

fun mk_edge_attr_map (edges: P.hostedge list) =
    let val host_edgeattr_ty = ``:hostgraph$edgeattr``
        val empty_tm = finite_mapSyntax.mk_fempty (edgeid_ty, host_edgeattr_ty)
        val pairs = map (fn e => pairSyntax.mk_pair (MK_edgeid (#eid e),
                                                    mk_host_edge_attr (#label e))) edges
        val pair_ty = pairSyntax.mk_prod (edgeid_ty, host_edgeattr_ty)
        val list_tm = listSyntax.mk_list (pairs, pair_ty)
    in finite_mapSyntax.mk_fupdate_list (empty_tm, list_tm)
    end

(* Main hostgraph construction function *)
fun mk_hostgraph_tm (graph: P.hostgraph) =
    let val {nodes, edges, ...} = graph
        val V = let val node_terms = map (MK_nodeid o #nid) nodes
                    val _ = print ("Creating node set with " ^ Int.toString (length node_terms) ^ " nodes\n")
                in if null node_terms
                   then (print "Creating empty node set\n"; pred_setSyntax.mk_empty nodeid_ty)
                   else pred_setSyntax.prim_mk_set (node_terms, nodeid_ty)
                end
        val E = let val edge_terms = map (MK_edgeid o #eid) edges
                    val _ = print ("Creating edge set with " ^ Int.toString (length edge_terms) ^ " edges\n")
                in if null edge_terms
                   then (print "Creating empty edge set\n"; pred_setSyntax.mk_empty edgeid_ty)
                   else pred_setSyntax.prim_mk_set (edge_terms, edgeid_ty)
                end
        val s = mk_srctrg_map ((#src: P.hostedge -> string), edges)
        val t = mk_srctrg_map ((#trg: P.hostedge -> string), edges)
        val l = mk_node_attr_map nodes
        val m = mk_edge_attr_map edges
        val p = mk_rooted_map nodes
        val components = [("V", V), ("E", E), ("s", s), ("t", t), ("l", l), ("m", m), ("p", p)]
    in TypeBase.mk_record (hostgraph_ty, components)
    end

end
