structure Parsetree =
struct

type position = {x: real, y:real};

type procid = string
type ruleid = string
type nodeid = string
type edgeid = string
type variable = string
type hostid = string

datatype ty =
    int_ty
  | char_ty
  | string_ty
  | atom_ty
  | list_ty

datatype mark =
	 red_mark
	 | green_mark
	 | blue_mark
	 | grey_mark
	 | dashed_mark
	 | any_mark

datatype hostexpr =
    hostexpr_num of int
  | hostexpr_str of string

type hostlist = hostexpr list
type hostlabel = {list: hostlist, mark: mark option}

type hostedge = {eid: hostid, src: hostid, trg: hostid, label: hostlabel}
type hostnode = {nid: hostid, rooted: bool, label: hostlabel, position: position option}

type hostgraph = {nodes: hostnode list, edges: hostedge list, position: position option}

(* rulegraph *)

datatype ruleexpr =
    ruleexpr_num of int
  | ruleexpr_str of string
  | ruleexpr_var of variable
  | ruleexpr_indeg of nodeid
  | ruleexpr_outdeg of nodeid
  | ruleexpr_length of variable
  | ruleexpr_add of ruleexpr * ruleexpr
  | ruleexpr_sub of ruleexpr * ruleexpr
  | ruleexpr_mult of ruleexpr * ruleexpr
  | ruleexpr_div of ruleexpr * ruleexpr
  | ruleexpr_concat of ruleexpr * ruleexpr
  | ruleexpr_negate of ruleexpr
type rulelist = ruleexpr list
type rulelabel = {list: rulelist, mark: mark option}


datatype cond =
	 cond_issubtype of ty * variable
       | cond_edgetest of nodeid * nodeid * (rulelabel option)
       | cond_eq of rulelist * rulelist
       | cond_neq of rulelist * rulelist
       | cond_expr_gt of ruleexpr * ruleexpr
       | cond_expr_gteq of ruleexpr * ruleexpr
       | cond_expr_lt of ruleexpr * ruleexpr
       | cond_expr_lteq of ruleexpr * ruleexpr
       | cond_and of cond * cond
       | cond_or of cond * cond
       | cond_not of cond

type ruleedge = {eid: edgeid, bidirectional: bool, src: nodeid, trg: nodeid, label: rulelabel}
type rulenode = {nid: nodeid, rooted: bool, label: rulelabel, position: position option}

type rulegraph = {nodes: rulenode list, edges: ruleedge list, position: position option}

type vardecl = {vars: variable list, ty: ty}

type ruledecl = {rid: ruleid, vars: vardecl list, lhs: rulegraph, rhs: rulegraph, interf: nodeid list, cond: cond option}



(* programs		     *)
datatype term =
	 term_seq of term list
	 | term_or of term * term
	 | term_ifte of term * term option * term option
	 | term_trte of term * term option * term option
	 | term_rscall of ruleid list
	 | term_rule of ruleid
	 | term_proc of procid
	 | term_alap of term
	 | term_skip
	 | term_fail
         | term_break
type comseq = term list

type procdecl = { pid: procid, cmds: comseq }


datatype decl =
	 decl_rule of ruledecl
	 | decl_proc of procdecl * (decl list) (* local decls *)

type program = decl list


datatype toplevel =
	 toplevel_hostgraph of hostgraph
	 | toplevel_program of program

end
