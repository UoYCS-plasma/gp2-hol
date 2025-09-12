signature rulegraphSyntax =
sig

  include Abbrev

  (* Basic types *)
  val nodeid_ty: hol_type
  val edgeid_ty: hol_type
  val varname_ty: hol_type

  (* Rule graph types *)
  val rulegraph_ty: hol_type
  val nodemark_ty: hol_type
  val edgemark_ty: hol_type

  (* Mark constructors *)
  val nodemark_red_tm: term
  val nodemark_green_tm: term
  val nodemark_blue_tm: term
  val nodemark_grey_tm: term
  val nodemark_any_tm: term
  val edgemark_red_tm: term
  val edgemark_green_tm: term
  val edgemark_blue_tm: term
  val edgemark_dashed_tm: term
  val edgemark_any_tm: term

  (* Label constructors - basic *)
  val label_integer_tm: term
  val mk_label_integer: term -> term
  val dest_label_integer: term -> term
  val is_label_integer: term -> bool

  val label_string_tm: term
  val mk_label_string: term -> term
  val dest_label_string: term -> term
  val is_label_string: term -> bool

  val label_char_tm: term
  val mk_label_char: term -> term
  val dest_label_char: term -> term
  val is_label_char: term -> bool

  val label_nil_tm: term
  val label_cons_tm: term
  val mk_label_cons: term * term -> term
  val dest_label_cons: term -> term * term
  val is_label_cons: term -> bool

  (* Label constructors - rule-specific *)
  val label_variable_tm: term
  val mk_label_variable: term -> term
  val dest_label_variable: term -> term
  val is_label_variable: term -> bool

  val label_indeg_tm: term
  val mk_label_indeg: term -> term
  val dest_label_indeg: term -> term
  val is_label_indeg: term -> bool

  val label_outdeg_tm: term
  val mk_label_outdeg: term -> term
  val dest_label_outdeg: term -> term
  val is_label_outdeg: term -> bool

  val label_length_tm: term
  val mk_label_length: term -> term
  val dest_label_length: term -> term
  val is_label_length: term -> bool

  val label_add_tm: term
  val mk_label_add: term * term -> term
  val dest_label_add: term -> term * term
  val is_label_add: term -> bool

  val label_sub_tm: term
  val mk_label_sub: term * term -> term
  val dest_label_sub: term -> term * term
  val is_label_sub: term -> bool

  val label_mult_tm: term
  val mk_label_mult: term * term -> term
  val dest_label_mult: term -> term * term
  val is_label_mult: term -> bool

  val label_div_tm: term
  val mk_label_div: term * term -> term
  val dest_label_div: term -> term * term
  val is_label_div: term -> bool

  val label_concat_tm: term
  val mk_label_concat: term * term -> term
  val dest_label_concat: term -> term * term
  val is_label_concat: term -> bool

  val label_negate_tm: term
  val mk_label_negate: term -> term
  val dest_label_negate: term -> term
  val is_label_negate: term -> bool

  (* Varname constructor *)
  val varname_tm: term
  val mk_varname: term -> term
  val dest_varname: term -> term
  val is_varname: term -> bool

  (* Well-formedness *)
  val wf_rulegraph_tm: term
  val mk_wf_rulegraph: term -> term
  val dest_wf_rulegraph: term -> term
  val is_wf_rulegraph: term -> bool

  (* Helper functions *)
  val MK_label_integer: int -> term
  val MK_label_string: string -> term
  val MK_label_char: char -> term
  val MK_varname: string -> term

  (* Translation from Parsetree *)
  val mk_rule_node_mark: Parsetree.mark option -> term
  val mk_rule_edge_mark: Parsetree.mark option -> term
  val mk_rule_label_from_expr: Parsetree.ruleexpr -> term
  val mk_rule_label_list: Parsetree.ruleexpr list -> term
  val mk_rule_node_attr: Parsetree.rulelabel -> term
  val mk_rule_edge_attr: Parsetree.rulelabel -> term
  val mk_rulegraph_tm: Parsetree.rulegraph -> term

  (* Helper for bidirectional edges *)
  val expand_bidirectional_edges: Parsetree.ruleedge list -> Parsetree.ruleedge list

end