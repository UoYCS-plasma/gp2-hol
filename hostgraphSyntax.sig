signature hostgraphSyntax =
sig

  include Abbrev

  (* Basic types *)
  val nodeid_ty: hol_type
  val edgeid_ty: hol_type

  (* Host graph types *)
  val hostgraph_ty: hol_type
  val nodemark_ty: hol_type
  val edgemark_ty: hol_type

  (* Mark constructors *)
  val nodemark_red_tm: term
  val nodemark_green_tm: term
  val nodemark_blue_tm: term
  val nodemark_grey_tm: term
  val edgemark_red_tm: term
  val edgemark_green_tm: term
  val edgemark_blue_tm: term
  val edgemark_dashed_tm: term

  (* Label constructors *)
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

  (* Well-formedness *)
  val wf_hostgraph_tm: term
  val mk_wf_hostgraph: term -> term
  val dest_wf_hostgraph: term -> term
  val is_wf_hostgraph: term -> bool

  (* Helper functions *)
  val MK_label_integer: int -> term
  val MK_label_string: string -> term
  val MK_label_char: char -> term

  (* Translation from Parsetree *)
  val mk_host_node_mark: Parsetree.mark option -> term
  val mk_host_edge_mark: Parsetree.mark option -> term
  val mk_host_label_from_expr: Parsetree.hostexpr -> term
  val mk_host_label_list: Parsetree.hostexpr list -> term
  val mk_host_node_attr: Parsetree.hostlabel -> term
  val mk_host_edge_attr: Parsetree.hostlabel -> term
  val mk_hostgraph_tm: Parsetree.hostgraph -> term

end