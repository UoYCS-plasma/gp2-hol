signature programSyntax =
sig

  include Abbrev

  (* Basic types *)
  val procid_ty: hol_type
  val ruleid_ty: hol_type
  val term_ty: hol_type
  val rule_ty: hol_type

  (* Program types *)
  val program_ty: hol_type

  (* Term constructors *)
  val term_seq_tm: term
  val mk_term_seq: term * term -> term
  val dest_term_seq: term -> term * term
  val is_term_seq: term -> bool

  val term_or_tm: term
  val mk_term_or: term * term -> term
  val dest_term_or: term -> term * term
  val is_term_or: term -> bool

  val term_ifte_tm: term
  val mk_term_ifte: term * term * term -> term
  val dest_term_ifte: term -> term * term * term
  val is_term_ifte: term -> bool

  val term_trte_tm: term
  val mk_term_trte: term * term * term -> term
  val dest_term_trte: term -> term * term * term
  val is_term_trte: term -> bool

  val term_rscall_tm: term
  val mk_term_rscall: term -> term
  val dest_term_rscall: term -> term
  val is_term_rscall: term -> bool

  val term_proc_tm: term
  val mk_term_proc: term -> term
  val dest_term_proc: term -> term
  val is_term_proc: term -> bool

  val term_alap_tm: term
  val mk_term_alap: term -> term
  val dest_term_alap: term -> term
  val is_term_alap: term -> bool

  val term_skip_tm: term
  val term_fail_tm: term
  val term_break_tm: term

  (* Rule ID constructor *)
  val ruleid_tm: term
  val mk_ruleid: term -> term
  val dest_ruleid: term -> term
  val is_ruleid: term -> bool

  (* Well-formedness *)
  val wf_program_tm: term
  val mk_wf_program: term -> term
  val dest_wf_program: term -> term
  val is_wf_program: term -> bool

  (* Helper functions *)
  val MK_procid: string -> term
  val MK_ruleid: string -> term

  (* Translation from Parsetree *)
  val mk_term_from_parsetree: Parsetree.term -> term
  val mk_ruledecl_from_parsetree: Parsetree.ruledecl -> term
  val mk_cond_from_parsetree: Parsetree.cond -> term
  val mk_program_tm: Parsetree.program -> term

end