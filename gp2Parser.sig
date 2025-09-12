signature gp2Parser =
sig
  val raw_read_stream : TextIO.instream -> Parsetree.toplevel;
  val raw_read_file : string -> Parsetree.toplevel;
  val raw_read_string: string -> Parsetree.toplevel;

  val print_parse_error : string -> unit;
end;
