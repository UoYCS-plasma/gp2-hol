structure gp2Parser :> gp2Parser =
struct

  structure GP2LrVals =
    GP2LrValsFun(structure Token = LrParser.Token)

  structure GP2Lex =
    GP2LexFun(structure Tokens = GP2LrVals.Tokens)

  structure gp2Parser =
    Join(structure ParserData = GP2LrVals.ParserData
	 structure Lex = GP2Lex
         structure LrParser=LrParser)


  fun print_parse_error s =
  let
     open PPBackEnd;
     val _ = Parse.print_with_style [FG OrangeRed, Bold, Underline] "Error:";
     val _ = Parse.print_with_style [] " ";
     val _ = Parse.print_with_style [FG OrangeRed] s
     val _ = Parse.print_with_style [] "\n";
  in
     ()
  end;

  fun invoke lexstream = let
    open PPBackEnd;

    val error_count = ref 0;
    fun print_error (s,(j:int,i:int),_) =
        ((if (!error_count > 0) then () else print "\n");
        (error_count := !error_count + 1);
        print_parse_error (" "^
            " line "^(Int.toString (i+1)) ^ ": " ^ s);
       (if (!error_count > 15) then Feedback.failwith("parse error") else ()));
    val r = (#1 (gp2Parser.parse(15,lexstream,print_error,())))
        handle GP2Lex.UserDeclarations.LexicalError (tok, j, i) =>
           let
              val s = "lex error - ill formed token \""^tok^"\"";
              val _ = print_error (s, (j, i), (j,i));
           in
              Feedback.failwith("lexing error")
           end;
  in
    (if (!error_count > 0) then Feedback.fail() else r)
  end


  fun raw_read_stream strm = let
    val lexer = gp2Parser.makeLexer (fn _ => Portable.input_line strm)
  in
    invoke lexer
  end

  fun raw_read_file fname = let
    val strm = TextIO.openIn fname
  in
    raw_read_stream strm before TextIO.closeIn strm
  end

  fun raw_read_string s = let
    val strm = TextIO.openString s
  in
    raw_read_stream strm before TextIO.closeIn strm
  end

end;
