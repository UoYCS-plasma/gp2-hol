open HolKernel boolLib bossLib
open gp2Parser programTheory programSyntax
open rulegraphSyntax

structure P = Parsetree;

fun remove_extension filename =
    case String.tokens (fn c => c = #".") filename of
        [] => filename
      | [name] => name
      | parts => String.concatWith "." (List.take (parts, length parts - 1))

fun capitalize_first_char s =
    if String.size s = 0 then s
    else String.str (Char.toUpper (String.sub (s, 0))) ^ String.extract (s, 1, NONE)

fun program_name_from_path filepath =
    let val filename = OS.Path.file filepath
        val basename = remove_extension filename
        (* Replace special characters with underscores for valid SML identifiers *)
        fun clean_char #"-" = #"_"
          | clean_char #"." = #"_"
          | clean_char #" " = #"_"
          | clean_char c = c
        val cleaned = String.translate (String.str o clean_char) basename
    in capitalize_first_char cleaned
    end

(* Sanitize identifier for HOL constant names *)
fun sanitize_id s =
    let fun clean_char #"-" = #"_"
          | clean_char #" " = #"_"
          | clean_char c = c
    in String.translate (String.str o clean_char) s
    end

fun pretty_print_term term =
    let val pp_term = Parse.term_to_string term
    in pp_term
    end

(* Collect declarations from a program, returning (procs, rules) *)
fun collect_decls (decls: P.decl list) =
    let fun process_decl (decl, (proc_acc, rule_acc)) = case decl of
            P.decl_rule rdecl =>
            let val rule_tm = programSyntax.mk_ruledecl_from_parsetree rdecl
                val rid = #rid rdecl
            in (proc_acc, (rid, rule_tm) :: rule_acc)
            end
          | P.decl_proc ({pid, cmds}, local_decls) =>
            let val term_tm = programSyntax.mk_term_from_parsetree (P.term_seq cmds)
                val (local_procs, local_rules) = collect_decls local_decls
            in ((pid, term_tm) :: (proc_acc @ local_procs), rule_acc @ local_rules)
            end
    in List.foldr process_decl ([], []) decls
    end

fun generate_theory_file filepath =
    let val program_name = program_name_from_path filepath
        val theory_name = program_name ^ "Theory"
        val output_file = program_name ^ "Script.sml"

        val _ = print ("Processing: " ^ filepath ^ "\n")
        val _ = print ("Program name: " ^ program_name ^ "\n")
        val _ = print ("Theory name: " ^ theory_name ^ "\n")
        val _ = print ("Output file: " ^ output_file ^ "\n\n")

        (* Parse the GP2 program *)
        val raw = raw_read_file filepath

    in case raw of
        P.toplevel_program prog =>
        let
            (* Expand bidirectional edges into rule copies *)
            val expanded_prog = programSyntax.expand_bidir_rules prog
            (* Collect rules and procs *)
            val (procs, rules) = collect_decls expanded_prog

            val _ = print ("Found " ^ Int.toString (length rules) ^ " rules\n")
            val _ = print ("Found " ^ Int.toString (length procs) ^ " procs\n")

            (* Generate rule definitions and wf_rule theorems *)
            fun mk_rule_def (rid, rule_tm) =
                let val const_name = "rule_" ^ sanitize_id rid
                    val term_str = pretty_print_term rule_tm
                in String.concat [
                    "Definition ", const_name, "_def:\n",
                    "  ", const_name, " =\n",
                    "    ", term_str, "\n",
                    "End\n\n",
                    "Theorem wf_", const_name, ":\n",
                    "  wf_rule ", const_name, "\n",
                    "Proof\n",
                    "  cheat\n",
                    "QED\n\n"
                ]
                end

            val rule_defs = String.concat (map mk_rule_def rules)

            (* Generate proc definitions *)
            fun mk_proc_def (pid, term_tm) =
                let val const_name = "proc_" ^ sanitize_id pid
                    val term_str = pretty_print_term term_tm
                in String.concat [
                    "Definition ", const_name, "_def:\n",
                    "  ", const_name, " = ", term_str, "\n",
                    "End\n\n"
                ]
                end

            val proc_defs = String.concat (map mk_proc_def procs)

            (* Generate program definition referencing the constants *)
            fun mk_rule_entry rid = "(ruleid \"" ^ rid ^ "\", rule_" ^ sanitize_id rid ^ ")"
            fun mk_proc_entry pid = "(\"" ^ pid ^ "\", proc_" ^ sanitize_id pid ^ ")"

            val rule_entries = String.concatWith ";\n       " (map (mk_rule_entry o #1) rules)
            val proc_entries = String.concatWith ";\n       " (map (mk_proc_entry o #1) procs)

            val program_def = String.concat [
                "Definition program_def:\n",
                "  program =\n",
                "    <| proc := FEMPTY |++ [", proc_entries, "];\n",
                "       rule := FEMPTY |++ [", rule_entries, "] |>\n",
                "End\n\n",
                "Theorem program_wf:\n",
                "  wf_program program\n",
                "Proof\n",
                "  cheat\n",
                "QED\n\n",
                "Theorem program_correct:\n",
                "  !P. WSPEC program P (term_proc \"Main\") (lift P)\n",
                "Proof\n",
                "  cheat\n",
                "QED\n\n"
            ]

            (* Create theory file content *)
            val theory_content = String.concat [
                "(* Generated theory file for GP2 program: ", filepath, " *)\n",
                "(* Original program converted to HOL4 representation *)\n\n",
                "open HolKernel boolLib bossLib\n",
                "open programTheory programSyntax ruleTheory rulegraphTheory hostgraphTheory\n",
                "open gp2LogicTheory\n\n",
                "val () = new_theory \"", program_name, "\"\n\n",
                "(* Rule definitions *)\n",
                rule_defs,
                "(* Procedure definitions *)\n",
                proc_defs,
                "(* Program definition *)\n",
                program_def,
                "val () = export_theory ()\n"
            ]

            (* Check if output file already exists *)
            val _ = if OS.FileSys.access (output_file, [])
                    then raise Fail ("Output file already exists: " ^ output_file ^
                                    ". Refuse to overwrite existing file.")
                    else ()

            (* Write to file *)
            val out_stream = TextIO.openOut output_file
            val _ = TextIO.output (out_stream, theory_content)
            val _ = TextIO.closeOut out_stream

            val _ = print ("Successfully generated: " ^ output_file ^ "\n")
            val _ = print ("Generated " ^ Int.toString (length rules) ^ " rule definitions\n")
            val _ = print ("Generated " ^ Int.toString (length procs) ^ " proc definitions\n")
            val _ = print ("Generated program definition: program\n")

        in ()
        end
      | P.toplevel_hostgraph _ =>
        let val _ = print ("Error: " ^ filepath ^ " contains a hostgraph, not a program\n")
        in ()
        end
    end
    handle
      exn => print ("Error processing " ^ filepath ^ ": " ^ exnMessage exn ^ "\n")

fun main () =
  case CommandLine.arguments () of
      [filepath] =>
      (if OS.FileSys.access (filepath, [OS.FileSys.A_READ])
       then generate_theory_file filepath
       else print ("Error: Cannot read file " ^ filepath ^ "\n"))
    | _ =>
      print ("Usage: gp2convert <gp2_file>\n" ^
             "  Converts a GP2 program file to a HOL4 theory file\n" ^
             "  Example: gp2convert examples/program/acyclic.gp2\n")
