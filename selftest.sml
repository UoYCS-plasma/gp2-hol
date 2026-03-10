open HolKernel boolLib bossLib
open gp2Parser
open hostgraphTheory hostgraphSyntax programTheory programSyntax

(*
open computeLib ruleTheory graphTheory finite_mapTheory pred_setTheory programTheory Conv Drule


val wf_graph_compset = computeLib.bool_compset ()
val () = computeLib.add_thms [wf_graph_def, graph_accfupds, combinTheory.K_THM] wf_graph_compset
val () = finite_mapLib.add_finite_map_compset wf_graph_compset
val () = pred_setLib.add_pred_set_compset wf_graph_compset
val () = computeLib.add_thms [finite_mapTheory.FRANGE_FUPDATE_DOMSUB, finite_mapTheory.DOMSUB_FUPDATE_THM,
                              finite_mapTheory.DOMSUB_FEMPTY, finite_mapTheory.FRANGE_FEMPTY] wf_graph_compset
val () = computeLib.add_conv (boolSyntax.equality, 2, stringLib.string_EQ_CONV) wf_graph_compset *)
(*
fun wf_graph_conv tm =
    if graphSyntax.is_wf_graph tm
    then let
        val thm = CBV_CONV wf_graph_compset tm
    in if boolSyntax.Teq $ rhs (snd $ dest_thm thm) then thm
       else raise UNCHANGED
    end
    else raise UNCHANGED
 *)

(*
val wf_rule_compset = computeLib.bool_compset ()
val () = computeLib.add_thms [wf_rule_def, rule_accfupds, combinTheory.K_THM] wf_rule_compset
val () = computeLib.add_conv (graphSyntax.wf_graph_term, 1, wf_graph_conv) wf_rule_compset
val () = computeLib.add_thms [graph_accfupds] wf_rule_compset
val () = computeLib.add_thms [EMPTY_SUBSET] wf_rule_compset
val () = computeLib.add_thms [wf_cond_def] wf_rule_compset

(*
fun wf_rule_conv tm = *)
    if ruleSyntax.is_wf_rule tm
    then let
        val thm = CBV_CONV wf_rule_compset tm
        val r = rhs $ snd (dest_thm thm)
    in if boolSyntax.Teq r then thm else raise UNCHANGED
    end
    else raise UNCHANGED
 *)


(* val wf_program_compset = computeLib.bool_compset () *)
(* val () = computeLib.add_thms [wf_program_def, prog_accfupds, combinTheory.K_THM, FEVERY_DEF] wf_program_compset *)
(* val () = computeLib.add_conv (ruleSyntax.wf_rule_term, 1, wf_rule_conv) wf_program_compset *)
(* val () = pairLib.add_pair_compset wf_program_compset *)
(* val () = finite_mapLib.add_finite_map_compset wf_program_compset *)
(* val () = computeLib.add_thms [finite_mapTheory.FEVERY_FEMPTY] wf_program_compset *)
(* val () = computeLib.add_thms [finite_mapTheory.FRANGE_FUPDATE_DOMSUB, finite_mapTheory.DOMSUB_FUPDATE_THM, *)
(*                               finite_mapTheory.DOMSUB_FEMPTY, finite_mapTheory.FRANGE_FEMPTY] wf_program_compset *)
(* val () = computeLib.add_conv (boolSyntax.equality, 2, stringLib.string_EQ_CONV) wf_program_compset *)

(* (* CBV_CONV wf_program_compset tm *) *)


(* val (file::x) = list_files program_path *)
(* val raw = raw_read_file file; *)
(* val (P.toplevel_program (decl::rest)) = raw *)
(* val prog_tm = programSyntax.mk_program_tm [decl] *)

(* val tm = “wf_program ^prog_tm” *)

structure P = Parsetree;

fun remove_special_chars #"-" = "_"
  | remove_special_chars #"." = "_"
  | remove_special_chars c = String.str c


fun test_file file = let
    val fname = OS.Path.file file;
    val _ = print ("Processing: " ^ fname ^ "\n");
    val raw = raw_read_file file;
    fun to_thm_name f = String.translate remove_special_chars f;
in
    case raw of
	P.toplevel_hostgraph g =>
	let
	  val g_tm = hostgraphSyntax.mk_hostgraph_tm g
	  val thm_term = “wf_hostgraph ^g_tm”
    val thm_name = "hostgraph_" ^ to_thm_name fname ^ "_wf"
            (* val _ = save_thm (thm_name, prove (thm_term, CONV_TAC wf_graph_conv)); *)
	in
            print ("Stored " ^ thm_name ^ "\n")
	end
      | P.toplevel_program p =>
	let
	    val p_expanded = programSyntax.expand_bidir_rules p
	    val p_tm = programSyntax.mk_program_tm p_expanded
	    val thm_term = "wf_program ^p_tm"
            val thm_name = "program_" ^ to_thm_name fname ^ "_wf"
            val _ = print ("Created program term for " ^ thm_name ^ "\n")
            (* val _ = save_thm (thm_name, wf_program_conv thm_term); *)

	in
	    print ("Program " ^ fname ^ " processed successfully\n")
	end
end


fun list_files b = map (fn f => b ^ "/" ^ f) (Portable.listDir b);

val hostgraph_path = "examples/hostgraph"
val program_path = "examples/program"

val _ = print "Hostgraph:\n"
val _ = map test_file (list_files hostgraph_path)

val _ = print "\n"
val _ = print "Program:\n"
val _ = map test_file (list_files program_path)
