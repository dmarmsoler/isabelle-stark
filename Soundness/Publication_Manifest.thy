theory Publication_Manifest
  imports FS_Square_192_137 FS_Square_First_Root_Comparison
    Square_Sequence_192_RO_Completeness
begin

section \<open>Publication statement and trust manifest\<close>

text \<open>This read-only checker exports existing results. It adds no theorem,
  axiom or locale premise. Generic locale predicates remain explicit premises;
  the imported axiom inventory is not a per-theorem minimal dependency claim.
  See PUBLICATION.md and REPRODUCING.md for scope and extraction instructions.\<close>

ML \<open>
local
  val thy = @{theory};
  val ctxt = Proof_Context.init_global thy
    |> Config.put Printer.show_types true
    |> Config.put Printer.show_sorts true
    |> Config.put Name_Space.names_long true;
  fun term_text t = (XML.content_of o YXML.parse_body) (Syntax.string_of_term ctxt t);
  fun lines xs = cat_lines xs ^ "\n";
  fun export name text =
    Export.export thy (Path.binding0 (Path.explode ("publication/" ^ name))) [XML.Text text];
  val entries =
    [("square_192_valid_trace_iff", 0, @{thm square_192_valid_trace_iff}),
     ("square_ro_honest_experiment_acceptance_one", 1,
       @{thm square_ro_honest_experiment_acceptance_one}),
     ("soundness.staged_fs_verifier_factorization", 1,
       @{thm soundness.staged_fs_verifier_factorization}),
     ("soundness.fs_compile_replay_acceptance", 3,
       @{thm soundness.fs_compile_replay_acceptance}),
     ("soundness.fs_compiled_mixture_acceptance", 2,
       @{thm soundness.fs_compiled_mixture_acceptance}),
     ("soundness.fs_replay_total_allowance", 1,
       @{thm soundness.fs_replay_total_allowance}),
     ("soundness.fs_first_root_soundness", 3,
       @{thm soundness.fs_first_root_soundness}),
     ("square_fs_first_root_ledger_balance", 0,
       @{thm square_fs_first_root_ledger_balance}),
     ("square_fs_137_prefix_target", 0, @{thm square_fs_137_prefix_target}),
     ("square_192_fs_137_incorrect_endpoint", 2,
       @{thm square_192_fs_137_incorrect_endpoint})];
  fun render (label, expected, th) =
    let
      val _ = if Thm.nprems_of th = expected andalso null (Thm.hyps_of th)
        andalso null (Thm.tpairs_of th) andalso null (Thm_Deps.all_oracles [th])
        then () else error ("Publication manifest check failed: " ^ label ^
          "; premises=" ^ string_of_int (Thm.nprems_of th) ^
          "; hypotheses=" ^ string_of_int (length (Thm.hyps_of th)) ^
          "; flex-flex=" ^ string_of_int (length (Thm.tpairs_of th)) ^
          "; oracles=" ^ string_of_int (length (Thm_Deps.all_oracles [th])));
      val deps = Thm_Deps.thm_deps thy [th]
        |> map (fn (_, (name, i)) => name ^ "(" ^ string_of_int i ^ ")")
        |> sort_distinct string_ord;
      val sorts = map ((XML.content_of o YXML.parse_body) o Syntax.string_of_sort ctxt) (Thm.shyps_of th);
    in lines
      (["THEOREM " ^ label,
        "derivation: " ^ #1 (Thm.derivation_name th),
        "premises: " ^ string_of_int (Thm.nprems_of th),
        "hidden_hypotheses: 0", "flex_flex_pairs: 0", "transitive_oracles: 0",
        "sort_hypotheses: " ^ commas sorts,
        "proposition:", term_text (Thm.full_prop_of th), "premise_propositions:"]
       @ map term_text (Thm.prems_of th)
       @ ["named_dependency_frontier:"] @ deps @ ["END THEOREM", ""])
    end;
  val axioms = Theory.all_axioms_of thy |> sort_by #1;
  val axiom_text = lines
    (["IMPORTED THEORY AXIOM INVENTORY",
      "Includes foundational axioms and definitional/type/class declarations.",
      "This is an environment inventory, NOT the minimal axioms used by each theorem.",
      "Empty oracle lists do not imply an axiom-free foundation.",
      "entries: " ^ string_of_int (length axioms), ""]
     @ maps (fn (name, prop) => [name, term_text prop, ""]) axioms);
  val manifest = lines
    ["STARK PUBLICATION MANIFEST v1",
     "Checks: exact exported premise count, no hidden hypotheses/flex-flex pairs/oracles.",
     "Propositions retain types/sorts and locale predicates among their premises.",
     "Named dependency frontier is not a minimal or transitive axiom-use certificate.",
     "Read alongside PUBLICATION.md and REPRODUCING.md.", ""]
    ^ String.concat (map render entries);
in
  val _ = export "manifest.txt" manifest;
  val _ = export "imported-axioms.txt" axiom_text;
  val _ = writeln ("Publication manifest: " ^ string_of_int (length entries) ^
    " checked statements; " ^ string_of_int (length axioms) ^ " imported axiom declarations");
end
\<close>

end
