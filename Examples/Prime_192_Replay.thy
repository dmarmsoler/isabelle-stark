(*  Title:      Stark/Prime_192_Replay.thy
    License:    BSD-3-Clause
*)

theory Prime_192_Replay
  imports "HOL-Number_Theory.Mod_Exp"
begin

section \<open>Kernel reconstruction of the fixed modular-power certificate\<close>

text \<open>The ML code computes only arithmetic hints. Every multiplication,
  quotient/remainder decomposition and strict remainder bound is proved in HOL.
  Each transition applies an equation of the original library @{const mod_exp_aux};
  endpoint and dependency checks reject malformed or oracle-backed results.
  This replay is specialized to the stated modulus and base 13. It is not
  a general primality decision procedure or a claim that 13 is a generator.
  Zero and one exponents are explicit terminal cases. The fixed positive
  modulus is never replaced by a conditional nonzero-modulus assumption.\<close>

lemma prime_192_terminal_equations:
  "mod_exp_aux (m::nat) y x 0 = y"
  "mod_exp_aux (m::nat) y x 1 = (x*y) mod m"
  "((x*y)::nat) mod 0 = x*y"
  "((x*y)::nat) mod 1 = 0"
  by simp_all

lemma prime_192_nat_modI:
  fixes m n q r :: nat
  assumes "m = q*n+r" "r<n"
  shows "m mod n=r"
  using assms by simp

ML \<open>
structure Prime_192_Replay_Arithmetic =
struct
  val ctxt = Proof_Context.init_global @{theory};
  val p : int = 3531942672373065915328229302366199208109272268385770536961;
  fun numeral n = HOLogic.mk_number HOLogic.natT n;
  fun times a b = HOLogic.mk_binop @{const_name times} (a,b);
  fun plus a b = HOLogic.mk_binop @{const_name plus} (a,b);
  fun eq a b = HOLogic.mk_Trueprop (HOLogic.mk_eq (a,b));
  fun less a b = HOLogic.mk_Trueprop (HOLogic.mk_binrel @{const_name less} (a,b));
  fun timed label seconds f =
    let
      val start = Timing.start ();
      val result = Exn.capture (Timeout.apply (Time.fromSeconds seconds) f) ();
      val timing = Timing.result start;
      val _ = writeln (label ^ ": " ^ Timing.message timing ^
        (case result of Exn.Res _ => " PASS" | Exn.Exn exn => " FAIL " ^ Runtime.exn_message exn));
    in Exn.release result end;
  fun prove prop =
    Goal.prove ctxt [] [] prop (fn {context,...} => ALLGOALS (Cooper.tac true [] [] context));
  fun inspect label th =
    if null (Thm.hyps_of th) andalso Thm.nprems_of th=0
       andalso null (Thm_Deps.all_oracles [th])
    then writeln (label ^ ": no hypotheses, premises or oracle dependencies")
    else error ("Unexpected proof dependency: " ^ label);
  fun mulmod label x y =
    let
      val (m,q,r) = timed (label ^ "/hints") 30
        (fn () => let val m=x*y in (m,m div p,m mod p) end);
      val _ = writeln (label ^ "/x=" ^ Int.toString x ^ "/y=" ^ Int.toString y ^
        "/m=" ^ Int.toString m ^ "/q=" ^ Int.toString q ^ "/r=" ^ Int.toString r);
      val product = timed (label ^ "/product") 30
        (fn () => prove (eq (times (numeral x) (numeral y)) (numeral m)));
      val decomposition = timed (label ^ "/decomposition") 30
        (fn () => prove (eq (numeral m) (plus (times (numeral q) (numeral p)) (numeral r))));
      val order = timed (label ^ "/order") 30
        (fn () => prove (less (numeral r) (numeral p)));
      val residue = timed (label ^ "/residue_assembly") 30
        (fn () => @{thm prime_192_nat_modI} OF [decomposition,order]);
      val _ = List.app (inspect label) [product,decomposition,order,residue];
    in (r,[product,residue]) end;
  val natT = HOLogic.natT;
  val aux = Const (@{const_name mod_exp_aux}, natT --> natT --> natT --> natT --> natT);
  fun state (x,y,e) = list_comb (aux,map numeral [p,y,x,e]);
  fun arithmetic_conv facts ct =
    let val current = Proof_Context.init_global (Thm.theory_of_cterm ct)
    in Simplifier.rewrite
      (put_simpset HOL_basic_ss current addsimps (@{thm power2_eq_square} :: facts)) ct end;
end;
\<close>

ML \<open>
structure Prime_192_Replay =
struct
  open Prime_192_Replay_Arithmetic;
  val current_ctxt = Proof_Context.init_global @{theory};
  val mod_exp_const = Const (@{const_name mod_exp}, natT --> natT --> natT --> natT);
  fun target exponent = list_comb (mod_exp_const,[numeral 13,exponent,numeral p]);
  fun terminal label (x,y,e) =
    if e=0 then
      let
        val result = Conv.rewr_conv (mk_meta_eq @{thm prime_192_terminal_equations(1)})
          (Thm.cterm_of current_ctxt (state (x,y,e)));
        val _ = inspect (label ^ "/zero_terminal") result;
      in (y,result) end
    else if e=1 then
      let
        val (r,facts) = mulmod (label ^ "/terminal_product") x y;
        val unfold = Conv.rewr_conv (mk_meta_eq @{thm prime_192_terminal_equations(2)})
          (Thm.cterm_of current_ctxt (state (x,y,e)));
        val result = Thm.transitive unfold (arithmetic_conv facts (Thm.rhs_of unfold));
        val _ = inspect (label ^ "/one_terminal") result;
      in (r,result) end
    else error "Terminal driver received a nonterminal exponent";
  fun nonterminal label (x,y,e) =
    if e<2 then error "Nonterminal driver received a terminal exponent"
    else
      let
        val (x',square_facts) = mulmod (label ^ "/square") x x;
        val (y',acc_facts) =
          if e mod 2=0 then (y,[]) else mulmod (label ^ "/accumulator") x y;
        val rule = mk_meta_eq (if e mod 2=0 then @{thm eval_mod_exp_aux(3)}
          else @{thm eval_mod_exp_aux(4)});
        val unfold = timed (label ^ "/library_equation") 30
          (fn () => Conv.rewr_conv rule (Thm.cterm_of current_ctxt (state (x,y,e))));
        val y_conv = if e mod 2=0 then Conv.all_conv else arithmetic_conv acc_facts;
        val arguments = timed (label ^ "/arithmetic_arguments") 30
          (fn () => Conv.fun_conv (Conv.combination_conv
            (Conv.arg_conv y_conv) (arithmetic_conv square_facts)) (Thm.rhs_of unfold));
        val exponent_conv = if e div 2=1
          then Conv.rewr_conv (mk_meta_eq @{thm numeral_One}) else Conv.all_conv;
        val canonical = timed (label ^ "/exponent_representation") 30
          (fn () => Conv.arg_conv exponent_conv (Thm.rhs_of arguments));
        val result = Thm.transitive unfold (Thm.transitive arguments canonical);
        val next = (x',y',e div 2);
        val _ = if Thm.term_of (Thm.lhs_of result) aconv state (x,y,e)
          andalso Thm.term_of (Thm.rhs_of result) aconv state next
          then () else error "Original-function nonterminal endpoint mismatch";
        val _ = inspect label result;
      in (next,result) end;
  fun replay label exponent_expr exponent =
    let
      val initial = (13,1,exponent);
      val normalized = timed (label ^ "/initial_exponent") 30
        (fn () => prove (eq exponent_expr (numeral exponent)));
      val initial_eq = timed (label ^ "/initial_expression") 30
        (fn () => Conv.fun_conv (Conv.arg_conv (Conv.rewr_conv (mk_meta_eq normalized)))
          (Thm.cterm_of current_ctxt (target exponent_expr)));
      val unfold = timed (label ^ "/mod_exp_code") 30
        (fn () => Conv.rewr_conv (mk_meta_eq @{thm mod_exp_code}) (Thm.rhs_of initial_eq));
      val start = Thm.reflexive (Thm.cterm_of current_ctxt (state initial));
      val chain_start = Timing.start ();
      fun loop count (s as (_,_,e)) chain =
        if e<2 then
          let
            val (r,last) = timed (label ^ "/terminal") 30 (fn () => terminal label s);
            val result = Thm.transitive chain last;
            val _ = if Thm.term_of (Thm.lhs_of result) aconv state initial
              andalso Thm.term_of (Thm.rhs_of result) aconv numeral r
              then () else error "Complete auxiliary-chain endpoint mismatch";
            val _ = writeln (label ^ "/chain_complete steps=" ^ Int.toString count ^
              " residue=" ^ Int.toString r ^ " " ^ Timing.message (Timing.result chain_start));
          in (r,result,count) end
        else
          let
            val (s',step) = nonterminal (label ^ "/step_" ^ Int.toString count) s;
            val chain' = Thm.transitive chain step;
            val (_,_,e') = s';
            val _ = if e'<e then () else error "Exponent failed to decrease";
            val _ = writeln (label ^ "/completed_step=" ^ Int.toString count ^
              " next_exponent=" ^ Int.toString e' ^ " " ^
              Timing.message (Timing.result chain_start));
          in loop (count+1) s' chain' end;
      val (r,chain,count) = loop 0 initial start;
      val outer_chain = timed (label ^ "/outer_chain_lift") 30
        (fn () => Conv.arg1_conv (Conv.rewr_conv chain) (Thm.rhs_of unfold));
      val outer_order = timed (label ^ "/outer_residue_bound") 30
        (fn () => prove (less (numeral r) (numeral p)));
      val outer_rule = mk_meta_eq (@{thm mod_less} OF [outer_order]);
      val outer = timed (label ^ "/outer_modulo") 30
        (fn () => Conv.rewr_conv outer_rule (Thm.rhs_of outer_chain));
      val result = timed (label ^ "/final_composition") 30
        (fn () => Thm.transitive initial_eq
          (Thm.transitive unfold (Thm.transitive outer_chain outer)));
      val _ = if Thm.term_of (Thm.lhs_of result) aconv target exponent_expr
        andalso Thm.term_of (Thm.rhs_of result) aconv numeral r
        then () else error "Original mod_exp endpoint mismatch";
      val _ = inspect (label ^ "/initial_exponent_fact") normalized;
      val _ = inspect (label ^ "/full_mod_exp_fact") result;
    in (r,result,count) end;
end;
\<close>
ML \<open>
fun run_full_half_power () =
  Prime_192_Replay_Arithmetic.timed "full_half_power/TOTAL" 300 (fn () =>
    let
      open Prime_192_Replay;
      val predecessor_expr = Syntax.read_term current_ctxt
        "(3531942672373065915328229302366199208109272268385770536961-1)::nat";
      val exponent_expr = Syntax.read_term current_ctxt
        "((3531942672373065915328229302366199208109272268385770536961-1) div 2)::nat";
      val exponent = (p-1) div 2;
      val predecessor = timed "full_half_power/predecessor_expression" 30
        (fn () => prove (eq predecessor_expr (numeral (p-1))));
      val (r,replayed,count) = replay "full_half_power" exponent_expr exponent;
      val _ = if r=p-1 then () else error "Exact half-power residue is not F-1";
      val result = timed "full_half_power/original_target" 30
        (fn () => HOLogic.mk_obj_eq
          (Thm.transitive replayed (Thm.symmetric (mk_meta_eq predecessor))));
      val _ = if Thm.prop_of result aconv eq (target exponent_expr) predecessor_expr
        then writeln "Exact original half-power theorem verified"
        else error "Original half-power proposition mismatch";
      val _ = inspect "full_half_power/exportable_theorem" result;
      val _ = writeln ("full_half_power/nonterminal_steps=" ^ Int.toString count);
    in result end);
\<close>

end
