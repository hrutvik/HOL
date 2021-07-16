structure l3_equivalenceLib :> l3_equivalenceLib =
struct

open HolKernel boolLib bossLib Parse
open armv86aTheory armv86a_terminationTheory armv86a_typesTheory
open arm8Theory arm8Lib arm8_stepTheory arm8_stepLib
open wordsTheory bitstringTheory finite_mapTheory listTheory
     arithmeticTheory integerTheory updateTheory
open wordsLib optionLib combinLib
open l3_equivalence_miscTheory l3_equivalence_lemmasTheory l3_equivalenceTheory

val _ = set_grammar_ancestry [
          "arm8_step", "arm8",
          "armv86a_termination",
          "l3_equivalence"
          ];

val _ = wordsLib.output_words_as_bin();
val _ = wordsLib.guess_lengths();

val _ = numLib.prefer_num();

val _ = Globals.show_assums := false;

val _ = augment_srw_ss [
    bitstringLib.v2w_n2w_ss,
    bitstringLib.BITSTRING_GROUND_ss,
    wordsLib.WORD_ss
  ];

(******************** L3 tactics ********************)
fun l3_eval thms = SIMP_RULE (srw_ss()) [] o
                   computeLib.CBV_CONV (arm8_compset thms);

fun l3_eval_tac thms = CONV_TAC (l3_eval thms);

local
  fun get tm =
    Option.getOpt
      (Lib.total lhs tm,
       if boolSyntax.is_neg tm then boolSyntax.F else boolSyntax.T)
in
  fun mk_blast_thm l =
    let
      val lty = Term.type_of l
      val ty = wordsSyntax.dest_word_type lty
      val r =
        blastLib.BBLAST_CONV (boolSyntax.mk_eq (l, Term.mk_var ("_", lty)))
        |> concl |> rhs |> strip_conj |> List.map get |> List.rev
        |> (fn l => listSyntax.mk_list (l, Type.bool))
        |> (fn tm => bitstringSyntax.mk_v2w (tm, ty))
    in
      blastLib.BBLAST_PROVE (boolSyntax.mk_eq (r, l)) |> SIMP_RULE bool_ss []
    end
end

(* Takes an opcode (which may be multiple concatenated fields) and attempts to
   decode fully, simplifying result. Uses arm8_stepLib.arm8_decode. *)
fun l3_decode tm =
  let val _ = type_of tm |>
              assert (fn ty => wordsSyntax.dest_word_type ty =
                        fcpSyntax.mk_numeric_type (Arbnum.fromInt 32))
      fun remove x [] = []
        | remove x (y::ys) = if x ~~ y then remove x ys else (y::remove x ys)
      fun remove_dups [] = []
        | remove_dups (x::xs) = x::(remove_dups (remove x xs));
      val blast_thm = mk_blast_thm tm
      val opc_list = concl blast_thm |> lhs
      val sub_blast_thms = if is_var tm then [] else
                           map mk_blast_thm (remove_dups (find_terms is_var tm))
      val decode_thm = arm8_decode (rand opc_list) |>
                       REWRITE_RULE sub_blast_thms
  in REWRITE_RULE [blast_thm] decode_thm end
  handle _ => raise (mk_HOL_ERR "l3_decode" "l3_decode" "l3_equivalenceLib");

(* Searches for `Decode opc` in goal and applies l3_decode to `opc` *)
val l3_decode_tac =
  let val decode_tm = prim_mk_const {Name = "Decode", Thy = "arm8"}
      fun find_decode tm = is_comb tm andalso
                           same_const (strip_comb tm |> fst) decode_tm
      fun apply_l3_decode tm = assume_tac (l3_decode (rand tm)) >> gvs[]
  in goal_term (fn tm => apply_l3_decode (find_term find_decode tm)) end

(* Takes `Decode opc = _` and gives possible next steps.
   Uses arm8_stepLib.arm8_next, arm8_stepLib.arm8_run. *)
fun l3_run tm =
  let val decode_tm = prim_mk_const {Name = "Decode", Thy = "arm8"}
      val _ = assert (fn tm => is_eq tm andalso
                      same_const (lhs tm |> strip_comb |> fst) decode_tm) tm
      (* mk_thm below should be OK - arm8_run immediately uses concl *)
      val run_thm = arm8_run (mk_thm ([], tm))
      val to_expand_tm = run_thm |> SPEC_ALL |> concl |> rhs |> rator
      val expand_thms = arm8_next to_expand_tm
  in map (fn thm => REWRITE_RULE [thm] run_thm) expand_thms end
  handle _ => raise (mk_HOL_ERR "l3_run" "l3_run" "l3_equivalenceLib");

(* Searches for `Decode opc = _` in assumptions and applies l3_run.
   Does not do anything to handle multiple possible next steps. *)
val l3_run_tac =
  qpat_assum `Decode _ = _` (fn thm =>
    map_every (assume_tac o DISCH_ALL) (l3_run (concl thm)) >> gvs[]);


(******************** ASL tactics ********************)

(***** custom compset *****)
local

  fun add_type cmp =
    computeLib.add_datatype_info cmp o Option.valOf o TypeBase.fetch
  fun add_types cmp l = List.app (add_type cmp) l

  val tyvars = [alpha, beta, gamma, delta, etyvar, ftyvar]
  fun mk_cmp_type (thy, (name, arity)) =
    mk_thy_type {Args = List.take (tyvars, arity), Thy = thy, Tyop = name}
  fun add_all_types cmp thy =
    add_types cmp (map (mk_cmp_type o pair thy) (types thy))

  fun add_defs cmp defs = computeLib.add_thms defs cmp
    handle (HOL_ERR _) => ((* PolyML.print defs;*) ())
  fun not_contains_tydef thm = thm |> concl |> find_terms
    (same_const (prim_mk_const {Name = "TYPE_DEFINITION", Thy = "bool"})) |>
    null
  fun add_all_defs cmp thy = app (add_defs cmp o single)
    (definitions thy |> map snd |> filter not_contains_tydef)

  val thys = [
      "lem_machine_word", "lem",
      "sail2_instr_kinds",
      "sail2_operators_bitlists", "sail2_operators_mwords", "sail2_operators",
      "sail2_stateAuxiliary", "sail2_state_monad", "sail2_state",
      "sail2_string", "sail2_valuesAuxiliary", "sail2_values",
      "prelude", "armv86a_types"
    ]
  (*
  val thys = [
      "lem_assert_extra", "lem_basic_classes", "lem_bool", "lem_either",
      "lem_function_extra", "lem_function",
      "lem_list_extra_sail", "lem_list", "lem_machine_word",
      "lem_map_extra", "lem_map", "lem_maybe_extra", "lem_maybe",
      "lem_num_extra", "lem_num", "lem_pervasives_extra_sail",
      "lem_pervasives_sail", "lem_relation", "lem", "lem_set_extra_sail",
      "lem_set_helpers", "lem_set", "lem_show_extra", "lem_show",
      "lem_sorting", "lem_string_extra_sail", "lem_string_sail",
      "lem_tuple", "lem_word",

      "sail2_instr_kinds", "sail2_operators_bitlists", "sail2_operators_mwords",
      "sail2_operators", "sail2_prompt_monad", "sail2_prompt",
      "sail2_stateAuxiliary", "sail2_state_monad", "sail2_state",
      "sail2_string", "sail2_valuesAuxiliary", "sail2_values",

      "prelude", "armv86a_types"
    ]
    *)
in

  val cmp = reduceLib.num_compset();
  val _ = pairLib.add_pair_compset cmp;
  val _ = optionLib.OPTION_rws cmp;
  val _ = combinLib.add_combin_compset cmp;
  val _ = wordsLib.add_words_compset true cmp;
  (* val _ = integer_wordLib.add_integer_word_compset cmp; *)
  val _ = intReduce.add_int_compset cmp;
  val _ = cmp |> computeLib.add_conv
    (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV);
  val _ = cmp |> computeLib.add_conv
    (``$= : α word -> α word -> bool``, 2, QCHANGED_CONV blastLib.BBLAST_CONV);
  val _ = bitstringLib.add_bitstring_compset cmp; (* has to come after BBLAST_CONV *)
  val _ = app (add_all_types cmp) thys;
  val _ = app (add_all_defs cmp) thys;
  val _ = cmp |> computeLib.add_thms [
              armv86aTheory.ExecuteA64_def,
              armv86aTheory.DecodeA64_def,
              armv86aTheory.Zeros_def
            ];
  (* don't look at conditional branches before guard is fully evaluated *)
  (* val _ = computeLib.set_skip cmp boolSyntax.conditional (SOME 1) *)
  val CEVAL = computeLib.CBV_CONV cmp

end

(* Uses `eval` to execute opcode `tm`. *)
fun asl_execute_helper eval tm =
  let val _ = type_of tm |>
              assert (fn ty => wordsSyntax.dest_word_type ty =
                        fcpSyntax.mk_numeric_type (Arbnum.fromInt 32))
      val blast_thm = mk_blast_thm tm
      val v2w_tm = concl blast_thm |> lhs
      fun remove x [] = []
        | remove x (y::ys) = if x ~~ y then remove x ys else (y::remove x ys)
      fun remove_dups [] = []
        | remove_dups (x::xs) = x::(remove_dups (remove x xs));
      val sub_blast_thms = if is_var tm then [] else
                           map mk_blast_thm (remove_dups (find_terms is_var tm))
      val eval_tm = ``seqS (write_regS SEE_ref (~1)) (ExecuteA64 ^v2w_tm) asl``
  in eval eval_tm |> GEN_ALL |> REWRITE_RULE (blast_thm::sub_blast_thms) end
  handle _ => raise (
    mk_HOL_ERR "asl_execute" "asl_execute" "l3_equivalenceLib");

val asl_execute = asl_execute_helper EVAL;
val asl_cexecute = asl_execute_helper CEVAL;

(* Looks for `ExecuteA64 opc` and assumes `asl_execute eval opc` *)
fun asl_execute_tac_helper eval =
  let val ExecuteA64_tm = prim_mk_const {Name = "ExecuteA64", Thy = "armv86a"};
      fun find_ExecuteA64 tm = is_comb tm andalso
                               same_const (strip_comb tm |> fst) ExecuteA64_tm
      fun apply_asl_execute tm = assume_tac (asl_execute_helper eval (rand tm))
  in
    goal_term
      (fn tm => apply_asl_execute (find_term find_ExecuteA64 tm))
  end;

val asl_execute_tac = asl_execute_tac_helper EVAL;
val asl_cexecute_tac = asl_execute_tac_helper CEVAL;


(******************** Other stuff ********************)

(***** current compset *****)
(*
  val _ = computeLib.add_convs [
    (wordsSyntax.word_extract_tm, 3, bitstringLib.extract_v2w_CONV)
    ];
  WORD_EXTRACT_ss
*)
val _ = computeLib.add_convs [
    (bitstringSyntax.v2w_tm, 1, bitstringLib.v2w_n2w_CONV)
  ];


(***** rewrites *****)
val armv86a_ss =
  simpLib.named_rewrites "armv86a_ss" [
    combinTheory.I_THM,
    lemTheory.w2ui_def,
    sail2_valuesTheory.make_the_value_def,
    nat_of_int,
    sail2_operators_mwordsTheory.zeros_def,
    sail2_operators_mwordsTheory.concat_vec_def,
    armv86aTheory.sail_ones_def,
    armv86aTheory.Zeros_def,
    armv86aTheory.IsZero_def,
    armv86aTheory.id_def,
    lem_machine_wordTheory.size_itself_def,
    sail2_valuesTheory.size_itself_int_def,
    armv86aTheory.ZeroExtend1_def,
    sail2_operators_mwordsTheory.zero_extend_def,
    sail2_operators_mwordsTheory.not_vec_def,
    EL0_def, EL1_def, EL2_def, EL3_def,
    place_slice_def, shiftl, shiftr,
    sail2_operators_mwordsTheory.extz_vec_def,
    sail2_operators_mwordsTheory.and_vec_def,
    sail2_operators_mwordsTheory.not_vec_def,
    sail2_operators_mwordsTheory.vector_truncate_def,
    sail2_stateTheory.internal_pickS_def,
    sail2_state_monadTheory.chooseS_def,
    sail2_state_monadTheory.choose_boolS_def,
    sail2_state_monadTheory.assert_expS_def,
    sail2_stateTheory.and_boolS_def,
    sail2_stateTheory.or_boolS_def,
    preludeTheory.undefined_bitvector_def,
    sail2_operators_mwordsTheory.subrange_vec_dec_def,
    sail2_operators_mwordsTheory.subrange_vec_inc_def,
    sail2_operators_mwordsTheory.update_subrange_vec_dec_def,
    sail2_operators_mwordsTheory.update_subrange_vec_inc_def,
    sail2_valuesTheory.update_list_def,
    sail2_valuesTheory.update_list_inc_def,
    sail2_valuesTheory.update_list_dec_def,
    sail2_valuesTheory.access_list_def,
    sail2_valuesTheory.access_list_inc_def ,
    sail2_valuesTheory.access_list_dec_def,
    sail2_valuesTheory.subrange_list_def ,
    sail2_valuesTheory.subrange_list_dec_def,
    sail2_valuesTheory.subrange_list_inc_def,
    sail2_operators_mwordsTheory.access_vec_inc_def,
    sail2_operators_mwordsTheory.access_vec_dec_def
  ];

val _ = augment_srw_ss [armv86a_ss];

val encode_ss =
  simpLib.named_rewrites "encode_ss" [
    Encode_def,
    e_data_def, e_branch_def, e_load_store_def, e_sf_def, e_LoadStoreImmediate_def,
    EncodeLogicalOp_def, NoOperation_def,
    ShiftType2num_thm, SystemHintOp2num_thm, ShiftType2num_thm
  ];

val monad_ss =
  simpLib.named_rewrites "monad_ss" [
    sail2_state_monadTheory.seqS_def,
    sail2_state_monadTheory.returnS_def,
    sail2_state_monadTheory.bindS_def,
    sail2_state_monadTheory.read_regS_def,
    sail2_state_monadTheory.readS_def,
    sail2_state_monadTheory.write_regS_def,
    sail2_state_monadTheory.updateS_def,
    sail2_state_monadTheory.chooseS_def,
    sail2_state_monadTheory.assert_expS_def,
    sail2_stateTheory.and_boolS_def,
    sail2_stateTheory.or_boolS_def,
    sail2_stateTheory.internal_pickS_def
  ];

val asl_word_ss =
  simpLib.named_rewrites "asl_word_ss" [
    sail2_valuesTheory.access_bv_dec_def,
    sail2_operators_mwordsTheory.vec_of_bits_def ,
    sail2_valuesTheory.of_bits_failwith_def,
    sail2_valuesTheory.maybe_failwith_def,
    wordsTheory.bit_field_insert_def,
    preludeTheory.undefined_bitvector_def |>
      REWRITE_RULE [Once FUN_EQ_THM, sail2_state_monadTheory.returnS_def],
    armv86aTheory.integer_subrange_def,
    sail2_operators_mwordsTheory.get_slice_int_def,
    sail2_operatorsTheory.get_slice_int_bv_def,
    l3_equivalence_lemmasTheory.bools_of_int_def,
    sail2_valuesTheory.add_one_bool_ignore_overflow_def,
    sail2_valuesTheory.instance_Sail2_values_Bitvector_Machine_word_mword_dict_def
  ];

val asl_reg_ss =
  simpLib.named_rewrites "asl_reg_ss" [
    sail2_state_monadTheory.read_regS_def,
    sail2_state_monadTheory.write_regS_def,
    sail2_state_monadTheory.readS_def,
    sail2_state_monadTheory.updateS_def,
    R_ref_def, PSTATE_ref_def, SEE_ref_def,
    SCTLR_EL1_ref_def, SCTLR_EL1_ref_def, SCTLR_EL2_ref_def, SCTLR_EL3_ref_def,
    PC_ref_def,
    SP_EL0_ref_def, SP_EL1_ref_def, SP_EL2_ref_def, SP_EL3_ref_def,
    TCR_EL1_ref_def, TCR_EL2_ref_def, TCR_EL3_ref_def
  ];

val l3_reg_ss =
  simpLib.named_rewrites "l3_reg_ss" [
    reg'TCR_EL1_def, reg'TCR_EL2_EL3_def, reg'SCTLRType_def
  ]

val sss = [encode_ss, monad_ss, asl_word_ss, asl_reg_ss, l3_reg_ss];
val _ = map simpLib.register_frag sss;
val [encode_rws, monad_rws, asl_word_rws, asl_reg_rws, l3_reg_rws] = map SF sss;

(* Rewrites using various state theorems and state relation *)
fun state_rel_tac thms =
  gvs ([
    flag_rel_def, pstate_rel_def, tcr_el1_rel_def, tcr_el2_3_rel_def,
    sctlr_rel_def, read_rel_def, reg_rel_def, mem_rel_def, state_rel_def,
    asl_reg_rws, l3_reg_rws,
    sail2_operators_mwordsTheory.vec_of_bits_def,
    sail2_valuesTheory.of_bits_failwith_def,
    sail2_valuesTheory.maybe_failwith_def
    ] @ thms) >>
  rw[FLOOKUP_UPDATE, EL_LUPDATE, APPLY_UPDATE_THM] >> gvs[];

(****************************************)

end
