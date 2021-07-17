open HolKernel boolLib bossLib Parse BasicProvers dep_rewrite
open armv86aTheory armv86a_terminationTheory armv86a_typesTheory
open arm8Theory arm8Lib arm8_stepTheory arm8_stepLib
open wordsTheory bitstringTheory finite_mapTheory listTheory
     arithmeticTheory integerTheory
open l3_equivalenceTheory l3_equivalence_miscTheory l3_equivalence_lemmasTheory
open wordsLib intLib l3_equivalenceLib

val _ = new_theory "l3_equivalenceProof";

(****************************************)

(* TODO
  - undefined stuff tactic
  - decode/execute unfolding tactic
  - renaming tactic for successive asl states
*)

fun b64 ty = INST_TYPE [ty |-> ``:64``];

Theorem bindS = sail2_state_monadTheory.bindS_def;

Theorem seqS =
  sail2_state_monadTheory.seqS_def |> SIMP_RULE std_ss [bindS, FUN_EQ_THM];

Theorem returnS = sail2_state_monadTheory.returnS_def;

Theorem bindS_returnS[simp]:
  bindS (returnS a) f = f a
Proof
  rw[FUN_EQ_THM, bindS, returnS]
QED

Theorem seqS_returnS[simp]:
  seqS (returnS a) f = f
Proof
  rw[FUN_EQ_THM, bindS, seqS, returnS]
QED

Theorem returnS_bindS:
  ∀f a x s.
  x s = returnS a s ⇒
  bindS x f s = f a s
Proof
  rw[bindS, returnS]
QED


(****************************************)

Theorem X_set_31:
  width = 32 ∨ width = 64 ⇒
  X_set width 31 v = returnS ()
Proof
  simp[X_set_def]
QED

Theorem X_set_not_31:
  ∀l3 asl1. state_rel l3 asl1 ⇒
  ∀width i v. (width = 32 ∨ width = 64) ∧ i ≥ 0 ∧ i < 31 ⇒
  ∃asl2.
    X_set width i v asl1 = returnS () asl2 ∧
    state_rel (write'X (v, n2w (nat_of_int i)) l3) asl2
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[X_set_def] >> IF_CASES_TAC >> gvs[returnS] >>
  simp[asl_reg_rws] >>
  IF_CASES_TAC >> gvs[] >- (strip_tac >> irule FALSITY >> ARITH_TAC) >>
  simp[bindS, returnS, write'X_def] >>
  reverse IF_CASES_TAC >> gvs[] >- (strip_tac >> irule FALSITY >> ARITH_TAC) >>
  rw[] >> state_rel_tac[] >> irule FALSITY >> ARITH_TAC
QED

Theorem X_read:
  ∀l3 asl. state_rel l3 asl ⇒
  ∀i. i ≥ 0 ∧ i ≤ 31 ⇒
  X_read 64 i asl = returnS (X (n2w (nat_of_int i)) l3 : 64 word) asl
Proof
  rw[] >> simp[X_read_def] >> IF_CASES_TAC >> gvs[] >>
  simp[asl_reg_rws, bindS, X_def, returnS] >>
  IF_CASES_TAC >> gvs[] >- (irule FALSITY >> ARITH_TAC) >>
  IF_CASES_TAC >> gvs[] >- (irule FALSITY >> ARITH_TAC) >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[] >>
  state_rel_tac[] >> first_x_assum $ irule o GSYM >> ARITH_TAC
QED

Theorem SP_read:
  ∀l3 asl. state_rel l3 asl ⇒
  SP_read 64 asl = returnS (SP l3 : 64 word) asl
Proof
  rw[] >> simp[SP_read_def, SP_def] >>
  state_rel_tac[] >> simp[bindS, returnS] >>
  DEP_REWRITE_TAC[EXTRACT_ALL_BITS] >> simp[]
QED

Theorem SP_set:
  ∀l3 asl. state_rel l3 asl ⇒
  ∀v. ∃asl2.
    SP_set 64 v asl = returnS () asl2 ∧
    state_rel (write'SP v l3) asl2
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[SP_set_def, asl_reg_rws, returnS, bindS, write'SP_def] >>
  IF_CASES_TAC >> gvs[] >- state_rel_tac[] >>
  IF_CASES_TAC >> gvs[] >- state_rel_tac[] >>
  simp[bindS, COND_RATOR, returnS] >>
  Cases_on_word_value `l3.PSTATE.EL` >> gvs[] >> state_rel_tac[]
QED

Theorem SetTheFlags_F[simp]:
  ∀rest s. SetTheFlags (F, rest) s = s
Proof
  PairCases >> rw[SetTheFlags_def]
QED

Theorem asl_extract_flags[simp]:
  (3 >< 3) (v2w [n;z;c;v] : word4) = v2w [n] : word1 ∧
  (2 >< 2) (v2w [n;z;c;v] : word4) = v2w [z] : word1 ∧
  (1 >< 1) (v2w [n;z;c;v] : word4) = v2w [c] : word1 ∧
  (0 >< 0) (v2w [n;z;c;v] : word4) = v2w [v] : word1
Proof
  EVAL_TAC
QED

Theorem l3_asl_SetTheFlags:
  ∀l3 asl1. state_rel l3 asl1 ⇒
  ∀n z c v. ∃asl2.
    do
      p1 <- read_regS PSTATE_ref;
      p2 <- do
          write_regS PSTATE_ref (p1 with ProcState_N := n);
          read_regS PSTATE_ref od;
      p3 <- do
          write_regS PSTATE_ref (p2 with ProcState_Z := z);
          read_regS PSTATE_ref od;
      p4 <- do
          write_regS PSTATE_ref (p3 with ProcState_C := c);
          read_regS PSTATE_ref od;
      write_regS PSTATE_ref (p4 with ProcState_V := v);
    od asl1 =
    returnS () asl2 : (unit, exception) result # regstate sequential_state ∧
    state_rel (SetTheFlags (T,HD (w2v n),HD (w2v z),HD (w2v c),HD (w2v v)) l3) asl2
Proof
  rw[returnS, seqS, bindS, asl_reg_rws, COND_RATOR, SetTheFlags_def] >>
  state_rel_tac[] >> rpt $ pop_assum kall_tac >>
  rename1 `foo = _` >> Cases_on_word_value `foo` >> gvs[]
QED



(****************************************)

Theorem l3_models_asl_NoOperation:
  l3_models_asl_instr NoOperation
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >>
  l3_decode_tac >> l3_run_tac >>
  asl_execute_tac >> gvs[] >>
  state_rel_tac []
QED

Theorem l3_models_asl_MoveWideOp_Z:
  ∀hw imm16 r.
    l3_models_asl_instr (Data (MoveWide@64 (1w, MoveWideOp_Z, hw, imm16, r)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >>
  asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
  simp[decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  simp[undefined_MoveWideOp_def] >>
  simp[execute_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  reverse IF_CASES_TAC >> gvs[] >- (Cases_on_word_value `hw` >> gvs[]) >>
  IF_CASES_TAC >> gvs[] >- (irule FALSITY >> ARITH_TAC) >>
  Cases_on `r = 31w` >> gvs[INT_ADD_CALCULATE]
  >- (DEP_REWRITE_TAC[X_set_31] >> simp[returnS] >> state_rel_tac[]) >>
  qmatch_goalsub_abbrev_tac `X_set _ reg v asl1` >>
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel _ asl` kall_tac >>
  dxrule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`reg`,`v`] mp_tac >> simp[Abbr `reg`, int_ge] >>
  impl_tac >- WORD_DECIDE_TAC >> strip_tac >> simp[] >> gvs[write'X_def, returnS]
QED

Theorem l3_models_asl_MoveWideOp_N:
  ∀hw imm16 r.
    l3_models_asl_instr (Data (MoveWide@64 (1w, MoveWideOp_N, hw, imm16, r)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >>
  asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
  gvs[decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[undefined_MoveWideOp_def] >>
  gvs[execute_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  reverse IF_CASES_TAC >> gvs[] >- (Cases_on_word_value `hw` >> gvs[]) >>
  IF_CASES_TAC >> gvs[] >- (irule FALSITY >> ARITH_TAC) >>
  Cases_on `r = 31w` >> gvs[INT_ADD_CALCULATE]
  >- (DEP_REWRITE_TAC[X_set_31] >> simp[returnS] >> state_rel_tac[]) >>
  qmatch_goalsub_abbrev_tac `X_set _ reg v asl1` >>
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel _ asl` kall_tac >>
  dxrule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`reg`,`v`] mp_tac >> simp[Abbr `reg`, int_ge] >>
  impl_tac >- WORD_DECIDE_TAC >> strip_tac >> simp[] >> gvs[write'X_def, returnS]
QED

Theorem l3_models_asl_MoveWideOp_K:
  ∀hw r.
    l3_models_asl_instr (Data (MoveWide@64 (1w, MoveWideOp_K, hw, i, r)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >>
  gvs[encode_rws] >>
  l3_decode_tac >> rw[] >> l3_run_tac >>
  asl_cexecute_tac >> gvs[] >> pop_assum kall_tac >>
  gvs[decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  gvs[undefined_MoveWideOp_def] >>
  gvs[execute_aarch64_instrs_integer_ins_ext_insert_movewide_def] >>
  reverse IF_CASES_TAC >> gvs[] >- (Cases_on_word_value `hw` >> gvs[]) >>
  IF_CASES_TAC >> gvs[] >- (irule FALSITY >> ARITH_TAC) >>
  qmatch_goalsub_abbrev_tac `bindS x f asl1` >>
  `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
  qpat_x_assum `state_rel _ asl` kall_tac >>
  drule X_read >> disch_then $ qspec_then `&w2n r` mp_tac >> impl_tac
  >- (simp[int_ge] >> WORD_DECIDE_TAC) >> strip_tac >>
  qspec_then `f` drule returnS_bindS  >> simp[Abbr `f`] >> strip_tac >>
  Cases_on `r = 31w` >> gvs[]
  >- (DEP_REWRITE_TAC[X_set_31] >> simp[returnS]) >>
  simp[INT_ADD_CALCULATE, X_def] >>
  qmatch_goalsub_abbrev_tac `X_set _ reg v _` >>
  dxrule $ b64 alpha X_set_not_31 >>
  disch_then $ qspecl_then [`64`,`reg`,`v`] mp_tac >> simp[Abbr `reg`, int_ge] >>
  impl_tac >- WORD_DECIDE_TAC >> strip_tac >> simp[] >> gvs[write'X_def, returnS]
QED

Theorem l3_asl_AddWithCarry:
  ∀x y carry_b carry_v.
    flag_rel carry_b carry_v
  ⇒ armv86a$AddWithCarry x y carry_v =
     (I ## (λ(a,b,c,d).v2w [a;b;c;d])) (arm8$AddWithCarry (x, y, carry_b))
Proof
  rw[flag_rel_def] >> gvs[armv86aTheory.AddWithCarry_def, AddWithCarry_def] >>
  simp[integer_subrange_def, asl_word_rws] >> conj_asm1_tac >>
  simp[lemTheory.w2ui_def, INT_ADD] >>
  simp[w2n_v2w, v2n, bitTheory.MOD_2EXP_def] >>
  qmatch_goalsub_abbrev_tac `b MOD 2` >>
  `b MOD 2 = b` by (unabbrev_all_tac >> rw[]) >> simp[]
  >- (
    map_every qmatch_goalsub_abbrev_tac [`n2w n`, `TAKE l`] >>
    qspec_then `fixwidth l (n2v n)` mp_tac TAKE_LENGTH_ID >>
    rewrite_tac[length_fixwidth] >> disch_then SUBST_ALL_TAC >>
    unabbrev_all_tac >> simp[v2w_fixwidth]
    ) >>
  simp[] >> qmatch_goalsub_abbrev_tac `n2w stuff` >>
  DEP_REWRITE_TAC[HD_MAP] >> conj_asm1_tac
  >- (
    qsuff_tac `LENGTH (w2v (n2w stuff)) ≠ 0` >- rw[] >>
    rewrite_tac[length_w2v] >> assume_tac EXISTS_HB >> gvs[]
    ) >>
  simp[sail2_valuesTheory.just_list_def] >>
  unabbrev_all_tac >> blastLib.BBLAST_TAC >> rw[] >> gvs[] >>
  qmatch_goalsub_abbrev_tac `w2v stuff` >>
  qspecl_then [`stuff`,`0`] mp_tac el_w2v >> simp[]
QED

(* TODO this proof has two very similar halves - perhaps these could be combined *)
Theorem l3_models_asl_AddSubImmediate:
  ∀b1 b2 i r2 r1.
    (i && ¬0b111111111111w ≠ 0b0w ⇒ i && ¬0b111111111111000000000000w = 0b0w)
  ⇒ l3_models_asl_instr
      (Data (AddSubImmediate@64 (1w, b1, b2, i, r2, r1)))
Proof
  rw[l3_models_asl_instr_def, l3_models_asl_def] >> simp[encode_rws] >>
  IF_CASES_TAC >> gvs[]
  >- (
    `i = (0w : 52 word) @@ ((11 >< 0) i : 12 word)` by
      blastLib.FULL_BBLAST_TAC >> gvs[] >>
    last_x_assum kall_tac >> rename1 `_ @@ _ @@ _ @@ _ @@ j @@ _ @@ _` >>
    qmatch_goalsub_abbrev_tac `Decode instr` >>
    `Decode instr =  Data (AddSubImmediate@64 (0b1w,b1,b2,w2w j,r2,r1))` by (
      unabbrev_all_tac >> Cases_on `b1` >> Cases_on `b2` >> l3_decode_tac) >>
    unabbrev_all_tac >> gvs[] >> rw[] >>
    qmatch_asmsub_abbrev_tac `Run (Data (addsubimm instr))` >>
    `Run (Data (addsubimm instr)) = dfn'AddSubImmediate instr` by (
      unabbrev_all_tac >> Cases_on `b1` >> Cases_on `b2` >>
      l3_run_tac >> rw[FUN_EQ_THM]) >>
    unabbrev_all_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac `seqS (wr i) ex` >>
    `∃i'. (do wr i; ex od asl) = (do wr i';
      execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
        (&w2n r1) 64 (w2w j : 64 word) (&w2n r2) b2 b1 od asl)` by (
      unabbrev_all_tac >>
      Cases_on `b1` >> Cases_on `b2` >> gvs[] >>
      asl_cexecute_tac >> simp[] >>
      gvs[
        decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
        decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
        decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
        decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def
        ] >>
      simp[asl_reg_rws, seqS, returnS]
      >- (qexists_tac `13` >> simp[])
      >- (qexists_tac `14` >> simp[])
      >- (qexists_tac `11` >> simp[])
      >- (qexists_tac `12` >> simp[])) >>
    simp[] >> pop_assum kall_tac >> unabbrev_all_tac >>
    simp[asl_reg_rws, seqS, Once returnS] >>
    qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
    `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
    qpat_x_assum `state_rel l3 asl` kall_tac >>
    simp[execute_aarch64_instrs_integer_arithmetic_add_sub_immediate_def] >>
    simp[dfn'AddSubImmediate_def] >>
    `(w2n r1 = 31 ⇔ r1 = 0b11111w) ∧ (w2n r2 = 31 ⇔ r2 = 0b11111w)` by WORD_DECIDE_TAC >>
    simp[] >>
    qpat_abbrev_tac `branch_asl = if b1 then _ else _` >>
    qpat_abbrev_tac `branch_l3 = if b1 then _ else _` >>
    `branch_asl = (λ(a,b). (v2w [b], a)) branch_l3` by (
      unabbrev_all_tac >> IF_CASES_TAC >> gvs[]) >>
    simp[] >>
    PairCases_on `branch_l3` >> gvs[] >>
    qpat_abbrev_tac `read_asl = if r2 = _ then _ else _` >>
    qpat_abbrev_tac `read_l3 = if r2 = _ then _ else _` >>
    `read_asl asl1 = returnS read_l3 asl1` by (
      unabbrev_all_tac >> IF_CASES_TAC >> gvs[]
      >- (irule SP_read >> simp[])
      >- (DEP_REWRITE_TAC[X_read] >> simp[int_ge] >> WORD_DECIDE_TAC)) >>
    simp[] >>
    qmatch_goalsub_abbrev_tac `bindS _ rest` >>
    drule $ INST_TYPE [gamma |-> ``:unit``] returnS_bindS >>
    simp[] >> strip_tac >> simp[Abbr `rest`] >>
    qspecl_then [`read_l3`,`branch_l30`,`branch_l31`] mp_tac l3_asl_AddWithCarry >>
    simp[flag_rel_def] >> strip_tac >>
    qmatch_goalsub_abbrev_tac `(_ ## _) add_res` >>
    PairCases_on `add_res` >> gvs[] >>
    reverse IF_CASES_TAC >> gvs[] >> simp[COND_RATOR]
    >- (
      drule $ b64 alpha SP_set >> drule $ b64 alpha X_set_not_31 >>
      disch_then $ qspecl_then [`64`,`&w2n r1`,`add_res0`] assume_tac >>
      disch_then $ qspec_then `add_res0` assume_tac >> gvs[int_ge] >>
      IF_CASES_TAC >> gvs[returnS] >>
      qpat_x_assum `w2n _ < _ ⇒ _` mp_tac >> impl_tac >- WORD_DECIDE_TAC >>
      strip_tac >> simp[]
      )
    >- (
      dxrule l3_asl_SetTheFlags >>
      disch_then $ qspecl_then
        [`v2w [add_res1]`,`v2w [add_res2]`,
         `v2w [add_res3]`,`v2w [add_res4]`] mp_tac >>
      strip_tac >> simp[seqS, returnS] >>
      drule $ b64 alpha X_set_not_31 >>
      disch_then $ qspecl_then [`64`,`&w2n r1`,`add_res0`] mp_tac >> simp[int_ge] >>
      Cases_on `r1 = 31w` >> gvs[]
      >- (gvs[X_set_31, returnS, write'X_def, w2v_v2w]) >>
      impl_tac >- WORD_DECIDE_TAC >>
      strip_tac >> simp[returnS] >> gvs[w2v_v2w]
      )
    )
  >- (
    `i = (0w : 40 word) @@ ((23 >< 12) i : 12 word) @@ (0w : 12 word)` by
      blastLib.FULL_BBLAST_TAC >> gvs[] >>
    qpat_x_assum `_ && i = _` kall_tac >>
    rename1 `_ @@ _ @@ _ @@ _ @@ j @@ _ @@ _` >>
    qmatch_goalsub_abbrev_tac `Decode instr` >>
    `Decode instr =  Data (AddSubImmediate@64 (0b1w,b1,b2,w2w j << 12,r2,r1))` by (
      unabbrev_all_tac >> Cases_on `b1` >> Cases_on `b2` >> l3_decode_tac) >>
    unabbrev_all_tac >> gvs[] >> rw[] >>
    qmatch_asmsub_abbrev_tac `Run (Data (addsubimm instr))` >>
    `Run (Data (addsubimm instr)) = dfn'AddSubImmediate instr` by (
      unabbrev_all_tac >> Cases_on `b1` >> Cases_on `b2` >>
      l3_run_tac >> rw[FUN_EQ_THM]) >>
    unabbrev_all_tac >> gvs[] >>
    qmatch_goalsub_abbrev_tac `seqS (wr i) ex` >>
    `∃i'. (do wr i; ex od asl) = (do wr i';
      execute_aarch64_instrs_integer_arithmetic_add_sub_immediate
        (&w2n r1) 64 ((w2w j << 12) : 64 word) (&w2n r2) b2 b1 od asl)` by (
      unabbrev_all_tac >> Cases_on `b1` >> Cases_on `b2` >> gvs[] >>
      asl_cexecute_tac >> simp[] >>
      gvs[
        decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
        decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
        decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def,
        decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate_def
        ] >>
      simp[asl_reg_rws, seqS, returnS]
      >- (
        qexists_tac `13` >> simp[] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
        EVAL_TAC >> simp[]
        )
      >- (
        qexists_tac `14` >> simp[] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
        EVAL_TAC >> simp[]
        )
      >- (
        qexists_tac `11` >> simp[] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
        EVAL_TAC >> simp[]
        )
      >- (
        qexists_tac `12` >> simp[] >> rpt (AP_TERM_TAC ORELSE AP_THM_TAC) >>
        EVAL_TAC >> simp[]
        )) >>
    simp[] >> pop_assum kall_tac >> unabbrev_all_tac >>
    simp[asl_reg_rws, seqS, Once returnS] >>
    qmatch_goalsub_abbrev_tac `asl1 : regstate sequential_state` >>
    `state_rel l3 asl1` by (unabbrev_all_tac >> state_rel_tac[]) >>
    qpat_x_assum `state_rel l3 asl` kall_tac >>
    simp[execute_aarch64_instrs_integer_arithmetic_add_sub_immediate_def] >>
    simp[dfn'AddSubImmediate_def] >>
    `(w2n r1 = 31 ⇔ r1 = 0b11111w) ∧ (w2n r2 = 31 ⇔ r2 = 0b11111w)` by WORD_DECIDE_TAC >>
    simp[] >>
    qpat_abbrev_tac `branch_asl = if b1 then _ else _` >>
    qpat_abbrev_tac `branch_l3 = if b1 then _ else _` >>
    `branch_asl = (λ(a,b). (v2w [b], a)) branch_l3` by (
      unabbrev_all_tac >> IF_CASES_TAC >> gvs[]) >>
    simp[] >>
    PairCases_on `branch_l3` >> gvs[] >>
    qpat_abbrev_tac `read_asl = if r2 = _ then _ else _` >>
    qpat_abbrev_tac `read_l3 = if r2 = _ then _ else _` >>
    `read_asl asl1 = returnS read_l3 asl1` by (
      unabbrev_all_tac >> IF_CASES_TAC >> gvs[]
      >- (irule SP_read >> simp[])
      >- (DEP_REWRITE_TAC[X_read] >> simp[int_ge] >> WORD_DECIDE_TAC)) >>
    simp[] >>
    qmatch_goalsub_abbrev_tac `bindS _ rest` >>
    drule $ INST_TYPE [gamma |-> ``:unit``] returnS_bindS >>
    simp[] >> strip_tac >> simp[Abbr `rest`] >>
    qspecl_then [`read_l3`,`branch_l30`,`branch_l31`] mp_tac l3_asl_AddWithCarry >>
    simp[flag_rel_def] >> strip_tac >>
    qmatch_goalsub_abbrev_tac `(_ ## _) add_res` >>
    PairCases_on `add_res` >> gvs[] >>
    reverse IF_CASES_TAC >> gvs[] >> simp[COND_RATOR]
    >- (
      drule $ b64 alpha SP_set >> drule $ b64 alpha X_set_not_31 >>
      disch_then $ qspecl_then [`64`,`&w2n r1`,`add_res0`] assume_tac >>
      disch_then $ qspec_then `add_res0` assume_tac >> gvs[int_ge] >>
      IF_CASES_TAC >> gvs[returnS] >>
      qpat_x_assum `w2n _ < _ ⇒ _` mp_tac >> impl_tac >- WORD_DECIDE_TAC >>
      strip_tac >> simp[]
      )
    >- (
      dxrule l3_asl_SetTheFlags >>
      disch_then $ qspecl_then
        [`v2w [add_res1]`,`v2w [add_res2]`,
         `v2w [add_res3]`,`v2w [add_res4]`] mp_tac >>
      strip_tac >> simp[seqS, returnS] >>
      drule $ b64 alpha X_set_not_31 >>
      disch_then $ qspecl_then [`64`,`&w2n r1`,`add_res0`] mp_tac >> simp[int_ge] >>
      Cases_on `r1 = 31w` >> gvs[]
      >- (gvs[X_set_31, returnS, write'X_def, w2v_v2w]) >>
      impl_tac >- WORD_DECIDE_TAC >>
      strip_tac >> simp[returnS] >> gvs[w2v_v2w]
      )
    )
QED

(****************************************)

val _ = export_theory();
