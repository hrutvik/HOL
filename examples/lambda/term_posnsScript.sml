open HolKernel Parse boolLib bossLib ncTheory ncLib chap2Theory

open BasicProvers pred_setTheory

val _ = new_theory "term_posns";

val _ = Hol_datatype `redpos = Lt | Rt | In`;

val _ = type_abbrev ("posn", ``:redpos list``)

val DNF_ss = rewrites [GSYM LEFT_FORALL_IMP_THM, GSYM RIGHT_FORALL_IMP_THM,
                       RIGHT_AND_OVER_OR, LEFT_AND_OVER_OR,
                       IMP_CONJ_THM, DISJ_IMP_THM, FORALL_AND_THM,
                       GSYM LEFT_EXISTS_AND_THM, GSYM RIGHT_EXISTS_AND_THM,
                       EXISTS_OR_THM]

val APPEND_CASES = store_thm(
  "APPEND_CASES",
  ``!l1 l2 m1 m2.
        (APPEND l1 l2 = APPEND m1 m2) =
        (l1 = m1) /\ (l2 = m2) \/
        (?n. (m1 = APPEND l1 n) /\ (l2 = APPEND n m2) /\ ~(n = [])) \/
        (?n. (l1 = APPEND m1 n) /\ (m2 = APPEND n l2) /\ ~(n = []))``,
  Induct THENL [
    SRW_TAC [][EQ_IMP_THM] THEN SRW_TAC [][] THEN
    PROVE_TAC [listTheory.APPEND],
    SRW_TAC [][] THEN Cases_on `m1` THENL [
      SRW_TAC [][] THEN PROVE_TAC [],
      SRW_TAC [][EQ_IMP_THM] THEN PROVE_TAC [listTheory.APPEND_ASSOC]
    ]
  ]);

val posn_lt_def = Define`
  (posn_lt _ [] = F) /\
  (posn_lt [] _ = T) /\
  (posn_lt (In::ps1) (In::ps2) = posn_lt ps1 ps2) /\
  (posn_lt (In::_) _ = F) /\
  (posn_lt (Lt::ps1) (Lt::ps2) = posn_lt ps1 ps2) /\
  (posn_lt (Lt::_) (In::_) = F) /\
  (posn_lt (Lt::_) (Rt::_) = T) /\
  (posn_lt (Rt::ps1) (Rt::ps2) = posn_lt ps1 ps2) /\
  (posn_lt (Rt::_) _ = F)
`;
val _ = export_rewrites ["posn_lt_def"]


val _ = overload_on ("<", ``posn_lt``);

val posn_lt_inj = store_thm(
  "posn_lt_inj",
  ``!h p1 p2. (h::p1) < (h::p2) = p1 < p2``,
  Cases THEN SRW_TAC [][]);
val _ = BasicProvers.export_rewrites ["posn_lt_inj"]

val posn_lt_nil = store_thm(
  "posn_lt_nil",
  ``!p : posn. ~(p < [])``,
  Cases THEN SRW_TAC [][] THEN Cases_on `h` THEN SRW_TAC [][]);
val _ = BasicProvers.export_rewrites ["posn_lt_nil"]

val posn_lt_trans = store_thm(
  "posn_lt_trans",
  ``!p1 p2 p3 : posn. p1 < p2 /\ p2 < p3 ==> p1 < p3``,
  Induct THENL [
    NTAC 2 (Cases THEN SIMP_TAC (srw_ss()) [posn_lt_def]),
    Cases THEN Induct THEN
    SIMP_TAC (srw_ss()) [posn_lt_def] THEN
    Cases THEN SIMP_TAC (srw_ss()) [posn_lt_def] THEN
    Induct THEN TRY Cases THEN ASM_SIMP_TAC (srw_ss()) [posn_lt_def] THEN
    PROVE_TAC []
  ]);

val posn_lt_irrefl = store_thm(
  "posn_lt_irrefl",
  ``!p : posn. ~(p < p)``,
  Induct THEN SRW_TAC [][]);
val _ = export_rewrites ["posn_lt_irrefl"]

val posn_lt_antisym = store_thm(
  "posn_lt_antisym",
  ``!p1 p2. p1 < p2 ==> ~(p2 < p1)``,
  HO_MATCH_MP_TAC (theorem "posn_lt_ind") THEN
  SRW_TAC [][]);

val posn_lt_Lt = store_thm(
  "posn_lt_Lt",
  ``!h p1 p2. ((h::p1) < (Lt::p2) = (h = Lt) /\ p1 < p2) /\
              ((Lt::p1) < (h::p2) = (h = Rt) \/ (h = Lt) /\ p1 < p2)``,
  Cases THEN SRW_TAC [][]);
val _ = export_rewrites ["posn_lt_Lt"]

val posn_lt_In = store_thm(
  "posn_lt_In",
  ``!h p1 p2. ((h::p1) < (In::p2) = (h = In) /\ p1 < p2) /\
              ((In::p1) < (h::p2) = (h = In) /\ p1 < p2)``,
  Cases THEN SRW_TAC [][]);
val _ = export_rewrites ["posn_lt_In"]

val posn_lt_Rt = store_thm(
  "posn_lt_Rt",
  ``!h p1 p2. ((h::p1) < (Rt::p2) = (h = Lt) \/ (h = Rt) /\ p1 < p2) /\
              ((Rt::p1) < (h::p2) = (h = Rt) /\ p1 < p2)``,
  Cases THEN SRW_TAC [][]);
val _ = export_rewrites ["posn_lt_Rt"]


val (valid_posns_thm, _) = define_recursive_term_function`
  (valid_posns (VAR s) = {[]}) /\
  (valid_posns (CON k) = {[]}) /\
  (valid_posns (t @@ u) = [] INSERT IMAGE (CONS Lt) (valid_posns t) UNION
                                    IMAGE (CONS Rt) (valid_posns u)) /\
  (valid_posns (LAM v t) = [] INSERT IMAGE (CONS In) (valid_posns t))
`;

val NIL_always_valid = store_thm(
  "NIL_always_valid",
  ``!t. [] IN valid_posns t``,
  GEN_TAC THEN Q.SPEC_THEN `t` STRUCT_CASES_TAC nc_CASES THEN
  SRW_TAC [][valid_posns_thm]);
val _ = export_rewrites ["NIL_always_valid"]

val valid_posns_FINITE = store_thm(
  "valid_posns_FINITE",
  ``!t : 'a nc. FINITE (valid_posns t)``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN SIMP_TAC (srw_ss()) [valid_posns_thm]);
val _ = export_rewrites ["valid_posns_FINITE"]

val all_valid_posns_comparable = store_thm(
  "all_valid_posns_comparable",
  ``!t p1 p2. p1 IN valid_posns t /\ p2 IN valid_posns t ==>
              p1 < p2 \/ (p1 = p2) \/ p2 < p1``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN SRW_TAC [][valid_posns_thm]);

val (var_posns_thm, _) = define_recursive_term_function`
   (var_posns (CON k : 'a nc) = {}) /\
   (var_posns (VAR s) = {[]}) /\
   (var_posns (t @@ u) = IMAGE (CONS Lt) (var_posns t) UNION
                         IMAGE (CONS Rt) (var_posns u)) /\
   (var_posns (LAM v t) = IMAGE (CONS In) (var_posns t))`;

val var_posns_FINITE = store_thm(
  "var_posns_FINITE",
  ``!t : 'a nc. FINITE (var_posns t)``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN SIMP_TAC (srw_ss()) [var_posns_thm]);

val _ = export_rewrites ["var_posns_FINITE"]

val var_posns_SUBSET_valid_posns = store_thm(
  "var_posns_SUBSET_valid_posns",
  ``!t p. p IN var_posns t ==> p IN valid_posns t``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [][valid_posns_thm, var_posns_thm]);

val vp_var = ``\s : string. if v = s then {[] : redpos list} else {}``
val vp_con = ``\k : 'a. {} : redpos list set``
val vp_app = ``\ (t:'a nc) (u:'a nc) rt ru.
                    IMAGE (CONS Lt) rt UNION IMAGE (CONS Rt) ru``
val vp_lam = ``\ (t : string -> 'a nc) rt.
                    let w = NEW (v INSERT FV (ABS t))
                    in
                      IMAGE (CONS In) (rt w)``

val v_posns_def = new_specification(
  "v_posns_def", ["v_posns"],
  (SIMP_RULE bool_ss [SKOLEM_THM, FORALL_AND_THM] o GEN_ALL o
   SIMP_RULE bool_ss [ABS_DEF] o
   ISPECL [vp_con, vp_var, vp_app, vp_lam]) nc_RECURSION_WEAK);

val v_posns_FV = store_thm(
  "v_posns_FV",
  ``!t v. ~(v IN FV t) ==> (v_posns v t = {})``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [][v_posns_def, IMAGE_EQ_EMPTY] THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN NEW_ELIM_TAC THEN
  SRW_TAC [][FV_SUB]);

val v_posns_vsubst = store_thm(
  "v_posns_vsubst",
  ``!M x y z.
        v_posns x ([VAR y/z] M) =
           if x = y then v_posns x M UNION v_posns z M
           else if x = z then {}
           else v_posns x M``,
  GEN_TAC THEN completeInduct_on `size M` THEN
  FULL_SIMP_TAC (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN
  Q.SPEC_THEN `M` STRUCT_CASES_TAC nc_CASES THENL [
    SIMP_TAC (srw_ss()) [v_posns_def, SUB_THM],

    REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN
    ASM_SIMP_TAC (srw_ss())[v_posns_def, SUB_THM, SUB_VAR] THEN
    REPEAT COND_CASES_TAC THEN SRW_TAC [][v_posns_def],

    SRW_TAC [numSimps.ARITH_ss, pred_setSimps.PRED_SET_AC_ss]
            [v_posns_def, SUB_THM, size_thm],

    SRW_TAC [][size_thm] THEN
    Q_TAC (NEW_TAC "p") `{x; y; z; x'} UNION FV u` THEN
    `LAM x u = LAM p ([VAR p/x] u)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    SRW_TAC [][SUB_THM, v_posns_def] THEN
    REPEAT NEW_ELIM_TAC THEN SRW_TAC [numSimps.ARITH_ss][]
  ]);

val v_posns_thm = store_thm(
  "v_posns_thm",
  ``(!v k. v_posns v (CON k : 'a nc) = {}) /\
    (!v s. v_posns v (VAR s : 'a nc) = if s = v then {[]} else {}) /\
    (!v M N. v_posns v (M @@ N : 'a nc) =
               IMAGE (CONS Lt) (v_posns v M) UNION
               IMAGE (CONS Rt) (v_posns v N)) /\
    (!v M. v_posns v (LAM v M : 'a nc) = {}) /\
    (!v w M. ~(v = w) ==> (v_posns v (LAM w M : 'a nc) =
                           IMAGE (CONS In) (v_posns v M)))``,
  SRW_TAC [][v_posns_def, IMAGE_EQ_EMPTY] THEN
  NEW_ELIM_TAC THEN SRW_TAC [][lemma14a, v_posns_vsubst]);

val v_posns_FV_EQ = store_thm(
  "v_posns_FV_EQ",
  ``!t v. (v_posns v t = {}) = ~(v IN FV t)``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM, v_posns_FV] THEN
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [][v_posns_thm, pred_setTheory.IMAGE_EQ_EMPTY] THEN
  Q_TAC (NEW_TAC "z") `{v;x} UNION FV t` THEN
  `LAM x t = LAM z ([VAR z/x] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
  FULL_SIMP_TAC (srw_ss()) [v_posns_thm, pred_setTheory.IMAGE_EQ_EMPTY] THEN
  FIRST_X_ASSUM (IMP_RES_THEN MP_TAC) THEN
  SRW_TAC [][FV_SUB]);

val v_posns_LAM_COND = store_thm(
  "v_posns_LAM_COND",
  ``!v w t. v_posns v (LAM w t) = if v = w then {}
                                  else IMAGE (CONS In) (v_posns v t)``,
  SRW_TAC [][v_posns_thm]);

val v_posns_SUBSET_var_posns = store_thm(
  "v_posns_SUBSET_var_posns",
  ``!t v p. p IN v_posns v t ==> p IN var_posns t``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [][v_posns_thm, var_posns_thm] THENL [
    PROVE_TAC [],
    PROVE_TAC [],
    Cases_on `v = x` THEN FULL_SIMP_TAC (srw_ss()) [v_posns_thm] THEN
    PROVE_TAC [lemma14a]
  ]);

val var_posns_subst = store_thm(
  "var_posns_subst",
  ``!x v t. var_posns ([t/v] x) =
               (var_posns x DIFF v_posns v x) UNION
               {APPEND p1 p2 | p1 IN v_posns v x /\ p2 IN var_posns t}``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [][var_posns_thm, v_posns_thm, SUB_THM,
               EXTENSION],
    SIMP_TAC (srw_ss() ++ boolSimps.COND_elim_ss ++ DNF_ss)
             [var_posns_thm, v_posns_thm, SUB_THM, SUB_VAR,
              EXTENSION, EQ_IMP_THM],
    SRW_TAC [][var_posns_thm, v_posns_thm, SUB_THM] THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [EXTENSION, EQ_IMP_THM] THEN
    REPEAT CONJ_TAC THEN PROVE_TAC [],
    REPEAT STRIP_TAC THEN
    Q_TAC (NEW_TAC "z") `FV x' UNION FV t UNION {x;v}` THEN
    `LAM x x' = LAM z ([VAR z/x] x')` by SRW_TAC [][SIMPLE_ALPHA] THEN
    ASM_SIMP_TAC (srw_ss())
                 [SUB_THM, var_posns_thm, v_posns_thm,
                  v_posns_LAM_COND, v_posns_vsubst, v_posns_FV] THEN
    ASM_SIMP_TAC (srw_ss() ++ DNF_ss ++ boolSimps.COND_elim_ss)
                 [EXTENSION, EQ_IMP_THM] THEN
    REPEAT CONJ_TAC THEN PROVE_TAC []
  ]);




val (bv_posns_def, _) = define_recursive_term_function
  `bv_posns (LAM v t : 'a nc) = IMAGE (CONS In) (v_posns v t)`;

val bv_posns_thm = store_thm(
  "bv_posns_thm",
  ``!v t. bv_posns (LAM v t) = IMAGE (CONS In) (v_posns v t)``,
  SRW_TAC [][bv_posns_def] THEN NEW_ELIM_TAC THEN
  ASM_SIMP_TAC (srw_ss()) [v_posns_vsubst, DISJ_IMP_THM, FORALL_AND_THM,
                           v_posns_FV]);

val (lam_posns_thm, _) = define_recursive_term_function`
  (lam_posns (VAR s : 'a nc) = {}) /\
  (lam_posns (CON k) = {}) /\
  (lam_posns (t @@ u) = IMAGE (CONS Lt) (lam_posns t) UNION
                        IMAGE (CONS Rt) (lam_posns u)) /\
  (lam_posns (LAM v t) = [] INSERT IMAGE (CONS In) (lam_posns t))
`;

val lam_posns_SUBSET_valid_posns = store_thm(
  "lam_posns_SUBSET_valid_posns",
  ``!t p. p IN lam_posns t ==> p IN valid_posns t``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [][valid_posns_thm, lam_posns_thm]);

val lam_posns_var_posns = store_thm(
  "lam_posns_var_posns",
  ``!t p. ~(p IN lam_posns t /\ p IN var_posns t)``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [][var_posns_thm, lam_posns_thm] THEN
  SPOSE_NOT_THEN STRIP_ASSUME_TAC THEN
  FULL_SIMP_TAC (srw_ss()) [] THEN PROVE_TAC []);

val (redex_posns_thm, _) = define_recursive_term_function`
  (redex_posns (VAR s : 'a nc) = {}) /\
  (redex_posns (CON k) = {}) /\
  (redex_posns (t @@ u) =
     IMAGE (CONS Lt) (redex_posns t) UNION
     IMAGE (CONS Rt) (redex_posns u) UNION
     (if is_abs t then {[]} else {})) /\
  (redex_posns (LAM v t) = IMAGE (CONS In) (redex_posns t))
`;

val redex_posns_are_valid = store_thm(
  "redex_posns_are_valid",
  ``!t p. p IN redex_posns t ==> p IN valid_posns t``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [][valid_posns_thm, redex_posns_thm]);

val (ncbody_def, _) = define_recursive_term_function`ncbody (LAM v t) = t`;

val bv_posns_at_def = Define`
  (bv_posns_at [] t = bv_posns t) /\
  (bv_posns_at (In::p) t = IMAGE (CONS In) (bv_posns_at p (ncbody t))) /\
  (bv_posns_at (Lt::p) t = IMAGE (CONS Lt) (bv_posns_at p (rator t))) /\
  (bv_posns_at (Rt::p) t = IMAGE (CONS Rt) (bv_posns_at p (rand t)))
`;

val pqr_lemma = prove(
  ``!p q r. (p ==> q /\ r) = (p ==> q) /\ (p ==> r)``,
  SRW_TAC [][EQ_IMP_THM]);

val bv_posns_at_vsubst = store_thm(
  "bv_posns_at_vsubst",
  ``!t v u p. p IN lam_posns t ==>
              (bv_posns_at p ([VAR v/u] t) = bv_posns_at p t)``,
  GEN_TAC THEN completeInduct_on `size t` THEN
  FULL_SIMP_TAC (srw_ss()) [GSYM RIGHT_FORALL_IMP_THM] THEN
  GEN_TAC THEN Q.SPEC_THEN `t` STRUCT_CASES_TAC nc_CASES THEN
  ASM_SIMP_TAC (srw_ss() ++ ARITH_ss)
               [lam_posns_thm, DISJ_IMP_THM, GSYM LEFT_FORALL_IMP_THM,
                FORALL_AND_THM, bv_posns_at_def, SUB_THM,
                size_thm, pqr_lemma, GSYM RIGHT_FORALL_IMP_THM] THEN
  REPEAT STRIP_TAC THENL [
    Q_TAC (NEW_TAC "z") `{u'; v'; x} UNION FV u` THEN
    `LAM x u = LAM z ([VAR z/x] u)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    ASM_SIMP_TAC (srw_ss()) [SUB_THM, bv_posns_thm, v_posns_vsubst,
                             v_posns_FV],
    VAR_EQ_TAC THEN
    Q_TAC (NEW_TAC "z") `{u'; v'; x} UNION FV u` THEN
    `LAM x u = LAM z ([VAR z/x] u)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    ASM_SIMP_TAC (srw_ss() ++ ARITH_ss) [SUB_THM, ncbody_def]
  ]);

val _ = export_rewrites ["bv_posns_at_vsubst"]

val bv_posns_at_thm = store_thm(
  "bv_posns_at_thm",
  ``(!v t. bv_posns_at [] (LAM v t) = IMAGE (CONS In) (v_posns v t)) /\
    (!v t p. p IN lam_posns t ==>
                (bv_posns_at (In::p) (LAM v t) =
                 IMAGE (CONS In) (bv_posns_at p t))) /\
    (!t u p. p IN lam_posns t ==>
                (bv_posns_at (Lt::p) (t @@ u) =
                 IMAGE (CONS Lt) (bv_posns_at p t))) /\
    (!t u p. p IN lam_posns u ==>
                (bv_posns_at (Rt::p) (t @@ u) =
                 IMAGE (CONS Rt) (bv_posns_at p u)))``,
  SRW_TAC [][bv_posns_at_def, bv_posns_thm, ncbody_def, bv_posns_at_vsubst]);

val bv_posns_at_SUBSET_var_posns = store_thm(
  "bv_posns_at_SUBSET_var_posns",
  ``!t p1 p2. p1 IN lam_posns t /\ p2 IN bv_posns_at p1 t ==>
              p2 IN var_posns t``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [][lam_posns_thm, var_posns_thm, bv_posns_at_thm,
             GSYM AND_IMP_INTRO] THEN
  Q.PAT_ASSUM `X IN bv_posns_at Y Z` MP_TAC THEN
  SRW_TAC [][bv_posns_at_thm] THEN
  PROVE_TAC [v_posns_SUBSET_var_posns]);

val lam_posns_subst = store_thm(
  "lam_posns_subst",
  ``!t u v. lam_posns ([u/v] t) = lam_posns t UNION
                                  {APPEND p1 p2 | p1 IN v_posns v t /\
                                                  p2 IN lam_posns u}``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [][SUB_THM, SUB_VAR, lam_posns_thm, v_posns_thm] THENL [
    SRW_TAC [][EXTENSION],
    SRW_TAC [][EXTENSION],
    SRW_TAC [][EXTENSION],
    SIMP_TAC (srw_ss() ++ DNF_ss) [EXTENSION] THEN PROVE_TAC [],
    Q_TAC (NEW_TAC "z") `{v; x} UNION FV u UNION FV t` THEN
    `LAM x t = LAM z ([VAR z/x] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    SRW_TAC [DNF_ss][SUB_THM, lam_posns_thm, v_posns_thm, EXTENSION] THEN
    PROVE_TAC []
  ]);

val v_posns_subst = store_thm(
  "v_posns_subst",
  ``!t u v w. v_posns v ([u/w] t) =
              if v = w then { APPEND p1 p2 | p1 IN v_posns v t /\
                                             p2 IN v_posns v u}
              else v_posns v t UNION
                   { APPEND p1 p2 | p1 IN v_posns w t /\ p2 IN v_posns v u}``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [][SUB_VAR, SUB_THM, v_posns_thm, EXTENSION] THENL [
    SRW_TAC [DNF_ss][] THEN REPEAT (POP_ASSUM (K ALL_TAC)) THEN PROVE_TAC [],
    Q_TAC (NEW_TAC "z") `{v;w;x} UNION FV u UNION FV t` THEN
    `LAM x t = LAM z ([VAR z/x] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    SRW_TAC [DNF_ss][SUB_THM, v_posns_thm] THEN
    REPEAT (POP_ASSUM (K ALL_TAC)) THEN PROVE_TAC []
  ]);

val bv_posns_at_subst = store_thm(
  "bv_posns_at_subst",
  ``!t u v p. p IN lam_posns t ==>
              (bv_posns_at p ([v/u] t) = bv_posns_at p t)``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [][lam_posns_thm, SUB_THM, SUB_VAR, bv_posns_at_thm] THEN
  SRW_TAC [][lam_posns_thm, SUB_THM, SUB_VAR, bv_posns_at_thm,
             lam_posns_subst] THEN
  Q_TAC (NEW_TAC "z") `{u; x} UNION FV t UNION FV v` THEN
  `LAM x t = LAM z ([VAR z/x] t)` by SRW_TAC [][SIMPLE_ALPHA] THENL [
    SRW_TAC [][SUB_THM, bv_posns_at_thm, v_posns_subst, v_posns_FV,
               v_posns_thm, EXTENSION],
    SRW_TAC [][SUB_THM, bv_posns_at_thm, lam_posns_subst]
  ]);

val bv_posns_at_subst2 = store_thm(
  "bv_posns_at_subst2",
  ``!t u v vp m.
       vp IN v_posns v t /\ m IN lam_posns u ==>
       (bv_posns_at (APPEND vp m) ([u/v] t) =
        IMAGE (APPEND vp) (bv_posns_at m u))``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [] [v_posns_thm, SUB_THM, SUB_VAR] THENL [
    SRW_TAC [][EXTENSION],
    `APPEND x m IN lam_posns ([u/v] t)`
        by (SRW_TAC [][lam_posns_subst] THEN PROVE_TAC []) THEN
    SRW_TAC [DNF_ss][bv_posns_at_thm, EXTENSION],
    `APPEND x m IN lam_posns ([u/v] t')`
        by (SRW_TAC [][lam_posns_subst] THEN PROVE_TAC []) THEN
    SRW_TAC [DNF_ss][bv_posns_at_thm, EXTENSION],
    Q_TAC (NEW_TAC "z") `FV t UNION FV u UNION {x;v}` THEN
    `LAM x t = LAM z ([VAR z/x] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    FULL_SIMP_TAC (srw_ss()) [SUB_THM, v_posns_thm] THEN
    `APPEND x' m IN lam_posns ([u/v] ([VAR z/x] t))`
       by (SRW_TAC [][lam_posns_subst] THEN PROVE_TAC []) THEN
    SRW_TAC [DNF_ss][bv_posns_at_thm, EXTENSION]
  ]);

val bv_posns_at_prefix_posn = store_thm(
  "bv_posns_at_prefix_posn",
  ``!p t bvp. p IN lam_posns t /\ bvp IN bv_posns_at p t ==>
              ?m. bvp = APPEND p (In::m)``,
  Induct THEN
  REPEAT GEN_TAC THEN SIMP_TAC (srw_ss()) [bv_posns_at_def] THEN
  Q.SPEC_THEN `t` STRUCT_CASES_TAC nc_CASES THEN
  ASM_SIMP_TAC (srw_ss() ++ DNF_ss ++ boolSimps.CONJ_ss)
               [lam_posns_thm, bv_posns_thm, bv_posns_at_thm] THEN
  PROVE_TAC []);

val v_posns_injective = store_thm(
  "v_posns_injective",
  ``!t v1 p. p IN v_posns v1 t ==> (p IN v_posns v2 t = (v1 = v2))``,
  SIMP_TAC (srw_ss() ++ DNF_ss) [EQ_IMP_THM] THEN
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  REPEAT CONJ_TAC THENL [
    SRW_TAC [][v_posns_thm],
    SRW_TAC [][v_posns_thm],
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [v_posns_thm] THEN
    ASM_REWRITE_TAC [],
    REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN
    Q_TAC (NEW_TAC "z") `{v1; v2; x} UNION FV t` THEN
    `LAM x t = LAM z ([VAR z/x] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    ASM_REWRITE_TAC [] THEN ASM_REWRITE_TAC [v_posns_LAM_COND] THEN
    REPEAT COND_CASES_TAC THEN SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN
    PROVE_TAC []
  ]);

val v_posns_arent_bv_posns = store_thm(
  "v_posns_arent_bv_posns",
  ``!t lp p. lp IN lam_posns t /\ p IN bv_posns_at lp t ==>
             !v. ~(p IN v_posns v t)``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [] [lam_posns_thm, bv_posns_at_thm, v_posns_thm] THEN
  POP_ASSUM MP_TAC THEN SRW_TAC [][bv_posns_at_thm] THENL [
    PROVE_TAC [],
    PROVE_TAC [],
    Q_TAC (NEW_TAC "z") `{v;x} UNION FV t` THEN
    `LAM x t = LAM z ([VAR z/x] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    SRW_TAC [][v_posns_thm, v_posns_vsubst] THEN
    PROVE_TAC [v_posns_injective],
    Q_TAC (NEW_TAC "z") `{v;x} UNION FV t` THEN
    `LAM x t = LAM z ([VAR z/x] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    SRW_TAC [][v_posns_thm, v_posns_vsubst] THEN PROVE_TAC [lemma14a]
  ]);

val no_var_posns_in_var_posn_prefix = store_thm(
  "no_var_posns_in_var_posn_prefix",
  ``!t p1 l.
       p1 IN var_posns t /\ APPEND p1 l IN var_posns t ==> (l = [])``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  REWRITE_TAC[var_posns_thm, theorem "var_posns_vsubst_invariant"] THEN
  REPEAT CONJ_TAC THENL [
    SIMP_TAC (srw_ss()) [],
    SIMP_TAC (srw_ss()) [],
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN ASM_REWRITE_TAC [],
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [] THEN ASM_REWRITE_TAC []
  ]);

val APPEND_var_posns = store_thm(
  "APPEND_var_posns",
  ``!vp1 vp2 t.
        vp1 IN var_posns t /\ vp2 IN var_posns t ==>
        !x y. (APPEND vp1 x = APPEND vp2 y) = (vp1 = vp2) /\ (x = y)``,
  SRW_TAC [][APPEND_CASES, EQ_IMP_THM] THEN
  PROVE_TAC [no_var_posns_in_var_posn_prefix]);

val valid_posns_subst = store_thm(
  "valid_posns_subst",
  ``!t u v. valid_posns ([u/v] t) =
              valid_posns t UNION
              {APPEND p1 p2 | p1 IN v_posns v t /\ p2 IN valid_posns u}``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN
  SRW_TAC [][valid_posns_thm, v_posns_thm, SUB_THM] THENL [
    SRW_TAC [][EXTENSION],
    SIMP_TAC (srw_ss() ++ DNF_ss)[EXTENSION, EQ_IMP_THM],
    SRW_TAC [][EXTENSION],
    SRW_TAC [][EXTENSION] THEN REPEAT (POP_ASSUM (K ALL_TAC)) THEN
    SRW_TAC [DNF_ss][] THEN PROVE_TAC [],
    Q_TAC (NEW_TAC "z") `{v;x} UNION FV u UNION FV t` THEN
    `LAM x t = LAM z ([VAR z/x] t)` by SRW_TAC [][SIMPLE_ALPHA] THEN
    SRW_TAC [][SUB_THM, valid_posns_thm, v_posns_thm, v_posns_vsubst] THEN
    SRW_TAC [DNF_ss][EXTENSION] THEN PROVE_TAC []
  ]);

val cant_be_deeper_than_var_posns = store_thm(
  "cant_be_deeper_than_var_posns",
  ``!t p1 p. p1 IN var_posns t /\ APPEND p1 p IN valid_posns t ==>
             (p = [])``,
  HO_MATCH_MP_TAC nc_INDUCTION THEN REPEAT CONJ_TAC THENL [
    SRW_TAC [][var_posns_thm, valid_posns_thm],
    SRW_TAC [][var_posns_thm, valid_posns_thm],
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [var_posns_thm, valid_posns_thm] THEN
    ASM_REWRITE_TAC [],
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    SIMP_TAC (srw_ss() ++ DNF_ss) [var_posns_thm, valid_posns_thm] THEN
    PROVE_TAC [lemma14a]
  ]);



val NIL_IN_v_posns = store_thm(
  "NIL_IN_v_posns",
  ``!t v. [] IN v_posns v t = (t = VAR v)``,
  GEN_TAC THEN
  Q.SPEC_THEN `t` STRUCT_CASES_TAC nc_CASES THEN
  SRW_TAC [][v_posns_thm, v_posns_LAM_COND]);

val v_posns_FINITE = store_thm(
  "v_posns_FINITE",
  ``!v t. FINITE (v_posns v t)``,
  PROVE_TAC [v_posns_SUBSET_var_posns, var_posns_FINITE,
             pred_setTheory.SUBSET_FINITE, pred_setTheory.SUBSET_DEF]);

val _ = export_rewrites ["v_posns_FINITE"]

val bv_posns_vsubst = store_thm(
  "bv_posns_vsubst",
  ``!t u v. bv_posns ([VAR v/u] t) = bv_posns t``,
  REPEAT GEN_TAC THEN
  Q.SPEC_THEN `t` STRUCT_CASES_TAC nc_CASES THEN
  SRW_TAC [][SUB_THM, SUB_VAR, bv_posns_thm, bv_posns_def] THEN
  Q_TAC (NEW_TAC "z") `{v;u;x} UNION FV u'` THEN
  `LAM x u' = LAM z ([VAR z/x] u')` by SRW_TAC [][SIMPLE_ALPHA] THEN
  SRW_TAC [][SUB_THM, bv_posns_thm, v_posns_vsubst, v_posns_FV]);



val _ = export_theory()

