theory SMT_Types
  imports QFUF.QFUF_Funs
begin

section \<open>The data types of general problems\<close>

text \<open>
  The types of general problems, models and answers (\<^verbatim>\<open>SmtProblem\<close>, \<^verbatim>\<open>SmtModel\<close>,
  \<^verbatim>\<open>SmtAnswer\<close> and the types they are built from) are generated from \<^verbatim>\<open>core/src/lib.rs\<close>
  into \<^verbatim>\<open>urust/\<close>. The specification depends on their exact shape, so this theory states
  it: every constructor with the types of its arguments, and every record field with its type. The
  lemmas are proved from the generated types, so a change to one of these types in the Rust code
  makes this theory fail to build. Every name is written with \<open>CONST\<close>, so a constructor or field
  that no longer exists is an error, not a new variable.

  This theory is the same in both solvers (QF\_UF and QF\_BV); only the session it imports differs.
\<close>

text \<open>\<^typ>\<open>SmtSort\<close> has exactly these constructors.\<close>
lemma SmtSort_shape:
  fixes x :: SmtSort
  obtains \<open>x = CONST SmtSort_Bool\<close>
  | a0 where \<open>x = CONST SmtSort_BitVec (a0 :: 64 word)\<close>
  | a0 where \<open>x = CONST SmtSort_Uninterpreted (a0 :: 64 word)\<close>
  by (cases x) auto

text \<open>\<^typ>\<open>SmtOp\<close> has exactly these constructors.\<close>
lemma SmtOp_shape:
  fixes x :: SmtOp
  obtains \<open>x = CONST SmtOp_Not\<close>
  | \<open>x = CONST SmtOp_And\<close>
  | \<open>x = CONST SmtOp_Or\<close>
  | \<open>x = CONST SmtOp_Xor\<close>
  | \<open>x = CONST SmtOp_Implies\<close>
  | \<open>x = CONST SmtOp_Eq\<close>
  | \<open>x = CONST SmtOp_Distinct\<close>
  | \<open>x = CONST SmtOp_Ite\<close>
  | \<open>x = CONST SmtOp_Concat\<close>
  | a0 a1 where \<open>x = CONST SmtOp_Extract (a0 :: 64 word) (a1 :: 64 word)\<close>
  | \<open>x = CONST SmtOp_Bvnot\<close>
  | \<open>x = CONST SmtOp_Bvand\<close>
  | \<open>x = CONST SmtOp_Bvor\<close>
  | \<open>x = CONST SmtOp_Bvneg\<close>
  | \<open>x = CONST SmtOp_Bvadd\<close>
  | \<open>x = CONST SmtOp_Bvmul\<close>
  | \<open>x = CONST SmtOp_Bvudiv\<close>
  | \<open>x = CONST SmtOp_Bvurem\<close>
  | \<open>x = CONST SmtOp_Bvshl\<close>
  | \<open>x = CONST SmtOp_Bvlshr\<close>
  | \<open>x = CONST SmtOp_Bvult\<close>
  | \<open>x = CONST SmtOp_Bvnand\<close>
  | \<open>x = CONST SmtOp_Bvnor\<close>
  | \<open>x = CONST SmtOp_Bvxor\<close>
  | \<open>x = CONST SmtOp_Bvxnor\<close>
  | \<open>x = CONST SmtOp_Bvcomp\<close>
  | \<open>x = CONST SmtOp_Bvsub\<close>
  | \<open>x = CONST SmtOp_Bvsdiv\<close>
  | \<open>x = CONST SmtOp_Bvsrem\<close>
  | \<open>x = CONST SmtOp_Bvsmod\<close>
  | \<open>x = CONST SmtOp_Bvashr\<close>
  | a0 where \<open>x = CONST SmtOp_Repeat (a0 :: 64 word)\<close>
  | a0 where \<open>x = CONST SmtOp_ZeroExtend (a0 :: 64 word)\<close>
  | a0 where \<open>x = CONST SmtOp_SignExtend (a0 :: 64 word)\<close>
  | a0 where \<open>x = CONST SmtOp_RotateLeft (a0 :: 64 word)\<close>
  | a0 where \<open>x = CONST SmtOp_RotateRight (a0 :: 64 word)\<close>
  | \<open>x = CONST SmtOp_Bvule\<close>
  | \<open>x = CONST SmtOp_Bvugt\<close>
  | \<open>x = CONST SmtOp_Bvuge\<close>
  | \<open>x = CONST SmtOp_Bvslt\<close>
  | \<open>x = CONST SmtOp_Bvsle\<close>
  | \<open>x = CONST SmtOp_Bvsgt\<close>
  | \<open>x = CONST SmtOp_Bvsge\<close>
  by (cases x) auto

text \<open>\<^typ>\<open>SmtTerm\<close> has exactly these constructors.\<close>
lemma SmtTerm_shape:
  fixes x :: SmtTerm
  obtains a0 where \<open>x = CONST SmtTerm_BoolConst (a0 :: bool)\<close>
  | a0 where \<open>x = CONST SmtTerm_BvConst (a0 :: bool rvec)\<close>
  | a0 where \<open>x = CONST SmtTerm_Param (a0 :: 64 word)\<close>
  | a0 a1 where \<open>x = CONST SmtTerm_Fun (a0 :: 64 word) (a1 :: SmtTerm rvec)\<close>
  | a0 a1 where \<open>x = CONST SmtTerm_Def (a0 :: 64 word) (a1 :: SmtTerm rvec)\<close>
  | a0 a1 where \<open>x = CONST SmtTerm_App (a0 :: SmtOp) (a1 :: SmtTerm rvec)\<close>
  by (cases x) auto

text \<open>\<^typ>\<open>SmtFun\<close> is a record with exactly these fields.\<close>
lemma SmtFun_shape:
  fixes x y :: SmtFun
  shows \<open>x = y \<longleftrightarrow>
     (CONST SmtFun_args x :: SmtSort rvec) = SmtFun_args y \<and>
     (CONST SmtFun_ret x :: SmtSort) = SmtFun_ret y\<close>
  by (cases x; cases y) simp

text \<open>\<^typ>\<open>SmtDef\<close> is a record with exactly these fields.\<close>
lemma SmtDef_shape:
  fixes x y :: SmtDef
  shows \<open>x = y \<longleftrightarrow>
     (CONST SmtDef_params x :: SmtSort rvec) = SmtDef_params y \<and>
     (CONST SmtDef_ret x :: SmtSort) = SmtDef_ret y \<and>
     (CONST SmtDef_body x :: SmtTerm) = SmtDef_body y\<close>
  by (cases x; cases y) simp

text \<open>\<^typ>\<open>SmtProblem\<close> is a record with exactly these fields.\<close>
lemma SmtProblem_shape:
  fixes x y :: SmtProblem
  shows \<open>x = y \<longleftrightarrow>
     (CONST SmtProblem_num_sorts x :: 64 word) = SmtProblem_num_sorts y \<and>
     (CONST SmtProblem_funs x :: SmtFun rvec) = SmtProblem_funs y \<and>
     (CONST SmtProblem_defs x :: SmtDef rvec) = SmtProblem_defs y \<and>
     (CONST SmtProblem_asserts x :: SmtTerm rvec) = SmtProblem_asserts y\<close>
  by (cases x; cases y) simp

text \<open>\<^typ>\<open>SmtValue\<close> has exactly these constructors.\<close>
lemma SmtValue_shape:
  fixes x :: SmtValue
  obtains a0 where \<open>x = CONST SmtValue_Bool (a0 :: bool)\<close>
  | a0 where \<open>x = CONST SmtValue_Bv (a0 :: bool rvec)\<close>
  | a0 where \<open>x = CONST SmtValue_Elem (a0 :: 64 word)\<close>
  by (cases x) auto

text \<open>\<^typ>\<open>SmtEntry\<close> is a record with exactly these fields.\<close>
lemma SmtEntry_shape:
  fixes x y :: SmtEntry
  shows \<open>x = y \<longleftrightarrow>
     (CONST SmtEntry_args x :: SmtValue rvec) = SmtEntry_args y \<and>
     (CONST SmtEntry_val x :: SmtValue) = SmtEntry_val y\<close>
  by (cases x; cases y) simp

text \<open>\<^typ>\<open>SmtInterp\<close> is a record with exactly these fields.\<close>
lemma SmtInterp_shape:
  fixes x y :: SmtInterp
  shows \<open>x = y \<longleftrightarrow>
     (CONST SmtInterp_entries x :: SmtEntry rvec) = SmtInterp_entries y \<and>
     (CONST SmtInterp_default x :: SmtValue) = SmtInterp_default y\<close>
  by (cases x; cases y) simp

text \<open>\<^typ>\<open>SmtModel\<close> is a record with exactly these fields.\<close>
lemma SmtModel_shape:
  fixes x y :: SmtModel
  shows \<open>x = y \<longleftrightarrow>
     (CONST SmtModel_domains x :: (64 word) rvec) = SmtModel_domains y \<and>
     (CONST SmtModel_funs x :: SmtInterp rvec) = SmtModel_funs y\<close>
  by (cases x; cases y) simp

text \<open>\<^typ>\<open>SmtAnswer\<close> has exactly these constructors.\<close>
lemma SmtAnswer_shape:
  fixes x :: SmtAnswer
  obtains a0 where \<open>x = CONST SmtAnswer_Sat (a0 :: SmtModel)\<close>
  | \<open>x = CONST SmtAnswer_Unsat\<close>
  | \<open>x = CONST SmtAnswer_Unknown\<close>
  by (cases x) auto

end
