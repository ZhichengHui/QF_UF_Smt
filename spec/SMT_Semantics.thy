theory SMT_Semantics
  imports QFUF.QFUF_Funs
begin

text \<open>\<open>map\<close> below is \<^const>\<open>List.map\<close>, not the iterator function of AutoCorrode.\<close>
hide_const (open) Rust_Iterator.map

section \<open>The semantics of general problems\<close>

text \<open>
  This theory is the same in both solvers (QF\_UF and QF\_BV); only the session it imports differs.
  It gives the meaning of the general problem structure \<^typ>\<open>SmtProblem\<close>, the interface between
  the SMT-LIB front end and the solvers (\<^verbatim>\<open>frontend/src/problem.rs\<close>, repeated in
  \<^verbatim>\<open>core/src/lib.rs\<close>). A problem is the content of an SMT-LIB 2.6 script in the logics QF\_UF,
  QF\_BV or QF\_UFBV after name resolution and sort checking: uninterpreted sorts, declared function
  symbols, defined functions (from \<open>define-fun\<close> and \<open>let\<close>) and assertions. Nothing is rewritten:
  the theory functions keep the arity they have in the script.

  Semantics (SMT-LIB 2.6, Section 5):
  \<^item> A value is a truth value, a bit-vector of width \<open>w\<close> (its number \<open>bv2nat\<close>, below \<open>2^w\<close>), or an
    element of an uninterpreted sort. Elements are natural numbers; the sorts are told apart by the
    sort-checking, not by the values.
  \<^item> An interpretation gives every declared function symbol a function on values. It respects
    sorts (\<open>smt_interp_ok\<close>): applied to values of the argument sorts it gives a value of the result
    sort. A defined function means its body, with the parameters bound to the arguments.
  \<^item> The theory functions of Core and of FixedSizeBitVectors with the QF\_BV extensions: as in the
    SMT-LIB 2.6 theory and logic declarations (the files in \<^verbatim>\<open>spec/smtlib-2.6/\<close> of the QF\_BV
    solver). \<open>and\<close>, \<open>or\<close>, \<open>xor\<close>, \<open>bvand\<close>, \<open>bvor\<close>, \<open>bvadd\<close>, \<open>bvmul\<close> are left-associative,
    \<open>=>\<close> right-associative, \<open>=\<close> chainable and \<open>distinct\<close> pairwise.
  \<^item> A problem is satisfiable if some interpretation makes every assertion true. The elements of
    the uninterpreted sorts range over all natural numbers; a quantifier-free problem that has a
    model with some domains has one with countable domains, so this is no restriction.
  \<^item> A model returned by a solver (\<^typ>\<open>SmtModel\<close>) gives every uninterpreted sort a finite
    domain and every declared function symbol a table with a default value.
\<close>

subsection \<open>Values\<close>

datatype sval = VBool bool | VBv nat nat | VElem nat

text \<open>\<open>VBv w x\<close>: a bit-vector of width \<open>w\<close> whose number is \<open>x\<close>.\<close>

text \<open>The number a bit list denotes, least significant bit first (\<open>bv2nat\<close>).\<close>
fun smt_bits_nat :: \<open>bool list \<Rightarrow> nat\<close> where
  \<open>smt_bits_nat [] = 0\<close>
| \<open>smt_bits_nat (b # bs) = of_bool b + 2 * smt_bits_nat bs\<close>

text \<open>The two's complement reading of a value \<open>x\<close> of width \<open>w\<close> (\<open>bv2int\<close>).\<close>
definition smt_sint :: \<open>nat \<Rightarrow> nat \<Rightarrow> int\<close> where
  \<open>smt_sint w x \<equiv> if x < 2 ^ (w - 1) then int x else int x - 2 ^ w\<close>

text \<open>An integer modulo \<open>2^w\<close> (\<open>nat2bv[w]\<close>, extended to negative integers).\<close>
definition smt_to_bv :: \<open>nat \<Rightarrow> int \<Rightarrow> nat\<close> where
  \<open>smt_to_bv w z \<equiv> nat (z mod 2 ^ w)\<close>

text \<open>Integer division rounding towards zero, and its remainder.\<close>
definition smt_tdiv :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where
  \<open>smt_tdiv a b \<equiv> if (a < 0) = (b < 0) then \<bar>a\<bar> div \<bar>b\<bar> else - (\<bar>a\<bar> div \<bar>b\<bar>)\<close>

definition smt_tmod :: \<open>int \<Rightarrow> int \<Rightarrow> int\<close> where
  \<open>smt_tmod a b \<equiv> a - b * smt_tdiv a b\<close>

text \<open>The value of \<open>((_ repeat j) t)\<close> for a value \<open>x\<close> of width \<open>w\<close>.\<close>
fun smt_repeat_val :: \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>smt_repeat_val w 0 x = 0\<close>
| \<open>smt_repeat_val w (Suc j) x = x * 2 ^ (w * j) + smt_repeat_val w j x\<close>

subsection \<open>Sorts\<close>

text \<open>The width of a bit-vector sort; 0 for the other sorts.\<close>
fun smt_width :: \<open>SmtSort \<Rightarrow> nat\<close> where
  \<open>smt_width (SmtSort_BitVec w) = unat w\<close>
| \<open>smt_width _ = 0\<close>

text \<open>A sort of a problem with \<open>ns\<close> uninterpreted sorts: a bit-vector width is at least 1, an
  uninterpreted sort is one of the \<open>ns\<close>.\<close>
fun smt_wf_sort :: \<open>nat \<Rightarrow> SmtSort \<Rightarrow> bool\<close> where
  \<open>smt_wf_sort ns SmtSort_Bool = True\<close>
| \<open>smt_wf_sort ns (SmtSort_BitVec w) = (1 \<le> unat w)\<close>
| \<open>smt_wf_sort ns (SmtSort_Uninterpreted s) = (unat s < ns)\<close>

fun smt_has_sort :: \<open>SmtSort \<Rightarrow> sval \<Rightarrow> bool\<close> where
  \<open>smt_has_sort SmtSort_Bool v = (case v of VBool _ \<Rightarrow> True | _ \<Rightarrow> False)\<close>
| \<open>smt_has_sort (SmtSort_BitVec w) v = (case v of VBv m x \<Rightarrow> m = unat w \<and> x < 2 ^ m | _ \<Rightarrow> False)\<close>
| \<open>smt_has_sort (SmtSort_Uninterpreted s) v = (case v of VElem _ \<Rightarrow> True | _ \<Rightarrow> False)\<close>

text \<open>The width of two bit-vector sorts of equal width.\<close>
fun smt_bin_width :: \<open>SmtSort list \<Rightarrow> nat option\<close> where
  \<open>smt_bin_width [SmtSort_BitVec a, SmtSort_BitVec b] = (if a = b then Some (unat a) else None)\<close>
| \<open>smt_bin_width _ = None\<close>

text \<open>The width of one or more bit-vector sorts of equal width.\<close>
definition smt_same_width :: \<open>SmtSort list \<Rightarrow> nat option\<close> where
  \<open>smt_same_width ss \<equiv>
     (case ss of SmtSort_BitVec w # _ \<Rightarrow> if (\<forall>s \<in> set ss. s = SmtSort_BitVec w) then Some (unat w) else None
               | _ \<Rightarrow> None)\<close>

text \<open>The result sort of a theory function applied to arguments of the sorts \<open>ss\<close>, if the
  application is well-sorted (the rank declarations of Core, FixedSizeBitVectors and QF\_BV). The
  widths of results stay below \<open>2^64\<close>, the range of the widths of \<^typ>\<open>SmtSort\<close>.\<close>
fun smt_op_sort :: \<open>SmtOp \<Rightarrow> SmtSort list \<Rightarrow> SmtSort option\<close> where
  \<open>smt_op_sort SmtOp_Not ss = (if ss = [SmtSort_Bool] then Some SmtSort_Bool else None)\<close>
| \<open>smt_op_sort SmtOp_And ss = (if 2 \<le> length ss \<and> set ss \<subseteq> {SmtSort_Bool} then Some SmtSort_Bool else None)\<close>
| \<open>smt_op_sort SmtOp_Or ss = (if 2 \<le> length ss \<and> set ss \<subseteq> {SmtSort_Bool} then Some SmtSort_Bool else None)\<close>
| \<open>smt_op_sort SmtOp_Xor ss = (if 2 \<le> length ss \<and> set ss \<subseteq> {SmtSort_Bool} then Some SmtSort_Bool else None)\<close>
| \<open>smt_op_sort SmtOp_Implies ss = (if 2 \<le> length ss \<and> set ss \<subseteq> {SmtSort_Bool} then Some SmtSort_Bool else None)\<close>
| \<open>smt_op_sort SmtOp_Eq ss = (if 2 \<le> length ss \<and> set ss \<subseteq> {hd ss} then Some SmtSort_Bool else None)\<close>
| \<open>smt_op_sort SmtOp_Distinct ss = (if 2 \<le> length ss \<and> set ss \<subseteq> {hd ss} then Some SmtSort_Bool else None)\<close>
| \<open>smt_op_sort SmtOp_Ite ss =
     (case ss of [c, a, b] \<Rightarrow> if c = SmtSort_Bool \<and> a = b then Some a else None | _ \<Rightarrow> None)\<close>
| \<open>smt_op_sort SmtOp_Concat ss =
     (case ss of [SmtSort_BitVec a, SmtSort_BitVec b] \<Rightarrow>
        if unat a + unat b < 2 ^ 64 then Some (SmtSort_BitVec (a + b)) else None
      | _ \<Rightarrow> None)\<close>
| \<open>smt_op_sort (SmtOp_Extract i j) ss =
     (case ss of [SmtSort_BitVec m] \<Rightarrow>
        if unat j \<le> unat i \<and> unat i < unat m then Some (SmtSort_BitVec (i - j + 1)) else None
      | _ \<Rightarrow> None)\<close>
| \<open>smt_op_sort SmtOp_Bvnot ss = (case ss of [SmtSort_BitVec m] \<Rightarrow> Some (SmtSort_BitVec m) | _ \<Rightarrow> None)\<close>
| \<open>smt_op_sort SmtOp_Bvneg ss = (case ss of [SmtSort_BitVec m] \<Rightarrow> Some (SmtSort_BitVec m) | _ \<Rightarrow> None)\<close>
| \<open>smt_op_sort SmtOp_Bvand ss = (if 2 \<le> length ss \<and> smt_same_width ss \<noteq> None then Some (hd ss) else None)\<close>
| \<open>smt_op_sort SmtOp_Bvor ss = (if 2 \<le> length ss \<and> smt_same_width ss \<noteq> None then Some (hd ss) else None)\<close>
| \<open>smt_op_sort SmtOp_Bvadd ss = (if 2 \<le> length ss \<and> smt_same_width ss \<noteq> None then Some (hd ss) else None)\<close>
| \<open>smt_op_sort SmtOp_Bvmul ss = (if 2 \<le> length ss \<and> smt_same_width ss \<noteq> None then Some (hd ss) else None)\<close>
| \<open>smt_op_sort SmtOp_Bvcomp ss = (if smt_bin_width ss \<noteq> None then Some (SmtSort_BitVec 1) else None)\<close>
| \<open>smt_op_sort SmtOp_Bvult ss = (if smt_bin_width ss \<noteq> None then Some SmtSort_Bool else None)\<close>
| \<open>smt_op_sort SmtOp_Bvule ss = (if smt_bin_width ss \<noteq> None then Some SmtSort_Bool else None)\<close>
| \<open>smt_op_sort SmtOp_Bvugt ss = (if smt_bin_width ss \<noteq> None then Some SmtSort_Bool else None)\<close>
| \<open>smt_op_sort SmtOp_Bvuge ss = (if smt_bin_width ss \<noteq> None then Some SmtSort_Bool else None)\<close>
| \<open>smt_op_sort SmtOp_Bvslt ss = (if smt_bin_width ss \<noteq> None then Some SmtSort_Bool else None)\<close>
| \<open>smt_op_sort SmtOp_Bvsle ss = (if smt_bin_width ss \<noteq> None then Some SmtSort_Bool else None)\<close>
| \<open>smt_op_sort SmtOp_Bvsgt ss = (if smt_bin_width ss \<noteq> None then Some SmtSort_Bool else None)\<close>
| \<open>smt_op_sort SmtOp_Bvsge ss = (if smt_bin_width ss \<noteq> None then Some SmtSort_Bool else None)\<close>
| \<open>smt_op_sort (SmtOp_Repeat i) ss =
     (case ss of [SmtSort_BitVec m] \<Rightarrow>
        if 1 \<le> unat i \<and> unat m * unat i < 2 ^ 64 then Some (SmtSort_BitVec (m * i)) else None
      | _ \<Rightarrow> None)\<close>
| \<open>smt_op_sort (SmtOp_ZeroExtend i) ss =
     (case ss of [SmtSort_BitVec m] \<Rightarrow>
        if unat m + unat i < 2 ^ 64 then Some (SmtSort_BitVec (m + i)) else None
      | _ \<Rightarrow> None)\<close>
| \<open>smt_op_sort (SmtOp_SignExtend i) ss =
     (case ss of [SmtSort_BitVec m] \<Rightarrow>
        if unat m + unat i < 2 ^ 64 then Some (SmtSort_BitVec (m + i)) else None
      | _ \<Rightarrow> None)\<close>
| \<open>smt_op_sort (SmtOp_RotateLeft i) ss = (case ss of [SmtSort_BitVec m] \<Rightarrow> Some (SmtSort_BitVec m) | _ \<Rightarrow> None)\<close>
| \<open>smt_op_sort (SmtOp_RotateRight i) ss = (case ss of [SmtSort_BitVec m] \<Rightarrow> Some (SmtSort_BitVec m) | _ \<Rightarrow> None)\<close>
| \<open>smt_op_sort _ ss = (if smt_bin_width ss \<noteq> None then Some (hd ss) else None)\<close>

text \<open>The last case covers the binary functions with result of the width of their operands:
  \<open>bvudiv\<close>, \<open>bvurem\<close>, \<open>bvshl\<close>, \<open>bvlshr\<close>, \<open>bvnand\<close>, \<open>bvnor\<close>, \<open>bvxor\<close>, \<open>bvxnor\<close>, \<open>bvsub\<close>,
  \<open>bvsdiv\<close>, \<open>bvsrem\<close>, \<open>bvsmod\<close>, \<open>bvashr\<close>.\<close>

text \<open>The sort of a term, if it is well-sorted, given the declared symbols \<open>fs\<close>, the definitions
  \<open>ds\<close> it may refer to, and the sorts \<open>ps\<close> of the parameters in scope.\<close>
fun smt_tsort :: \<open>SmtFun list \<Rightarrow> SmtDef list \<Rightarrow> SmtSort list \<Rightarrow> SmtTerm \<Rightarrow> SmtSort option\<close> where
  \<open>smt_tsort fs ds ps (SmtTerm_BoolConst b) = Some SmtSort_Bool\<close>
| \<open>smt_tsort fs ds ps (SmtTerm_BvConst bs) =
     (if 0 < length bs \<and> length bs < 2 ^ 64 then Some (SmtSort_BitVec (of_nat (length bs))) else None)\<close>
| \<open>smt_tsort fs ds ps (SmtTerm_Param k) = (if unat k < length ps then Some (ps ! unat k) else None)\<close>
| \<open>smt_tsort fs ds ps (SmtTerm_Fun f args) =
     (if unat f < length fs \<and> map (smt_tsort fs ds ps) args = map Some (SmtFun_args (fs ! unat f))
      then Some (SmtFun_ret (fs ! unat f)) else None)\<close>
| \<open>smt_tsort fs ds ps (SmtTerm_Def d args) =
     (if unat d < length ds \<and> map (smt_tsort fs ds ps) args = map Some (SmtDef_params (ds ! unat d))
      then Some (SmtDef_ret (ds ! unat d)) else None)\<close>
| \<open>smt_tsort fs ds ps (SmtTerm_App op args) =
     (if None \<notin> set (map (smt_tsort fs ds ps) args)
      then smt_op_sort op (map (the \<circ> smt_tsort fs ds ps) args) else None)\<close>

text \<open>A well-sorted problem: all sorts are sorts of the problem; the body of definition \<open>d\<close> has the
  declared result sort, over the parameters of \<open>d\<close> and the definitions before \<open>d\<close>; every assertion
  is Boolean and has no parameters.\<close>
definition smt_wf :: \<open>SmtProblem \<Rightarrow> bool\<close> where
  \<open>smt_wf p \<equiv>
     let ns = unat (SmtProblem_num_sorts p) in let fs = SmtProblem_funs p in let ds = SmtProblem_defs p in
     (\<forall>f \<in> set fs. (\<forall>s \<in> set (SmtFun_args f). smt_wf_sort ns s) \<and> smt_wf_sort ns (SmtFun_ret f)) \<and>
     (\<forall>d < length ds. (\<forall>s \<in> set (SmtDef_params (ds ! d)). smt_wf_sort ns s) \<and>
        smt_wf_sort ns (SmtDef_ret (ds ! d)) \<and>
        smt_tsort fs (take d ds) (SmtDef_params (ds ! d)) (SmtDef_body (ds ! d)) = Some (SmtDef_ret (ds ! d))) \<and>
     (\<forall>t \<in> set (SmtProblem_asserts p). smt_tsort fs ds [] t = Some SmtSort_Bool)\<close>

subsection \<open>Evaluation\<close>

fun smt_true :: \<open>sval \<Rightarrow> bool\<close> where
  \<open>smt_true (VBool b) = b\<close>
| \<open>smt_true _ = False\<close>

fun smt_bv_width :: \<open>sval \<Rightarrow> nat\<close> where
  \<open>smt_bv_width (VBv w x) = w\<close>
| \<open>smt_bv_width _ = 0\<close>

fun smt_bv_val :: \<open>sval \<Rightarrow> nat\<close> where
  \<open>smt_bv_val (VBv w x) = x\<close>
| \<open>smt_bv_val _ = 0\<close>

text \<open>A binary bit-vector function on the numbers \<open>x\<close>, \<open>y\<close> of operands of width \<open>w\<close>. The functions
  of FixedSizeBitVectors (\<open>:definition\<close>) and the extensions of QF\_BV (each the number its
  abbreviation denotes), as transcribed with the text of SMT-LIB in \<^verbatim>\<open>BVSmt_Spec\<close>:
  \<^item> \<open>bvand\<close>, \<open>bvor\<close>: bitwise; \<open>bvadd\<close>, \<open>bvmul\<close>: modulo \<open>2^w\<close>; \<open>bvudiv\<close> by 0 is all ones,
    \<open>bvurem\<close> by 0 the dividend; \<open>bvshl\<close>, \<open>bvlshr\<close>: by the number of \<open>y\<close>.
  \<^item> \<open>bvnand\<close>, \<open>bvnor\<close>, \<open>bvxor\<close>, \<open>bvxnor\<close>: bitwise; \<open>bvsub\<close>: \<open>x - y\<close> modulo \<open>2^w\<close>.
  \<^item> \<open>bvsdiv\<close>, \<open>bvsrem\<close>, \<open>bvsmod\<close>: on the two's complement values, with the division by 0 that
    the case definitions of QF\_BV inherit from \<open>bvudiv\<close> and \<open>bvurem\<close>; \<open>bvashr\<close>: the two's
    complement value divided by \<open>2^y\<close>, rounded down.\<close>
fun smt_bv_bin :: \<open>SmtOp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>smt_bv_bin SmtOp_Bvand w x y = Bit_Operations.and x y\<close>
| \<open>smt_bv_bin SmtOp_Bvor w x y = Bit_Operations.or x y\<close>
| \<open>smt_bv_bin SmtOp_Bvxor w x y = Bit_Operations.xor x y\<close>
| \<open>smt_bv_bin SmtOp_Bvnand w x y = 2 ^ w - 1 - Bit_Operations.and x y\<close>
| \<open>smt_bv_bin SmtOp_Bvnor w x y = 2 ^ w - 1 - Bit_Operations.or x y\<close>
| \<open>smt_bv_bin SmtOp_Bvxnor w x y = 2 ^ w - 1 - Bit_Operations.xor x y\<close>
| \<open>smt_bv_bin SmtOp_Bvadd w x y = (x + y) mod 2 ^ w\<close>
| \<open>smt_bv_bin SmtOp_Bvsub w x y = (x + (2 ^ w - y)) mod 2 ^ w\<close>
| \<open>smt_bv_bin SmtOp_Bvmul w x y = (x * y) mod 2 ^ w\<close>
| \<open>smt_bv_bin SmtOp_Bvudiv w x y = (if y = 0 then 2 ^ w - 1 else x div y)\<close>
| \<open>smt_bv_bin SmtOp_Bvurem w x y = (if y = 0 then x else x mod y)\<close>
| \<open>smt_bv_bin SmtOp_Bvsdiv w x y =
     (if y = 0 then (if smt_sint w x < 0 then 1 else 2 ^ w - 1)
      else smt_to_bv w (smt_tdiv (smt_sint w x) (smt_sint w y)))\<close>
| \<open>smt_bv_bin SmtOp_Bvsrem w x y = (if y = 0 then x else smt_to_bv w (smt_tmod (smt_sint w x) (smt_sint w y)))\<close>
| \<open>smt_bv_bin SmtOp_Bvsmod w x y = (if y = 0 then x else smt_to_bv w (smt_sint w x mod smt_sint w y))\<close>
| \<open>smt_bv_bin SmtOp_Bvshl w x y = (x * 2 ^ y) mod 2 ^ w\<close>
| \<open>smt_bv_bin SmtOp_Bvlshr w x y = x div 2 ^ y\<close>
| \<open>smt_bv_bin SmtOp_Bvashr w x y = smt_to_bv w (smt_sint w x div 2 ^ y)\<close>
| \<open>smt_bv_bin _ w x y = 0\<close>

text \<open>A binary bit-vector predicate on the numbers of operands of width \<open>w\<close>: \<open>bvult\<close>
  (FixedSizeBitVectors) and the comparisons of QF\_BV (unsigned, and signed on the two's
  complement values).\<close>
fun smt_bv_cmp :: \<open>SmtOp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>smt_bv_cmp SmtOp_Bvult w x y = (x < y)\<close>
| \<open>smt_bv_cmp SmtOp_Bvule w x y = (x \<le> y)\<close>
| \<open>smt_bv_cmp SmtOp_Bvugt w x y = (y < x)\<close>
| \<open>smt_bv_cmp SmtOp_Bvuge w x y = (y \<le> x)\<close>
| \<open>smt_bv_cmp SmtOp_Bvslt w x y = (smt_sint w x < smt_sint w y)\<close>
| \<open>smt_bv_cmp SmtOp_Bvsle w x y = (smt_sint w x \<le> smt_sint w y)\<close>
| \<open>smt_bv_cmp SmtOp_Bvsgt w x y = (smt_sint w y < smt_sint w x)\<close>
| \<open>smt_bv_cmp SmtOp_Bvsge w x y = (smt_sint w y \<le> smt_sint w x)\<close>
| \<open>smt_bv_cmp _ w x y = False\<close>

text \<open>A theory function applied to the values \<open>vs\<close> of its arguments. For a well-sorted application,
  the cases of Core: \<open>not\<close>; \<open>and\<close>, \<open>or\<close> (all, some argument true); \<open>xor\<close> (left-associative: an
  odd number of arguments true); \<open>=>\<close> (right-associative: some argument but the last false, or the
  last true); \<open>=\<close> (chainable: all arguments equal); \<open>distinct\<close> (pairwise); \<open>ite\<close>. Of the
  bit-vector theory: \<open>concat\<close> (the first argument the high part); \<open>extract\<close> (bits \<open>j\<close> to \<open>i\<close>);
  \<open>bvnot\<close>, \<open>bvneg\<close>; the left-associative \<open>bvand\<close>, \<open>bvor\<close>, \<open>bvadd\<close>, \<open>bvmul\<close> (folded from the
  left); \<open>bvcomp\<close> (1 iff equal); the predicates; \<open>repeat\<close>; \<open>zero_extend\<close> (the number
  unchanged); \<open>sign_extend\<close> (the two's complement value at the larger width); \<open>rotate_left\<close>,
  \<open>rotate_right\<close> by \<open>i mod w\<close> places; the other binary functions by \<^const>\<open>smt_bv_bin\<close>.\<close>
fun smt_op_sem :: \<open>SmtOp \<Rightarrow> sval list \<Rightarrow> sval\<close> where
  \<open>smt_op_sem SmtOp_Not vs = VBool (\<not> smt_true (hd vs))\<close>
| \<open>smt_op_sem SmtOp_And vs = VBool (\<forall>v \<in> set vs. smt_true v)\<close>
| \<open>smt_op_sem SmtOp_Or vs = VBool (\<exists>v \<in> set vs. smt_true v)\<close>
| \<open>smt_op_sem SmtOp_Xor vs = VBool (odd (length (filter smt_true vs)))\<close>
| \<open>smt_op_sem SmtOp_Implies vs = VBool ((\<exists>v \<in> set (butlast vs). \<not> smt_true v) \<or> smt_true (last vs))\<close>
| \<open>smt_op_sem SmtOp_Eq vs = VBool (\<forall>i. Suc i < length vs \<longrightarrow> vs ! i = vs ! Suc i)\<close>
| \<open>smt_op_sem SmtOp_Distinct vs = VBool (distinct vs)\<close>
| \<open>smt_op_sem SmtOp_Ite vs = (if smt_true (vs ! 0) then vs ! 1 else vs ! 2)\<close>
| \<open>smt_op_sem SmtOp_Concat vs =
     VBv (smt_bv_width (vs ! 0) + smt_bv_width (vs ! 1))
         (smt_bv_val (vs ! 0) * 2 ^ smt_bv_width (vs ! 1) + smt_bv_val (vs ! 1))\<close>
| \<open>smt_op_sem (SmtOp_Extract i j) vs =
     VBv (unat i - unat j + 1) ((smt_bv_val (hd vs) div 2 ^ unat j) mod 2 ^ (unat i - unat j + 1))\<close>
| \<open>smt_op_sem SmtOp_Bvnot vs = (let w = smt_bv_width (hd vs) in VBv w (2 ^ w - 1 - smt_bv_val (hd vs)))\<close>
| \<open>smt_op_sem SmtOp_Bvneg vs =
     (let w = smt_bv_width (hd vs) in VBv w ((2 ^ w - smt_bv_val (hd vs)) mod 2 ^ w))\<close>
| \<open>smt_op_sem SmtOp_Bvcomp vs = VBv 1 (of_bool (vs ! 0 = vs ! 1))\<close>
| \<open>smt_op_sem (SmtOp_Repeat i) vs =
     (let w = smt_bv_width (hd vs) in VBv (w * unat i) (smt_repeat_val w (unat i) (smt_bv_val (hd vs))))\<close>
| \<open>smt_op_sem (SmtOp_ZeroExtend i) vs = VBv (smt_bv_width (hd vs) + unat i) (smt_bv_val (hd vs))\<close>
| \<open>smt_op_sem (SmtOp_SignExtend i) vs =
     (let w = smt_bv_width (hd vs) in VBv (w + unat i) (smt_to_bv (w + unat i) (smt_sint w (smt_bv_val (hd vs)))))\<close>
| \<open>smt_op_sem (SmtOp_RotateLeft i) vs =
     (let w = smt_bv_width (hd vs) in let r = unat i mod w in let x = smt_bv_val (hd vs) in
      VBv w ((x mod 2 ^ (w - r)) * 2 ^ r + x div 2 ^ (w - r)))\<close>
| \<open>smt_op_sem (SmtOp_RotateRight i) vs =
     (let w = smt_bv_width (hd vs) in let r = unat i mod w in let x = smt_bv_val (hd vs) in
      VBv w ((x mod 2 ^ r) * 2 ^ (w - r) + x div 2 ^ r))\<close>
| \<open>smt_op_sem SmtOp_Bvult vs = VBool (smt_bv_cmp SmtOp_Bvult (smt_bv_width (vs ! 0)) (smt_bv_val (vs ! 0)) (smt_bv_val (vs ! 1)))\<close>
| \<open>smt_op_sem SmtOp_Bvule vs = VBool (smt_bv_cmp SmtOp_Bvule (smt_bv_width (vs ! 0)) (smt_bv_val (vs ! 0)) (smt_bv_val (vs ! 1)))\<close>
| \<open>smt_op_sem SmtOp_Bvugt vs = VBool (smt_bv_cmp SmtOp_Bvugt (smt_bv_width (vs ! 0)) (smt_bv_val (vs ! 0)) (smt_bv_val (vs ! 1)))\<close>
| \<open>smt_op_sem SmtOp_Bvuge vs = VBool (smt_bv_cmp SmtOp_Bvuge (smt_bv_width (vs ! 0)) (smt_bv_val (vs ! 0)) (smt_bv_val (vs ! 1)))\<close>
| \<open>smt_op_sem SmtOp_Bvslt vs = VBool (smt_bv_cmp SmtOp_Bvslt (smt_bv_width (vs ! 0)) (smt_bv_val (vs ! 0)) (smt_bv_val (vs ! 1)))\<close>
| \<open>smt_op_sem SmtOp_Bvsle vs = VBool (smt_bv_cmp SmtOp_Bvsle (smt_bv_width (vs ! 0)) (smt_bv_val (vs ! 0)) (smt_bv_val (vs ! 1)))\<close>
| \<open>smt_op_sem SmtOp_Bvsgt vs = VBool (smt_bv_cmp SmtOp_Bvsgt (smt_bv_width (vs ! 0)) (smt_bv_val (vs ! 0)) (smt_bv_val (vs ! 1)))\<close>
| \<open>smt_op_sem SmtOp_Bvsge vs = VBool (smt_bv_cmp SmtOp_Bvsge (smt_bv_width (vs ! 0)) (smt_bv_val (vs ! 0)) (smt_bv_val (vs ! 1)))\<close>
| \<open>smt_op_sem op vs =
     (let w = smt_bv_width (hd vs) in
      foldl (\<lambda>a b. VBv w (smt_bv_bin op w (smt_bv_val a) (smt_bv_val b))) (hd vs) (tl vs))\<close>

text \<open>The last case: the binary functions of \<^const>\<open>smt_bv_bin\<close>, and the left-associative ones with
  any number of arguments (for two arguments the fold is one application).\<close>

text \<open>The value of a term under the interpretation \<open>I\<close> of the declared symbols, the meanings \<open>dv\<close>
  of the definitions (functions from the values of their parameters), and the values \<open>vs\<close> of
  the parameters in scope.\<close>
fun smt_eval :: \<open>(nat \<Rightarrow> sval list \<Rightarrow> sval) \<Rightarrow> (sval list \<Rightarrow> sval) list \<Rightarrow> sval list \<Rightarrow> SmtTerm \<Rightarrow> sval\<close> where
  \<open>smt_eval I dv vs (SmtTerm_BoolConst b) = VBool b\<close>
| \<open>smt_eval I dv vs (SmtTerm_BvConst bs) = VBv (length bs) (smt_bits_nat bs)\<close>
| \<open>smt_eval I dv vs (SmtTerm_Param k) = vs ! unat k\<close>
| \<open>smt_eval I dv vs (SmtTerm_Fun f args) = I (unat f) (map (smt_eval I dv vs) args)\<close>
| \<open>smt_eval I dv vs (SmtTerm_Def d args) = (dv ! unat d) (map (smt_eval I dv vs) args)\<close>
| \<open>smt_eval I dv vs (SmtTerm_App op args) = smt_op_sem op (map (smt_eval I dv vs) args)\<close>

text \<open>The meanings of the definitions, in order: definition \<open>d\<close> means its body with the parameters
  bound to the arguments and the definitions before \<open>d\<close> meaning what they mean.\<close>
definition smt_def_sems :: \<open>(nat \<Rightarrow> sval list \<Rightarrow> sval) \<Rightarrow> SmtDef list \<Rightarrow> (sval list \<Rightarrow> sval) list\<close> where
  \<open>smt_def_sems I ds \<equiv> foldl (\<lambda>dv d. dv @ [\<lambda>vs. smt_eval I dv vs (SmtDef_body d)]) [] ds\<close>

text \<open>An interpretation that respects the sorts of the declared symbols.\<close>
definition smt_interp_ok :: \<open>SmtProblem \<Rightarrow> (nat \<Rightarrow> sval list \<Rightarrow> sval) \<Rightarrow> bool\<close> where
  \<open>smt_interp_ok p I \<equiv>
     \<forall>f < length (SmtProblem_funs p). \<forall>vs.
       list_all2 smt_has_sort (SmtFun_args (SmtProblem_funs p ! f)) vs \<longrightarrow>
       smt_has_sort (SmtFun_ret (SmtProblem_funs p ! f)) (I f vs)\<close>

text \<open>Every assertion is true under \<open>I\<close>.\<close>
definition smt_satisfies :: \<open>SmtProblem \<Rightarrow> (nat \<Rightarrow> sval list \<Rightarrow> sval) \<Rightarrow> bool\<close> where
  \<open>smt_satisfies p I \<equiv>
     let dv = smt_def_sems I (SmtProblem_defs p) in
     \<forall>t \<in> set (SmtProblem_asserts p). smt_eval I dv [] t = VBool True\<close>

definition smt_satisfiable :: \<open>SmtProblem \<Rightarrow> bool\<close> where
  \<open>smt_satisfiable p \<equiv> \<exists>I. smt_interp_ok p I \<and> smt_satisfies p I\<close>

subsection \<open>Models\<close>

fun smt_val_of :: \<open>SmtValue \<Rightarrow> sval\<close> where
  \<open>smt_val_of (SmtValue_Bool b) = VBool b\<close>
| \<open>smt_val_of (SmtValue_Bv bs) = VBv (length bs) (smt_bits_nat bs)\<close>
| \<open>smt_val_of (SmtValue_Elem e) = VElem (unat e)\<close>

text \<open>A table: at the arguments \<open>vs\<close>, the value of the first entry with these arguments, otherwise
  the default.\<close>
definition smt_interp_of :: \<open>SmtInterp \<Rightarrow> sval list \<Rightarrow> sval\<close> where
  \<open>smt_interp_of t vs \<equiv>
     (case List.find (\<lambda>e. List.map smt_val_of (SmtEntry_args e) = vs) (SmtInterp_entries t) of
        Some e \<Rightarrow> smt_val_of (SmtEntry_val e)
      | None \<Rightarrow> smt_val_of (SmtInterp_default t))\<close>

definition smt_model_interp :: \<open>SmtModel \<Rightarrow> nat \<Rightarrow> sval list \<Rightarrow> sval\<close> where
  \<open>smt_model_interp m f vs \<equiv> smt_interp_of (SmtModel_funs m ! f) vs\<close>

text \<open>A value of sort \<open>s\<close> in a model with the domain sizes \<open>dms\<close>: an element is below the size of
  the domain of its sort.\<close>
fun smt_model_value_ok :: \<open>64 word list \<Rightarrow> SmtSort \<Rightarrow> SmtValue \<Rightarrow> bool\<close> where
  \<open>smt_model_value_ok dms SmtSort_Bool (SmtValue_Bool b) = True\<close>
| \<open>smt_model_value_ok dms (SmtSort_BitVec w) (SmtValue_Bv bs) = (length bs = unat w)\<close>
| \<open>smt_model_value_ok dms (SmtSort_Uninterpreted s) (SmtValue_Elem e) =
     (unat s < length dms \<and> unat e < unat (dms ! unat s))\<close>
| \<open>smt_model_value_ok dms _ _ = False\<close>

text \<open>A well-formed model of \<open>p\<close>: a non-empty domain for every uninterpreted sort, a table for
  every declared symbol, and every value in the tables of the right sort and in its domain.\<close>
definition smt_model_wf :: \<open>SmtProblem \<Rightarrow> SmtModel \<Rightarrow> bool\<close> where
  \<open>smt_model_wf p m \<equiv>
     let dms = SmtModel_domains m in let fs = SmtProblem_funs p in let ts = SmtModel_funs m in
     length dms = unat (SmtProblem_num_sorts p) \<and> (\<forall>n \<in> set dms. 0 < unat n) \<and>
     length ts = length fs \<and>
     (\<forall>f < length fs.
        smt_model_value_ok dms (SmtFun_ret (fs ! f)) (SmtInterp_default (ts ! f)) \<and>
        (\<forall>e \<in> set (SmtInterp_entries (ts ! f)).
           list_all2 (smt_model_value_ok dms) (SmtFun_args (fs ! f)) (SmtEntry_args e) \<and>
           smt_model_value_ok dms (SmtFun_ret (fs ! f)) (SmtEntry_val e)))\<close>

text \<open>A model of \<open>p\<close>: well-formed, and every assertion true under its interpretation.\<close>
definition smt_is_model :: \<open>SmtProblem \<Rightarrow> SmtModel \<Rightarrow> bool\<close> where
  \<open>smt_is_model p m \<equiv> smt_model_wf p m \<and> smt_satisfies p (smt_model_interp m)\<close>

subsection \<open>The size of a problem\<close>

text \<open>The weight of a node of a term of sort \<open>s\<close> (or none) with \<open>n\<close> arguments of sorts \<open>ss\<close>: the
  square of \<open>n + 1\<close> times the sum of the cubes of the widths (plus one) of the node and its
  arguments.\<close>
definition smt_wcube :: \<open>SmtSort option \<Rightarrow> nat\<close> where
  \<open>smt_wcube s \<equiv> (case s of Some s \<Rightarrow> smt_width s | None \<Rightarrow> 0) + 1\<close>

definition smt_node_weight :: \<open>SmtFun list \<Rightarrow> SmtDef list \<Rightarrow> SmtSort list \<Rightarrow> SmtTerm \<Rightarrow> SmtTerm list \<Rightarrow> nat\<close> where
  \<open>smt_node_weight fs ds ps t args \<equiv>
     Suc (length args) ^ 2 *
     (smt_wcube (smt_tsort fs ds ps t) ^ 3 + sum_list (map (\<lambda>a. smt_wcube (smt_tsort fs ds ps a) ^ 3) args))\<close>

text \<open>The weight of a term: the weights of its nodes, where a definition with parameters counts
  with the weight of its body at every application (a solver may expand it there).\<close>
function smt_weight :: \<open>SmtFun list \<Rightarrow> SmtDef list \<Rightarrow> SmtSort list \<Rightarrow> SmtTerm \<Rightarrow> nat\<close> where
  \<open>smt_weight fs ds ps (SmtTerm_BoolConst b) = smt_node_weight fs ds ps (SmtTerm_BoolConst b) []\<close>
| \<open>smt_weight fs ds ps (SmtTerm_BvConst bs) = smt_node_weight fs ds ps (SmtTerm_BvConst bs) [] + length bs\<close>
| \<open>smt_weight fs ds ps (SmtTerm_Param k) = smt_node_weight fs ds ps (SmtTerm_Param k) []\<close>
| \<open>smt_weight fs ds ps (SmtTerm_Fun f args) =
     smt_node_weight fs ds ps (SmtTerm_Fun f args) args + sum_list (map (smt_weight fs ds ps) args)\<close>
| \<open>smt_weight fs ds ps (SmtTerm_Def d args) =
     smt_node_weight fs ds ps (SmtTerm_Def d args) args + sum_list (map (smt_weight fs ds ps) args) +
     (if unat d < length ds \<and> SmtDef_params (ds ! unat d) \<noteq> []
      then smt_weight fs (take (unat d) ds) (SmtDef_params (ds ! unat d)) (SmtDef_body (ds ! unat d)) else 0)\<close>
| \<open>smt_weight fs ds ps (SmtTerm_App op args) =
     smt_node_weight fs ds ps (SmtTerm_App op args) args + sum_list (map (smt_weight fs ds ps) args)\<close>
  by pat_completeness auto
termination
  by (relation \<open>measures [\<lambda>(_, ds, _, _). length ds, \<lambda>(_, _, _, t). size t]\<close>)
     (auto intro: size_list_estimation' simp: less_Suc_eq_le)

text \<open>The size of a problem, a bound on the work and the memory of a solver, and so on its
  counters (of type \<^verbatim>\<open>usize\<close>) and on the fuel it needs: \<open>10^9\<close> times one plus the numbers of
  declared symbols, definitions and assertions, the widths (plus one) of the result sorts of the
  declared symbols, and the weights of the bodies of the definitions without parameters and of
  the assertions.\<close>
definition smt_size_bound :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>smt_size_bound p \<equiv>
     let fs = SmtProblem_funs p in let ds = SmtProblem_defs p in
     1000000000 *
       (1 + length fs + length ds + length (SmtProblem_asserts p) +
        sum_list (map (\<lambda>f. smt_width (SmtFun_ret f) + 1) fs) +
        sum_list (map (\<lambda>d. if SmtDef_params (ds ! d) = [] then smt_weight fs (take d ds) [] (SmtDef_body (ds ! d)) else 0)
                   [0..<length ds]) +
        sum_list (map (smt_weight fs ds []) (SmtProblem_asserts p)))\<close>

text \<open>The condition on the size: it fits in a 64-bit word. The constant and the powers in
  \<^const>\<open>smt_size_bound\<close> are generous, so this excludes some problems a solver could handle.\<close>
definition smt_sizes_ok :: \<open>SmtProblem \<Rightarrow> bool\<close> where
  \<open>smt_sizes_ok p \<equiv> smt_size_bound p < 2 ^ 64\<close>

end
