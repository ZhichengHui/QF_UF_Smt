theory SMT_Semantics
  imports SMT_Types
begin

text \<open>\<open>map\<close> below is \<^const>\<open>List.map\<close>, not the iterator function of AutoCorrode.\<close>
hide_const (open) Rust_Iterator.map

section \<open>The semantics of general problems\<close>

text \<open>
  This theory is the same in both solvers (QF\_UF and QF\_BV).
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
    SMT-LIB 2.6 theory and logic declarations, whose text is quoted beside each bit-vector
    function below (the files are in \<^verbatim>\<open>spec/smtlib-2.6/\<close> of the solver of each logic).
    \<open>and\<close>, \<open>or\<close>, \<open>xor\<close>, \<open>bvand\<close>, \<open>bvor\<close>, \<open>bvadd\<close>, \<open>bvmul\<close>, \<open>bvxor\<close> are left-associative, \<open>=>\<close>
    right-associative, \<open>=\<close> chainable and \<open>distinct\<close> pairwise.
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
| \<open>smt_op_sort SmtOp_Bvxor ss = (if 2 \<le> length ss \<and> smt_same_width ss \<noteq> None then Some (hd ss) else None)\<close>
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

text \<open>A binary bit-vector function on the numbers \<open>x\<close>, \<open>y\<close> of operands of width \<open>w\<close>. The text of
  SMT-LIB 2.6 is quoted for each case; \<open>s\<close>, \<open>t\<close> are the operands, \<open>m\<close> their width.

  FixedSizeBitVectors, \<open>:definition\<close>:
  \<^item> \<open>bvand\<close>, \<open>bvor\<close>: \<open>[[(bvand s t)]] := \<lambda>x:[0, m). if [[s]](x) = 0 then 0 else [[t]](x)\<close>,
    \<open>[[(bvor s t)]] := \<lambda>x:[0, m). if [[s]](x) = 1 then 1 else [[t]](x)\<close>: the bitwise operations
    on numbers (\<^const>\<open>Bit_Operations.and\<close>, \<^const>\<open>Bit_Operations.or\<close>).
  \<^item> \<open>bvadd\<close>: \<open>nat2bv[m](bv2nat([[s]]) + bv2nat([[t]]))\<close>; \<open>bvmul\<close>: \<open>nat2bv[m](bv2nat([[s]]) * bv2nat([[t]]))\<close>.
  \<^item> \<open>bvudiv\<close>: \<open>if bv2nat([[t]]) = 0 then \<lambda>x:[0, m). 1 else nat2bv[m](bv2nat([[s]]) div bv2nat([[t]]))\<close>.
  \<^item> \<open>bvurem\<close>: \<open>if bv2nat([[t]]) = 0 then [[s]] else nat2bv[m](bv2nat([[s]]) rem bv2nat([[t]]))\<close>.
  \<^item> \<open>bvshl\<close>: \<open>nat2bv[m](bv2nat([[s]]) * 2^(bv2nat([[t]])))\<close>; \<open>bvlshr\<close>: \<open>nat2bv[m](bv2nat([[s]]) div 2^(bv2nat([[t]])))\<close>.

  QF\_BV, \<open>:extensions\<close>:
  \<^item> \<open>bvnand s t\<close> abbreviates \<open>(bvnot (bvand s t))\<close>; \<open>bvnor\<close>: \<open>(bvnot (bvor s t))\<close>.
  \<^item> \<open>bvxor s t\<close> abbreviates \<open>(bvor (bvand s (bvnot t)) (bvand (bvnot s) t))\<close>: the bitwise exclusive
    or; \<open>bvxnor s t\<close> abbreviates \<open>(bvor (bvand s t) (bvand (bvnot s) (bvnot t)))\<close>: its negation.
  \<^item> \<open>bvsub s t\<close> abbreviates \<open>(bvadd s (bvneg t))\<close>: \<open>s - t\<close> modulo \<open>2^m\<close>.
  \<^item> \<open>bvsdiv s t\<close>: \<open>(bvudiv s t)\<close> if both sign bits are 0; \<open>(bvneg (bvudiv (bvneg s) t))\<close> if they are
    1, 0; \<open>(bvneg (bvudiv s (bvneg t)))\<close> if 0, 1; \<open>(bvudiv (bvneg s) (bvneg t))\<close> if 1, 1. For
    \<open>t \<noteq> 0\<close>, this is the quotient of the two's complement values rounded towards zero
    (\<^const>\<open>smt_tdiv\<close>), modulo \<open>2^m\<close>. For \<open>t = 0\<close> (sign bit 0), \<open>bvudiv\<close> by 0 gives all ones: the
    result is all ones (\<open>2^m - 1\<close>) when the sign bit of \<open>s\<close> is 0, and \<open>bvneg\<close> of all ones, 1, when
    it is 1.
  \<^item> \<open>bvsrem s t\<close>: \<open>(bvurem s t)\<close>; \<open>(bvneg (bvurem (bvneg s) t))\<close>; \<open>(bvurem s (bvneg t))\<close>;
    \<open>(bvneg (bvurem (bvneg s) (bvneg t)))\<close> for the same four cases: the remainder of that
    division, with the sign of \<open>s\<close> (\<^const>\<open>smt_tmod\<close>), modulo \<open>2^m\<close>. For \<open>t = 0\<close>, \<open>bvurem\<close> by 0
    gives the dividend, so the result is \<open>s\<close>.
  \<^item> \<open>bvsmod s t\<close>: with \<open>u = (bvurem abs_s abs_t)\<close> of the absolute values: \<open>u\<close> if \<open>u = 0\<close> or both
    sign bits are 0; \<open>(bvadd (bvneg u) t)\<close> if they are 1, 0; \<open>(bvadd u t)\<close> if 0, 1; \<open>(bvneg u)\<close> if
    1, 1. For \<open>t \<noteq> 0\<close>, this is the remainder with the sign of \<open>t\<close>: \<open>mod\<close> of the two's complement
    values (the \<open>mod\<close> of Isabelle/HOL rounds the quotient down), modulo \<open>2^m\<close>. For \<open>t = 0\<close>, \<open>u\<close> is
    \<open>abs_s\<close> and every case gives \<open>s\<close>.
  \<^item> \<open>bvashr s t\<close> abbreviates
    \<open>(ite (= ((_ extract |m-1| |m-1|) s) #b0) (bvlshr s t) (bvnot (bvlshr (bvnot s) t)))\<close>: the two's
    complement value of \<open>s\<close> divided by \<open>2^t\<close>, rounded down, modulo \<open>2^m\<close>.\<close>
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

text \<open>A binary bit-vector predicate on the numbers of operands of width \<open>w\<close>, with the text of
  SMT-LIB 2.6:
  \<^item> \<open>bvult\<close> (FixedSizeBitVectors): \<open>true iff bv2nat([[s]]) < bv2nat([[t]])\<close>.
  \<^item> QF\_BV: \<open>bvule s t\<close> abbreviates \<open>(or (bvult s t) (= s t))\<close>; \<open>bvugt s t\<close>: \<open>(bvult t s)\<close>;
    \<open>bvuge s t\<close>: \<open>(or (bvult t s) (= s t))\<close>.
  \<^item> QF\_BV: \<open>bvslt s t\<close> abbreviates
    \<open>(or (and (= msb_s #b1) (= msb_t #b0)) (and (= msb_s msb_t) (bvult s t)))\<close>: the two's
    complement value of \<open>s\<close> is below that of \<open>t\<close>; \<open>bvsle\<close>: the same with \<open>bvule\<close>;
    \<open>bvsgt s t\<close>: \<open>(bvslt t s)\<close>; \<open>bvsge s t\<close>: \<open>(bvsle t s)\<close>.\<close>
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
  bit-vector theory, with the text of SMT-LIB 2.6 (\<open>s\<close>, \<open>t\<close> the operands, \<open>m\<close> the width of \<open>t\<close>):
  \<^item> \<open>concat\<close>: \<open>\<lambda>x:[0, n+m). if (x < m) then [[t]](x) else [[s]](x - m)\<close>: \<open>s\<close> above the \<open>m\<close>
    bits of \<open>t\<close>.
  \<^item> \<open>((_ extract i j) s)\<close>: \<open>\<lambda>x:[0, i-j+1). [[s]](j + x)\<close>: bits \<open>j\<close> to \<open>i\<close>.
  \<^item> \<open>bvnot\<close>: \<open>\<lambda>x:[0, m). if [[s]](x) = 0 then 1 else 0\<close>: every bit flipped, \<open>2^m - 1 - x\<close>.
  \<^item> \<open>bvneg\<close>: \<open>nat2bv[m](2^m - bv2nat([[s]]))\<close>.
  \<^item> The left-associative \<open>bvand\<close>, \<open>bvor\<close>, \<open>bvadd\<close>, \<open>bvmul\<close> and (QF\_BV) \<open>bvxor\<close>: folded from the
    left with \<^const>\<open>smt_bv_bin\<close>.
  \<^item> \<open>bvcomp s t\<close> (QF\_BV): \<open>bvxnor\<close> of the bits, conjoined over all bits: \<open>#b1\<close> iff \<open>s\<close> and \<open>t\<close>
    are equal.
  \<^item> The predicates: \<^const>\<open>smt_bv_cmp\<close>.
  \<^item> \<open>((_ repeat i) t)\<close> (QF\_BV): \<open>t\<close> concatenated with itself \<open>i\<close> times (\<^const>\<open>smt_repeat_val\<close>).
  \<^item> \<open>((_ zero_extend i) t)\<close> abbreviates \<open>(concat ((_ repeat i) #b0) t)\<close> (and \<open>t\<close> for \<open>i = 0\<close>): the
    number is unchanged.
  \<^item> \<open>((_ sign_extend i) t)\<close> abbreviates \<open>(concat ((_ repeat i) ((_ extract |m-1| |m-1|) t)) t)\<close>:
    the two's complement value of \<open>t\<close>, as a value of width \<open>m + i\<close>.
  \<^item> \<open>((_ rotate_left i) t)\<close> abbreviates
    \<open>((_ rotate_left |i-1|) (concat ((_ extract |m-2| 0) t) ((_ extract |m-1| |m-1|) t)))\<close> (and \<open>t\<close>
    for \<open>i = 0\<close> or \<open>m = 1\<close>): with \<open>r = i mod m\<close>, the low \<open>m - r\<close> bits of \<open>t\<close> end up above its
    high \<open>r\<close> bits.
  \<^item> \<open>((_ rotate_right i) t)\<close> abbreviates
    \<open>((_ rotate_right |i-1|) (concat ((_ extract 0 0) t) ((_ extract |m-1| 1) t)))\<close>: with
    \<open>r = i mod m\<close>, the low \<open>r\<close> bits of \<open>t\<close> end up above its high \<open>m - r\<close> bits.
  \<^item> The other binary functions: \<^const>\<open>smt_bv_bin\<close>.\<close>
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
      VBv w (foldl (\<lambda>x v. smt_bv_bin op w x (smt_bv_val v)) (smt_bv_val (hd vs)) (tl vs)))\<close>

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

subsection \<open>The representation condition\<close>

text \<open>Every list in the term \<open>t\<close> (the bits of a constant, the arguments of an application) has
  fewer than \<open>2^63\<close> elements.\<close>
fun smt_term_repr :: \<open>SmtTerm \<Rightarrow> bool\<close> where
  \<open>smt_term_repr (SmtTerm_BvConst bs) = (length bs < 2 ^ 63)\<close>
| \<open>smt_term_repr (SmtTerm_Fun f args) = (length args < 2 ^ 63 \<and> (\<forall>a \<in> set args. smt_term_repr a))\<close>
| \<open>smt_term_repr (SmtTerm_Def d args) = (length args < 2 ^ 63 \<and> (\<forall>a \<in> set args. smt_term_repr a))\<close>
| \<open>smt_term_repr (SmtTerm_App op args) = (length args < 2 ^ 63 \<and> (\<forall>a \<in> set args. smt_term_repr a))\<close>
| \<open>smt_term_repr _ = True\<close>

text \<open>\<open>smt_repr_ok p\<close>: every list in \<open>p\<close> has fewer than \<open>2^63\<close> elements. Rust ensures
  this for every \<^verbatim>\<open>Vec\<close> whose elements are not zero-sized, because an allocation has at most
  \<^verbatim>\<open>isize::MAX\<close> \<open>= 2^63 - 1\<close> bytes; so the condition holds for every value a Rust program can
  pass. The translation represents a \<^verbatim>\<open>Vec\<close> as a HOL list, which has no such bound, so a
  contract states it.\<close>
definition smt_repr_ok :: \<open>SmtProblem \<Rightarrow> bool\<close> where
  \<open>smt_repr_ok p \<equiv>
     length (SmtProblem_funs p) < 2 ^ 63 \<and> (\<forall>f \<in> set (SmtProblem_funs p). length (SmtFun_args f) < 2 ^ 63) \<and>
     length (SmtProblem_defs p) < 2 ^ 63 \<and>
     (\<forall>d \<in> set (SmtProblem_defs p). length (SmtDef_params d) < 2 ^ 63 \<and> smt_term_repr (SmtDef_body d)) \<and>
     length (SmtProblem_asserts p) < 2 ^ 63 \<and> (\<forall>t \<in> set (SmtProblem_asserts p). smt_term_repr t)\<close>

subsection \<open>The size of a problem\<close>

text \<open>Measures of a problem as it is written, independent of any solver. A solver states with
  them the range of problems for which it promises an answer other than \<^verbatim>\<open>Unknown\<close>.\<close>

text \<open>The number of nodes of a term. An application of a definition with parameters counts with
  the nodes of the body of the definition as well, since it stands for that body.\<close>
function smt_nodes :: \<open>SmtDef list \<Rightarrow> SmtTerm \<Rightarrow> nat\<close> where
  \<open>smt_nodes ds (SmtTerm_BoolConst b) = 1\<close>
| \<open>smt_nodes ds (SmtTerm_BvConst bs) = 1\<close>
| \<open>smt_nodes ds (SmtTerm_Param k) = 1\<close>
| \<open>smt_nodes ds (SmtTerm_Fun f args) = Suc (sum_list (map (smt_nodes ds) args))\<close>
| \<open>smt_nodes ds (SmtTerm_Def d args) =
     Suc (sum_list (map (smt_nodes ds) args)) +
     (if unat d < length ds \<and> SmtDef_params (ds ! unat d) \<noteq> []
      then smt_nodes (take (unat d) ds) (SmtDef_body (ds ! unat d)) else 0)\<close>
| \<open>smt_nodes ds (SmtTerm_App op args) = Suc (sum_list (map (smt_nodes ds) args))\<close>
  by pat_completeness auto
termination
  by (relation \<open>measures [\<lambda>(ds, _). length ds, \<lambda>(_, t). size t]\<close>)
     (auto intro: size_list_estimation' simp: less_Suc_eq_le)

text \<open>The size of a problem: the numbers of declared symbols, definitions and assertions, and the
  nodes of the assertions and of the bodies of the definitions without parameters.\<close>
definition smt_size :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>smt_size p \<equiv>
     let ds = SmtProblem_defs p in
     length (SmtProblem_funs p) + length ds + length (SmtProblem_asserts p) +
     sum_list (map (\<lambda>d. if SmtDef_params (ds ! d) = [] then smt_nodes (take d ds) (SmtDef_body (ds ! d)) else 0)
                [0..<length ds]) +
     sum_list (map (smt_nodes ds) (SmtProblem_asserts p))\<close>

text \<open>The subterms of a term, the term included.\<close>
fun smt_subterms :: \<open>SmtTerm \<Rightarrow> SmtTerm list\<close> where
  \<open>smt_subterms (SmtTerm_Fun f args) = SmtTerm_Fun f args # concat (map smt_subterms args)\<close>
| \<open>smt_subterms (SmtTerm_Def d args) = SmtTerm_Def d args # concat (map smt_subterms args)\<close>
| \<open>smt_subterms (SmtTerm_App op args) = SmtTerm_App op args # concat (map smt_subterms args)\<close>
| \<open>smt_subterms t = [t]\<close>

text \<open>The width of the sort of a term (0 if it is not a bit-vector).\<close>
definition smt_twidth :: \<open>SmtFun list \<Rightarrow> SmtDef list \<Rightarrow> SmtSort list \<Rightarrow> SmtTerm \<Rightarrow> nat\<close> where
  \<open>smt_twidth fs ds ps t \<equiv> (case smt_tsort fs ds ps t of Some s \<Rightarrow> smt_width s | None \<Rightarrow> 0)\<close>

text \<open>The widths of the subterms satisfying \<open>Q\<close> of the bodies of the definitions (over their
  parameters) and of the assertions.\<close>
definition smt_term_widths :: \<open>(SmtTerm \<Rightarrow> bool) \<Rightarrow> SmtProblem \<Rightarrow> nat set\<close> where
  \<open>smt_term_widths Q p \<equiv>
     let fs = SmtProblem_funs p in let ds = SmtProblem_defs p in
     (\<Union>d < length ds. smt_twidth fs (take d ds) (SmtDef_params (ds ! d)) `
        Set.filter Q (set (smt_subterms (SmtDef_body (ds ! d))))) \<union>
     (\<Union>t \<in> set (SmtProblem_asserts p). smt_twidth fs ds [] ` Set.filter Q (set (smt_subterms t)))\<close>

text \<open>The widths of the sorts of the declared symbols and of the definitions.\<close>
definition smt_sort_widths :: \<open>SmtProblem \<Rightarrow> nat set\<close> where
  \<open>smt_sort_widths p \<equiv>
     (\<Union>f \<in> set (SmtProblem_funs p). smt_width ` set (SmtFun_ret f # SmtFun_args f)) \<union>
     (\<Union>d \<in> set (SmtProblem_defs p). smt_width ` set (SmtDef_ret d # SmtDef_params d))\<close>

text \<open>The largest bit-vector width in a problem (0 if there is none).\<close>
definition smt_max_width :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>smt_max_width p \<equiv> Max (insert 0 (smt_sort_widths p \<union> smt_term_widths (\<lambda>_. True) p))\<close>

text \<open>Multiplication, division and remainder: the bit-vector functions whose usual circuits grow
  with the square of the width.\<close>
fun smt_mul_div :: \<open>SmtTerm \<Rightarrow> bool\<close> where
  \<open>smt_mul_div (SmtTerm_App op args) = (op \<in> {SmtOp_Bvmul, SmtOp_Bvudiv, SmtOp_Bvurem, SmtOp_Bvsdiv, SmtOp_Bvsrem, SmtOp_Bvsmod})\<close>
| \<open>smt_mul_div _ = False\<close>

text \<open>The largest width of a multiplication, division or remainder in a problem (0 if there is
  none).\<close>
definition smt_max_mul_width :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>smt_max_mul_width p \<equiv> Max (insert 0 (smt_term_widths smt_mul_div p))\<close>

end
