theory QFUF_SmtSize
  imports "QFUF_Smt.QFUF_SmtModel"
begin

section \<open>The size check of \<^verbatim>\<open>check_sat\<close>\<close>

text \<open>The Rust function \<^verbatim>\<open>uf_size\<close> computes, with additions and multiplications that saturate
  at \<open>2^63\<close>, a bound on the size of the translation of a problem. Each Rust function of the size
  check computes \<open>sat\<close> of an exact value defined here.\<close>

subsection \<open>Saturation\<close>

definition sat :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>sat x \<equiv> min x (2 ^ 63)\<close>

lemma sat_0: \<open>sat 0 = 0\<close>
  by (simp add: sat_def)

lemma word_eq_of_unat: \<open>unat x = y \<Longrightarrow> x = (word_of_nat y :: 64 word)\<close>
  by auto

lemma sat_le: \<open>sat x \<le> 2 ^ 63\<close>
  by (simp add: sat_def)

lemma sat_lt_iff: \<open>(sat x < 2 ^ 63) = (x < 2 ^ 63)\<close>
  by (simp add: sat_def min_less_iff_disj)

lemma sat_add_sat: \<open>sat (sat x + sat y) = sat (x + y)\<close>
  by (simp add: sat_def)

lemma sat_mul_sat: \<open>sat (sat x * sat y) = sat (x * y)\<close>
proof (cases \<open>x = 0 \<or> y = 0\<close>)
  case True
  then show ?thesis by (auto simp: sat_def)
next
  case False
  then have x1: \<open>1 \<le> x\<close> and y1: \<open>1 \<le> y\<close> by auto
  show ?thesis
  proof (cases \<open>x * y < 2 ^ 63\<close>)
    case True
    have xc: \<open>x < 2 ^ 63\<close> using True y1 by (metis le_less_trans mult_le_mono2 nat_mult_1_right)
    have yc: \<open>y < 2 ^ 63\<close> using True x1 by (metis le_less_trans mult_le_mono1 nat_mult_1)
    show ?thesis using True xc yc by (simp add: sat_def)
  next
    case False
    have \<open>2 ^ 63 \<le> min x (2 ^ 63) * min y (2 ^ 63)\<close>
    proof (cases \<open>x < 2 ^ 63\<close>; cases \<open>y < 2 ^ 63\<close>)
    qed (use False x1 y1 in \<open>auto simp: min_def intro: order.trans[OF _ mult_le_mono1] order.trans[OF _ mult_le_mono2]\<close>)
    then show ?thesis using False by (simp add: sat_def)
  qed
qed

lemma sat_sat: \<open>sat (sat x) = sat x\<close>
  by (simp add: sat_def)

lemma sat_add_sat_l: \<open>sat (sat x + y) = sat (x + y)\<close>
  by (metis sat_add_sat sat_sat)

lemma sat_add_sat_r: \<open>sat (x + sat y) = sat (x + y)\<close>
  by (metis sat_add_sat sat_sat)

lemma sat_1: \<open>sat (Suc 0) = Suc 0\<close>
  by (simp add: sat_def)

lemma le_div_iff_mul: \<open>0 < (a :: nat) \<Longrightarrow> (b \<le> c div a) = (a * b \<le> c)\<close>
  by (simp add: less_eq_div_iff_mult_less_eq mult.commute)

lemma ge_mul_left: \<open>1 \<le> (a :: nat) \<Longrightarrow> c \<le> b \<Longrightarrow> c \<le> a * b\<close>
  by (metis mult_le_mono nat_mult_1)

lemma ge_mul_right: \<open>1 \<le> (b :: nat) \<Longrightarrow> c \<le> a \<Longrightarrow> c \<le> a * b\<close>
  by (metis mult_le_mono nat_mult_1_right)

lemma big_mul_word:
  fixes a b :: \<open>64 word\<close>
  shows \<open>a \<noteq> 0 \<Longrightarrow> 9223372036854775808 \<le> unat b \<Longrightarrow> 9223372036854775808 \<le> unat a * unat b\<close>
    and \<open>b \<noteq> 0 \<Longrightarrow> 9223372036854775808 \<le> unat a \<Longrightarrow> 9223372036854775808 \<le> unat a * unat b\<close>
    and \<open>a \<noteq> 0 \<Longrightarrow> 9223372036854775807 div unat a < unat b \<Longrightarrow> 9223372036854775808 \<le> unat a * unat b\<close>
proof -
  show \<open>a \<noteq> 0 \<Longrightarrow> 9223372036854775808 \<le> unat b \<Longrightarrow> 9223372036854775808 \<le> unat a * unat b\<close>
    by (rule ge_mul_left) (simp_all add: Suc_le_eq unat_gt_0)
  show \<open>b \<noteq> 0 \<Longrightarrow> 9223372036854775808 \<le> unat a \<Longrightarrow> 9223372036854775808 \<le> unat a * unat b\<close>
    by (rule ge_mul_right) (simp_all add: Suc_le_eq unat_gt_0)
  assume a0: \<open>a \<noteq> 0\<close> and lt: \<open>9223372036854775807 div unat a < unat b\<close>
  have \<open>0 < unat a\<close> using a0 by (simp add: unat_gt_0)
  then have \<open>\<not> unat a * unat b \<le> 9223372036854775807\<close> using lt le_div_iff_mul[of \<open>unat a\<close> \<open>unat b\<close> 9223372036854775807] by (meson not_le)
  then show \<open>9223372036854775808 \<le> unat a * unat b\<close> by simp
qed

lemma sat_add3: \<open>sat (x + (sat a + sat b)) = sat (x + (a + b))\<close>
  by (simp add: sat_def min_def)

lemma sat_add_ss: \<open>sat (x + sat (Suc (Suc (sat c)))) = sat (x + Suc (Suc c))\<close>
  by (simp add: sat_def min_def)

lemma sat_16: \<open>sat 16 = 16\<close>
  by (simp add: sat_def)

lemma sat_2: \<open>sat 2 = 2\<close>
  by (simp add: sat_def)

subsection \<open>The exact values\<close>

text \<open>The weight of a node with \<open>k\<close> arguments (\<^verbatim>\<open>node_weight\<close>).\<close>
definition nw :: \<open>nat \<Rightarrow> nat\<close> where
  \<open>nw k \<equiv> 16 * (k + 1) ^ 2\<close>

lemma nw_sat: \<open>sat (16 * sat (sat (Suc x) * sat (Suc x))) = sat (nw x)\<close>
proof -
  have a: \<open>sat (sat (Suc x) * sat (Suc x)) = sat ((Suc x) * (Suc x))\<close> by (rule sat_mul_sat)
  have \<open>sat (16 * sat (sat (Suc x) * sat (Suc x))) = sat (sat 16 * sat (sat (Suc x) * sat (Suc x)))\<close>
    by (simp only: sat_16)
  also have \<open>\<dots> = sat (sat 16 * sat ((Suc x) * (Suc x)))\<close> by (simp only: a)
  also have \<open>\<dots> = sat (16 * ((Suc x) * (Suc x)))\<close> by (rule sat_mul_sat)
  finally show ?thesis by (simp add: nw_def power2_eq_square)
qed

text \<open>\<^verbatim>\<open>uf_count\<close> and \<^verbatim>\<open>uf_count_args\<close> without saturation, with the definitions below \<open>n\<close>
  expanded (as \<^const>\<open>tr_term_m\<close>). As in Rust, an application of a definition without
  parameters counts only its node, and one of a definition with parameters its node, its arguments
  and the body of the definition.\<close>
function (sequential) ucnt :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> SmtTerm \<Rightarrow> nat\<close>
  and ucnt_args :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> SmtTerm list \<Rightarrow> nat\<close>
  where
  \<open>ucnt p n (SmtTerm_Fun f args) = nw (length args) + ucnt_args p n args\<close>
| \<open>ucnt p n (SmtTerm_Def d args) =
     (if SmtDef_params (SmtProblem_defs p ! unat d) = [] then nw (length args)
      else nw (length args) + (ucnt_args p n args +
             (if unat d < n then ucnt p (unat d) (SmtDef_body (SmtProblem_defs p ! unat d)) else 0)))\<close>
| \<open>ucnt p n (SmtTerm_App op args) = nw (length args) + ucnt_args p n args\<close>
| \<open>ucnt p n _ = nw 0\<close>
| \<open>ucnt_args p n [] = 0\<close>
| \<open>ucnt_args p n (a # rest) = ucnt p n a + ucnt_args p n rest\<close>
  by pat_completeness auto
termination
  by (relation \<open>measures [\<lambda>x. case x of Inl (_, n, _) \<Rightarrow> n | Inr (_, n, _) \<Rightarrow> n,
                          \<lambda>x. case x of Inl (_, _, t) \<Rightarrow> size t | Inr (_, _, ts) \<Rightarrow> size_list size ts]\<close>)
     auto

text \<open>The value \<^verbatim>\<open>uf_size\<close> computes, without saturation: 16, the number of declared symbols,
  the counts of the bodies of the definitions without parameters, and the counts plus 2 of the
  assertions.\<close>
definition usize_m :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>usize_m p \<equiv>
     16 + length (SmtProblem_funs p) +
     sum_list (map (\<lambda>d. if SmtDef_params (SmtProblem_defs p ! d) = []
                         then ucnt p d (SmtDef_body (SmtProblem_defs p ! d)) else 0)
                [0..<length (SmtProblem_defs p)]) +
     sum_list (map (\<lambda>t. ucnt p (length (SmtProblem_defs p)) t + 2) (SmtProblem_asserts p))\<close>

text \<open>The definitions part of \<^const>\<open>usize_m\<close> for the first \<open>d\<close> definitions.\<close>
definition dsum :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>dsum p d \<equiv> sum_list (map (\<lambda>i. if SmtDef_params (SmtProblem_defs p ! i) = []
                                   then ucnt p i (SmtDef_body (SmtProblem_defs p ! i)) else 0) [0..<d])\<close>

lemma dsum_0: \<open>dsum p 0 = 0\<close>
  by (simp add: dsum_def)

lemma dsum_Suc: \<open>dsum p (Suc d) = dsum p d +
  (if SmtDef_params (SmtProblem_defs p ! d) = [] then ucnt p d (SmtDef_body (SmtProblem_defs p ! d)) else 0)\<close>
  by (simp add: dsum_def)

lemma usize_dsum: \<open>usize_m p = 16 + length (SmtProblem_funs p) + dsum p (length (SmtProblem_defs p)) +
  sum_list (map (\<lambda>t. ucnt p (length (SmtProblem_defs p)) t + 2) (SmtProblem_asserts p))\<close>
  by (simp add: usize_m_def dsum_def)

subsection \<open>The precondition of the counting\<close>

text \<open>\<open>dok n F t\<close>: every definition \<open>t\<close> applies is below \<open>n\<close>, and every argument list in \<open>t\<close> has
  fewer than \<open>2^63\<close> and at most \<open>F\<close> elements (\<open>F\<close> is the fuel, which bounds the iterations of
  a loop).\<close>
fun dok :: \<open>nat \<Rightarrow> nat \<Rightarrow> SmtTerm \<Rightarrow> bool\<close> where
  \<open>dok n F (SmtTerm_Fun f args) = (length args < 2 ^ 63 \<and> length args \<le> F \<and> (\<forall>a \<in> set args. dok n F a))\<close>
| \<open>dok n F (SmtTerm_Def d args) =
     (unat d < n \<and> length args < 2 ^ 63 \<and> length args \<le> F \<and> (\<forall>a \<in> set args. dok n F a))\<close>
| \<open>dok n F (SmtTerm_App op args) = (length args < 2 ^ 63 \<and> length args \<le> F \<and> (\<forall>a \<in> set args. dok n F a))\<close>
| \<open>dok n F _ = True\<close>

text \<open>Every definition has fewer than \<open>2^64\<close> parameters (so that \<^verbatim>\<open>len\<close> reads their
  number exactly).\<close>
definition params_ok :: \<open>SmtProblem \<Rightarrow> bool\<close> where
  \<open>params_ok p \<equiv> \<forall>e \<in> set (SmtProblem_defs p). length (SmtDef_params e) < 2 ^ 64\<close>

lemma params_ok_nth: \<open>params_ok p \<Longrightarrow> d < length (SmtProblem_defs p) \<Longrightarrow>
  ((word_of_nat (length (SmtDef_params (SmtProblem_defs p ! d))) :: 64 word) = 0) = (SmtDef_params (SmtProblem_defs p ! d) = [])\<close>
proof -
  assume a: \<open>params_ok p\<close> and b: \<open>d < length (SmtProblem_defs p)\<close>
  have L: \<open>length (SmtDef_params (SmtProblem_defs p ! d)) < 2 ^ 64\<close> using a b by (simp add: params_ok_def)
  show ?thesis using L by (auto simp: word_of_nat_eq_0_iff dest: nat_dvd_not_less)
qed

lemma nth_size_lt: \<open>i < length ts \<Longrightarrow> size (ts ! i) < size_list size ts\<close>
proof (induction ts arbitrary: i)
  case Nil
  then show ?case by simp
next
  case (Cons a ts)
  then show ?case by (cases i) fastforce+
qed

lemma nth_size_le: \<open>i < length ts \<Longrightarrow> size_list size ts \<le> k \<Longrightarrow> Suc (size (ts ! i)) \<le> k\<close>
  using nth_size_lt[of i ts] by simp

lemma unat_inc: \<open>unat (i :: 64 word) < n \<Longrightarrow> n < 2 ^ 64 \<Longrightarrow> unat (i + 1) = Suc (unat i)\<close>
  by (rule unat_plus_one_of_less_bound) simp_all

lemma ucnt_args_sum: \<open>ucnt_args p n ts = sum_list (map (ucnt p n) ts)\<close>
  by (induction ts) auto

lemma ucnt_args_take_Suc:
  \<open>i < length ts \<Longrightarrow> ucnt_args p n (take (Suc i) ts) = ucnt_args p n (take i ts) + ucnt p n (ts ! i)\<close>
  by (simp add: ucnt_args_sum take_Suc_conv_app_nth)

text \<open>The table \<^verbatim>\<open>dc\<close> of \<^verbatim>\<open>uf_size\<close> for the first \<open>n\<close> definitions: for a definition with
  parameters, the count of its body where it is expanded.\<close>
definition dcv :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>dcv p d \<equiv> if SmtDef_params (SmtProblem_defs p ! d) = [] then 0 else sat (ucnt p d (SmtDef_body (SmtProblem_defs p ! d)))\<close>

definition dcw :: \<open>SmtProblem \<Rightarrow> nat \<Rightarrow> 64 word list\<close> where
  \<open>dcw p n \<equiv> map (\<lambda>d. word_of_nat (dcv p d)) [0..<n]\<close>

lemma dcv_le: \<open>dcv p d \<le> 2 ^ 63\<close>
  by (simp add: dcv_def sat_def min_le_iff_disj)

lemma unat_dcw: \<open>d < n \<Longrightarrow> unat (dcw p n ! d) = dcv p d\<close>
  using dcv_le[of p d] by (simp add: dcw_def unat_of_nat_eq)

lemma dcw_Suc: \<open>dcw p (Suc d) = dcw p d @ [word_of_nat (dcv p d)]\<close>
  by (simp add: dcw_def)

lemma dcw_0: \<open>dcw p 0 = []\<close>
  by (simp add: dcw_def)

lemma dc_unat: \<open>dc = dcw p (length dc) \<Longrightarrow> d < length dc \<Longrightarrow> unat (dc ! d) = dcv p d\<close>
  by (metis unat_dcw)

lemma length_dcw: \<open>length (dcw p n) = n\<close>
  by (simp add: dcw_def)

text \<open>What \<^verbatim>\<open>uf_size\<close> needs: the definitions refer to earlier ones and the assertions to
  definitions; every term and list is within the fuel and below \<open>2^63\<close>.\<close>
definition usize_pre :: \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> bool\<close> where
  \<open>usize_pre F p \<equiv>
     let ds = SmtProblem_defs p in
     params_ok p \<and> length (SmtProblem_funs p) < 2 ^ 63 \<and> length ds < 2 ^ 63 \<and> length ds \<le> F \<and>
     length (SmtProblem_asserts p) < 2 ^ 63 \<and> length (SmtProblem_asserts p) \<le> F \<and>
     (\<forall>d < length ds. dok d F (SmtDef_body (ds ! d)) \<and> Suc (size (SmtDef_body (ds ! d))) \<le> F) \<and>
     (\<forall>t \<in> set (SmtProblem_asserts p). dok (length ds) F t \<and> Suc (size t) \<le> F)\<close>

subsection \<open>The precondition holds for well-sorted problems\<close>

text \<open>A bound on the fuel that \<^verbatim>\<open>uf_size\<close> needs: the numbers of definitions and assertions and the
  sizes of the bodies of the definitions and of the assertions.\<close>
definition usize_fuel :: \<open>SmtProblem \<Rightarrow> nat\<close> where
  \<open>usize_fuel p \<equiv>
     Suc (length (SmtProblem_defs p) + length (SmtProblem_asserts p) +
          sum_list (map (\<lambda>e. size (SmtDef_body e)) (SmtProblem_defs p)) +
          sum_list (map size (SmtProblem_asserts p)))\<close>

lemma map_eq_Some_ne: \<open>map f xs = map Some ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> f x \<noteq> None\<close>
proof -
  assume e: \<open>map f xs = map Some ys\<close> and x: \<open>x \<in> set xs\<close>
  have \<open>f x \<in> set (map Some ys)\<close> using x e[symmetric] by (metis image_eqI list.set_map)
  then show ?thesis by auto
qed

lemma arg_size_le: \<open>a \<in> set args \<Longrightarrow> size a \<le> sum_list (map size args)\<close>
  by (rule member_le_sum_list) auto

lemma tsort_dok:
  \<open>smt_tsort fs ds ps t \<noteq> None \<Longrightarrow> smt_term_repr t \<Longrightarrow> size t \<le> F \<Longrightarrow> dok (length ds) F t\<close>
proof (induction t)
  case (SmtTerm_Fun f args)
  have s: \<open>size a \<le> F\<close> if \<open>a \<in> set args\<close> for a
    using SmtTerm_Fun.prems(3) arg_size_le[OF that] by (simp add: size_list_conv_sum_list)
  have t: \<open>smt_tsort fs ds ps a \<noteq> None\<close> if \<open>a \<in> set args\<close> for a
    using SmtTerm_Fun.prems(1) map_eq_Some_ne that by (auto split: if_splits)
  show ?case using SmtTerm_Fun s t by (auto simp: size_list_conv_sum_list)
next
  case (SmtTerm_Def d args)
  have s: \<open>size a \<le> F\<close> if \<open>a \<in> set args\<close> for a
    using SmtTerm_Def.prems(3) arg_size_le[OF that] by (simp add: size_list_conv_sum_list)
  have t: \<open>smt_tsort fs ds ps a \<noteq> None\<close> if \<open>a \<in> set args\<close> for a
    using SmtTerm_Def.prems(1) map_eq_Some_ne that by (auto split: if_splits)
  have d: \<open>unat d < length ds\<close> using SmtTerm_Def.prems(1) by (auto split: if_splits)
  show ?case using SmtTerm_Def s t d by (auto simp: size_list_conv_sum_list)
next
  case (SmtTerm_App op args)
  have s: \<open>size a \<le> F\<close> if \<open>a \<in> set args\<close> for a
    using SmtTerm_App.prems(3) arg_size_le[OF that] by (simp add: size_list_conv_sum_list)
  have t: \<open>smt_tsort fs ds ps a \<noteq> None\<close> if \<open>a \<in> set args\<close> for a
  proof -
    have n: \<open>None \<notin> set (map (smt_tsort fs ds ps) args)\<close> using SmtTerm_App.prems(1) by (auto split: if_splits)
    show ?thesis using n that by (metis imageI list.set_map)
  qed
  show ?case using SmtTerm_App s t by (auto simp: size_list_conv_sum_list)
qed auto

lemma usize_pre_wf:
  assumes \<open>smt_wf p\<close> \<open>smt_repr_ok p\<close> \<open>usize_fuel p \<le> F\<close>
  shows \<open>usize_pre F p\<close>
proof -
  have W: \<open>smt_wf p\<close> and R: \<open>smt_repr_ok p\<close> and B: \<open>usize_fuel p \<le> F\<close> using assms by simp_all
  have D: \<open>\<forall>d < length (SmtProblem_defs p).
              dok d F (SmtDef_body (SmtProblem_defs p ! d)) \<and> Suc (size (SmtDef_body (SmtProblem_defs p ! d))) \<le> F\<close>
  proof (intro allI impI)
    fix d assume d: \<open>d < length (SmtProblem_defs p)\<close>
    have m: \<open>SmtProblem_defs p ! d \<in> set (SmtProblem_defs p)\<close> using d by simp
    have \<open>size (SmtDef_body (SmtProblem_defs p ! d)) \<le> sum_list (map (\<lambda>e. size (SmtDef_body e)) (SmtProblem_defs p))\<close>
      using m by (auto intro!: member_le_sum_list)
    then have s: \<open>Suc (size (SmtDef_body (SmtProblem_defs p ! d))) \<le> F\<close> using B by (simp add: usize_fuel_def)
    have ts: \<open>smt_tsort (SmtProblem_funs p) (take d (SmtProblem_defs p)) (SmtDef_params (SmtProblem_defs p ! d))
                (SmtDef_body (SmtProblem_defs p ! d)) = Some (SmtDef_ret (SmtProblem_defs p ! d))\<close>
      using W d by (simp add: smt_wf_def Let_def)
    have r: \<open>smt_term_repr (SmtDef_body (SmtProblem_defs p ! d))\<close> using R m by (simp add: smt_repr_ok_def)
    have n: \<open>smt_tsort (SmtProblem_funs p) (take d (SmtProblem_defs p)) (SmtDef_params (SmtProblem_defs p ! d))
                (SmtDef_body (SmtProblem_defs p ! d)) \<noteq> None\<close> using ts by simp
    have \<open>dok (length (take d (SmtProblem_defs p))) F (SmtDef_body (SmtProblem_defs p ! d))\<close>
      using tsort_dok[OF n r] s by simp
    then show \<open>dok d F (SmtDef_body (SmtProblem_defs p ! d)) \<and> Suc (size (SmtDef_body (SmtProblem_defs p ! d))) \<le> F\<close>
      using d s by (simp add: min_def)
  qed
  have A: \<open>\<forall>t \<in> set (SmtProblem_asserts p). dok (length (SmtProblem_defs p)) F t \<and> Suc (size t) \<le> F\<close>
  proof
    fix t assume m: \<open>t \<in> set (SmtProblem_asserts p)\<close>
    have \<open>size t \<le> sum_list (map size (SmtProblem_asserts p))\<close>
      using m by (auto intro!: member_le_sum_list)
    then have s: \<open>Suc (size t) \<le> F\<close> using B by (simp add: usize_fuel_def)
    have ts: \<open>smt_tsort (SmtProblem_funs p) (SmtProblem_defs p) [] t = Some SmtSort_Bool\<close>
      using W m by (simp add: smt_wf_def Let_def)
    have r: \<open>smt_term_repr t\<close> using R m by (simp add: smt_repr_ok_def)
    have n: \<open>smt_tsort (SmtProblem_funs p) (SmtProblem_defs p) [] t \<noteq> None\<close> using ts by simp
    show \<open>dok (length (SmtProblem_defs p)) F t \<and> Suc (size t) \<le> F\<close> using tsort_dok[OF n r] s by simp
  qed
  have P: \<open>params_ok p\<close> using R by (auto simp: params_ok_def smt_repr_ok_def)
  show ?thesis using D A P R B by (simp add: usize_pre_def smt_repr_ok_def usize_fuel_def)
qed

lemma unat_add_s: \<open>unat a + unat b < 2 ^ 64 \<Longrightarrow> unat (a + b) = unat a + unat (b :: 64 word)\<close>
  using unat_add_lem[of a b] by simp

lemma unat_mult_s: \<open>unat a * unat b < 2 ^ 64 \<Longrightarrow> unat (a * b) = unat a * unat (b :: 64 word)\<close>
  using unat_mult_lem[of a b] by simp

context QFUF_ctx
begin

subsection \<open>Saturating arithmetic\<close>

definition cap_contract :: \<open>('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>cap_contract \<equiv>
     make_function_contract can_alloc_reference (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = 2 ^ 63\<rangle>)\<close>

lemma cap_spec [crush_specs]:
  shows \<open>\<Gamma>; cap \<Turnstile>\<^sub>F cap_contract\<close>
  by (crush_boot f: cap_def contract: cap_contract_def) crush_base

definition sat_add_contract :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>sat_add_contract a b \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat (unat a + unat b)\<rangle>)\<close>

lemma sat_add_spec [crush_specs]:
  shows \<open>\<Gamma>; sat_add a b \<Turnstile>\<^sub>F sat_add_contract a b\<close>
  apply (crush_boot f: sat_add_def contract: sat_add_contract_def)
  apply (crush_base simp add: sat_def word_le_nat_alt word_less_nat_alt unat_sub)
  apply (rule unat_add_s; simp)
  done

definition sat_mul_contract :: \<open>64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>sat_mul_contract a b \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat (unat a * unat b)\<rangle>)\<close>

lemma sat_mul_spec [crush_specs]:
  shows \<open>\<Gamma>; sat_mul a b \<Turnstile>\<^sub>F sat_mul_contract a b\<close>
  apply (crush_boot f: sat_mul_def contract: sat_mul_contract_def)
  apply (crush_base simp add: sat_def word_le_nat_alt word_less_nat_alt unat_sub unat_div)
  apply (auto simp: le_div_iff_mul unat_gt_0 not_less min_def unat_mult_s Suc_le_eq
      intro: antisym big_mul_word)
  done

definition node_weight_contract :: \<open>64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>node_weight_contract k \<equiv>
     make_function_contract can_alloc_reference
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat (nw (unat k))\<rangle>)\<close>

lemma node_weight_spec [crush_specs]:
  shows \<open>\<Gamma>; node_weight k \<Turnstile>\<^sub>F node_weight_contract k\<close>
  apply (crush_boot f: node_weight_def contract: node_weight_contract_def)
  apply (crush_base)
  apply (simp add: nw_sat)
  done

subsection \<open>\<^verbatim>\<open>uf_count\<close> and \<^verbatim>\<open>uf_count_args\<close>\<close>

text \<open>The \<open>k\<close>-th unfolding of the mutual recursion: its precondition requires the recursion depth
  to be at most \<open>k\<close>. The table \<open>dc\<close> is \<^const>\<open>dcw\<close> of its length \<open>n\<close>, and definitions are expanded
  below \<open>n\<close>.\<close>
definition uf_count_contract :: \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> 64 word list \<Rightarrow> SmtTerm \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>uf_count_contract k p dc t \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>Suc (size t) \<le> k \<and> dc = dcw p (length dc) \<and> length dc \<le> length (SmtProblem_defs p) \<and>
         params_ok p \<and> dok (length dc) urust_fuel t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat (ucnt p (length dc) t)\<rangle>)\<close>

definition uf_count_args_contract :: \<open>nat \<Rightarrow> SmtProblem \<Rightarrow> 64 word list \<Rightarrow> SmtTerm list \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>uf_count_args_contract k p dc ts \<equiv>
     make_function_contract
       (can_alloc_reference \<star>
        \<langle>Suc (size_list size ts) \<le> k \<and> dc = dcw p (length dc) \<and> length dc \<le> length (SmtProblem_defs p) \<and>
         params_ok p \<and> length ts < 2 ^ 63 \<and> length ts \<le> urust_fuel \<and> (\<forall>a \<in> set ts. dok (length dc) urust_fuel a)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat (ucnt_args p (length dc) ts)\<rangle>)\<close>

lemma uf_count_step_spec:
  assumes IH1: \<open>\<And>p dc t. \<Gamma>; f p dc t \<Turnstile>\<^sub>F uf_count_contract k p dc t\<close>
      and IH2: \<open>\<And>p dc ts. \<Gamma>; g p dc ts \<Turnstile>\<^sub>F uf_count_args_contract k p dc ts\<close>
  shows \<open>\<Gamma>; fst (uf_count_rec_step (f, g)) p dc t \<Turnstile>\<^sub>F uf_count_contract (Suc k) p dc t\<close>
    and \<open>\<Gamma>; snd (uf_count_rec_step (f, g)) p dc ts \<Turnstile>\<^sub>F uf_count_args_contract (Suc k) p dc ts\<close>
proof -
  show \<open>\<Gamma>; fst (uf_count_rec_step (f, g)) p dc t \<Turnstile>\<^sub>F uf_count_contract (Suc k) p dc t\<close>
  proof (cases t)
    case (SmtTerm_Fun i args)
    show ?thesis unfolding SmtTerm_Fun uf_count_rec_step_def prod.case fst_conv
      apply (crush_boot contract: uf_count_contract_def)
      apply (crush_base specs add: IH2 contracts add: uf_count_args_contract_def
          simp add: sat_add_sat unat_of_nat_eq)
      done
  next
    case (SmtTerm_Def d args)
    show ?thesis unfolding SmtTerm_Def uf_count_rec_step_def prod.case fst_conv
      apply (crush_boot contract: uf_count_contract_def)
      apply (crush_base specs add: IH2 contracts add: uf_count_args_contract_def
          simp add: sat_add_sat unat_of_nat_eq)
      apply (auto simp: dc_unat dcv_def sat_add_sat params_ok_nth sat_add3)
      done
  next
    case (SmtTerm_App op args)
    show ?thesis unfolding SmtTerm_App uf_count_rec_step_def prod.case fst_conv
      apply (crush_boot contract: uf_count_contract_def)
      apply (crush_base specs add: IH2 contracts add: uf_count_args_contract_def
          simp add: sat_add_sat unat_of_nat_eq)
      done
  next
    case (SmtTerm_BoolConst b)
    show ?thesis unfolding SmtTerm_BoolConst uf_count_rec_step_def prod.case fst_conv
      apply (crush_boot contract: uf_count_contract_def)
      apply (crush_base)
      done
  next
    case (SmtTerm_BvConst bs)
    show ?thesis unfolding SmtTerm_BvConst uf_count_rec_step_def prod.case fst_conv
      apply (crush_boot contract: uf_count_contract_def)
      apply (crush_base)
      done
  next
    case (SmtTerm_Param i)
    show ?thesis unfolding SmtTerm_Param uf_count_rec_step_def prod.case fst_conv
      apply (crush_boot contract: uf_count_contract_def)
      apply (crush_base)
      done
  qed
  show \<open>\<Gamma>; snd (uf_count_rec_step (f, g)) p dc ts \<Turnstile>\<^sub>F uf_count_args_contract (Suc k) p dc ts\<close>
    unfolding uf_count_rec_step_def prod.case snd_conv
    apply (crush_boot contract: uf_count_args_contract_def)
    apply (crush_base)
    subgoal for n_ref i_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>j. \<Squnion>gn n gi i. n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
                 \<langle>unat i \<le> length ts \<and> unat n = sat (ucnt_args p (length dc) (take (unat i) ts)) \<and>
                  length ts - unat i \<le> j\<rangle>\<close> and
          INV'=\<open>\<lambda>j. \<Squnion>gn n gi i. n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> i_ref \<mapsto>\<langle>\<top>\<rangle> gi\<down>i \<star> can_alloc_reference \<star>
                 \<langle>unat i < length ts \<and> unat n = sat (ucnt_args p (length dc) (take (unat i) ts)) \<and>
                  length ts - unat i \<le> Suc j\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base specs add: IH1 contracts add: uf_count_contract_def
          simp add: word_less_nat_alt unat_inc ucnt_args_take_Suc sat_add_sat)
      apply (auto simp: unat_of_nat_eq sat_0 intro: nth_size_le)
      done
    done
qed

lemma uf_count_rec_spec:
  shows \<open>(\<forall>p dc t. \<Gamma>; fst ((uf_count_rec_step ^^ k) h) p dc t \<Turnstile>\<^sub>F uf_count_contract k p dc t) \<and>
         (\<forall>p dc ts. \<Gamma>; snd ((uf_count_rec_step ^^ k) h) p dc ts \<Turnstile>\<^sub>F uf_count_args_contract k p dc ts)\<close>
proof (induction k)
  case 0
  show ?case
    apply (intro conjI allI)
     apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: uf_count_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: uf_count_args_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  obtain f g where fg: \<open>(uf_count_rec_step ^^ k) h = (f, g)\<close> by (cases \<open>(uf_count_rec_step ^^ k) h\<close>)
  show ?case
    using uf_count_step_spec[where f=f and g=g and k=k] Suc.IH unfolding funpow.simps(2) comp_def fg by simp
qed

lemma uf_count_spec [crush_specs]:
  shows \<open>\<Gamma>; uf_count p dc t \<Turnstile>\<^sub>F uf_count_contract urust_fuel p dc t\<close>
  unfolding uf_count_def using uf_count_rec_spec by blast

lemma uf_count_args_spec [crush_specs]:
  shows \<open>\<Gamma>; uf_count_args p dc ts \<Turnstile>\<^sub>F uf_count_args_contract urust_fuel p dc ts\<close>
  unfolding uf_count_args_def using uf_count_rec_spec by blast

subsection \<open>\<^verbatim>\<open>uf_size\<close>\<close>

definition uf_size_contract :: \<open>SmtProblem \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>uf_size_contract p \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>usize_pre urust_fuel p\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat (usize_m p)\<rangle>)\<close>

lemma uf_size_spec [crush_specs]:
  shows \<open>\<Gamma>; uf_size p \<Turnstile>\<^sub>F uf_size_contract p\<close>
  apply (crush_boot f: uf_size_def contract: uf_size_contract_def)
  apply (crush_base simp add: usize_pre_def Let_def)
  subgoal for dc_ref n0 n_ref d_ref
    apply (ucincl_discharge\<open>
      rule_tac
        INV=\<open>\<lambda>j. \<Squnion>gc c gn n gd d. dc_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star>
               can_alloc_reference \<star>
               \<langle>unat d \<le> length (SmtProblem_defs p) \<and> c = dcw p (unat d) \<and>
                unat n = sat (16 + length (SmtProblem_funs p) + dsum p (unat d)) \<and>
                length (SmtProblem_defs p) - unat d \<le> j\<rangle>\<close> and
        INV'=\<open>\<lambda>j. \<Squnion>gc c gn n gd d. dc_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>c \<star> n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> d_ref \<mapsto>\<langle>\<top>\<rangle> gd\<down>d \<star>
               can_alloc_reference \<star>
               \<langle>unat d < length (SmtProblem_defs p) \<and> c = dcw p (unat d) \<and>
                unat n = sat (16 + length (SmtProblem_funs p) + dsum p (unat d)) \<and>
                length (SmtProblem_defs p) - unat d \<le> Suc j\<rangle>\<close> and
        \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
        \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_bounded_while_framedI\<close>)
    apply (crush_base inline: vec_push_def contracts add: uf_count_contract_def
        simp add: word_less_nat_alt unat_inc dsum_Suc dsum_0 dcw_Suc dcw_0 length_dcw sat_add_sat
          unat_of_nat_eq params_ok_nth sat_0)
    prefer 4
    subgoal for gc gn n gd d j_ref
      apply (ucincl_discharge\<open>
        rule_tac
          INV=\<open>\<lambda>j. \<Squnion>gc gn n gj jj. dc_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>dcw p (length (SmtProblem_defs p)) \<star>
                 n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>jj \<star> can_alloc_reference \<star>
                 \<langle>unat jj \<le> length (SmtProblem_asserts p) \<and>
                  unat n = sat (16 + length (SmtProblem_funs p) + dsum p (length (SmtProblem_defs p)) +
                     sum_list (map (\<lambda>t. ucnt p (length (SmtProblem_defs p)) t + 2)
                                (take (unat jj) (SmtProblem_asserts p)))) \<and>
                  length (SmtProblem_asserts p) - unat jj \<le> j\<rangle>\<close> and
          INV'=\<open>\<lambda>j. \<Squnion>gc gn n gj jj. dc_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>dcw p (length (SmtProblem_defs p)) \<star>
                 n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star> j_ref \<mapsto>\<langle>\<top>\<rangle> gj\<down>jj \<star> can_alloc_reference \<star>
                 \<langle>unat jj < length (SmtProblem_asserts p) \<and>
                  unat n = sat (16 + length (SmtProblem_funs p) + dsum p (length (SmtProblem_defs p)) +
                     sum_list (map (\<lambda>t. ucnt p (length (SmtProblem_defs p)) t + 2)
                                (take (unat jj) (SmtProblem_asserts p)))) \<and>
                  length (SmtProblem_asserts p) - unat jj \<le> Suc j\<rangle>\<close> and
          \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close> and
          \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_bounded_while_framedI\<close>)
      apply (crush_base contracts add: uf_count_contract_def
          simp add: word_less_nat_alt unat_inc length_dcw unat_of_nat_eq sat_add_sat sat_add_sat_l
            take_Suc_conv_app_nth usize_dsum)
      apply (simp only: sat_add_ss)
      apply (rule arg_cong[where f=sat])
      apply linarith
      done
    apply (auto intro: word_eq_of_unat simp: dcv_def add.assoc)
    done
  done

end

end
