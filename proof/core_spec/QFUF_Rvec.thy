theory QFUF_Rvec
  imports "QFUF_Spec.QFUF_Spec"
begin

section \<open>Vectors as lists\<close>

text \<open>
  The translation represents every \<^verbatim>\<open>Vec<T>\<close> as a value of \<^typ>\<open>'a rvec\<close> (AutoCorrode's
  \<^verbatim>\<open>StdLib_Vec\<close>): its elements \<^const>\<open>rvec_elems\<close>, its capacity and the layout of
  \<open>T\<close>. The proofs reason about the elements only. This theory is the bridge:
  \<^item> a list view of every field of type \<^typ>\<open>'a rvec\<close>, named after the field with the suffix
    \<open>_l\<close> (an abbreviation, so \<open>Problem_terms_l p\<close> is \<open>rvec_elems (Problem_terms p)\<close>, the form in
    which the generated code reads the field);
  \<^item> simplification rules that turn the operations that create or grow a vector (\<^verbatim>\<open>vec![x; n]\<close>,
    \<^verbatim>\<open>to_vec\<close>, \<^verbatim>\<open>clone\<close>, \<^verbatim>\<open>push\<close>) into operations on its elements. Growing a vector
    panics when the capacity would exceed its bound (\<^const>\<open>rvec_cap_max\<close>); for the element
    layouts of this solver the bound is at least \<open>2^57\<close>, so a vector with fewer than \<open>2^56\<close>
    elements can grow by one without a panic, whatever its capacity.
\<close>

subsection \<open>List views of the fields\<close>

abbreviation \<open>Term_args_l t \<equiv> rvec_elems (Term_args t)\<close>
abbreviation \<open>Clause_lits_l c \<equiv> rvec_elems (Clause_lits c)\<close>
abbreviation \<open>Problem_terms_l p \<equiv> rvec_elems (Problem_terms p)\<close>
abbreviation \<open>Problem_atoms_l p \<equiv> rvec_elems (Problem_atoms p)\<close>
abbreviation \<open>Problem_clauses_l p \<equiv> rvec_elems (Problem_clauses p)\<close>
abbreviation \<open>Entry_args_l e \<equiv> rvec_elems (Entry_args e)\<close>
abbreviation \<open>Model_entries_l m \<equiv> rvec_elems (Model_entries m)\<close>
abbreviation \<open>Tr_terms_l r \<equiv> rvec_elems (Tr_terms r)\<close>
abbreviation \<open>Tr_atoms_l r \<equiv> rvec_elems (Tr_atoms r)\<close>
abbreviation \<open>Tr_clauses_l r \<equiv> rvec_elems (Tr_clauses r)\<close>
abbreviation \<open>SmtFun_args_l f \<equiv> rvec_elems (SmtFun_args f)\<close>
abbreviation \<open>SmtDef_params_l d \<equiv> rvec_elems (SmtDef_params d)\<close>
abbreviation \<open>SmtProblem_funs_l p \<equiv> rvec_elems (SmtProblem_funs p)\<close>
abbreviation \<open>SmtProblem_defs_l p \<equiv> rvec_elems (SmtProblem_defs p)\<close>
abbreviation \<open>SmtProblem_asserts_l p \<equiv> rvec_elems (SmtProblem_asserts p)\<close>
abbreviation \<open>SmtEntry_args_l e \<equiv> rvec_elems (SmtEntry_args e)\<close>
abbreviation \<open>SmtInterp_entries_l t \<equiv> rvec_elems (SmtInterp_entries t)\<close>
abbreviation \<open>SmtModel_domains_l m \<equiv> rvec_elems (SmtModel_domains m)\<close>
abbreviation \<open>SmtModel_funs_l m \<equiv> rvec_elems (SmtModel_funs m)\<close>

subsection \<open>The capacity bound of the layouts\<close>

text \<open>Every element type of this solver has a size of at most 48 bytes and an alignment of at
  most 8; the bound on the capacity is then at least \<open>2^57\<close>.\<close>
lemma rvec_cap_max_ge:
  assumes \<open>0 < layout_size l\<close> \<open>layout_size l \<le> 48\<close> \<open>layout_align l \<le> 8\<close>
  shows \<open>2 ^ 57 \<le> rvec_cap_max l\<close>
proof -
  have \<open>2 ^ 57 * layout_size l \<le> isize_max - (layout_align l - 1)\<close>
  proof -
    have \<open>(2::nat) ^ 57 * layout_size l \<le> 2 ^ 57 * 48\<close>
      using assms(2) by simp
    also have \<open>\<dots> \<le> isize_max - (layout_align l - 1)\<close>
      using assms(3) by (simp add: isize_max_def)
    finally show ?thesis .
  qed
  then show ?thesis
    using assms(1) by (simp add: rvec_cap_max_def less_eq_div_iff_mult_less_eq)
qed

lemma rvec_cap_max_make [simp]:
  \<open>0 < s \<Longrightarrow> s \<le> 48 \<Longrightarrow> a \<le> 8 \<Longrightarrow> 2 ^ 57 \<le> rvec_cap_max (make_elem_layout s a)\<close>
  by (rule rvec_cap_max_ge) simp_all

text \<open>A vector of fewer than \<open>2^56\<close> elements can be created (\<^verbatim>\<open>vec![x; n]\<close>, \<^verbatim>\<open>to_vec\<close>).\<close>
lemma rvec_cap_max_make_le [simp]:
  \<open>n < 2 ^ 56 \<Longrightarrow> 0 < s \<Longrightarrow> s \<le> 48 \<Longrightarrow> a \<le> 8 \<Longrightarrow> n \<le> rvec_cap_max (make_elem_layout s a)\<close>
  by (rule order.trans[OF _ rvec_cap_max_make[of s a]]) simp_all

subsection \<open>Creating a vector\<close>

lemma rvec_from_elem_val_eq_Some [simp]:
  \<open>rvec_from_elem_val l x n = Some r \<longleftrightarrow>
     n \<le> rvec_cap_max l \<and> r = rvec_make l (replicate n x) (rvec_alloc_cap l n)\<close>
  by (auto simp add: rvec_from_elem_val_def)

lemma rvec_alloc_val_eq_Some [simp]:
  \<open>rvec_alloc_val l xs = Some r \<longleftrightarrow>
     length xs \<le> rvec_cap_max l \<and> r = rvec_make l xs (rvec_alloc_cap l (length xs))\<close>
  by (auto simp add: rvec_alloc_val_def)

lemma rvec_from_list_val_components [simp]:
  \<open>rvec_elems (rvec_from_list_val l xs) = xs\<close>
  \<open>rvec_layout (rvec_from_list_val l xs) = l\<close>
  by (simp_all add: rvec_from_list_val_def)

lemma rvec_clone_val_components [simp]:
  \<open>rvec_elems (rvec_clone_val v) = rvec_elems v\<close>
  \<open>rvec_layout (rvec_clone_val v) = rvec_layout v\<close>
  by (simp_all add: rvec_clone_val_def)

subsection \<open>Updating the elements\<close>

text \<open>A write through \<^const>\<open>rvec_elems_focus\<close> (an assignment to an element) updates the elements
  and keeps the capacity and the layout.\<close>
lemma rvec_elems_focus_modify [simp]:
  \<open>focus_modify rvec_elems_focus f v = update_rvec_elems f v\<close>
  by (simp add: focus_modify_def' rvec_elems_focus_components rvec.expand)

subsection \<open>Growing a vector\<close>

text \<open>Appending to a vector does not panic if twice its new length is within the bound, whatever
  its capacity: the amortised growth happens only when the capacity is below the new length, and
  gives at most twice the old capacity, the new length, or the smallest non-zero capacity.\<close>
lemma rvec_reserve_val_not_None_len:
  assumes \<open>2 * (rvec_length v + n) \<le> rvec_cap_max (rvec_layout v)\<close>
      and \<open>8 \<le> rvec_cap_max (rvec_layout v)\<close>
  shows \<open>rvec_reserve_val v n \<noteq> None\<close>
proof -
  let ?l = \<open>rvec_layout v\<close> and ?c = \<open>rvec_cap v\<close> and ?m = \<open>rvec_length v + n\<close>
  have \<open>rvec_grow_cap ?l ?c ?m \<le> rvec_cap_max ?l\<close> if \<open>?c < ?m\<close>
  proof -
    have \<open>rvec_min_non_zero_cap ?l \<le> 8\<close>
      by (simp add: rvec_min_non_zero_cap_def)
    then have \<open>max (2 * ?c) (max ?m (rvec_min_non_zero_cap ?l)) \<le> rvec_cap_max ?l\<close>
      using assms that by auto
    then show ?thesis
      using rvec_grow_cap_bounds(2)[of ?l ?c ?m] by linarith
  qed
  then show ?thesis
    by (auto simp add: rvec_reserve_val_def Let_def)
qed

lemma rvec_append_val_not_None [simp]:
  assumes \<open>rvec_length v + length xs < 2 ^ 56\<close> and \<open>2 ^ 57 \<le> rvec_cap_max (rvec_layout v)\<close>
  shows \<open>rvec_append_val v xs \<noteq> None\<close>
  using assms rvec_reserve_val_not_None_len[of v \<open>length xs\<close>]
  by (simp add: rvec_append_val_None_iff)

lemma rvec_append_val_components [simp]:
  assumes \<open>rvec_append_val v xs \<noteq> None\<close>
  shows \<open>rvec_elems (the (rvec_append_val v xs)) = rvec_elems v @ xs\<close>
    and \<open>rvec_layout (the (rvec_append_val v xs)) = rvec_layout v\<close>
  using assms
  by (auto simp add: rvec_append_val_def rvec_reserve_val_def Let_def split: if_splits)

end
