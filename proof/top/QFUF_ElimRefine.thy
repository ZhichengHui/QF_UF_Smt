theory QFUF_ElimRefine
  imports QFUF_ElimSem
begin

section \<open>The Rust functions of the equality elimination compute their models\<close>

lemma occs_take_Suc: \<open>i < length ts \<Longrightarrow> occs_m c (take (Suc i) ts) = occs_m c (take i ts) + occ_m c (ts ! i)\<close>
  by (simp add: occs_sum take_Suc_conv_app_nth)

lemma argss_ok_nth: \<open>argss_ok ts \<Longrightarrow> i < length ts \<Longrightarrow> args_ok (ts ! i)\<close>
  by (simp add: argss_ok_iff)

lemma find_first:
  \<open>\<forall>j < i. \<not> P (ts ! j) \<Longrightarrow> i < length ts \<Longrightarrow> P (ts ! i) \<Longrightarrow> List.find P ts = Some (ts ! i)\<close>
  by (auto simp: find_Some_iff)

lemma find_none: \<open>\<forall>j < length ts. \<not> P (ts ! j) \<Longrightarrow> List.find P ts = None\<close>
  by (auto simp: find_None_iff in_set_conv_nth)

lemma find_conjs_find:
  \<open>find_conjs_m c tot n ts =
     (case List.find (\<lambda>t. find_conj_m c tot n t < n) ts of Some t \<Rightarrow> find_conj_m c tot n t | None \<Rightarrow> n)\<close>
  by (induction ts) auto

lemma wlen0:
  assumes \<open>length xs < 2 ^ 64\<close> shows \<open>((word_of_nat (length xs) :: 64 word) = 0) = (xs = [])\<close>
proof
  assume \<open>(word_of_nat (length xs) :: 64 word) = 0\<close>
  then have \<open>unat (word_of_nat (length xs) :: 64 word) = 0\<close> by simp
  then show \<open>xs = []\<close> using assms by (simp add: unat_of_nat_eq)
qed simp

lemma wlen2:
  assumes \<open>length xs < 2 ^ 64\<close> shows \<open>((word_of_nat (length xs) :: 64 word) = 2) = (length xs = 2)\<close>
proof
  assume \<open>(word_of_nat (length xs) :: 64 word) = 2\<close>
  then have \<open>unat (word_of_nat (length xs) :: 64 word) = 2\<close> by simp
  then show \<open>length xs = 2\<close> using assms by (simp add: unat_of_nat_eq)
qed simp

context QFUF_ctx
begin

subsection \<open>\<^verbatim>\<open>occ\<close> and \<^verbatim>\<open>occs\<close>\<close>

definition occ_contract :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> SmtTerm \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>occ_contract k c t \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>Suc (size t) \<le> k \<and> args_ok t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat (occ_m c t)\<rangle>)\<close>

definition occs_contract :: \<open>nat \<Rightarrow> 64 word \<Rightarrow> SmtTerm list \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>occs_contract k c ts \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>Suc (size_list size ts) \<le> k \<and> argss_ok ts \<and> length ts < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>unat r = sat (occs_m c ts)\<rangle>)\<close>

lemma occ_step_spec:
  assumes IH1: \<open>\<And>ts c. \<Gamma>; f ts c \<Turnstile>\<^sub>F occs_contract k c ts\<close>
      and IH2: \<open>\<And>t c. \<Gamma>; g t c \<Turnstile>\<^sub>F occ_contract k c t\<close>
  shows \<open>\<Gamma>; fst (occs_rec_step (f, g)) ts c \<Turnstile>\<^sub>F occs_contract (Suc k) c ts\<close>
    and \<open>\<Gamma>; snd (occs_rec_step (f, g)) t c \<Turnstile>\<^sub>F occ_contract (Suc k) c t\<close>
proof -
  show \<open>\<Gamma>; fst (occs_rec_step (f, g)) ts c \<Turnstile>\<^sub>F occs_contract (Suc k) c ts\<close>
    unfolding occs_rec_step_def prod.case fst_conv
    apply (crush_boot contract: occs_contract_def)
    apply crush_base
    subgoal for n_ref
      apply (ucincl_discharge\<open>
        rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>gn n. n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star>
                   \<langle>unat n = sat (occs_m c (take i ts))\<rangle>)\<close>
          and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
          and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_raw_for_loop_framedI'\<close>)
      apply (crush_base specs add: IH2 contracts add: occ_contract_def
          simp add: unat_of_nat_eq less_Suc_eq occs_take_Suc sat_add_sat sat_0 argss_ok_nth nth_size_le)
      done
    done
  show \<open>\<Gamma>; snd (occs_rec_step (f, g)) t c \<Turnstile>\<^sub>F occ_contract (Suc k) c t\<close>
    unfolding occs_rec_step_def prod.case snd_conv
    apply (crush_boot contract: occ_contract_def)
    apply (crush_base specs add: IH1 contracts add: occs_contract_def split: SmtTerm.splits
        simp add: sat_add_sat sat_add_sat_r sat_0 sat_1 sat_sat sat_Suc_sat)
    done
qed

lemma occ_rec_spec:
  shows \<open>(\<forall>ts c. \<Gamma>; fst ((occs_rec_step ^^ k) h) ts c \<Turnstile>\<^sub>F occs_contract k c ts) \<and>
         (\<forall>t c. \<Gamma>; snd ((occs_rec_step ^^ k) h) t c \<Turnstile>\<^sub>F occ_contract k c t)\<close>
proof (induction k)
  case 0
  show ?case
    apply (intro conjI allI)
     apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: occs_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: occ_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  obtain f g where fg: \<open>(occs_rec_step ^^ k) h = (f, g)\<close> by (cases \<open>(occs_rec_step ^^ k) h\<close>)
  show ?case
    using occ_step_spec[where f=f and g=g and k=k] Suc.IH unfolding funpow.simps(2) comp_def fg by simp
qed

lemma occ_spec [crush_specs]:
  shows \<open>\<Gamma>; occ t c \<Turnstile>\<^sub>F occ_contract urust_fuel c t\<close>
  unfolding occ_def using occ_rec_spec by blast

lemma occs_spec [crush_specs]:
  shows \<open>\<Gamma>; occs ts c \<Turnstile>\<^sub>F occs_contract urust_fuel c ts\<close>
  unfolding occs_def using occ_rec_spec by blast

subsection \<open>The conjuncts\<close>

definition const_sym_contract :: \<open>SmtTerm \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>const_sym_contract t n \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>args_ok t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = const_sym_m n t\<rangle>)\<close>

lemma const_sym_spec [crush_specs]:
  shows \<open>\<Gamma>; const_sym t n \<Turnstile>\<^sub>F const_sym_contract t n\<close>
  apply (crush_boot f: const_sym_def contract: const_sym_contract_def)
  apply (crush_base split: SmtTerm.splits simp add: const_sym_m_def wlen0)
  done

definition eq_partner_contract :: \<open>SmtTerm \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>eq_partner_contract t c n \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>args_ok t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = eq_partner_m c n t\<rangle>)\<close>

lemma eq_partner_spec [crush_specs]:
  shows \<open>\<Gamma>; eq_partner t c n \<Turnstile>\<^sub>F eq_partner_contract t c n\<close>
  apply (crush_boot f: eq_partner_def contract: eq_partner_contract_def)
  apply (crush_base split: SmtTerm.splits SmtOp.splits simp add: eq_partner_m_def wlen2 argss_ok_nth)
  done

definition eq_count_contract :: \<open>SmtTerm list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>eq_count_contract ts c n \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>argss_ok ts \<and> length ts < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = word_of_nat (eq_count_m c n ts)\<rangle>)\<close>

lemma eq_count_take_Suc:
  \<open>i < length ts \<Longrightarrow> eq_count_m c n (take (Suc i) ts) =
     eq_count_m c n (take i ts) + (if eq_partner_m c n (ts ! i) < n then 1 else 0)\<close>
  by (simp add: eq_count_m_def take_Suc_conv_app_nth)

lemma eq_count_le: \<open>eq_count_m c n ts \<le> length ts\<close>
  by (simp add: eq_count_m_def)

lemma eq_count_spec [crush_specs]:
  shows \<open>\<Gamma>; eq_count ts c n \<Turnstile>\<^sub>F eq_count_contract ts c n\<close>
  apply (crush_boot f: eq_count_def contract: eq_count_contract_def)
  apply crush_base
  subgoal for k_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>gk k. k_ref \<mapsto>\<langle>\<top>\<rangle> gk\<down>k \<star>
                 \<langle>unat k = eq_count_m c n (take i ts)\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base simp add: unat_of_nat_eq less_Suc_eq eq_count_take_Suc argss_ok_nth)
    subgoal for i gk r using eq_count_le[of c n \<open>take i ts\<close>] unat_inc[of r \<open>length ts\<close>] by simp
    subgoal for i gk r using eq_count_le[of c n \<open>take i ts\<close>] by simp
    subgoal for gk r using eq_count_le[of c n ts] by (intro word_eq_unatI) (simp add: unat_of_nat_eq)
    subgoal by (simp add: eq_count_m_def)
    done
  done

definition first_partner_contract :: \<open>SmtTerm list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>first_partner_contract ts c n \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>argss_ok ts \<and> length ts < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = first_partner_m c n ts\<rangle>)\<close>

lemma first_partner_spec [crush_specs]:
  shows \<open>\<Gamma>; first_partner ts c n \<Turnstile>\<^sub>F first_partner_contract ts c n\<close>
  apply (crush_boot f: first_partner_def contract: first_partner_contract_def)
  apply crush_base
  apply (ucincl_discharge\<open>
    rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> \<langle>\<forall>j < i. \<not> eq_partner_m c n (ts ! j) < n\<rangle>\<close>
      and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
      and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = first_partner_m c n ts\<rangle>\<close>
      and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
    in wp_raw_for_loop_framedI'\<close>)
  apply (crush_base simp add: unat_of_nat_eq less_Suc_eq argss_ok_nth)
  subgoal for i by (simp add: first_partner_m_def find_first[where P=\<open>\<lambda>t. eq_partner_m c n t < n\<close>])
  subgoal by (simp add: first_partner_m_def find_none[where P=\<open>\<lambda>t. eq_partner_m c n t < n\<close>])
  done

subsection \<open>\<^verbatim>\<open>find_conj\<close> and \<^verbatim>\<open>find_conjs\<close>\<close>

definition find_conj_contract :: \<open>nat \<Rightarrow> SmtTerm \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>find_conj_contract k t c tot n \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>Suc (size t) \<le> k \<and> args_ok t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = find_conj_m c tot n t\<rangle>)\<close>

definition find_conjs_contract :: \<open>nat \<Rightarrow> SmtTerm list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>find_conjs_contract k ts c tot n \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>Suc (size_list size ts) \<le> k \<and> argss_ok ts \<and> length ts < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = find_conjs_m c tot n ts\<rangle>)\<close>

lemma find_conj_step_spec:
  assumes IH1: \<open>\<And>ts c tot n. \<Gamma>; f ts c tot n \<Turnstile>\<^sub>F find_conjs_contract k ts c tot n\<close>
      and IH2: \<open>\<And>t c tot n. \<Gamma>; g t c tot n \<Turnstile>\<^sub>F find_conj_contract k t c tot n\<close>
  shows \<open>\<Gamma>; fst (find_conjs_rec_step (f, g)) ts c tot n \<Turnstile>\<^sub>F find_conjs_contract (Suc k) ts c tot n\<close>
    and \<open>\<Gamma>; snd (find_conjs_rec_step (f, g)) t c tot n \<Turnstile>\<^sub>F find_conj_contract (Suc k) t c tot n\<close>
proof -
  show \<open>\<Gamma>; fst (find_conjs_rec_step (f, g)) ts c tot n \<Turnstile>\<^sub>F find_conjs_contract (Suc k) ts c tot n\<close>
    unfolding find_conjs_rec_step_def prod.case fst_conv
    apply (crush_boot contract: find_conjs_contract_def)
    apply crush_base
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> \<langle>\<forall>j < i. \<not> find_conj_m c tot n (ts ! j) < n\<rangle>\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>r. can_alloc_reference \<star> \<langle>r = find_conjs_m c tot n ts\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base specs add: IH2 contracts add: find_conj_contract_def
        simp add: unat_of_nat_eq less_Suc_eq argss_ok_nth nth_size_le)
    subgoal for i by (simp add: find_conjs_find find_first[where P=\<open>\<lambda>t. find_conj_m c tot n t < n\<close>])
    subgoal by (simp add: find_conjs_find find_none[where P=\<open>\<lambda>t. find_conj_m c tot n t < n\<close>])
    done
  show \<open>\<Gamma>; snd (find_conjs_rec_step (f, g)) t c tot n \<Turnstile>\<^sub>F find_conj_contract (Suc k) t c tot n\<close>
    unfolding find_conjs_rec_step_def prod.case snd_conv
    apply (crush_boot contract: find_conj_contract_def)
    apply (crush_base specs add: IH1 contracts add: find_conjs_contract_def split: SmtTerm.splits SmtOp.splits)
    done
qed

lemma find_conj_rec_spec:
  shows \<open>(\<forall>ts c tot n. \<Gamma>; fst ((find_conjs_rec_step ^^ k) h) ts c tot n \<Turnstile>\<^sub>F find_conjs_contract k ts c tot n) \<and>
         (\<forall>t c tot n. \<Gamma>; snd ((find_conjs_rec_step ^^ k) h) t c tot n \<Turnstile>\<^sub>F find_conj_contract k t c tot n)\<close>
proof (induction k)
  case 0
  show ?case
    apply (intro conjI allI)
     apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: find_conjs_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: find_conj_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  obtain f g where fg: \<open>(find_conjs_rec_step ^^ k) h = (f, g)\<close> by (cases \<open>(find_conjs_rec_step ^^ k) h\<close>)
  show ?case
    using find_conj_step_spec[where f=f and g=g and k=k] Suc.IH unfolding funpow.simps(2) comp_def fg by simp
qed

lemma find_conjs_spec [crush_specs]:
  shows \<open>\<Gamma>; find_conjs ts c tot n \<Turnstile>\<^sub>F find_conjs_contract urust_fuel ts c tot n\<close>
  unfolding find_conjs_def using find_conj_rec_spec by blast

subsection \<open>\<^verbatim>\<open>occ_all\<close> and \<^verbatim>\<open>elim_partner\<close>\<close>

text \<open>What the functions of the elimination need of the assertions \<open>a\<close> and the definitions of
  \<open>p\<close>: no list longer than \<open>2^64\<close>, and enough fuel for the recursion.\<close>
definition ea_pre :: \<open>SmtProblem \<Rightarrow> SmtTerm list \<Rightarrow> bool\<close> where
  \<open>ea_pre p a \<equiv>
     argss_ok a \<and> length a < 2 ^ 64 \<and> Suc (size_list size a) \<le> urust_fuel \<and>
     length (SmtProblem_defs_l p) < 2 ^ 64 \<and>
     (\<forall>d \<in> set (SmtProblem_defs_l p). args_ok (SmtDef_body d) \<and> Suc (size (SmtDef_body d)) \<le> urust_fuel)\<close>

definition occ_all_contract :: \<open>SmtProblem \<Rightarrow> SmtTerm list \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>occ_all_contract p a c \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>ea_pre p a\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = word_of_nat (sat (occ_all_m p a c))\<rangle>)\<close>

lemma occ_defs_take_Suc:
  \<open>i < length ds \<Longrightarrow> sum_list (map (\<lambda>d. occ_m c (SmtDef_body d)) (take (Suc i) ds)) =
     sum_list (map (\<lambda>d. occ_m c (SmtDef_body d)) (take i ds)) + occ_m c (SmtDef_body (ds ! i))\<close>
  by (simp add: take_Suc_conv_app_nth)

lemma unat_eq_of_nat: \<open>unat (x :: 64 word) = n \<Longrightarrow> x = word_of_nat n\<close>
  by auto

lemma occ_all_spec [crush_specs]:
  shows \<open>\<Gamma>; occ_all p a c \<Turnstile>\<^sub>F occ_all_contract p a c\<close>
  apply (crush_boot f: occ_all_def contract: occ_all_contract_def)
  apply (crush_base simp add: ea_pre_def)
  subgoal for n0 n_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>gn n. n_ref \<mapsto>\<langle>\<top>\<rangle> gn\<down>n \<star>
                 \<langle>unat n = sat (occs_m c a + sum_list (map (\<lambda>d. occ_m c (SmtDef_body d)) (take i (SmtProblem_defs_l p))))\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base simp add: unat_of_nat_eq less_Suc_eq occ_defs_take_Suc sat_add_sat_l add.assoc
        ea_pre_def occ_all_m_def)
    apply (metis add.assoc sat_add_sat_r)
    apply (rule unat_eq_of_nat, simp add: occ_all_m_def)
    done
  done

lemma unat_sat: \<open>unat (word_of_nat (sat x) :: 64 word) = sat x\<close>
  using sat_le[of x] by (simp add: unat_of_nat_eq)

lemma sat_w0: \<open>((word_of_nat (sat x) :: 64 word) = 0) = (sat x = 0)\<close>
proof
  assume \<open>(word_of_nat (sat x) :: 64 word) = 0\<close>
  then have \<open>unat (word_of_nat (sat x) :: 64 word) = 0\<close> by simp
  then show \<open>sat x = 0\<close> by (simp only: unat_sat)
qed simp

lemma wargs0:
  \<open>\<forall>f \<in> set fs. length (SmtFun_args_l f) < 2 ^ 63 \<Longrightarrow> j < length fs \<Longrightarrow>
   ((word_of_nat (length (SmtFun_args_l (fs ! j))) :: 64 word) = 0) = (SmtFun_args_l (fs ! j) = [])\<close>
  by (rule wlen0) (use nth_mem in fastforce)

definition elim_partner_contract :: \<open>SmtProblem \<Rightarrow> SmtTerm list \<Rightarrow> 64 word \<Rightarrow> ('s, 64 word, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>elim_partner_contract p a c \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>ea_pre p a \<and> unat c < length (SmtProblem_funs_l p) \<and> length (SmtProblem_funs_l p) < 2 ^ 63 \<and>
          (\<forall>f \<in> set (SmtProblem_funs_l p). length (SmtFun_args_l f) < 2 ^ 63)\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = elim_partner_m p a c\<rangle>)\<close>

lemma elim_partner_spec [crush_specs]:
  shows \<open>\<Gamma>; elim_partner p a c \<Turnstile>\<^sub>F elim_partner_contract p a c\<close>
  apply (crush_boot f: elim_partner_def contract: elim_partner_contract_def)
  apply (crush_base simp add: ea_pre_def)
  apply (auto simp: elim_partner_m_def Let_def wargs0 word_less_nat_alt word_le_nat_alt unat_of_nat_eq unat_sat sat_w0)
  done

subsection \<open>\<^verbatim>\<open>rename\<close> and \<^verbatim>\<open>renames\<close>\<close>

definition rename_contract :: \<open>nat \<Rightarrow> SmtTerm \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, SmtTerm, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>rename_contract k t c g \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>Suc (size t) \<le> k \<and> args_ok t\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = rename_m c g t\<rangle>)\<close>

definition renames_contract :: \<open>nat \<Rightarrow> SmtTerm list \<Rightarrow> 64 word \<Rightarrow> 64 word \<Rightarrow> ('s, SmtTerm list, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>renames_contract k ts c g \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>Suc (size_list size ts) \<le> k \<and> argss_ok ts \<and> length ts < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = renames_m c g ts\<rangle>)\<close>

lemma renames_take_Suc: \<open>i < length ts \<Longrightarrow> renames_m c g (take (Suc i) ts) = renames_m c g (take i ts) @ [rename_m c g (ts ! i)]\<close>
  by (simp add: renames_map take_Suc_conv_app_nth)

lemma rename_step_spec:
  assumes IH1: \<open>\<And>ts c g. \<Gamma>; f ts c g \<Turnstile>\<^sub>F renames_contract k ts c g\<close>
      and IH2: \<open>\<And>t c g. \<Gamma>; h t c g \<Turnstile>\<^sub>F rename_contract k t c g\<close>
  shows \<open>\<Gamma>; fst (renames_rec_step (f, h)) ts c g \<Turnstile>\<^sub>F renames_contract (Suc k) ts c g\<close>
    and \<open>\<Gamma>; snd (renames_rec_step (f, h)) t c g \<Turnstile>\<^sub>F rename_contract (Suc k) t c g\<close>
proof -
  show \<open>\<Gamma>; fst (renames_rec_step (f, h)) ts c g \<Turnstile>\<^sub>F renames_contract (Suc k) ts c g\<close>
    unfolding renames_rec_step_def prod.case fst_conv
    apply (crush_boot contract: renames_contract_def)
    apply (crush_base inline: vec_push_def)
    subgoal for out_ref
      apply (ucincl_discharge\<open>
        rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>go xs. out_ref \<mapsto>\<langle>\<top>\<rangle> go\<down>xs \<star>
                   \<langle>xs = renames_m c g (take i ts)\<rangle>)\<close>
          and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
          and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
          and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        in wp_raw_for_loop_framedI'\<close>)
      apply (crush_base specs add: IH2 contracts add: rename_contract_def inline: vec_push_def
          simp add: unat_of_nat_eq less_Suc_eq renames_take_Suc argss_ok_nth nth_size_le)
      done
    done
  show \<open>\<Gamma>; snd (renames_rec_step (f, h)) t c g \<Turnstile>\<^sub>F rename_contract (Suc k) t c g\<close>
    unfolding renames_rec_step_def prod.case snd_conv
    apply (crush_boot contract: rename_contract_def)
    apply (crush_base specs add: IH1 contracts add: renames_contract_def split: SmtTerm.splits)
    done
qed

lemma rename_rec_spec:
  shows \<open>(\<forall>ts c g. \<Gamma>; fst ((renames_rec_step ^^ k) h) ts c g \<Turnstile>\<^sub>F renames_contract k ts c g) \<and>
         (\<forall>t c g. \<Gamma>; snd ((renames_rec_step ^^ k) h) t c g \<Turnstile>\<^sub>F rename_contract k t c g)\<close>
proof (induction k)
  case 0
  show ?case
    apply (intro conjI allI)
     apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: renames_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    apply (ucincl_discharge\<open>intro satisfies_function_contractI\<close>; subst wp_sstriple_iff;
        simp add: rename_contract_def Let_def apure_precise_False asepconj_bot_zero2 bot_aentails_all)
    done
next
  case (Suc k)
  obtain f g where fg: \<open>(renames_rec_step ^^ k) h = (f, g)\<close> by (cases \<open>(renames_rec_step ^^ k) h\<close>)
  show ?case
    using rename_step_spec[where f=f and h=g and k=k] Suc.IH unfolding funpow.simps(2) comp_def fg by simp
qed

lemma renames_spec [crush_specs]:
  shows \<open>\<Gamma>; renames ts c g \<Turnstile>\<^sub>F renames_contract urust_fuel ts c g\<close>
  unfolding renames_def using rename_rec_spec by blast

subsection \<open>\<^verbatim>\<open>eliminate\<close>\<close>

text \<open>What \<^verbatim>\<open>eliminate\<close> needs: the representation condition and enough fuel for the recursion
  over the assertions and the bodies of the definitions.\<close>
definition elim_pre :: \<open>SmtProblem \<Rightarrow> bool\<close> where
  \<open>elim_pre p \<equiv>
     smt_repr_ok p \<and> Suc (size_list size (SmtProblem_asserts_l p)) \<le> urust_fuel \<and>
     (\<forall>d \<in> set (SmtProblem_defs_l p). Suc (size (SmtDef_body d)) \<le> urust_fuel)\<close>

definition eliminate_contract :: \<open>SmtProblem \<Rightarrow> ('s, SmtTerm list \<times> 64 word list \<times> 64 word list \<times> tnil, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>eliminate_contract p \<equiv>
     make_function_contract (can_alloc_reference \<star> \<langle>elim_pre p\<rangle>)
       (\<lambda>r. can_alloc_reference \<star>
          \<langle>(fst r, fst (snd r), fst (snd (snd r))) = eliminate_m p\<rangle>)\<close>

lemma elim_pre_ea:
  assumes P: \<open>elim_pre p\<close> and I: \<open>elim_inv p (a, cs, gs)\<close>
  shows \<open>ea_pre p a\<close>
proof -
  have R: \<open>smt_repr_ok p\<close> using P by (simp add: elim_pre_def)
  have \<open>smt_repr_ok (wa p a)\<close> \<open>size_list size a = size_list size (SmtProblem_asserts_l p)\<close>
    \<open>length a = length (SmtProblem_asserts_l p)\<close>
    using I R by (simp_all add: elim_inv_def)
  then show ?thesis
    using P reprs_argss_ok repr_args_ok
    by (auto simp: ea_pre_def elim_pre_def smt_repr_ok_def)
qed

lemma elim_step_foldl:
  \<open>foldl (elim_step_m p) s [0..<Suc i] = elim_step_m p (foldl (elim_step_m p) s [0..<i]) i\<close>
  by simp

lemma elim_loop_facts:
  assumes P: \<open>elim_pre p\<close> and I: \<open>i < unat (word_of_nat (length (SmtProblem_funs_l p)) :: 64 word)\<close>
    and V: \<open>elim_inv p (a, cs, gs)\<close>
  shows \<open>ea_pre p a \<and> unat (word_of_nat i :: 64 word) = i \<and> i < length (SmtProblem_funs_l p) \<and>
         length (SmtProblem_funs_l p) < 2 ^ 63 \<and> (\<forall>f \<in> set (SmtProblem_funs_l p). length (SmtFun_args_l f) < 2 ^ 63) \<and>
         length a < 2 ^ 64 \<and> argss_ok a \<and> Suc (size_list size a) \<le> urust_fuel \<and>
         elim_inv p (elim_step_m p (a, cs, gs) i)\<close>
proof -
  have R: \<open>smt_repr_ok p\<close> using P by (simp add: elim_pre_def)
  then have L: \<open>length (SmtProblem_funs_l p) < 2 ^ 63\<close> by (simp add: smt_repr_ok_def)
  then have i: \<open>i < length (SmtProblem_funs_l p)\<close> using I by (simp add: unat_of_nat_eq)
  note V' = V
  have E: \<open>ea_pre p a\<close> using elim_pre_ea[OF P V'] .
  show ?thesis
    using E L i R elim_inv_step[OF R i V'] by (auto simp: ea_pre_def unat_of_nat_eq smt_repr_ok_def)
qed

lemma eliminate_spec [crush_specs]:
  shows \<open>\<Gamma>; eliminate p \<Turnstile>\<^sub>F eliminate_contract p\<close>
  apply (crush_boot f: eliminate_def contract: eliminate_contract_def)
  apply (crush_base inline: vec_push_def)
  subgoal for a_ref cs_ref gs_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ i. can_alloc_reference \<star> (\<Squnion>ga a. a_ref \<mapsto>\<langle>\<top>\<rangle> ga\<down>a \<star>
                 (\<Squnion>gc cs. cs_ref \<mapsto>\<langle>\<top>\<rangle> gc\<down>cs \<star> (\<Squnion>gg gs. gs_ref \<mapsto>\<langle>\<top>\<rangle> gg\<down>gs \<star>
                 \<langle>foldl (elim_step_m p) (SmtProblem_asserts_l p, [], []) [0..<i] = (a, cs, gs) \<and>
                  elim_inv p (a, cs, gs)\<rangle>)))\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base inline: vec_push_def simp add: unat_of_nat_eq less_Suc_eq)
    apply (all \<open>(frule elim_loop_facts, assumption+)?\<close>)
    apply (auto simp: elim_step_m_def Let_def eliminate_m_def elim_pre_def smt_repr_ok_def unat_of_nat_eq
        intro: elim_inv_foldl[where k=0, simplified])
    done
  done

subsection \<open>\<^verbatim>\<open>restore\<close>\<close>

lemma rev_idx_le:
  assumes \<open>i < L\<close> \<open>L < 2 ^ 64\<close>
  shows \<open>(1 :: 64 word) \<le> word_of_nat L\<close> \<open>unat (word_of_nat L - 1 :: 64 word) = L - 1\<close>
    and \<open>(word_of_nat i :: 64 word) \<le> word_of_nat L - 1\<close>
proof -
  have u: \<open>unat (word_of_nat L :: 64 word) = L\<close> \<open>unat (word_of_nat i :: 64 word) = i\<close>
    using assms by (simp_all add: unat_of_nat_eq)
  show o: \<open>(1 :: 64 word) \<le> word_of_nat L\<close> using assms u by (simp add: word_le_nat_alt)
  show l: \<open>unat (word_of_nat L - 1 :: 64 word) = L - 1\<close> using unat_sub[OF o] u by simp
  show \<open>(word_of_nat i :: 64 word) \<le> word_of_nat L - 1\<close> using assms l u by (simp add: word_le_nat_alt)
qed

lemma rev_idx:
  assumes \<open>i < L\<close> \<open>L < 2 ^ 64\<close>
  shows \<open>unat (word_of_nat L - 1 - word_of_nat i :: 64 word) = L - 1 - i\<close>
  using unat_sub[OF rev_idx_le(3)[OF assms]] rev_idx_le(2)[OF assms] assms by (simp add: unat_of_nat_eq)

lemma length_fix_m: \<open>length (fix_m cs gs fs k) = length fs\<close>
  by (simp add: fix_m_def Let_def)

lemma length_foldl_fix_m: \<open>length (foldl (fix_m cs gs) fs ks) = length fs\<close>
  by (induction ks arbitrary: fs rule: rev_induct) (simp_all add: length_fix_m)

definition restore_contract :: \<open>SmtModel \<Rightarrow> 64 word list \<Rightarrow> 64 word list \<Rightarrow> ('s, SmtModel, 'abort) function_contract\<close> where
  [crush_contracts]: \<open>restore_contract m cs gs \<equiv>
     make_function_contract
       (can_alloc_reference \<star> \<langle>length cs < 2 ^ 64 \<and> length gs < 2 ^ 64 \<and> length (SmtModel_funs_l m) < 2 ^ 64\<rangle>)
       (\<lambda>r. can_alloc_reference \<star> \<langle>r = restore_m m cs gs\<rangle>)\<close>

lemma restore_spec [crush_specs]:
  shows \<open>\<Gamma>; restore m cs gs \<Turnstile>\<^sub>F restore_contract m cs gs\<close>
  apply (crush_boot f: restore_def contract: restore_contract_def)
  apply (crush_base inline: SmtModel_mk_def)
  subgoal for funs_ref
    apply (ucincl_discharge\<open>
      rule_tac INV=\<open>\<lambda>_ k. can_alloc_reference \<star> (\<Squnion>gf fs. funs_ref \<mapsto>\<langle>\<top>\<rangle> gf\<down>fs \<star>
                 \<langle>fs = foldl (fix_m cs gs) (SmtModel_funs_l m) [0..<k]\<rangle>)\<close>
        and BRK=\<open>\<lambda>_ _. \<langle>False\<rangle>\<close>
        and \<tau>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
        and \<theta>=\<open>\<lambda>_. \<langle>False\<rangle>\<close>
      in wp_raw_for_loop_framedI'\<close>)
    apply (crush_base inline: SmtModel_mk_def simp add: unat_of_nat_eq less_Suc_eq)
    apply (auto simp: rev_idx length_foldl_fix_m word_less_nat_alt unat_of_nat_eq fix_m_def Let_def restore_m_def)
    apply (simp_all add: rev_idx_le)
    done
  done

end

lemma elim_lengths:
  \<open>k \<le> length (SmtProblem_funs_l p) \<Longrightarrow>
   length (fst (snd (foldl (elim_step_m p) (SmtProblem_asserts_l p, [], []) [0..<k]))) \<le> k \<and>
   length (snd (snd (foldl (elim_step_m p) (SmtProblem_asserts_l p, [], []) [0..<k]))) \<le> k\<close>
  by (induction k) (auto simp: elim_step_m_def Let_def split: prod.splits)

lemma eliminate_lengths:
  \<open>eliminate_m p = (a, cs, gs) \<Longrightarrow> length cs \<le> length (SmtProblem_funs_l p) \<and> length gs \<le> length (SmtProblem_funs_l p)\<close>
  using elim_lengths[OF order.refl, of p] by (simp add: eliminate_m_def)

end
