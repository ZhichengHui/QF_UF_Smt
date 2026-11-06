theory QFUF_Spec
  imports QFUF.QFUF_Funs
begin

section \<open>The top-level specification of the QF\_UF solver\<close>

text \<open>
  REVIEW NOTES

  Source: \<^verbatim>\<open>solver/src/lib.rs\<close>; the specified function is \<^verbatim>\<open>pub fn solve(p: &Problem) -> Answer\<close>.

  A problem is a CNF formula over equalities between ground terms of one uninterpreted sort. Term
  \<open>i\<close> of \<^const>\<open>Problem_terms\<close> applies function symbol \<^const>\<open>Term_fun\<close> (a number; constants are
  0-ary symbols) to the terms whose indices are listed in \<^const>\<open>Term_args\<close>. Atom \<open>k\<close> is the
  equality between the terms \<^const>\<open>Atom_lhs\<close> and \<^const>\<open>Atom_rhs\<close>; a literal is an atom index
  with a polarity; a clause is a disjunction of literals; the problem is the conjunction of its
  clauses.

  The contract states:
  \<^item> if \<^verbatim>\<open>solve\<close> answers \<^verbatim>\<open>Sat(m)\<close>, the interpretation \<open>model_interp\<close> \<open>m\<close> makes the
    problem true (a correct model);
  \<^item> if it answers \<^verbatim>\<open>Unsat\<close>, no interpretation makes the problem true;
  \<^item> it does not panic or abort (\<^const>\<open>make_function_contract\<close> makes the abort postcondition
    false).

  Transcription choices (to check):
  \<^item> An interpretation of the sort and the symbols is a function \<open>I f vs\<close> giving the value of
    symbol \<open>f\<close> applied to the values \<open>vs\<close>. The domain in \<open>satisfiable\<close> is \<^typ>\<open>nat\<close>.
    For the answer \<^verbatim>\<open>Unsat\<close> this loses nothing: a problem has finitely many terms, so a model
    over any domain maps injectively into \<^typ>\<open>nat\<close>. The proof theories prove this (lemma
    \<open>satisfiable_of_any_domain\<close>) and the corollary \<open>solve_unsat_any_domain\<close>.
    A symbol has no fixed arity: the same number applied to different numbers of arguments
    denotes different functions of the interpretation \<open>I f\<close> (a function on lists).
  \<^item> \<open>model_interp\<close> reads the model as the solver's documentation describes it: the sort is
    \<^typ>\<open>nat\<close>, symbol \<open>f\<close> applied to \<open>vs\<close> has the value of the first entry with symbol \<open>f\<close> and
    arguments \<open>vs\<close>, and value 0 if there is none. Entries store \<^verbatim>\<open>usize\<close> values, read as
    \<^term>\<open>unat\<close> of the words.
  \<^item> Preconditions:
    \<^item> \<open>wf_problem\<close>: the term list is a DAG in index order (every argument index is
      smaller than the term's index), and atom and literal indices are in bounds. Rust would
      panic on an out-of-bounds index, so the contract (which excludes panics) must assume it.
    \<^item> \<open>sizes_ok\<close>: every \<^verbatim>\<open>Vec\<close> in the problem has fewer than \<open>2^63\<close> elements. Rust guarantees
      this for every \<^verbatim>\<open>Vec\<close> of non-zero-sized elements (an allocation has at most
      \<^verbatim>\<open>isize::MAX\<close> bytes); the translation's lists have no such bound.
    \<^item> \<open>length (Problem_atoms p) < urust_fuel\<close>: the translation defines the recursive function
      \<^verbatim>\<open>search\<close> by unfolding it \<^term>\<open>urust_fuel\<close> times (a locale parameter). \<^verbatim>\<open>search\<close>
      recurses once per atom, so this says that the fuel suffices; it is an artefact of the
      translation, not of the Rust program.
    \<^item> \<open>can_alloc_reference\<close>: AutoCorrode's permission to allocate the solver's mutable locals.
  \<^item> \<^verbatim>\<open>p\<close> is passed by shared reference, which the translation passes by value.
\<close>

subsection \<open>Semantics of problems\<close>

text \<open>The value of term \<open>i\<close> under the interpretation \<open>I\<close>. (The guard \<open>unat x < i\<close> only makes
  the recursion well-founded; under \<open>wf_problem\<close> it always holds.)\<close>
function term_val :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> Term list \<Rightarrow> nat \<Rightarrow> 'd\<close> where
  \<open>term_val I ts i =
     I (unat (Term_fun (ts ! i)))
       (List.map (\<lambda>x. if unat x < i then term_val I ts (unat x) else undefined) (Term_args (ts ! i)))\<close>
  by auto
termination
  by (relation \<open>measure (\<lambda>(_, _, i). i)\<close>) auto

declare term_val.simps [simp del]

definition atom_true :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> Problem \<Rightarrow> Atom \<Rightarrow> bool\<close> where
  \<open>atom_true I p at \<equiv>
     term_val I (Problem_terms p) (unat (Atom_lhs at)) = term_val I (Problem_terms p) (unat (Atom_rhs at))\<close>

definition lit_true :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> Problem \<Rightarrow> Lit \<Rightarrow> bool\<close> where
  \<open>lit_true I p l \<equiv> atom_true I p (Problem_atoms p ! unat (Lit_atom l)) = Lit_pos l\<close>

definition clause_true :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> Problem \<Rightarrow> Clause \<Rightarrow> bool\<close> where
  \<open>clause_true I p c \<equiv> \<exists>l \<in> set (Clause_lits c). lit_true I p l\<close>

definition problem_true :: \<open>(nat \<Rightarrow> 'd list \<Rightarrow> 'd) \<Rightarrow> Problem \<Rightarrow> bool\<close> where
  \<open>problem_true I p \<equiv> \<forall>c \<in> set (Problem_clauses p). clause_true I p c\<close>

definition satisfiable :: \<open>Problem \<Rightarrow> bool\<close> where
  \<open>satisfiable p \<equiv> \<exists>I :: nat \<Rightarrow> nat list \<Rightarrow> nat. problem_true I p\<close>

subsection \<open>Models\<close>

definition model_interp :: \<open>Model \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> nat\<close> where
  \<open>model_interp m f vs \<equiv>
     (case List.find (\<lambda>e. unat (Entry_fun e) = f \<and> List.map unat (Entry_args e) = vs) (Model_entries m) of
        Some e \<Rightarrow> unat (Entry_val e)
      | None \<Rightarrow> 0)\<close>

subsection \<open>Preconditions\<close>

definition wf_problem :: \<open>Problem \<Rightarrow> bool\<close> where
  \<open>wf_problem p \<equiv>
     (\<forall>i < length (Problem_terms p). \<forall>x \<in> set (Term_args (Problem_terms p ! i)). unat x < i) \<and>
     (\<forall>at \<in> set (Problem_atoms p).
        unat (Atom_lhs at) < length (Problem_terms p) \<and> unat (Atom_rhs at) < length (Problem_terms p)) \<and>
     (\<forall>c \<in> set (Problem_clauses p). \<forall>l \<in> set (Clause_lits c).
        unat (Lit_atom l) < length (Problem_atoms p))\<close>

definition sizes_ok :: \<open>Problem \<Rightarrow> bool\<close> where
  \<open>sizes_ok p \<equiv>
     length (Problem_terms p) < 2^63 \<and> (\<forall>t \<in> set (Problem_terms p). length (Term_args t) < 2^63) \<and>
     length (Problem_atoms p) < 2^63 \<and>
     length (Problem_clauses p) < 2^63 \<and> (\<forall>c \<in> set (Problem_clauses p). length (Clause_lits c) < 2^63)\<close>

subsection \<open>The contract\<close>

context QFUF_ctx
begin

definition solve_contract :: \<open>Problem \<Rightarrow> ('s, Answer, 'abort) function_contract\<close> where
  \<open>solve_contract p \<equiv>
     let pre = can_alloc_reference \<star>
        \<langle>wf_problem p \<and> sizes_ok p \<and> length (Problem_atoms p) < urust_fuel\<rangle> in
     let post = \<lambda>r. can_alloc_reference \<star>
        \<langle>case r of
           Answer_Sat m \<Rightarrow> problem_true (model_interp m) p
         | Answer_Unsat \<Rightarrow> \<not> satisfiable p\<rangle> in
     make_function_contract pre post\<close>

text \<open>The statement to prove (proved in \<^verbatim>\<open>QFUF_Proof\<close>).\<close>
lemma
  shows \<open>\<Gamma>; solve p \<Turnstile>\<^sub>F solve_contract p\<close>
  oops

end

end
