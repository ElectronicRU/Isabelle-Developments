theory Relspace
  imports Main
begin

section \<open>Relational vocabulary over a set of rows\<close>

text \<open>A \<^emph>\<open>relspace\<close> is just a set of rows \<open>D\<close>. Key spaces are given by arbitrary functions
  (projections) on rows; nothing here depends on their nature. All relations are stated through
  \<^emph>\<open>co-occurrence\<close> of keys, so that \<open>D\<close> is mentioned only in its definition.\<close>

locale relspace =
  fixes D :: "'d set"
begin

definition cooc :: "'a \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> bool"
    ("_ \<langle>_\<bowtie>_\<rangle> _" [51, 0, 0, 51] 50) where
  "k \<langle>p\<bowtie>q\<rangle> \<kappa> \<longleftrightarrow> (\<exists>d\<in>D. p d = k \<and> q d = \<kappa>)"

lemma cooc_fibres: "k \<langle>p\<bowtie>q\<rangle> \<kappa> \<longleftrightarrow> D \<inter> p -` {k} \<inter> q -` {\<kappa>} \<noteq> {}"
  by (auto simp: cooc_def)

subsection \<open>Functional dependence\<close>

definition determines :: "('d \<Rightarrow> 'a) \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> bool" (infix "\<Rrightarrow>" 50) where
  "p \<Rrightarrow> q \<longleftrightarrow> (\<forall>k \<kappa> \<kappa>'. k \<langle>p\<bowtie>q\<rangle> \<kappa> \<longrightarrow> k \<langle>p\<bowtie>q\<rangle> \<kappa>' \<longrightarrow> \<kappa> = \<kappa>')"

lemma determines_rows: "p \<Rrightarrow> q \<longleftrightarrow> (\<forall>d\<in>D. \<forall>d'\<in>D. p d = p d' \<longrightarrow> q d = q d')"
  unfolding determines_def cooc_def by metis

lemma determines_comp: "p \<Rrightarrow> f \<circ> p"
  by (simp add: determines_rows)

lemma determines_refl: "p \<Rrightarrow> p"
  by (simp add: determines_rows)

lemma determines_trans: "p \<Rrightarrow> q \<Longrightarrow> q \<Rrightarrow> r \<Longrightarrow> p \<Rrightarrow> r"
  unfolding determines_rows by blast

lemma determines_pair: "p \<Rrightarrow> q \<Longrightarrow> p \<Rrightarrow> r \<Longrightarrow> p \<Rrightarrow> (\<lambda>d. (q d, r d))"
  unfolding determines_rows by blast

definition fequiv :: "('d \<Rightarrow> 'a) \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> bool" (infix "\<Leftrightarrow>" 50) where
  "p \<Leftrightarrow> q \<longleftrightarrow> p \<Rrightarrow> q \<and> q \<Rrightarrow> p"

subsection \<open>Splitting (unconditional independence)\<close>

definition splits :: "('d \<Rightarrow> 'a) \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> bool" where
  "splits p q \<longleftrightarrow> (\<forall>k \<kappa> k' \<kappa>'. k \<langle>p\<bowtie>q\<rangle> \<kappa> \<longrightarrow> k' \<langle>p\<bowtie>q\<rangle> \<kappa>' \<longrightarrow> k \<langle>p\<bowtie>q\<rangle> \<kappa>')"

lemma splits_rows:
  "splits p q \<longleftrightarrow> (\<forall>d\<^sub>1\<in>D. \<forall>d\<^sub>2\<in>D. \<exists>d\<in>D. p d = p d\<^sub>1 \<and> q d = q d\<^sub>2)"
  unfolding splits_def cooc_def by blast

lemma splits_sym: "splits p q \<Longrightarrow> splits q p"
  unfolding splits_rows by metis

lemma splits_antimono: "splits p q \<Longrightarrow> p \<Rrightarrow> p' \<Longrightarrow> q \<Rrightarrow> q' \<Longrightarrow> splits p' q'"
  unfolding splits_rows determines_rows by metis

subsection \<open>Divisibility at a grain\<close>

text \<open>\<open>t\<close> divides \<open>a\<close> at grain \<open>n\<close>: up to functional equivalence, \<open>a\<close> is \<open>t\<close> joined with a
  cofactor that is independent of \<open>t\<close> and \<open>n\<close> together. Cofactors are labelled by rows.\<close>

definition divides :: "('d \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> bool" where
  "divides n t a \<longleftrightarrow> (\<exists>i :: 'd \<Rightarrow> 'd. splits (\<lambda>d. (t d, n d)) i \<and> a \<Leftrightarrow> (\<lambda>d. (t d, i d)))"

subsection \<open>Equivalence up to a grain\<close>

text \<open>\<open>a\<close> and \<open>t\<close> are equivalent at grain \<open>n\<close> when co-occurring keys have the same
  co-occurring \<open>n\<close>-keys.\<close>

definition equiv_upto :: "('d \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> bool" where
  "equiv_upto n a t \<longleftrightarrow>
     (\<forall>k \<kappa>. k \<langle>a\<bowtie>t\<rangle> \<kappa> \<longrightarrow> {\<nu>. k \<langle>a\<bowtie>n\<rangle> \<nu>} = {\<nu>. \<kappa> \<langle>t\<bowtie>n\<rangle> \<nu>})"

lemma equiv_upto_refl: "equiv_upto n a a"
  unfolding equiv_upto_def cooc_def by auto

lemma equiv_upto_sym:
  assumes "equiv_upto n a t" shows "equiv_upto n t a"
  unfolding equiv_upto_def
proof (intro allI impI)
  fix k \<kappa> assume "k \<langle>t\<bowtie>a\<rangle> \<kappa>"
  then have "\<kappa> \<langle>a\<bowtie>t\<rangle> k" by (auto simp: cooc_def)
  with assms show "{\<nu>. k \<langle>t\<bowtie>n\<rangle> \<nu>} = {\<nu>. \<kappa> \<langle>a\<bowtie>n\<rangle> \<nu>}"
    unfolding equiv_upto_def by simp
qed

lemma equiv_upto_trans:
  assumes at: "equiv_upto n a t" and ts: "equiv_upto n t s" shows "equiv_upto n a s"
  unfolding equiv_upto_def
proof (intro allI impI)
  fix k \<sigma> assume "k \<langle>a\<bowtie>s\<rangle> \<sigma>"
  then obtain d where "d \<in> D" "a d = k" "s d = \<sigma>" by (auto simp: cooc_def)
  then have "k \<langle>a\<bowtie>t\<rangle> t d" "t d \<langle>t\<bowtie>s\<rangle> \<sigma>" by (auto simp: cooc_def)
  with at ts show "{\<nu>. k \<langle>a\<bowtie>n\<rangle> \<nu>} = {\<nu>. \<sigma> \<langle>s\<bowtie>n\<rangle> \<nu>}"
    unfolding equiv_upto_def by simp
qed

lemma fequiv_equiv_upto:
  assumes "a \<Leftrightarrow> t" shows "equiv_upto n a t"
  unfolding equiv_upto_def
proof (intro allI impI)
  fix k \<kappa> assume "k \<langle>a\<bowtie>t\<rangle> \<kappa>"
  then obtain d\<^sub>0 where d\<^sub>0: "d\<^sub>0 \<in> D" "a d\<^sub>0 = k" "t d\<^sub>0 = \<kappa>" by (auto simp: cooc_def)
  from assms have "a \<Rrightarrow> t" "t \<Rrightarrow> a" by (auto simp: fequiv_def)
  with d\<^sub>0 show "{\<nu>. k \<langle>a\<bowtie>n\<rangle> \<nu>} = {\<nu>. \<kappa> \<langle>t\<bowtie>n\<rangle> \<nu>}"
    unfolding cooc_def determines_rows by metis
qed

lemma divides_equiv_upto:
  assumes "divides n t a" shows "equiv_upto n a t"
proof -
  from assms obtain i :: "'d \<Rightarrow> 'd"
    where sp: "splits (\<lambda>d. (t d, n d)) i" and eq: "a \<Leftrightarrow> (\<lambda>d. (t d, i d))"
    by (auto simp: divides_def)
  from eq have a_ti: "a \<Rrightarrow> (\<lambda>d. (t d, i d))" and ti_a: "(\<lambda>d. (t d, i d)) \<Rrightarrow> a"
    by (auto simp: fequiv_def)
  show ?thesis unfolding equiv_upto_def
  proof (intro allI impI)
    fix k \<kappa> assume "k \<langle>a\<bowtie>t\<rangle> \<kappa>"
    then obtain d\<^sub>0 where d\<^sub>0: "d\<^sub>0 \<in> D" "a d\<^sub>0 = k" "t d\<^sub>0 = \<kappa>" by (auto simp: cooc_def)
    have "\<kappa> \<langle>t\<bowtie>n\<rangle> \<nu>" if "k \<langle>a\<bowtie>n\<rangle> \<nu>" for \<nu>
    proof -
      from that obtain d where d: "d \<in> D" "a d = k" "n d = \<nu>" by (auto simp: cooc_def)
      from a_ti d d\<^sub>0 have "(t d, i d) = (t d\<^sub>0, i d\<^sub>0)" unfolding determines_rows by metis
      with d d\<^sub>0 show ?thesis by (auto simp: cooc_def)
    qed
    moreover have "k \<langle>a\<bowtie>n\<rangle> \<nu>" if "\<kappa> \<langle>t\<bowtie>n\<rangle> \<nu>" for \<nu>
    proof -
      from that obtain d where d: "d \<in> D" "t d = \<kappa>" "n d = \<nu>" by (auto simp: cooc_def)
      from sp d(1) d\<^sub>0(1) obtain e where e: "e \<in> D" "(t e, n e) = (t d, n d)" "i e = i d\<^sub>0"
        unfolding splits_rows by blast
      from e d d\<^sub>0 have "(t e, i e) = (t d\<^sub>0, i d\<^sub>0)" by simp
      with ti_a e(1) d\<^sub>0(1) have "a e = a d\<^sub>0" unfolding determines_rows by metis
      with e d d\<^sub>0 show ?thesis by (auto simp: cooc_def)
    qed
    ultimately show "{\<nu>. k \<langle>a\<bowtie>n\<rangle> \<nu>} = {\<nu>. \<kappa> \<langle>t\<bowtie>n\<rangle> \<nu>}" by blast
  qed
qed

subsection \<open>Equivalence modulo a grain\<close>

text \<open>\<open>a\<close> and \<open>t\<close> are equivalent modulo \<open>n\<close> when rows with distinct \<open>n\<close>-keys agree on \<open>a\<close>
  exactly when they agree on \<open>t\<close>.  This is a condition on pairs of rows, so it is inherited by
  every subset of rows; it is the largest such relation within @{const equiv_upto}.  At row grain
  it is functional equivalence; it is vacuous when both sides determine \<open>n\<close>.\<close>

definition equiv_mod :: "('d \<Rightarrow> 'c) \<Rightarrow> ('d \<Rightarrow> 'a) \<Rightarrow> ('d \<Rightarrow> 'b) \<Rightarrow> bool" where
  "equiv_mod n a t \<longleftrightarrow> (\<forall>d\<in>D. \<forall>d'\<in>D. n d \<noteq> n d' \<longrightarrow> (a d = a d' \<longleftrightarrow> t d = t d'))"

lemma equiv_mod_refl: "equiv_mod n a a"
  by (simp add: equiv_mod_def)

lemma equiv_mod_sym: "equiv_mod n a t \<Longrightarrow> equiv_mod n t a"
  by (simp add: equiv_mod_def)

lemma equiv_mod_trans: "equiv_mod n a t \<Longrightarrow> equiv_mod n t s \<Longrightarrow> equiv_mod n a s"
  by (simp add: equiv_mod_def)

text \<open>Adding the same component to both sides, and replacing either side by a functionally
  equivalent one, preserve the equivalence.\<close>

lemma equiv_mod_pair: "equiv_mod n a t \<Longrightarrow> equiv_mod n (\<lambda>d. (a d, m d)) (\<lambda>d. (t d, m d))"
  by (auto simp: equiv_mod_def)

lemma equiv_mod_fequiv: "a \<Leftrightarrow> a' \<Longrightarrow> t \<Leftrightarrow> t' \<Longrightarrow> equiv_mod n a t \<Longrightarrow> equiv_mod n a' t'"
  unfolding equiv_mod_def fequiv_def determines_rows by metis

lemma fequiv_equiv_mod: "a \<Leftrightarrow> t \<Longrightarrow> equiv_mod n a t"
  unfolding equiv_mod_def fequiv_def determines_rows by metis

lemma equiv_mod_equiv_upto:
  assumes "equiv_mod n a t" shows "equiv_upto n a t"
  unfolding equiv_upto_def
proof (intro allI impI)
  fix k \<kappa> assume "k \<langle>a\<bowtie>t\<rangle> \<kappa>"
  then obtain d\<^sub>0 where d\<^sub>0: "d\<^sub>0 \<in> D" "a d\<^sub>0 = k" "t d\<^sub>0 = \<kappa>" by (auto simp: cooc_def)
  have "\<kappa> \<langle>t\<bowtie>n\<rangle> \<nu>" if "k \<langle>a\<bowtie>n\<rangle> \<nu>" for \<nu>
  proof -
    from that obtain d where d: "d \<in> D" "a d = k" "n d = \<nu>" by (auto simp: cooc_def)
    show ?thesis
    proof (cases "n d = n d\<^sub>0")
      case True with d d\<^sub>0 show ?thesis by (auto simp: cooc_def)
    next
      case False
      with assms d d\<^sub>0 have "t d = t d\<^sub>0" unfolding equiv_mod_def by metis
      with d d\<^sub>0 show ?thesis by (auto simp: cooc_def)
    qed
  qed
  moreover have "k \<langle>a\<bowtie>n\<rangle> \<nu>" if "\<kappa> \<langle>t\<bowtie>n\<rangle> \<nu>" for \<nu>
  proof -
    from that obtain d where d: "d \<in> D" "t d = \<kappa>" "n d = \<nu>" by (auto simp: cooc_def)
    show ?thesis
    proof (cases "n d = n d\<^sub>0")
      case True with d d\<^sub>0 show ?thesis by (auto simp: cooc_def)
    next
      case False
      with assms d d\<^sub>0 have "a d = a d\<^sub>0" unfolding equiv_mod_def by metis
      with d d\<^sub>0 show ?thesis by (auto simp: cooc_def)
    qed
  qed
  ultimately show "{\<nu>. k \<langle>a\<bowtie>n\<rangle> \<nu>} = {\<nu>. \<kappa> \<langle>t\<bowtie>n\<rangle> \<nu>}" by blast
qed

end

lemma equiv_mod_subset:
  "D' \<subseteq> D \<Longrightarrow> relspace.equiv_mod D n a t \<Longrightarrow> relspace.equiv_mod D' n a t"
  unfolding relspace.equiv_mod_def by blast

end
