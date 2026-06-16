theory Koenigs imports Main begin

context
  fixes rel :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix \<open>\<sqsubseteq>\<close> 50)
begin

primrec winnow :: "nat \<Rightarrow> (nat \<Rightarrow> 'a set) \<Rightarrow> (nat \<Rightarrow> 'a set)"
  where winnow_0: "winnow 0 S = S"
  | winnow_suc: "winnow (Suc i) S j = {x \<in> winnow i S j. \<exists> y \<in> winnow i S (Suc j). x \<sqsubseteq> y}"

abbreviation (input) upper_le_set (infix \<open>\<preceq>\<sharp>\<close> 50)
  where "upper_le_set X Y \<equiv> \<forall>y \<in> Y. \<exists>x \<in> X. x \<sqsubseteq> y"

lemma winnow_chain: assumes "\<forall>i. S i \<preceq>\<sharp> S (Suc i)"
  shows "\<forall>i. winnow n S i \<preceq>\<sharp> winnow n S (Suc i)"
proof (induction n)
  case 0
  then show ?case using assms by simp
next
  case (Suc n)
  then show ?case by fastforce
qed

lemma winnow_ne_empty: assumes ne: "\<forall>i. S i \<noteq> {}" and chain:  "\<forall>i. S i \<preceq>\<sharp> S (Suc i)"
  shows "\<forall>i. winnow n S i \<noteq> {}"
proof (induction n)
  case 0
  then show ?case using ne by simp
next
  case (Suc n)
  with winnow_chain[of S n, OF chain]
  show ?case by fastforce
qed

lemma winnow_descending: "winnow (Suc n) S i \<subseteq> winnow n S i" by simp

lemma winnow_antimono: "antimono (\<lambda>n. winnow n S i)"
  unfolding antimono_iff_le_Suc by (simp add: winnow_descending)

definition winnow_fix where "winnow_fix S i = (\<Inter>n. winnow n S i)"

theorem descending_finite_chain:
  fixes C :: "nat \<Rightarrow> 'a set"
  assumes "\<forall>i. C (Suc i) \<subseteq> C i"
    and "\<forall>i. C i \<noteq> {}"
    and "finite (C 0)"
  shows "(\<Inter>i. C i) \<noteq> {}"
proof
  assume "(\<Inter>n. C n) = {}"
  then have "\<exists>n. x \<notin> C n" if "x \<in> C 0" for x by blast
  note Least = this[THEN LeastI_ex]
  have "antimono C" unfolding antimono_iff_le_Suc by fact
  note mono = this[THEN antimonoD]
  define I where "I \<equiv> {LEAST n. x \<notin> C n | x. x \<in> C 0}"
  with \<open>finite (C 0)\<close> have "finite I" by simp
  then have "n \<le> Max I" if "n \<in> I" for n by (simp add: that)
  with I_def mono Least have "x \<notin> C (Max I)" if "x \<in> C 0" for x
    using that by blast
  with mono \<open>\<forall>i. C i \<noteq> {}\<close> show False by blast
qed

lemma winnow_fix:
  assumes ne: "\<forall>i. S i \<noteq> {}"
    and finite: "\<forall>i. finite (S i)"
    and chain: "\<forall>i. S i \<preceq>\<sharp> S (Suc i)"
  shows winnow_fix_ne: "winnow_fix S i \<noteq> {}"
    and winnow_fix_strong_chain: "\<forall>x \<in> winnow_fix S i. \<exists>y \<in> winnow_fix S (Suc i). x \<sqsubseteq> y"
proof -
  show fix_ne: "winnow_fix S i \<noteq> {}"
    unfolding winnow_fix_def
  proof (intro allI descending_finite_chain winnow_descending)
    fix i
    show "winnow n S i \<noteq> {}" for n using winnow_ne_empty[OF ne chain] by simp
    show "finite (winnow 0 S i)" using finite by simp
  qed
  show "\<forall>x \<in> winnow_fix S i. \<exists>y \<in> winnow_fix S (Suc i). x \<sqsubseteq> y"
  proof (intro strip)
    fix x assume "x \<in> winnow_fix S i"
    then have "x \<in> winnow n S i" for n by (simp add: winnow_fix_def)
    then have "x \<in> winnow (Suc n) S i" for n .
    then have 1: "\<exists>y \<in> winnow n S (Suc i). x \<sqsubseteq> y" for n by simp
    have "(\<Inter>n. {y \<in> winnow n S (Suc i). x \<sqsubseteq> y}) \<noteq> {}"
    proof (intro descending_finite_chain allI, clarsimp)
      show "{y \<in> winnow n S (Suc i). x \<sqsubseteq> y} \<noteq> {}" for n
        using 1 by blast
      show "finite {y \<in> winnow 0 S (Suc i). x \<sqsubseteq> y}" by (simp add: finite)
    qed
    then show "\<exists>y \<in> winnow_fix S (Suc i). x \<sqsubseteq> y"
      unfolding winnow_fix_def by blast
  qed
qed

lemma winnow_fix_subset: "winnow_fix S i \<subseteq> S i"
  unfolding winnow_fix_def
  by (intro Inter_lower range_eqI[where x = 0]) simp

lemma obtain_infinite_path:
  fixes S :: "nat \<Rightarrow> 'a set"
  assumes ne: "\<And>i. S i \<noteq> {}" 
   and finite: "\<And>i. finite (S i)" 
   and chain: "\<And>i. S i \<preceq>\<sharp> S (Suc i)"
 obtains f where "\<forall>i. f i \<in> S i" and "\<forall>i. f i \<sqsubseteq> f (Suc i)"
proof -
  from winnow_fix assms
  have "winnow_fix S i \<noteq> {}" and "\<forall>x \<in> winnow_fix S i. \<exists>y \<in> winnow_fix S (Suc i). x \<sqsubseteq> y"
    for i
    by auto
  then have "\<exists>f. \<forall>i. f i \<in> winnow_fix S i \<and> f i \<sqsubseteq> f (Suc i)"
    by (intro dependent_nat_choice) fast+
  with winnow_fix_subset show thesis using that by blast
qed

end

end