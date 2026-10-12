theory Definitions imports HOLCF begin

lemma (in pcpo) lub_empty[simp]: "{} <<| \<bottom>" by (simp add: is_lub_def)

context po begin

definition below_strict (infix \<open>\<sqsubset>\<close> 50) where "a \<sqsubset> b = (a \<sqsubseteq> b \<and> \<not>(b \<sqsubseteq> a))"

text \<open>Stated as a fact rather than a \<open>sublocale\<close>: a sublocale into a locale with derived constants
  breaks later subclasses whose assumptions need a finer sort (Isabelle class bug).\<close>

lemma below_order: "class.order below below_strict"
  by unfold_locales (fact below_strict_def below_refl below_trans below_antisym)+

theorem lub_below_iff': "A <<| a \<Longrightarrow> a \<sqsubseteq> x \<longleftrightarrow> (\<forall>y \<in> A. y \<sqsubseteq> x)"
  using is_lub_below_iff is_ub_def by blast

theorem lub_below_iff_b: "f ` A <<| a \<Longrightarrow> a \<sqsubseteq> x \<longleftrightarrow> (\<forall>y \<in> A. f y \<sqsubseteq> x)"
  using lub_below_iff' by blast

definition join (infixl \<open>\<squnion>\<close> 65) where
  "a \<squnion> b \<equiv> lub {a, b}"

lemma join_sym: "a \<squnion> b = b \<squnion> a"
  by (simp add: join_def insert_commute)

lemma join_idem[simp]: "a \<squnion> a = a"
  by (simp add: join_def)

lemma join_absorb: "a \<sqsubseteq> b \<Longrightarrow> a \<squnion> b = b"
  by (simp add: join_def lub_bin)

lemma join_absorb2: "a \<sqsubseteq> b \<Longrightarrow> b \<squnion> a = b"
  by (simp add: join_sym join_absorb)

lemma bin_join_ex_symm: "{a, b} <<| z \<longleftrightarrow> {b, a} <<| z"
  unfolding insert_commute ..

lemma binLubI:
  assumes "a \<sqsubseteq> w" "b \<sqsubseteq> w" "\<And>z. a \<sqsubseteq> z \<Longrightarrow> b \<sqsubseteq> z \<Longrightarrow> w \<sqsubseteq> z"
  shows "{a, b} <<| w"
  unfolding is_lub_def is_ub_def using assms by blast

definition "is_glb A a \<equiv> \<forall>b. (\<forall>x \<in> A. b \<sqsubseteq> x) \<longleftrightarrow> b \<sqsubseteq> a"

definition "glb A \<equiv> THE a. is_glb A a"

lemma is_glbI:
  assumes "\<And>x. x \<in> A \<Longrightarrow> a \<sqsubseteq> x"
    and "\<And>b. \<forall>x \<in> A. b \<sqsubseteq> x \<Longrightarrow> b \<sqsubseteq> a"
  shows "is_glb A a"
  unfolding is_glb_def
  using assms
  by (auto simp add: is_glb_def dest: below_trans)

lemma is_glb_unique: "is_glb A a \<Longrightarrow> is_glb A b \<Longrightarrow> a = b"
  unfolding is_glb_def by (blast intro: below_antisym)

lemma is_glb_glb: "is_glb A a \<Longrightarrow> is_glb A (glb A)"
  unfolding glb_def by (rule theI[OF _ is_glb_unique])

lemma glb_eqI: "is_glb A a \<Longrightarrow> glb A = a"
  using is_glb_unique[OF is_glb_glb] .

lemma is_glb_below: "is_glb S a \<Longrightarrow> x \<in> S \<Longrightarrow> a \<sqsubseteq> x"
  unfolding is_glb_def by auto

lemma is_glb_greatest: "is_glb S a \<Longrightarrow> (\<forall>x \<in> S. b \<sqsubseteq> x) \<Longrightarrow> b \<sqsubseteq> a"
  unfolding is_glb_def by auto

definition meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl \<open>\<sqinter>\<close> 70)
  where "a \<sqinter> b = glb {a, b}"

lemma meet_idem: "a \<sqinter> a = a"
  unfolding meet_def
  by (rule glb_eqI) (simp add: is_glb_def)

lemma meet_sym: "a \<sqinter> b = b \<sqinter> a"
  by (simp add: meet_def insert_commute)

lemma meet_absorb: "a \<sqsubseteq> b \<Longrightarrow> a \<sqinter> b = a"
  unfolding meet_def
  by (rule glb_eqI) (auto simp add: is_glb_def dest: below_trans)

lemma meet_absorb2: "a \<sqsubseteq> b \<Longrightarrow> b \<sqinter> a = a"
  by (simp add: meet_sym meet_absorb)

end

lemma (in pcpo) join_bottom[simp]: "\<bottom> \<squnion> a = a" "a \<squnion> \<bottom> = a"
  by (simp_all add: join_absorb join_absorb2)


lemma obtain_compact_chain:
  fixes x :: "'a::profinite"
  obtains X where "chain X" "\<forall>i. compact (X i)" "x = (\<Squnion>i. X i)"
proof -
  from compact_basis.obtain_principal_chain
  obtain B' where B': "\<forall>i. B' i \<sqsubseteq> B' (Suc i)" "up\<cdot>x = (\<Squnion>i. Rep_compact_basis (B' i))"
    .
  define X' where "X' i = Rep_compact_basis (B' i)" for i
  have "chain X'" unfolding X'_def using B'(1) by (rule compact_basis.ch2ch_principal)
  have upx: "up\<cdot>x = (\<Squnion>i. X' i)" unfolding X'_def by fact
  have "compact (X' i)" for i unfolding X'_def by simp
  obtain X n where upX: "\<forall>i. up\<cdot>(X i) = X' (i + n)"
    and "chain X" and x: "x = (\<Squnion>i. X i)"
    using \<open>chain X'\<close>
  proof (cases rule: up_chain_cases)
    case 1
    then have "(\<Squnion>i. X' i) = \<bottom>" by simp
    with upx show ?thesis by simp
  next
    case (2 X n)
    with upx show ?thesis using that by simp
  qed
  from upX \<open>\<And>i. compact (X' i)\<close> compact_upD have "\<forall>i. compact (X i)" 
    by metis
  from \<open>chain X\<close> this x show ?thesis by (rule that)
qed

lemma compact_induct':
  fixes x :: "'a::profinite"
  assumes adm: "adm P"
  assumes compact: "\<And>xx. compact xx \<Longrightarrow> xx \<sqsubseteq> x \<Longrightarrow> P xx"
  shows "P x"
proof -
  obtain X where X: "chain X" "\<forall>i. compact (X i)" "x = (\<Squnion>i. X i)"
    by (rule obtain_compact_chain)
  from X(1, 3) have "\<And>i. X i \<sqsubseteq> x" using is_ub_thelub by blast
  from X(2) this have "\<And>i. P (X i)" using compact by blast
  with adm[THEN admD, OF X(1)] X(3) show "P x" by presburger
qed

end