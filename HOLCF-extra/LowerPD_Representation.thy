theory LowerPD_Representation
  imports HOLCF HOLCF.LowerPD Distributive

begin

definition lower_mem :: "'a::bifinite \<Rightarrow> ('a)\<flat> \<Rightarrow> bool" (infix \<open>\<in>\<flat>\<close> 50)
  where "x \<in>\<flat> X \<longleftrightarrow> {x}\<flat> \<union>\<flat> X = X"

definition lower_pd_set :: "('a::bifinite)\<flat> \<Rightarrow> 'a set"
where "lower_pd_set X \<equiv> {x. x \<in>\<flat> X}"

lemma lower_mem_equiv: "x \<in>\<flat> X \<longleftrightarrow> {x}\<flat> \<sqsubseteq> X"
  unfolding lower_mem_def by (simp add: lower_join_eq lower_pd_lattice.sup.absorb_iff2)

lemma lower_mem_principal: "x \<in>\<flat> {y}\<flat> \<longleftrightarrow> x \<sqsubseteq> y"
  unfolding lower_mem_equiv by simp

corollary lower_principal_rep: "lower_pd_set {y}\<flat> = {x. x \<sqsubseteq> y}"
  unfolding lower_mem_principal lower_pd_set_def ..

lemma lower_mem_union: "x \<in>\<flat> X \<union>\<flat> Y \<longleftrightarrow> x \<in>\<flat> X \<or> x \<in>\<flat> Y"
  unfolding lower_mem_equiv
  by (rule lower_unit_below_plus_iff)

corollary lowerset_union: "lower_pd_set (X \<union>\<flat> Y) = lower_pd_set X \<union> lower_pd_set Y"
  unfolding lower_mem_union lower_pd_set_def by blast

definition set_approximants :: "'a::bifinite set \<Rightarrow> 'a compact_basis set"
  where "set_approximants X \<equiv> \<Union>x \<in> X. approximants x"

lemma lower_pd_ideal_PDPlus:
  assumes "lower_le.ideal A"
    and "x \<in> A"
    and "y \<in> A"
  shows "PDPlus x y \<in> A"
proof -
  from assms obtain z where xy: "x \<le>\<flat> z" "y \<le>\<flat> z" and z: "z \<in> A"
    by (blast dest: lower_le.idealD2)
  from xy have "PDPlus x y \<le>\<flat> z" by (simp add: lower_le_PDPlus_iff)
  from assms(1) this z show "PDPlus x y \<in> A" by (rule lower_le.idealD3)
qed

definition lower_pd_set_ideal :: "'a::bifinite set \<Rightarrow> 'a pd_basis set"
  where "lower_pd_set_ideal A \<equiv> {Abs_pd_basis B | B. B \<subseteq> set_approximants A \<and> finite B \<and> B \<noteq> {}}"

lemma lower_pd_ideal_is_set_ideal:
  assumes ideal: "lower_le.ideal A"
  defines "KA \<equiv> (\<Union>P\<in>A. Rep_pd_basis P)"
  shows "A = {B. Rep_pd_basis B \<subseteq> KA}"
proof (rule subset_antisym)
  show "A \<subseteq> {B. Rep_pd_basis B \<subseteq> KA}" unfolding KA_def by blast
  show "{B. Rep_pd_basis B \<subseteq> KA} \<subseteq> A"
  proof (safe)
    fix B assume B: "Rep_pd_basis B \<subseteq> KA"
    {
      fix k assume "k \<in> Rep_pd_basis B"
      with B obtain P where 1: "P \<in> A" and 2: "k \<in> Rep_pd_basis P"
        unfolding KA_def by auto
      from 2 have "PDUnit k \<le>\<flat> P" unfolding lower_le_def
        by (auto simp add: Rep_PDUnit)
      from ideal this 1 have "PDUnit k \<in> A" by (rule lower_le.idealD3)
    }
    then have base: "k \<in> Rep_pd_basis B \<Longrightarrow> PDUnit k \<in> A" for k .
    have ind: "Rep_pd_basis C \<subseteq> Rep_pd_basis B \<Longrightarrow> C \<in> A" for C
    proof (induction C rule: pd_basis_induct)
      case (PDUnit a)
      then show ?case by (simp add: Rep_PDUnit base)
    next
      case (PDPlus t u)
      then have "t \<in> A" "u \<in> A" by (simp_all add: Rep_PDPlus)
      with ideal show "PDPlus t u \<in> A" by (rule lower_pd_ideal_PDPlus)
    qed
    then show "B \<in> A" by simp
  qed
qed

lemma exists_approx: "\<exists>b. b \<in> approximants (a::'a::bifinite)"
  by (metis compact_basis.ideal_rep below.ideal_def)

lemma set_approximants_ne: "A \<noteq> {} \<Longrightarrow> set_approximants A \<noteq> {}"
proof -
  assume "A \<noteq> {}"
  then obtain a where a: "a \<in> A" by blast
  obtain b where "b \<in> approximants a" by (rule exE[OF exists_approx])
  with a have "b \<in> set_approximants A" unfolding set_approximants_def by blast
  then show ?thesis by auto
qed

lemma lower_pd_set_ideal_mem: "x \<in> lower_pd_set_ideal A \<longleftrightarrow> Rep_pd_basis x \<subseteq> set_approximants A"
  unfolding lower_pd_set_ideal_def mem_Collect_eq
proof
  assume "\<exists>B. x = Abs_pd_basis B \<and> B \<subseteq> set_approximants A \<and> finite B \<and> B \<noteq> {}"
  then obtain B where x: "x = Abs_pd_basis B" and B: "B \<subseteq> set_approximants A"
    and dom: "finite B" "B \<noteq> {}" by blast
  from dom have "B \<in> pd_basis" unfolding pd_basis_def by simp
  then have "Rep_pd_basis x = B" unfolding x by (rule Abs_pd_basis_inverse)

  with B show "Rep_pd_basis x \<subseteq> set_approximants A" by simp
next
  assume B: "Rep_pd_basis x \<subseteq> set_approximants A"
  show "\<exists>B. x = Abs_pd_basis B \<and>
        B \<subseteq> set_approximants A \<and> finite B \<and> B \<noteq> {}"
    by (rule exI[of _ "Rep_pd_basis x"])
      (simp add: B Rep_pd_basis_inverse[of x])
qed

lemma set_approximants_alt: "set_approximants A = {x. \<exists>y \<in> A. Rep_compact_basis x \<sqsubseteq> y}"
  unfolding set_approximants_def approximants_def by blast

lemma set_approximants_downward_closed: "y \<sqsubseteq> x \<Longrightarrow> x \<in> set_approximants A \<Longrightarrow> y \<in> set_approximants A"
  unfolding set_approximants_def approximants_def compact_le_def
  using below_trans by blast

lemma lower_pd_set_ideal: assumes "A \<noteq> {}" shows "lower_le.ideal (lower_pd_set_ideal A)"
proof (rule lower_le.idealI)
  obtain b where "b \<in> set_approximants A" using set_approximants_ne[OF assms] by blast
  then have "Abs_pd_basis {b} \<in> lower_pd_set_ideal A"
    unfolding lower_pd_set_ideal_def by blast
  then show "\<exists>x. x \<in> lower_pd_set_ideal A" by auto
next
  fix x y assume "x \<in> lower_pd_set_ideal A" "y \<in> lower_pd_set_ideal A"
  then have xy: "Rep_pd_basis x \<subseteq> set_approximants A" "Rep_pd_basis y \<subseteq> set_approximants A"
    by (simp_all add: lower_pd_set_ideal_mem)
  then have "Rep_pd_basis (PDPlus x y) \<subseteq> set_approximants A"
    unfolding Rep_PDPlus by simp
  then have *: "PDPlus x y \<in> lower_pd_set_ideal A" by (simp add: lower_pd_set_ideal_mem)
  show "\<exists>z \<in> lower_pd_set_ideal A. x \<le>\<flat> z \<and> y \<le>\<flat> z"
    using * PDPlus_lower_le PDPlus_commute[of x y] by metis
next
  show "x \<le>\<flat> y \<Longrightarrow> y \<in> lower_pd_set_ideal A \<Longrightarrow> x \<in> lower_pd_set_ideal A"
    for x y
    unfolding lower_pd_set_ideal_mem lower_le_def
    using set_approximants_downward_closed by blast
qed

definition lower_pd_of_set :: "('a::bifinite) set \<Rightarrow> 'a lower_pd"
  where "lower_pd_of_set A = Abs_lower_pd (lower_pd_set_ideal A)"

lemma Rep_lower_pd_of_set: assumes "A \<noteq> {}" shows "Rep_lower_pd (lower_pd_of_set A) = lower_pd_set_ideal A"
  unfolding lower_pd_of_set_def
  by (rule Abs_lower_pd_inverse) (simp add: lower_pd_set_ideal[OF assms])

definition lowerset :: "'a::po set \<Rightarrow> 'a set"
  where "lowerset A = {y. \<exists>x \<in> A. y \<sqsubseteq> x}"

lemma lowerset_idem: "lowerset (lowerset A) = lowerset A"
  unfolding lowerset_def using below_trans by blast

definition completion :: "'a::cpo set \<Rightarrow> 'a set"
  where "completion A = {(\<Squnion>i. S i) | S. chain S \<and> range S \<subseteq> A}"

definition closure :: "'a::cpo set \<Rightarrow> 'a set"
  where "closure A = completion (lowerset A)"

lemma approximant_lower:
  "(x::'a::bifinite compact_basis) \<in> set_approximants A \<Longrightarrow> Rep_compact_basis x \<in> lowerset A"
  unfolding set_approximants_alt lowerset_def by blast

lemma lower_approximants:
  assumes "x \<in> lowerset A"
  shows "approximants x \<subseteq> set_approximants A"
proof -
  from assms[unfolded lowerset_def] obtain y where 1: "y \<in> A" and 2: "x \<sqsubseteq> y"
    by blast
  from 2 have "approximants x \<subseteq> approximants y" by (rule compact_basis.rep_mono)
  also have "approximants y \<subseteq> set_approximants A"
    unfolding set_approximants_def using 1 by auto
  finally show ?thesis .
qed

lemma adm_set_approximants: "adm (\<lambda>x::'a::bifinite. approximants x \<subseteq> set_approximants A)"
  by (rule admI) (blast dest: compact_basis.rep_lub)

lemma adm_not_set_approximants: "adm (\<lambda>x::'a::bifinite. \<not>(approximants x \<subseteq> set_approximants A))"
  apply (rule admI)
  unfolding compact_basis.rep_lub by fast

lemma adm_lower_mem: "adm (\<lambda>x. x \<in>\<flat> A)"
  unfolding lower_mem_equiv
  by auto

lemma adm_not_lower_mem: "adm (\<lambda>x. \<not>(x \<in>\<flat> A))"
  unfolding lower_mem_equiv
  by auto

lemma closure_approximants: "approximants (x::'a::bifinite) \<subseteq> set_approximants A \<longleftrightarrow>
  x \<in> closure A"
proof
  assume "x \<in> closure A"
  from this[unfolded closure_def completion_def]
  obtain S where x: "x = (\<Squnion>i. S i)" and chain: "chain S" and ss: "range S \<subseteq> lowerset A"
    by blast
  from ss lower_approximants have "\<And>i. approximants (S i) \<subseteq> set_approximants A"
    by auto
  then have "approximants (\<Squnion>i. S i) \<subseteq> set_approximants A"
    unfolding compact_basis.rep_lub[OF chain] by auto
  with x show "approximants x \<subseteq> set_approximants A" by simp
next
  assume *: "approximants x \<subseteq> set_approximants A"
  obtain approx :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where "approx_chain approx" 
    by (rule exE[OF bifinite])
  then interpret approx_chain approx .
  define S where "S i = approx i\<cdot>x" for i
  have chain: "chain S" unfolding S_def by auto
  have subset: "range S \<subseteq> lowerset A" unfolding S_def
  proof (rule subsetI, erule rangeE, hypsubst)
    fix i
    have "Abs_compact_basis (approx i\<cdot>x) \<in> approximants x"
      by (simp add: approximants_def approx_below)
    then have "Abs_compact_basis (approx i\<cdot>x) \<in> set_approximants A"
      by (rule subsetD[OF *])
    then have "Rep_compact_basis (Abs_compact_basis (approx i\<cdot>x)) \<in> lowerset A"
      by (rule approximant_lower)
    then show "approx i\<cdot>x \<in> lowerset A" by simp
  qed
  have lub: "x = (\<Squnion>i. S i)" unfolding S_def using lub_approx
    contlub_cfun_fun[OF chain_approx] by simp
  from lub chain subset show "x \<in> closure A"
    unfolding closure_def completion_def
    by auto
qed

lemma Abs_lower_pd_principal:
  "Rep_lower_pd (lower_principal x) = {u. u \<le>\<flat> x}"
  unfolding lower_principal_def 
  by (intro Abs_lower_pd_inverse CollectI lower_le.ideal_principal)

lemma compact_pd_set_ideal:
  assumes "A \<noteq> {}"
  shows "{u. u \<le>\<flat> PDUnit b} \<subseteq> lower_pd_set_ideal A \<longleftrightarrow> approximants (Rep_compact_basis b) \<subseteq> set_approximants A"
proof -
  have "{u. u \<le>\<flat> PDUnit b} \<subseteq> lower_pd_set_ideal A \<longleftrightarrow> PDUnit b \<in> lower_pd_set_ideal A"
    (is "?ss \<longleftrightarrow> ?mem")
  proof
    show "?ss \<Longrightarrow> ?mem" using lower_le_refl[of "PDUnit b"] by blast
    show "?mem \<Longrightarrow> ?ss"
      using lower_le.idealD3[OF lower_pd_set_ideal[OF assms], of _ "PDUnit b"]
      by blast
  qed
  also have "PDUnit b \<in> lower_pd_set_ideal A \<longleftrightarrow> b \<in> set_approximants A"
    unfolding lower_pd_set_ideal_mem Rep_PDUnit by simp
  also have "b \<in> set_approximants A \<longleftrightarrow> approximants (Rep_compact_basis b) \<subseteq> set_approximants A"
    unfolding approximants_def
    using set_approximants_downward_closed
    by auto
  finally show ?thesis .
qed

lemma lower_pd_of_set_mem_iff:
  assumes "(A::'a::bifinite set) \<noteq> {}"
  shows "x \<in>\<flat> lower_pd_of_set A \<longleftrightarrow> x \<in> closure A"
  unfolding closure_approximants[symmetric]
proof (induction x rule: compact_basis.principal_induct)
  case 1
  show "adm (\<lambda>a. (a \<in>\<flat> lower_pd_of_set A) =
             (approximants a \<subseteq> set_approximants A))"
    by (simp add: adm_set_approximants adm_not_set_approximants
        adm_lower_mem adm_not_lower_mem)
next
  case (2 b)
  have "Rep_compact_basis b \<in>\<flat> lower_pd_of_set A \<longleftrightarrow>
    lower_principal (PDUnit b) \<sqsubseteq> lower_pd_of_set A"
    unfolding lower_mem_equiv by simp
  also have "... \<longleftrightarrow> {u. u \<le>\<flat> PDUnit b} \<subseteq> lower_pd_set_ideal A"
    unfolding below_lower_pd_def
      Rep_lower_pd_of_set[OF assms]
      Abs_lower_pd_principal
    ..
  also note compact_pd_set_ideal[OF assms]
  finally show ?case .
qed

lemma lower_ext_subset:
  assumes "\<And>p. {p}\<flat> \<sqsubseteq> x \<Longrightarrow> {p}\<flat> \<sqsubseteq> y"
  shows "x \<sqsubseteq> y"
proof -
  have "lower_principal h \<sqsubseteq> x \<Longrightarrow> lower_principal h \<sqsubseteq> y" for h
  proof (induct rule: pd_basis_induct)
    case (PDUnit a)
    then show ?case using assms[of "Rep_compact_basis a"] by simp
  next
    case (PDPlus t u)
    from PDPlus.prems have "lower_principal t \<sqsubseteq> x" "lower_principal u \<sqsubseteq> x"
      by (metis lower_plus_below_iff lower_plus_principal)+
    with PDPlus.hyps show "lower_principal (PDPlus t u) \<sqsubseteq> y"
      by (metis lower_plus_below_iff lower_plus_principal)
  qed

  then have "h \<sqsubseteq> x \<Longrightarrow> h \<sqsubseteq> y" for h
    by (induct h rule: lower_pd.principal_induct, simp)
  then show "x \<sqsubseteq> y" by simp
qed

lemma lower_pd_set_iff: "x \<sqsubseteq> y \<longleftrightarrow> lower_pd_set x \<subseteq> lower_pd_set y"
  unfolding lower_pd_set_def lower_mem_equiv
  by (auto intro: lower_ext_subset below_trans)

corollary lower_pd_set_inj: "lower_pd_set x = lower_pd_set y \<Longrightarrow> x = y"
  by (auto intro!: below_antisym simp add: lower_pd_set_iff)

lemma lower_pd_set_meet[simp]: "lower_pd_set (x \<sqinter> y) = lower_pd_set x \<inter> lower_pd_set y"
  unfolding lower_pd_set_def lower_mem_equiv
  by auto

lemma lower_pd_set_join[simp]: "lower_pd_set (x \<squnion> y) = lower_pd_set x \<union> lower_pd_set y"
  unfolding lower_join_eq lower_pd_set_def lower_mem_equiv lower_unit_below_plus_iff
  by auto

instance lower_pd :: (bifinite) distributive_cpo
proof
  fix a b c :: "'a lower_pd"
  show "c \<sqinter> (a \<squnion> b) = (c \<sqinter> a) \<squnion> (c \<sqinter> b)"
    by (auto intro!: lower_pd_set_inj)
qed

end