theory LowerPD_Representation
  imports HOLCF HOLCF.LowerPD Distributive Directed Top

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

section \<open>Lower powerdomain elements are generated by their maximal members\<close>

text \<open>The members of a lower powerdomain element form a Scott-closed set: closed downwards
  and under directed lubs.  By Zorn's lemma every member lies below a maximal one, so the set is
  the down-closure of its maximal members.\<close>

lemma lower_mem_below: "x \<in>\<flat> X \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> y \<in>\<flat> X"
  unfolding lower_mem_equiv by (blast intro: below_trans monofun_cfun_arg)

lemma lower_mem_directed_lub:
  assumes D: "directed D" "D \<noteq> {}" and mem: "\<And>x. x \<in> D \<Longrightarrow> x \<in>\<flat> X"
  shows "lub D \<in>\<flat> X"
proof -
  obtain C where C: "chain C" "\<forall>i. C i \<in> D" "(\<Squnion>i. C i) = lub D"
    by (rule obtain_directed_chain[OF D])
  have "(\<Squnion>i. C i) \<in>\<flat> X" using admD[OF adm_lower_mem C(1)] C(2) mem by blast
  then show ?thesis by (simp only: C(3))
qed

lemma lower_mem_lub: "chain Y \<Longrightarrow> x \<in>\<flat> Y i \<Longrightarrow> x \<in>\<flat> (\<Squnion>i. Y i)"
  unfolding lower_mem_equiv by (blast intro: below_trans is_ub_thelub)

lemma lower_mem_chain: "chain Y \<Longrightarrow> x \<in>\<flat> Y i \<Longrightarrow> i \<le> j \<Longrightarrow> x \<in>\<flat> Y j"
  unfolding lower_mem_equiv by (blast intro: below_trans chain_mono)

lemma lower_mem_compact_lub:
  assumes Y: "chain Y" and x: "compact x" and mem: "x \<in>\<flat> (\<Squnion>i. Y i)"
  obtains i where "x \<in>\<flat> Y i"
  using mem compact_below_lub_iff[OF compact_lower_unit[OF x] Y] by (auto simp add: lower_mem_equiv)

definition lower_maximal :: "'a::bifinite lower_pd \<Rightarrow> 'a set" where
  "lower_maximal X = {m. m \<in>\<flat> X \<and> (\<forall>y. y \<in>\<flat> X \<longrightarrow> m \<sqsubseteq> y \<longrightarrow> y = m)}"

theorem lower_mem_maximal_above:
  assumes x: "x \<in>\<flat> X"
  obtains m where "m \<in> lower_maximal X" "x \<sqsubseteq> m"
proof -
  have ub: "\<exists>a \<in> lower_pd_set X. T <| a" if T: "T \<subseteq> lower_pd_set X" "directed T" for T
  proof (cases "T = {}")
    case True
    then show ?thesis using x by (auto simp add: lower_pd_set_def)
  next
    case False
    have "lub T \<in>\<flat> X" using lower_mem_directed_lub[OF T(2) False] T(1) by (auto simp add: lower_pd_set_def)
    then show ?thesis using is_lubD1[OF directed_lub[OF T(2)]] by (auto simp add: lower_pd_set_def)
  qed
  obtain m where "m \<in> lower_pd_set X" "x \<sqsubseteq> m" "\<forall>z \<in> lower_pd_set X. m \<sqsubseteq> z \<longrightarrow> m = z"
    using obtain_total_above[of x "lower_pd_set X"] x ub by (auto simp add: lower_pd_set_def)
  then show ?thesis using that by (auto simp add: lower_maximal_def lower_pd_set_def)
qed

corollary lower_pd_set_maximal: "lower_pd_set X = lowerset (lower_maximal X)"
proof (rule set_eqI, rule iffI)
  fix x assume "x \<in> lower_pd_set X"
  then obtain m where "m \<in> lower_maximal X" "x \<sqsubseteq> m"
    by (auto elim: lower_mem_maximal_above simp add: lower_pd_set_def)
  then show "x \<in> lowerset (lower_maximal X)" unfolding lowerset_def by blast
next
  fix x assume "x \<in> lowerset (lower_maximal X)"
  then show "x \<in> lower_pd_set X"
    unfolding lowerset_def lower_maximal_def lower_pd_set_def by (blast intro: lower_mem_below)
qed

section \<open>Binds and maps through members\<close>

text \<open>A bind lies below \<open>Z\<close> as soon as the image of every member does.\<close>

lemma lower_bind_below:
  assumes g: "\<And>y. y \<in>\<flat> Y \<Longrightarrow> g\<cdot>y \<sqsubseteq> Z"
  shows "lower_bind\<cdot>Y\<cdot>g \<sqsubseteq> Z"
proof -
  have "W \<sqsubseteq> Y \<longrightarrow> lower_bind\<cdot>W\<cdot>g \<sqsubseteq> Z" for W
  proof (induct W rule: lower_pd_induct)
    case adm
    then show ?case by (rule adm_imp) simp_all
  next
    case (lower_unit a)
    then show ?case using g by (simp add: lower_mem_equiv)
  next
    case (lower_plus xs ys)
    then show ?case by simp
  qed
  then show ?thesis by simp
qed

lemma lower_bind_mem:
  "y \<in>\<flat> Y \<Longrightarrow> g\<cdot>y \<sqsubseteq> lower_bind\<cdot>Y\<cdot>g"
  using monofun_cfun_fun[of "lower_bind\<cdot>{y}\<flat>" "lower_bind\<cdot>Y" g]
  by (simp add: lower_mem_equiv monofun_cfun_arg)

lemma lower_map_mem: "x \<in>\<flat> X \<Longrightarrow> f\<cdot>x \<in>\<flat> lower_map\<cdot>f\<cdot>X"
  using monofun_cfun_arg[of "{x}\<flat>" X "lower_map\<cdot>f"] by (simp add: lower_mem_equiv)

text \<open>A compact member of an image lies below the image of a member.\<close>

lemma lower_map_mem_compact:
  assumes v: "compact v" and mem: "v \<in>\<flat> lower_map\<cdot>f\<cdot>Z"
  obtains w where "w \<in>\<flat> Z" "v \<sqsubseteq> f\<cdot>w"
proof -
  have "\<forall>v. compact v \<longrightarrow> {v}\<flat> \<sqsubseteq> lower_map\<cdot>f\<cdot>W \<longrightarrow> (\<exists>w. w \<in>\<flat> W \<and> v \<sqsubseteq> f\<cdot>w)" for W
  proof (induct W rule: lower_pd_induct)
    case adm
    show ?case
    proof (rule admI, intro allI impI)
      fix Ws v assume Ws: "chain Ws"
        and all: "\<forall>i. \<forall>v. compact v \<longrightarrow> {v}\<flat> \<sqsubseteq> lower_map\<cdot>f\<cdot>(Ws i) \<longrightarrow> (\<exists>w. w \<in>\<flat> Ws i \<and> v \<sqsubseteq> f\<cdot>w)"
        and v: "compact v" and le: "{v}\<flat> \<sqsubseteq> lower_map\<cdot>f\<cdot>(\<Squnion>i. Ws i)"
      have "{v}\<flat> \<sqsubseteq> (\<Squnion>i. lower_map\<cdot>f\<cdot>(Ws i))" using le by (simp add: contlub_cfun_arg[OF Ws])
      then obtain i where "{v}\<flat> \<sqsubseteq> lower_map\<cdot>f\<cdot>(Ws i)"
        using compact_below_lub_iff[OF compact_lower_unit[OF v]] Ws by auto
      then obtain w where "w \<in>\<flat> Ws i" "v \<sqsubseteq> f\<cdot>w" using all v by blast
      then show "\<exists>w. w \<in>\<flat> (\<Squnion>i. Ws i) \<and> v \<sqsubseteq> f\<cdot>w" using lower_mem_lub[OF Ws] by blast
    qed
  next
    case (lower_unit a)
    then show ?case by (auto simp add: lower_mem_principal)
  next
    case (lower_plus xs ys)
    then show ?case by (auto simp add: lower_mem_union)
  qed
  then show ?thesis using v mem that by (auto simp add: lower_mem_equiv)
qed

section \<open>Rows with a top adjoined\<close>

text \<open>Mapping \<open>down\<close> over a lower powerdomain element identifies it with a Top-free element of the
  lower powerdomain over rows with a top: its members are exactly the \<open>down\<close>s of the members.\<close>

lemma lower_mem_map_down: "v \<in>\<flat> lower_map\<cdot>down\<cdot>Z \<longleftrightarrow> (\<exists>w. w \<in>\<flat> Z \<and> v = down\<cdot>w)"
proof
  assume mem: "v \<in>\<flat> lower_map\<cdot>down\<cdot>Z"
  obtain ap :: "nat \<Rightarrow> 'a top \<rightarrow> 'a top" where ap: "approx_chain ap" using bifinite by blast
  have "\<exists>u. ap i\<cdot>v = down\<cdot>u \<and> u \<in>\<flat> Z" for i
  proof -
    have "ap i\<cdot>v \<in>\<flat> lower_map\<cdot>down\<cdot>Z"
      using mem approx_chain.approx_below[OF ap] by (rule lower_mem_below)
    then obtain w where w: "w \<in>\<flat> Z" and le: "ap i\<cdot>v \<sqsubseteq> down\<cdot>w"
      using approx_chain.compact_approx[OF ap] by (blast elim: lower_map_mem_compact)
    show ?thesis
    proof (cases "ap i\<cdot>v")
      case (down u)
      then show ?thesis using le w by (auto intro: lower_mem_below)
    next
      case Top
      then show ?thesis using le by simp
    qed
  qed
  then obtain us where us: "\<And>i. ap i\<cdot>v = down\<cdot>(us i)" and mem_us: "\<And>i. us i \<in>\<flat> Z" by metis
  have ch: "chain us"
  proof (rule chainI)
    fix i
    have "ap i\<cdot>v \<sqsubseteq> ap (Suc i)\<cdot>v"
      using approx_chain.chain_approx[OF ap] by (simp add: monofun_cfun_fun chainE)
    then show "us i \<sqsubseteq> us (Suc i)" by (simp add: us)
  qed
  have "v = (\<Squnion>i. ap i\<cdot>v)"
    using approx_chain.chain_approx[OF ap] approx_chain.lub_approx[OF ap] by (simp flip: contlub_cfun_fun)
  also have "\<dots> = down\<cdot>(\<Squnion>i. us i)" by (simp add: us contlub_cfun_arg[OF ch])
  finally show "\<exists>w. w \<in>\<flat> Z \<and> v = down\<cdot>w" using admD[OF adm_lower_mem ch] mem_us by blast
next
  assume "\<exists>w. w \<in>\<flat> Z \<and> v = down\<cdot>w"
  then show "v \<in>\<flat> lower_map\<cdot>down\<cdot>Z" by (auto intro: lower_map_mem)
qed

lemma Top_not_mem_map_down: "\<not> Top \<in>\<flat> lower_map\<cdot>down\<cdot>Z"
  by (simp add: lower_mem_map_down)

lemma lower_map_down_below_iff: "lower_map\<cdot>down\<cdot>X \<sqsubseteq> lower_map\<cdot>down\<cdot>Z \<longleftrightarrow> X \<sqsubseteq> Z"
proof
  assume le: "lower_map\<cdot>down\<cdot>X \<sqsubseteq> lower_map\<cdot>down\<cdot>Z"
  have "x \<in>\<flat> Z" if "x \<in>\<flat> X" for x
  proof -
    have "down\<cdot>x \<in>\<flat> lower_map\<cdot>down\<cdot>Z"
      using lower_map_mem[OF that] le by (auto simp add: lower_mem_equiv intro: below_trans)
    then show ?thesis by (auto simp add: lower_mem_map_down dest: down_inject)
  qed
  then show "X \<sqsubseteq> Z" by (simp add: lower_pd_set_iff lower_pd_set_def subset_iff)
qed (rule monofun_cfun_arg)

text \<open>Conversely every Top-free element comes from the rows.\<close>

theorem lower_map_down_onto:
  assumes nT: "\<not> Top \<in>\<flat> Y"
  obtains Z where "Y = lower_map\<cdot>down\<cdot>Z"
proof -
  define A where "A = {w. down\<cdot>w \<in>\<flat> Y}"
  have "\<bottom> \<in> A" unfolding A_def lower_mem_equiv by (simp add: down_strict)
  then have ne: "A \<noteq> {}" by blast
  have down_closed: "lowerset A = A"
    unfolding lowerset_def A_def by (auto intro: lower_mem_below monofun_cfun_arg)
  have closed: "closure A = A"
  proof (rule set_eqI, rule iffI)
    fix x assume "x \<in> closure A"
    then obtain S where x: "x = (\<Squnion>i. S i)" and S: "chain S" "range S \<subseteq> A"
      unfolding closure_def completion_def down_closed by blast
    have "down\<cdot>(\<Squnion>i. S i) = (\<Squnion>i. down\<cdot>(S i))" by (rule contlub_cfun_arg[OF S(1)])
    moreover have "(\<Squnion>i. down\<cdot>(S i)) \<in>\<flat> Y"
      using admD[OF adm_lower_mem ch2ch_Rep_cfunR[OF S(1)]] S(2) unfolding A_def by blast
    ultimately show "x \<in> A" by (simp add: A_def x)
  next
    fix x assume "x \<in> A"
    then show "x \<in> closure A"
      unfolding closure_def completion_def down_closed
      by (auto intro!: exI[of _ "\<lambda>_. x"])
  qed
  have "Y = lower_map\<cdot>down\<cdot>(lower_pd_of_set A)"
  proof (rule lower_pd_set_inj, rule set_eqI)
    fix v
    have "v \<in>\<flat> Y \<longleftrightarrow> (\<exists>w. w \<in> A \<and> v = down\<cdot>w)"
      using nT by (cases v) (auto simp add: A_def dest: down_inject)
    then show "v \<in> lower_pd_set Y \<longleftrightarrow> v \<in> lower_pd_set (lower_map\<cdot>down\<cdot>(lower_pd_of_set A))"
      by (simp add: lower_pd_set_def lower_mem_map_down lower_pd_of_set_mem_iff[OF ne] closed)
  qed
  then show ?thesis by (rule that)
qed

end
