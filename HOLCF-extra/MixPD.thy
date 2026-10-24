theory MixPD
  imports HOLCF
begin

section \<open>The mixed powerdomain\<close>

text \<open>Gunter's mixed powerdomain, built like HOLCF's own powerdomains as the ideal completion
  of a preordered basis. A basis element is a pair of finite sets of compact elements: a
  definite part @{text l}, ordered as in the lower (Hoare) powerdomain, and a possible part
  @{text u}, ordered as in the upper (Smyth) powerdomain, subject to the consistency condition
  that every definite element lies above some possible one. Both parts may be empty: an empty
  definite part is the Hoare bottom (nothing definite), an empty possible part the Smyth top
  (definitely nothing), which consistency forces to come with an empty definite part.\<close>

subsection \<open>Finite sets of compact basis elements, possibly empty\<close>

typedef 'a::bifinite pde_basis = "{S::'a compact_basis set. finite S}"
  by auto

lemma finite_Rep_pde_basis [simp]: "finite (Rep_pde_basis u)"
  using Rep_pde_basis [of u] by simp

lemma Abs_pde_basis_inverse' [simp]: "finite S \<Longrightarrow> Rep_pde_basis (Abs_pde_basis S) = S"
  by (simp add: Abs_pde_basis_inverse)

lemma pde_basis_countable: "\<exists>f::'a::bifinite pde_basis \<Rightarrow> nat. inj f"
proof -
  obtain g :: "'a compact_basis \<Rightarrow> nat" where "inj g"
    using compact_basis.countable ..
  hence image_g_eq: "g ` A = g ` B \<longleftrightarrow> A = B" for A B
    by (rule inj_image_eq_iff)
  have "inj (\<lambda>t. set_encode (g ` Rep_pde_basis t))"
    by (simp add: inj_on_def set_encode_eq image_g_eq Rep_pde_basis_inject)
  thus ?thesis by blast
qed

definition PDEEmpty :: "'a::bifinite pde_basis"
  where "PDEEmpty = Abs_pde_basis {}"

definition PDEUnit :: "'a::bifinite compact_basis \<Rightarrow> 'a pde_basis"
  where "PDEUnit a = Abs_pde_basis {a}"

definition PDEPlus :: "'a::bifinite pde_basis \<Rightarrow> 'a pde_basis \<Rightarrow> 'a pde_basis"
  where "PDEPlus t u = Abs_pde_basis (Rep_pde_basis t \<union> Rep_pde_basis u)"

lemma Rep_PDEEmpty [simp]: "Rep_pde_basis PDEEmpty = {}"
  unfolding PDEEmpty_def by simp

lemma Rep_PDEUnit [simp]: "Rep_pde_basis (PDEUnit a) = {a}"
  unfolding PDEUnit_def by simp

lemma Rep_PDEPlus [simp]: "Rep_pde_basis (PDEPlus t u) = Rep_pde_basis t \<union> Rep_pde_basis u"
  unfolding PDEPlus_def by simp

lemma PDEPlus_assoc: "PDEPlus (PDEPlus t u) v = PDEPlus t (PDEPlus u v)"
  unfolding Rep_pde_basis_inject [symmetric] by (simp add: Un_assoc)

lemma PDEPlus_commute: "PDEPlus t u = PDEPlus u t"
  unfolding Rep_pde_basis_inject [symmetric] by (simp add: Un_commute)

lemma PDEPlus_absorb [simp]: "PDEPlus t t = t"
  unfolding Rep_pde_basis_inject [symmetric] by simp

lemma PDEPlus_empty [simp]: "PDEPlus t PDEEmpty = t" "PDEPlus PDEEmpty t = t"
  unfolding Rep_pde_basis_inject [symmetric] by simp_all

lemma pde_basis_induct [case_names PDEEmpty PDEPlus]:
  assumes PDEEmpty: "P PDEEmpty"
  assumes PDEPlus: "\<And>a t. P t \<Longrightarrow> P (PDEPlus (PDEUnit a) t)"
  shows "P x"
proof (induct x)
  case (Abs_pde_basis y)
  then have "finite y" by simp
  then show ?case
  proof (induct rule: finite_induct)
    case empty
    show ?case by (rule PDEEmpty [unfolded PDEEmpty_def])
  next
    case (insert x F)
    from insert(3) have "P (PDEPlus (PDEUnit x) (Abs_pde_basis F))" by (rule PDEPlus)
    with insert(1) show ?case
      by (simp add: PDEUnit_def PDEPlus_def)
  qed
qed


subsection \<open>Upper and lower preorders on possibly empty sets\<close>

definition upper_le0 :: "'a::bifinite pde_basis \<Rightarrow> 'a pde_basis \<Rightarrow> bool"
  where "upper_le0 u v \<longleftrightarrow> (\<forall>y\<in>Rep_pde_basis v. \<exists>x\<in>Rep_pde_basis u. x \<sqsubseteq> y)"

definition lower_le0 :: "'a::bifinite pde_basis \<Rightarrow> 'a pde_basis \<Rightarrow> bool"
  where "lower_le0 u v \<longleftrightarrow> (\<forall>x\<in>Rep_pde_basis u. \<exists>y\<in>Rep_pde_basis v. x \<sqsubseteq> y)"

lemma upper_le0_refl [simp]: "upper_le0 t t"
  unfolding upper_le0_def by fast

lemma lower_le0_refl [simp]: "lower_le0 t t"
  unfolding lower_le0_def by fast

lemma upper_le0_trans: "\<lbrakk>upper_le0 t u; upper_le0 u v\<rbrakk> \<Longrightarrow> upper_le0 t v"
  unfolding upper_le0_def by (meson below_trans)

lemma lower_le0_trans: "\<lbrakk>lower_le0 t u; lower_le0 u v\<rbrakk> \<Longrightarrow> lower_le0 t v"
  unfolding lower_le0_def by (meson below_trans)


subsection \<open>The basis of the mixed powerdomain\<close>

typedef 'a::bifinite mix_basis = "{(l, u). upper_le0 u l} :: ('a pde_basis \<times> 'a pde_basis) set"
  by (rule exI [of _ "(PDEEmpty, PDEEmpty)"]) (simp add: upper_le0_def)

definition mdef :: "'a::bifinite mix_basis \<Rightarrow> 'a pde_basis"
  where "mdef t = fst (Rep_mix_basis t)"

definition mposs :: "'a::bifinite mix_basis \<Rightarrow> 'a pde_basis"
  where "mposs t = snd (Rep_mix_basis t)"

definition MixB :: "'a::bifinite pde_basis \<Rightarrow> 'a pde_basis \<Rightarrow> 'a mix_basis"
  where "MixB l u = Abs_mix_basis (l, u)"

lemma mix_basis_consistent: "upper_le0 (mposs t) (mdef t)"
  using Rep_mix_basis [of t] by (auto simp: mdef_def mposs_def split: prod.splits)

lemma mix_basis_consistentD:
  "x \<in> Rep_pde_basis (mdef t) \<Longrightarrow> \<exists>y\<in>Rep_pde_basis (mposs t). y \<sqsubseteq> x"
  using mix_basis_consistent [of t] unfolding upper_le0_def by fast

lemma mix_basis_eqI: "\<lbrakk>mdef s = mdef t; mposs s = mposs t\<rbrakk> \<Longrightarrow> s = t"
  by (simp add: mdef_def mposs_def Rep_mix_basis_inject [symmetric] prod_eq_iff)

lemma mdef_MixB [simp]: "upper_le0 u l \<Longrightarrow> mdef (MixB l u) = l"
  by (simp add: mdef_def MixB_def Abs_mix_basis_inverse)

lemma mposs_MixB [simp]: "upper_le0 u l \<Longrightarrow> mposs (MixB l u) = u"
  by (simp add: mposs_def MixB_def Abs_mix_basis_inverse)

lemma mix_basis_countable: "\<exists>f::'a::bifinite mix_basis \<Rightarrow> nat. inj f"
proof -
  obtain g :: "'a pde_basis \<Rightarrow> nat" where g: "inj g"
    using pde_basis_countable ..
  have "inj (\<lambda>t. prod_encode (g (mdef t), g (mposs t)))"
    by (rule injI) (auto dest: injD [OF g] intro: mix_basis_eqI)
  thus ?thesis by blast
qed

definition mix_le :: "'a::bifinite mix_basis \<Rightarrow> 'a mix_basis \<Rightarrow> bool"
  where "mix_le s t \<longleftrightarrow> lower_le0 (mdef s) (mdef t) \<and> upper_le0 (mposs s) (mposs t)"

lemma mix_le_refl [simp]: "mix_le t t"
  unfolding mix_le_def by simp

lemma mix_le_trans: "\<lbrakk>mix_le t u; mix_le u v\<rbrakk> \<Longrightarrow> mix_le t v"
  unfolding mix_le_def by (blast intro: lower_le0_trans upper_le0_trans)

interpretation mix_le: preorder mix_le
  by (rule preorder.intro, rule mix_le_refl, rule mix_le_trans)


subsection \<open>Type definition\<close>

typedef 'a::bifinite mix_pd = "{S::'a mix_basis set. mix_le.ideal S}"
  by (rule mix_le.ex_ideal)

instantiation mix_pd :: (bifinite) below
begin

definition
  "x \<sqsubseteq> y \<longleftrightarrow> Rep_mix_pd x \<subseteq> Rep_mix_pd y"

instance ..
end

instance mix_pd :: (bifinite) po
  using type_definition_mix_pd below_mix_pd_def
  by (rule mix_le.typedef_ideal_po)

instance mix_pd :: (bifinite) cpo
  using type_definition_mix_pd below_mix_pd_def
  by (rule mix_le.typedef_ideal_cpo)

definition mix_principal :: "'a::bifinite mix_basis \<Rightarrow> 'a mix_pd"
  where "mix_principal t = Abs_mix_pd {u. mix_le u t}"

interpretation mix_pd: ideal_completion mix_le mix_principal Rep_mix_pd
  using type_definition_mix_pd below_mix_pd_def
  using mix_principal_def mix_basis_countable
  by (rule mix_le.typedef_ideal_completion)

text \<open>The mixed powerdomain is pointed: the least element has no definite part and the
  possible part @{text "{\<bottom>}"}.\<close>

definition MBot :: "'a::bifinite mix_basis"
  where "MBot = MixB PDEEmpty (PDEUnit compact_bot)"

lemma mix_le_MBot [simp]: "mix_le MBot t"
  unfolding MBot_def mix_le_def by (simp add: upper_le0_def lower_le0_def)

lemma mix_pd_minimal: "mix_principal MBot \<sqsubseteq> ys"
  by (induct ys rule: mix_pd.principal_induct, simp, simp)

instance mix_pd :: (bifinite) pcpo
  by intro_classes (fast intro: mix_pd_minimal)

lemma inst_mix_pd_pcpo: "\<bottom> = mix_principal MBot"
  by (rule mix_pd_minimal [THEN bottomI, symmetric])


subsection \<open>Basis constructors\<close>

definition MUnit :: "'a::bifinite compact_basis \<Rightarrow> 'a mix_basis"
  where "MUnit a = MixB (PDEUnit a) (PDEUnit a)"

definition MPlus :: "'a::bifinite mix_basis \<Rightarrow> 'a mix_basis \<Rightarrow> 'a mix_basis"
  where "MPlus s t = MixB (PDEPlus (mdef s) (mdef t)) (PDEPlus (mposs s) (mposs t))"

definition MEmpty :: "'a::bifinite mix_basis"
  where "MEmpty = MixB PDEEmpty PDEEmpty"

definition MMaybe :: "'a::bifinite mix_basis \<Rightarrow> 'a mix_basis"
  where "MMaybe t = MixB PDEEmpty (mposs t)"

text \<open>A set read both definitely and possibly.\<close>

definition MSet :: "'a::bifinite pde_basis \<Rightarrow> 'a mix_basis"
  where "MSet s = MixB s s"

lemma mdef_MUnit [simp]: "mdef (MUnit a) = PDEUnit a"
  and mposs_MUnit [simp]: "mposs (MUnit a) = PDEUnit a"
  unfolding MUnit_def by simp_all

lemma mdef_MPlus [simp]: "mdef (MPlus s t) = PDEPlus (mdef s) (mdef t)"
  and mposs_MPlus [simp]: "mposs (MPlus s t) = PDEPlus (mposs s) (mposs t)"
proof -
  have "upper_le0 (PDEPlus (mposs s) (mposs t)) (PDEPlus (mdef s) (mdef t))"
    using mix_basis_consistent [of s] mix_basis_consistent [of t]
    unfolding upper_le0_def by fastforce
  then show "mdef (MPlus s t) = PDEPlus (mdef s) (mdef t)"
    and "mposs (MPlus s t) = PDEPlus (mposs s) (mposs t)"
    unfolding MPlus_def by simp_all
qed

lemma mdef_MEmpty [simp]: "mdef MEmpty = PDEEmpty"
  and mposs_MEmpty [simp]: "mposs MEmpty = PDEEmpty"
  unfolding MEmpty_def by (simp_all add: upper_le0_def)

lemma mdef_MMaybe [simp]: "mdef (MMaybe t) = PDEEmpty"
  and mposs_MMaybe [simp]: "mposs (MMaybe t) = mposs t"
  unfolding MMaybe_def by (simp_all add: upper_le0_def)

lemma mdef_MSet [simp]: "mdef (MSet s) = s"
  and mposs_MSet [simp]: "mposs (MSet s) = s"
  unfolding MSet_def by simp_all

lemma mdef_MBot [simp]: "mdef MBot = PDEEmpty"
  and mposs_MBot [simp]: "mposs MBot = PDEUnit compact_bot"
  unfolding MBot_def by (simp_all add: upper_le0_def)

lemma MUnit_mix_mono: "a \<sqsubseteq> b \<Longrightarrow> mix_le (MUnit a) (MUnit b)"
  unfolding mix_le_def upper_le0_def lower_le0_def by simp

lemma MPlus_mix_mono: "\<lbrakk>mix_le s t; mix_le u v\<rbrakk> \<Longrightarrow> mix_le (MPlus s u) (MPlus t v)"
  unfolding mix_le_def upper_le0_def lower_le0_def by auto

lemma MMaybe_mix_mono: "mix_le s t \<Longrightarrow> mix_le (MMaybe s) (MMaybe t)"
  unfolding mix_le_def upper_le0_def lower_le0_def by simp

lemma MMaybe_mix_le: "mix_le (MMaybe t) t"
  unfolding mix_le_def upper_le0_def lower_le0_def by auto

lemma MMaybe_mix_le_MEmpty: "mix_le (MMaybe t) MEmpty"
  unfolding mix_le_def upper_le0_def lower_le0_def by simp

text \<open>Every basis element is its definite part, read as a set, plus its possible part,
  read as a set and weakened to possible.\<close>

lemma mix_basis_decomp:
  "mix_le t (MPlus (MSet (mdef t)) (MMaybe (MSet (mposs t))))"
  "mix_le (MPlus (MSet (mdef t)) (MMaybe (MSet (mposs t)))) t"
  using mix_basis_consistentD [of _ t]
  unfolding mix_le_def upper_le0_def lower_le0_def by auto

lemma MSet_PDEEmpty: "MSet PDEEmpty = MEmpty"
  by (rule mix_basis_eqI) simp_all

lemma MSet_PDEPlus: "MSet (PDEPlus (PDEUnit a) s) = MPlus (MUnit a) (MSet s)"
  by (rule mix_basis_eqI) simp_all



subsection \<open>Unit, plus, empty and maybe\<close>

definition mix_unit :: "'a::bifinite \<rightarrow> 'a mix_pd"
  where "mix_unit = compact_basis.extension (\<lambda>a. mix_principal (MUnit a))"

definition mix_plus :: "'a::bifinite mix_pd \<rightarrow> 'a mix_pd \<rightarrow> 'a mix_pd"
  where "mix_plus = mix_pd.extension (\<lambda>t. mix_pd.extension (\<lambda>u.
      mix_principal (MPlus t u)))"

abbreviation mix_add :: "'a::bifinite mix_pd \<Rightarrow> 'a mix_pd \<Rightarrow> 'a mix_pd" (infixl \<open>\<union>\<^sub>m\<close> 65)
  where "xs \<union>\<^sub>m ys \<equiv> mix_plus\<cdot>xs\<cdot>ys"

definition mix_empty :: "'a::bifinite mix_pd"
  where "mix_empty = mix_principal MEmpty"

definition mix_maybe :: "'a::bifinite mix_pd \<rightarrow> 'a mix_pd"
  where "mix_maybe = mix_pd.extension (\<lambda>t. mix_principal (MMaybe t))"

lemma mix_unit_Rep_compact_basis [simp]:
  "mix_unit\<cdot>(Rep_compact_basis a) = mix_principal (MUnit a)"
  unfolding mix_unit_def
  by (simp add: compact_basis.extension_principal MUnit_mix_mono)

lemma mix_plus_principal [simp]:
  "mix_principal t \<union>\<^sub>m mix_principal u = mix_principal (MPlus t u)"
  unfolding mix_plus_def
  by (simp add: mix_pd.extension_principal mix_pd.extension_mono MPlus_mix_mono)

lemma mix_maybe_principal [simp]:
  "mix_maybe\<cdot>(mix_principal t) = mix_principal (MMaybe t)"
  unfolding mix_maybe_def
  by (simp add: mix_pd.extension_principal MMaybe_mix_mono)

lemma mix_principal_eqI: "\<lbrakk>mdef s = mdef t; mposs s = mposs t\<rbrakk> \<Longrightarrow> mix_principal s = mix_principal t"
  by (drule (1) mix_basis_eqI) simp

interpretation mix_add: semilattice_neutr mix_add mix_empty
proof
  fix xs ys zs :: "'a mix_pd"
  show "(xs \<union>\<^sub>m ys) \<union>\<^sub>m zs = xs \<union>\<^sub>m (ys \<union>\<^sub>m zs)"
    apply (induct xs rule: mix_pd.principal_induct, simp)
    apply (induct ys rule: mix_pd.principal_induct, simp)
    apply (induct zs rule: mix_pd.principal_induct, simp)
    apply (simp, rule mix_principal_eqI, simp_all add: PDEPlus_assoc)
    done
  show "xs \<union>\<^sub>m ys = ys \<union>\<^sub>m xs"
    apply (induct xs rule: mix_pd.principal_induct, simp)
    apply (induct ys rule: mix_pd.principal_induct, simp)
    apply (simp, rule mix_principal_eqI, simp_all add: PDEPlus_commute)
    done
  show "xs \<union>\<^sub>m xs = xs"
    apply (induct xs rule: mix_pd.principal_induct, simp)
    apply (simp, rule mix_principal_eqI, simp_all)
    done
  show "xs \<union>\<^sub>m mix_empty = xs"
    apply (induct xs rule: mix_pd.principal_induct, simp)
    apply (simp add: mix_empty_def, rule mix_principal_eqI, simp_all)
    done
qed

lemmas mix_plus_assoc = mix_add.assoc
lemmas mix_plus_commute = mix_add.commute
lemmas mix_plus_absorb = mix_add.idem
lemmas mix_plus_left_commute = mix_add.left_commute
lemmas mix_plus_left_absorb = mix_add.left_idem
lemmas mix_plus_empty1 [simp] = mix_add.left_neutral
lemmas mix_plus_empty2 [simp] = mix_add.right_neutral

lemmas mix_plus_ac = mix_plus_assoc mix_plus_commute mix_plus_left_commute
lemmas mix_plus_aci = mix_plus_ac mix_plus_absorb mix_plus_left_absorb

lemma mix_maybe_plus [simp]: "mix_maybe\<cdot>(xs \<union>\<^sub>m ys) = mix_maybe\<cdot>xs \<union>\<^sub>m mix_maybe\<cdot>ys"
  apply (induct xs rule: mix_pd.principal_induct, simp)
  apply (induct ys rule: mix_pd.principal_induct, simp)
  apply (simp, rule mix_principal_eqI, simp_all)
  done

lemma mix_maybe_maybe [simp]: "mix_maybe\<cdot>(mix_maybe\<cdot>xs) = mix_maybe\<cdot>xs"
  apply (induct xs rule: mix_pd.principal_induct, simp)
  apply (simp, rule mix_principal_eqI, simp_all)
  done

lemma mix_maybe_empty [simp]: "mix_maybe\<cdot>mix_empty = mix_empty"
  by (simp add: mix_empty_def, rule mix_principal_eqI, simp_all)

text \<open>A collection absorbs its own weakening.\<close>

lemma mix_plus_maybe_absorb [simp]: "xs \<union>\<^sub>m mix_maybe\<cdot>xs = xs"
  apply (induct xs rule: mix_pd.principal_induct, simp)
  apply (simp, rule mix_principal_eqI, simp_all)
  done

lemma mix_maybe_below: "mix_maybe\<cdot>xs \<sqsubseteq> xs"
  apply (induct xs rule: mix_pd.principal_induct, simp)
  apply (simp add: MMaybe_mix_le)
  done

lemma mix_maybe_below_empty: "mix_maybe\<cdot>xs \<sqsubseteq> mix_empty"
  apply (induct xs rule: mix_pd.principal_induct, simp)
  apply (simp add: mix_empty_def MMaybe_mix_le_MEmpty)
  done

text \<open>On weakened collections, plus is the Smyth meet.\<close>

lemma mix_plus_maybe_below1: "xs \<union>\<^sub>m mix_maybe\<cdot>ys \<sqsubseteq> xs"
proof -
  have "xs \<union>\<^sub>m mix_maybe\<cdot>ys \<sqsubseteq> xs \<union>\<^sub>m mix_empty"
    by (rule monofun_cfun_arg, rule mix_maybe_below_empty)
  then show ?thesis by simp
qed

lemma mix_maybe_greatest:
  "\<lbrakk>mix_maybe\<cdot>xs \<sqsubseteq> ys; mix_maybe\<cdot>xs \<sqsubseteq> zs\<rbrakk> \<Longrightarrow> mix_maybe\<cdot>xs \<sqsubseteq> ys \<union>\<^sub>m zs"
  by (subst mix_plus_absorb [of "mix_maybe\<cdot>xs", symmetric])
    (erule (1) monofun_cfun [OF monofun_cfun_arg])

lemma mix_unit_below_iff [simp]: "mix_unit\<cdot>x \<sqsubseteq> mix_unit\<cdot>y \<longleftrightarrow> x \<sqsubseteq> y"
  apply (induct x rule: compact_basis.principal_induct, simp)
  apply (induct y rule: compact_basis.principal_induct, simp)
  apply (simp add: mix_le_def upper_le0_def lower_le0_def)
  done

lemma mix_unit_eq_iff [simp]: "mix_unit\<cdot>x = mix_unit\<cdot>y \<longleftrightarrow> x = y"
  unfolding po_eq_conv by simp

lemma mix_bottom_maybe_unit: "\<bottom> = mix_maybe\<cdot>(mix_unit\<cdot>\<bottom>)"
proof -
  have "mix_maybe\<cdot>(mix_unit\<cdot>(Rep_compact_basis compact_bot)) = mix_principal MBot"
    by (simp only: mix_unit_Rep_compact_basis mix_maybe_principal, rule mix_principal_eqI, simp_all)
  then show ?thesis unfolding Rep_compact_bot inst_mix_pd_pcpo by (rule sym)
qed

lemma mix_maybe_strict [simp]: "mix_maybe\<cdot>\<bottom> = \<bottom>"
  by (subst (1 2) mix_bottom_maybe_unit) (rule mix_maybe_maybe)

lemma compact_mix_unit: "compact x \<Longrightarrow> compact (mix_unit\<cdot>x)"
  by (auto dest!: compact_basis.compact_imp_principal)

lemma compact_mix_plus [simp]: "\<lbrakk>compact xs; compact ys\<rbrakk> \<Longrightarrow> compact (xs \<union>\<^sub>m ys)"
  by (auto dest!: mix_pd.compact_imp_principal)

lemma compact_mix_maybe [simp]: "compact xs \<Longrightarrow> compact (mix_maybe\<cdot>xs)"
  by (auto dest!: mix_pd.compact_imp_principal)

lemma compact_mix_empty [simp]: "compact mix_empty"
  by (simp add: mix_empty_def)


subsection \<open>Induction\<close>

lemma mix_pd_induct [case_names adm mix_empty mix_unit mix_plus mix_maybe, induct type: mix_pd]:
  assumes P: "adm P"
  assumes empty: "P mix_empty"
  assumes unit: "\<And>x. P (mix_unit\<cdot>x)"
  assumes plus: "\<And>xs ys. \<lbrakk>P xs; P ys\<rbrakk> \<Longrightarrow> P (xs \<union>\<^sub>m ys)"
  assumes maybe: "\<And>xs. P xs \<Longrightarrow> P (mix_maybe\<cdot>xs)"
  shows "P (xs::'a::bifinite mix_pd)"
proof (induct xs rule: mix_pd.principal_induct)
  have set: "P (mix_principal (MSet s))" for s
  proof (induct s rule: pde_basis_induct)
    case PDEEmpty
    then show ?case using empty by (simp add: MSet_PDEEmpty mix_empty_def)
  next
    case (PDEPlus a t)
    then show ?case
      unfolding MSet_PDEPlus mix_plus_principal [symmetric] mix_unit_Rep_compact_basis [symmetric]
      by (rule plus [OF unit])
  qed
  show "P (mix_principal t)" for t
  proof -
    have eq: "mix_principal t = mix_principal (MSet (mdef t)) \<union>\<^sub>m mix_maybe\<cdot>(mix_principal (MSet (mposs t)))"
      by (simp add: mix_pd.principal_eq_iff mix_basis_decomp)
    show ?thesis by (subst eq) (rule plus [OF set maybe [OF set]])
  qed
qed (rule P)



subsection \<open>Finite sums\<close>

interpretation mix_Sum: comm_monoid_set mix_add mix_empty ..

lemma mix_Sum_absorb:
  "\<lbrakk>finite A; x \<in> A\<rbrakk> \<Longrightarrow> g x \<union>\<^sub>m mix_Sum.F g A = mix_Sum.F g A"
  by (simp add: mix_Sum.remove mix_plus_left_absorb)

lemma mix_Sum_insert' [simp]:
  "finite A \<Longrightarrow> mix_Sum.F g (insert x A) = g x \<union>\<^sub>m mix_Sum.F g A"
  by (cases "x \<in> A") (simp_all add: insert_absorb mix_Sum_absorb)

lemma mix_Sum_union:
  "\<lbrakk>finite A; finite B\<rbrakk> \<Longrightarrow> mix_Sum.F g (A \<union> B) = mix_Sum.F g A \<union>\<^sub>m mix_Sum.F g B"
  by (induct A rule: finite_induct) (simp_all add: mix_plus_assoc)

lemma cont_mix_Sum [simp, cont2cont]: "cont (\<lambda>f. mix_Sum.F (\<lambda>a. f\<cdot>(g a)) S)"
proof (cases "finite S")
  case True
  then show ?thesis by (induct S rule: finite_induct) simp_all
qed simp

text \<open>Weakened sums are ordered as in the upper powerdomain.\<close>

lemma mix_maybe_Sum_mono:
  assumes mono: "\<And>a b. a \<sqsubseteq> b \<Longrightarrow> g a \<sqsubseteq> g b"
  assumes fin: "finite U" "finite U'"
  assumes le: "\<forall>y'\<in>U'. \<exists>y\<in>U. y \<sqsubseteq> y'"
  shows "mix_maybe\<cdot>(mix_Sum.F g U) \<sqsubseteq> mix_maybe\<cdot>(mix_Sum.F g U')"
  using fin(2) le
proof (induct U' rule: finite_induct)
  case empty
  then show ?case by (simp add: mix_maybe_below_empty)
next
  case (insert y' U')
  from insert(4) obtain y where y: "y \<in> U" "y \<sqsubseteq> y'" by auto
  have "mix_maybe\<cdot>(mix_Sum.F g U) = mix_maybe\<cdot>(g y) \<union>\<^sub>m mix_maybe\<cdot>(mix_Sum.F g U)"
    by (simp only: mix_maybe_plus [symmetric] mix_Sum_absorb [OF fin(1) y(1)])
  also have "\<dots> \<sqsubseteq> mix_maybe\<cdot>(g y)"
    by (rule mix_plus_maybe_below1)
  also have "\<dots> \<sqsubseteq> mix_maybe\<cdot>(g y')"
    by (rule monofun_cfun_arg, rule mono, rule y(2))
  finally have "mix_maybe\<cdot>(mix_Sum.F g U) \<sqsubseteq> mix_maybe\<cdot>(g y')" .
  moreover from insert(3,4) have "mix_maybe\<cdot>(mix_Sum.F g U) \<sqsubseteq> mix_maybe\<cdot>(mix_Sum.F g U')"
    by simp
  ultimately show ?case
    using insert(1) by (simp add: mix_maybe_greatest)
qed

text \<open>A sum below a lower-larger sum is absorbed, given the weakening of the latter.\<close>

lemma mix_Sum_lower_absorb:
  assumes mono: "\<And>a b. a \<sqsubseteq> b \<Longrightarrow> g a \<sqsubseteq> g b"
  assumes fin: "finite L" "finite L'"
  assumes le: "\<forall>x\<in>L. \<exists>x'\<in>L'. x \<sqsubseteq> x'"
  shows "mix_Sum.F g L \<union>\<^sub>m mix_maybe\<cdot>(mix_Sum.F g L') \<sqsubseteq> mix_Sum.F g L'"
  using fin(1) le
proof (induct L rule: finite_induct)
  case empty
  then show ?case by (simp add: mix_maybe_below)
next
  case (insert x L)
  from insert(4) obtain x' where x': "x' \<in> L'" "x \<sqsubseteq> x'" by auto
  from insert(3,4) have IH: "mix_Sum.F g L \<union>\<^sub>m mix_maybe\<cdot>(mix_Sum.F g L') \<sqsubseteq> mix_Sum.F g L'"
    by simp
  have "mix_Sum.F g (insert x L) \<union>\<^sub>m mix_maybe\<cdot>(mix_Sum.F g L')
      = g x \<union>\<^sub>m (mix_Sum.F g L \<union>\<^sub>m mix_maybe\<cdot>(mix_Sum.F g L'))"
    using insert(1) by (simp add: mix_plus_assoc)
  also have "\<dots> \<sqsubseteq> g x' \<union>\<^sub>m mix_Sum.F g L'"
    by (rule monofun_cfun [OF monofun_cfun_arg [OF mono [OF x'(2)]] IH])
  also have "\<dots> = mix_Sum.F g L'"
    by (rule mix_Sum_absorb [OF fin(2) x'(1)])
  finally show ?case .
qed


subsection \<open>Monadic bind\<close>

definition mix_bind_basis :: "'a::bifinite mix_basis \<Rightarrow> ('a \<rightarrow> 'b mix_pd) \<rightarrow> 'b::bifinite mix_pd"
  where "mix_bind_basis t = (\<Lambda> f.
    mix_Sum.F (\<lambda>a. f\<cdot>(Rep_compact_basis a)) (Rep_pde_basis (mdef t)) \<union>\<^sub>m
    mix_maybe\<cdot>(mix_Sum.F (\<lambda>a. f\<cdot>(Rep_compact_basis a)) (Rep_pde_basis (mposs t))))"

lemma mix_bind_basis_beta:
  "mix_bind_basis t\<cdot>f =
    mix_Sum.F (\<lambda>a. f\<cdot>(Rep_compact_basis a)) (Rep_pde_basis (mdef t)) \<union>\<^sub>m
    mix_maybe\<cdot>(mix_Sum.F (\<lambda>a. f\<cdot>(Rep_compact_basis a)) (Rep_pde_basis (mposs t)))"
  unfolding mix_bind_basis_def by simp

lemma mono_Rep_compact_basis_app:
  "a \<sqsubseteq> b \<Longrightarrow> f\<cdot>(Rep_compact_basis a) \<sqsubseteq> f\<cdot>(Rep_compact_basis b)"
  by (rule monofun_cfun_arg) (simp add: compact_le_def)

lemma mix_bind_basis_mono:
  assumes "mix_le s t"
  shows "mix_bind_basis s \<sqsubseteq> mix_bind_basis t"
proof (rule cfun_belowI)
  fix f :: "'a \<rightarrow> 'b::bifinite mix_pd"
  define g where "g a = f\<cdot>(Rep_compact_basis a)" for a
  have mono: "a \<sqsubseteq> b \<Longrightarrow> g a \<sqsubseteq> g b" for a b
    unfolding g_def by (rule mono_Rep_compact_basis_app)
  let ?F = "\<lambda>A. mix_Sum.F g (Rep_pde_basis A)"
  from assms have lo: "lower_le0 (mdef s) (mdef t)" and up: "upper_le0 (mposs s) (mposs t)"
    unfolding mix_le_def by simp_all
  have P1: "mix_maybe\<cdot>(?F (mposs s)) \<sqsubseteq> mix_maybe\<cdot>(?F (mposs t))"
    using up unfolding upper_le0_def by (intro mix_maybe_Sum_mono mono) simp_all
  have "\<forall>x'\<in>Rep_pde_basis (mdef t). \<exists>y\<in>Rep_pde_basis (mposs s). y \<sqsubseteq> x'"
    using up mix_basis_consistentD [of _ t] unfolding upper_le0_def by (meson below_trans)
  then have P2: "mix_maybe\<cdot>(?F (mposs s)) \<sqsubseteq> mix_maybe\<cdot>(?F (mdef t))"
    by (intro mix_maybe_Sum_mono mono) simp_all
  have "?F (mdef s) \<union>\<^sub>m mix_maybe\<cdot>(?F (mposs s))
      \<sqsubseteq> ?F (mdef s) \<union>\<^sub>m (mix_maybe\<cdot>(?F (mposs t)) \<union>\<^sub>m mix_maybe\<cdot>(?F (mdef t)))"
    by (rule monofun_cfun_arg, rule mix_maybe_greatest [OF P1 P2])
  also have "\<dots> = (?F (mdef s) \<union>\<^sub>m mix_maybe\<cdot>(?F (mdef t))) \<union>\<^sub>m mix_maybe\<cdot>(?F (mposs t))"
    by (simp only: mix_plus_ac)
  also have "\<dots> \<sqsubseteq> ?F (mdef t) \<union>\<^sub>m mix_maybe\<cdot>(?F (mposs t))"
    using lo unfolding lower_le0_def
    by (intro monofun_cfun_fun monofun_cfun_arg mix_Sum_lower_absorb mono) simp_all
  finally show "mix_bind_basis s\<cdot>f \<sqsubseteq> mix_bind_basis t\<cdot>f"
    by (simp only: mix_bind_basis_beta g_def [abs_def])
qed

definition mix_bind :: "'a::bifinite mix_pd \<rightarrow> ('a \<rightarrow> 'b mix_pd) \<rightarrow> 'b::bifinite mix_pd"
  where "mix_bind = mix_pd.extension mix_bind_basis"

lemma mix_bind_principal [simp]: "mix_bind\<cdot>(mix_principal t) = mix_bind_basis t"
  unfolding mix_bind_def
  by (rule mix_pd.extension_principal) (erule mix_bind_basis_mono)

lemma mix_bind_unit [simp]: "mix_bind\<cdot>(mix_unit\<cdot>x)\<cdot>f = f\<cdot>x"
  by (induct x rule: compact_basis.principal_induct, simp, simp add: mix_bind_basis_beta)

lemma mix_bind_plus [simp]:
  "mix_bind\<cdot>(xs \<union>\<^sub>m ys)\<cdot>f = mix_bind\<cdot>xs\<cdot>f \<union>\<^sub>m mix_bind\<cdot>ys\<cdot>f"
  apply (induct xs rule: mix_pd.principal_induct, simp)
  apply (induct ys rule: mix_pd.principal_induct, simp)
  apply (simp add: mix_bind_basis_beta mix_Sum_union mix_plus_ac)
  done

lemma mix_bind_empty [simp]: "mix_bind\<cdot>mix_empty\<cdot>f = mix_empty"
  unfolding mix_empty_def mix_bind_principal mix_bind_basis_beta
  by (simp add: mix_empty_def [symmetric])

lemma mix_bind_maybe [simp]: "mix_bind\<cdot>(mix_maybe\<cdot>xs)\<cdot>f = mix_maybe\<cdot>(mix_bind\<cdot>xs\<cdot>f)"
proof (induct xs rule: mix_pd.principal_induct)
  fix t
  define g where "g a = f\<cdot>(Rep_compact_basis a)" for a
  have mono: "a \<sqsubseteq> b \<Longrightarrow> g a \<sqsubseteq> g b" for a b
    unfolding g_def by (rule mono_Rep_compact_basis_app)
  let ?D = "mix_maybe\<cdot>(mix_Sum.F g (Rep_pde_basis (mdef t)))"
  let ?P = "mix_maybe\<cdot>(mix_Sum.F g (Rep_pde_basis (mposs t)))"
  have "?P \<sqsubseteq> ?D"
    using mix_basis_consistentD [of _ t] by (intro mix_maybe_Sum_mono mono) simp_all
  then have "?P = ?D \<union>\<^sub>m ?P"
    by (intro below_antisym mix_maybe_greatest)
      (simp_all add: mix_plus_maybe_below1 mix_plus_commute [of ?D])
  then show "mix_bind\<cdot>(mix_maybe\<cdot>(mix_principal t))\<cdot>f = mix_maybe\<cdot>(mix_bind\<cdot>(mix_principal t)\<cdot>f)"
    by (simp add: mix_bind_basis_beta g_def [abs_def])
qed simp

lemma mix_bind_strict [simp]: "mix_bind\<cdot>\<bottom>\<cdot>f = mix_maybe\<cdot>(f\<cdot>\<bottom>)"
  by (subst mix_bottom_maybe_unit) simp

lemma mix_bind_bind:
  "mix_bind\<cdot>(mix_bind\<cdot>xs\<cdot>f)\<cdot>g = mix_bind\<cdot>xs\<cdot>(\<Lambda> x. mix_bind\<cdot>(f\<cdot>x)\<cdot>g)"
  by (induct xs) simp_all


subsection \<open>Map\<close>

definition mix_map :: "('a::bifinite \<rightarrow> 'b::bifinite) \<rightarrow> 'a mix_pd \<rightarrow> 'b mix_pd"
  where "mix_map = (\<Lambda> f xs. mix_bind\<cdot>xs\<cdot>(\<Lambda> x. mix_unit\<cdot>(f\<cdot>x)))"

lemma mix_map_unit [simp]: "mix_map\<cdot>f\<cdot>(mix_unit\<cdot>x) = mix_unit\<cdot>(f\<cdot>x)"
  unfolding mix_map_def by simp

lemma mix_map_plus [simp]: "mix_map\<cdot>f\<cdot>(xs \<union>\<^sub>m ys) = mix_map\<cdot>f\<cdot>xs \<union>\<^sub>m mix_map\<cdot>f\<cdot>ys"
  unfolding mix_map_def by simp

lemma mix_map_empty [simp]: "mix_map\<cdot>f\<cdot>mix_empty = mix_empty"
  unfolding mix_map_def by simp

lemma mix_map_maybe [simp]: "mix_map\<cdot>f\<cdot>(mix_maybe\<cdot>xs) = mix_maybe\<cdot>(mix_map\<cdot>f\<cdot>xs)"
  unfolding mix_map_def by simp

lemma mix_map_bottom [simp]: "mix_map\<cdot>f\<cdot>\<bottom> = mix_maybe\<cdot>(mix_unit\<cdot>(f\<cdot>\<bottom>))"
  unfolding mix_map_def by simp

lemma mix_map_ident: "mix_map\<cdot>(\<Lambda> x. x)\<cdot>xs = xs"
  by (induct xs) simp_all

lemma mix_map_ID: "mix_map\<cdot>ID = ID"
  by (simp add: cfun_eq_iff ID_def mix_map_ident)

lemma mix_map_map: "mix_map\<cdot>f\<cdot>(mix_map\<cdot>g\<cdot>xs) = mix_map\<cdot>(\<Lambda> x. f\<cdot>(g\<cdot>x))\<cdot>xs"
  by (induct xs) simp_all

lemma ep_pair_mix_map: "ep_pair e p \<Longrightarrow> ep_pair (mix_map\<cdot>e) (mix_map\<cdot>p)"
  apply standard
   apply (induct_tac x rule: mix_pd_induct, simp_all add: ep_pair.e_inverse)
  apply (induct_tac y rule: mix_pd_induct)
      apply (simp_all add: ep_pair.e_p_below monofun_cfun)
  done

lemma deflation_mix_map: "deflation d \<Longrightarrow> deflation (mix_map\<cdot>d)"
  apply standard
   apply (induct_tac x rule: mix_pd_induct, simp_all add: deflation.idem)
  apply (induct_tac x rule: mix_pd_induct)
      apply (simp_all add: deflation.below monofun_cfun)
  done

lemma finite_deflation_mix_map:
  assumes "finite_deflation d" shows "finite_deflation (mix_map\<cdot>d)"
proof (rule finite_deflation_intro)
  interpret d: finite_deflation d by fact
  from d.deflation_axioms show "deflation (mix_map\<cdot>d)"
    by (rule deflation_mix_map)
  define R where "R = Rep_compact_basis -` range (\<lambda>x. d\<cdot>x)"
  have "finite R"
    unfolding R_def using d.finite_range
    by (rule finite_vimageI) (simp add: inj_on_def Rep_compact_basis_inject)
  define T where "T = {t. Rep_pde_basis (mdef t) \<subseteq> R \<and> Rep_pde_basis (mposs t) \<subseteq> R}"
  have "finite (Rep_pde_basis -` Pow R)"
    using \<open>finite R\<close> by (intro finite_vimageI) (simp_all add: inj_on_def Rep_pde_basis_inject)
  then have "finite ((\<lambda>t. (mdef t, mposs t)) -` (Rep_pde_basis -` Pow R \<times> Rep_pde_basis -` Pow R))"
    by (intro finite_vimageI) (simp_all add: inj_on_def mix_basis_eqI)
  then have "finite T"
    by (rule rev_finite_subset) (auto simp: T_def)
  then have *: "finite (mix_principal ` T)" by simp
  have unit: "d\<cdot>x \<in> Rep_compact_basis ` R" for x
    unfolding R_def
    by (rule image_eqI [of _ _ "Abs_compact_basis (d\<cdot>x)"])
      (simp_all add: Abs_compact_basis_inverse d.compact)
  have "mix_map\<cdot>d\<cdot>xs \<in> mix_principal ` T" for xs
  proof (induct xs rule: mix_pd_induct)
    case adm
    then show ?case by (simp add: adm_mem_finite *)
  next
    case mix_empty
    show ?case by (simp only: mix_map_empty, simp only: mix_empty_def) (rule imageI, simp add: T_def)
  next
    case (mix_unit x)
    from unit [of x] obtain b where b: "b \<in> R" "d\<cdot>x = Rep_compact_basis b" by blast
    show ?case
      unfolding mix_map_unit b(2) mix_unit_Rep_compact_basis T_def
      using b(1) by (intro imageI) simp
  next
    case (mix_plus xs ys)
    then obtain s t where "s \<in> T" "t \<in> T" "mix_map\<cdot>d\<cdot>xs = mix_principal s"
        "mix_map\<cdot>d\<cdot>ys = mix_principal t" by blast
    then show ?case
      unfolding mix_map_plus by (simp add: T_def)
  next
    case (mix_maybe xs)
    then obtain t where "t \<in> T" "mix_map\<cdot>d\<cdot>xs = mix_principal t" by blast
    then show ?case
      unfolding mix_map_maybe by (simp add: T_def)
  qed
  then have "range (\<lambda>xs. mix_map\<cdot>d\<cdot>xs) \<subseteq> mix_principal ` T" by blast
  then have "finite (range (\<lambda>xs. mix_map\<cdot>d\<cdot>xs))"
    using * by (rule finite_subset)
  then show "finite {xs. mix_map\<cdot>d\<cdot>xs = xs}"
    by (rule finite_range_imp_finite_fixes)
qed


subsection \<open>The mixed powerdomain is bifinite\<close>

lemma approx_chain_mix_map:
  assumes "approx_chain a"
  shows "approx_chain (\<lambda>i. mix_map\<cdot>(a i))"
  using assms unfolding approx_chain_def
  by (simp add: lub_APP mix_map_ID finite_deflation_mix_map)

instance mix_pd :: (bifinite) bifinite
proof
  show "\<exists>(a::nat \<Rightarrow> 'a mix_pd \<rightarrow> 'a mix_pd). approx_chain a"
    using bifinite [where 'a='a]
    by (fast intro!: approx_chain_mix_map)
qed

end
