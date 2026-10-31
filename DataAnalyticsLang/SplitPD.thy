theory SplitPD
  imports Views "HOLCF-extra.Top" "HOLCF-extra.UpperPD_Representation"
begin

default_sort bifinite

section \<open>The split powerdomain\<close>

text \<open>A dataset in the split powerdomain has two parts in different types: \<^emph>\<open>definite rows\<close>,
  ordered as in the lower (Hoare) powerdomain over the row type, and \<^emph>\<open>possible keys\<close>, ordered
  as in the upper (Smyth) powerdomain over the key type.  The two are tied through the key of a
  row, @{text row_key}: every definite row has its key above some possible key.  Like HOLCF's
  powerdomains and the mixed powerdomain (the case where the key of a row is the row itself), it
  is the ideal completion of a preordered basis of pairs of finite sets of compact elements, and
  the consistency condition is stated on the generators of a basis element: on Hoare closures it
  would force the bottom key.  Both parts may be empty: no definite rows is the Hoare bottom, no
  possible keys the Smyth top (definitely no rows), which consistency forces to come with no
  definite rows.

  The key of a row is the constant @{const row_key}, given by instances for particular row and
  key types.  The split powerdomain is pointed; it is bifinite only for suitable keys (spectral ones),
  so no generic bifinite instance is given.\<close>



subsection \<open>The basis\<close>

definition split_consistent :: "'r compact_basis set \<Rightarrow> 'k compact_basis set \<Rightarrow> bool" where
  "split_consistent X U \<longleftrightarrow> (\<forall>x\<in>X. \<exists>u\<in>U. Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x))"

lemma split_consistent_empty [simp]: "split_consistent {} U"
  by (simp add: split_consistent_def)

lemma split_consistent_Un:
  "split_consistent X U \<Longrightarrow> split_consistent Y V \<Longrightarrow> split_consistent (X \<union> Y) (U \<union> V)"
  unfolding split_consistent_def by blast

typedef (overloaded) ('r, 'k) split_basis =
  "{(X, U). finite X \<and> finite U \<and> split_consistent X U} :: ('r compact_basis set \<times> 'k compact_basis set) set"
  by (rule exI [of _ "({}, {})"]) simp

definition srows :: "('r, 'k) split_basis \<Rightarrow> 'r compact_basis set" where
  "srows t = fst (Rep_split_basis t)"

definition skeys :: "('r, 'k) split_basis \<Rightarrow> 'k compact_basis set" where
  "skeys t = snd (Rep_split_basis t)"

definition SplitB :: "'r compact_basis set \<Rightarrow> 'k compact_basis set \<Rightarrow> ('r, 'k) split_basis" where
  "SplitB X U = Abs_split_basis (X, U)"

lemma finite_srows [simp]: "finite (srows t)"
  and finite_skeys [simp]: "finite (skeys t)"
  and split_basis_consistent: "split_consistent (srows t) (skeys t)"
  using Rep_split_basis [of t] by (auto simp: srows_def skeys_def split: prod.splits)

lemma split_basis_consistentD:
  "x \<in> srows t \<Longrightarrow> \<exists>u\<in>skeys t. Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x)"
  using split_basis_consistent [of t] unfolding split_consistent_def by blast

lemma split_basis_eqI: "\<lbrakk>srows s = srows t; skeys s = skeys t\<rbrakk> \<Longrightarrow> s = t"
  by (simp add: srows_def skeys_def Rep_split_basis_inject [symmetric] prod_eq_iff)

lemma srows_SplitB [simp]: "\<lbrakk>finite X; finite U; split_consistent X U\<rbrakk> \<Longrightarrow> srows (SplitB X U) = X"
  and skeys_SplitB [simp]: "\<lbrakk>finite X; finite U; split_consistent X U\<rbrakk> \<Longrightarrow> skeys (SplitB X U) = U"
  by (simp_all add: srows_def skeys_def SplitB_def Abs_split_basis_inverse)

lemma split_basis_countable: "\<exists>f::('r, 'k) split_basis \<Rightarrow> nat. inj f"
proof -
  obtain g :: "'r compact_basis \<Rightarrow> nat" where g: "inj g"
    using compact_basis.countable ..
  obtain h :: "'k compact_basis \<Rightarrow> nat" where h: "inj h"
    using compact_basis.countable ..
  have "inj (\<lambda>t::('r, 'k) split_basis. prod_encode (set_encode (g ` srows t), set_encode (h ` skeys t)))"
  proof (rule injI)
    fix s t :: "('r, 'k) split_basis"
    assume "prod_encode (set_encode (g ` srows s), set_encode (h ` skeys s))
      = prod_encode (set_encode (g ` srows t), set_encode (h ` skeys t))"
    then have "set_encode (g ` srows s) = set_encode (g ` srows t)"
      and "set_encode (h ` skeys s) = set_encode (h ` skeys t)"
      by (simp_all add: prod_encode_eq)
    then have "g ` srows s = g ` srows t" and "h ` skeys s = h ` skeys t"
      by (simp_all add: set_encode_eq)
    then have "srows s = srows t" and "skeys s = skeys t"
      by (simp_all add: inj_image_eq_iff [OF g] inj_image_eq_iff [OF h])
    then show "s = t" by (rule split_basis_eqI)
  qed
  then show ?thesis by blast
qed


subsection \<open>The preorder\<close>

definition hoare_le :: "'a::pcpo compact_basis set \<Rightarrow> 'a compact_basis set \<Rightarrow> bool" where
  "hoare_le X Y \<longleftrightarrow> (\<forall>x\<in>X. \<exists>y\<in>Y. x \<sqsubseteq> y)"

definition smyth_le :: "'a::pcpo compact_basis set \<Rightarrow> 'a compact_basis set \<Rightarrow> bool" where
  "smyth_le U V \<longleftrightarrow> (\<forall>v\<in>V. \<exists>u\<in>U. u \<sqsubseteq> v)"

lemma hoare_le_refl [simp]: "hoare_le X X"
  and smyth_le_refl [simp]: "smyth_le U U"
  unfolding hoare_le_def smyth_le_def by blast+

lemma hoare_le_trans: "\<lbrakk>hoare_le X Y; hoare_le Y Z\<rbrakk> \<Longrightarrow> hoare_le X Z"
  and smyth_le_trans: "\<lbrakk>smyth_le U V; smyth_le V W\<rbrakk> \<Longrightarrow> smyth_le U W"
  unfolding hoare_le_def smyth_le_def by (meson below_trans)+

lemma hoare_le_empty [simp]: "hoare_le {} Y"
  and smyth_le_empty [simp]: "smyth_le U {}"
  unfolding hoare_le_def smyth_le_def by simp_all

lemma hoare_le_Un: "\<lbrakk>hoare_le X Y; hoare_le X' Y'\<rbrakk> \<Longrightarrow> hoare_le (X \<union> X') (Y \<union> Y')"
  unfolding hoare_le_def by (meson UnCI UnE)

lemma smyth_le_Un: "\<lbrakk>smyth_le U V; smyth_le U' V'\<rbrakk> \<Longrightarrow> smyth_le (U \<union> U') (V \<union> V')"
  unfolding smyth_le_def by (meson UnCI UnE)

definition split_le :: "('r, 'k) split_basis \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> bool" where
  "split_le s t \<longleftrightarrow> hoare_le (srows s) (srows t) \<and> smyth_le (skeys s) (skeys t)"

lemma split_le_refl [simp]: "split_le t t"
  unfolding split_le_def by simp

lemma split_le_trans: "\<lbrakk>split_le s t; split_le t u\<rbrakk> \<Longrightarrow> split_le s u"
  unfolding split_le_def by (blast intro: hoare_le_trans smyth_le_trans)

interpretation split_le: preorder split_le
  by (rule preorder.intro, rule split_le_refl, rule split_le_trans)


subsection \<open>Type definition\<close>

typedef (overloaded) ('r, 'k) split_pd =
  "{S::('r, 'k) split_basis set. split_le.ideal S}"
  by (rule split_le.ex_ideal)

instantiation split_pd :: (bifinite, bifinite) below
begin

definition
  "x \<sqsubseteq> y \<longleftrightarrow> Rep_split_pd x \<subseteq> Rep_split_pd y"

instance ..
end

instance split_pd :: (bifinite, bifinite) po
  using type_definition_split_pd below_split_pd_def
  by (rule split_le.typedef_ideal_po)

instance split_pd :: (bifinite, bifinite) cpo
  using type_definition_split_pd below_split_pd_def
  by (rule split_le.typedef_ideal_cpo)

definition split_principal :: "('r, 'k) split_basis \<Rightarrow> ('r, 'k) split_pd" where
  "split_principal t = Abs_split_pd {u. split_le u t}"

interpretation split_pd: ideal_completion split_le split_principal Rep_split_pd
  using type_definition_split_pd below_split_pd_def
  using split_principal_def split_basis_countable
  by (rule split_le.typedef_ideal_completion)

text \<open>The least element has no definite rows and the possible key \<open>\<bottom>\<close>: the open world.\<close>

definition SBot :: "('r, 'k) split_basis" where
  "SBot = SplitB {} {compact_bot}"

lemma srows_SBot [simp]: "srows SBot = {}"
  and skeys_SBot [simp]: "skeys SBot = {compact_bot}"
  unfolding SBot_def by simp_all

lemma split_le_SBot [simp]: "split_le SBot t"
  unfolding split_le_def by (simp add: smyth_le_def)

lemma split_pd_minimal: "split_principal SBot \<sqsubseteq> ys"
  by (induct ys rule: split_pd.principal_induct, simp, simp)

instance split_pd :: (bifinite, bifinite) pcpo
  by intro_classes (fast intro: split_pd_minimal)

lemma inst_split_pd_pcpo: "\<bottom> = split_principal SBot"
  by (rule split_pd_minimal [THEN bottomI, symmetric])

lemma split_principal_eqI: "\<lbrakk>srows s = srows t; skeys s = skeys t\<rbrakk> \<Longrightarrow> split_principal s = split_principal t"
  by (drule (1) split_basis_eqI) simp


subsection \<open>Basis constructors\<close>

text \<open>The empty dataset (definitely no rows), the union, the weakening to possible (the definite
  rows dropped), a row with an unconstrained key (the open unit), and a possible key without
  rows (the maybe-unit: whatever rows there are have keys above it).\<close>

definition SEmpty :: "('r, 'k) split_basis" where
  "SEmpty = SplitB {} {}"

definition SPlus :: "('r, 'k) split_basis \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> ('r, 'k) split_basis" where
  "SPlus s t = SplitB (srows s \<union> srows t) (skeys s \<union> skeys t)"

definition SMaybe :: "('r, 'k) split_basis \<Rightarrow> ('r, 'k) split_basis" where
  "SMaybe t = SplitB {} (skeys t)"

definition SOpen :: "'r compact_basis \<Rightarrow> ('r, 'k) split_basis" where
  "SOpen a = SplitB {a} {compact_bot}"

definition SKey :: "'k compact_basis \<Rightarrow> ('r, 'k) split_basis" where
  "SKey k = SplitB {} {k}"

lemma srows_SEmpty [simp]: "srows SEmpty = {}"
  and skeys_SEmpty [simp]: "skeys SEmpty = {}"
  unfolding SEmpty_def by simp_all

lemma srows_SPlus [simp]: "srows (SPlus s t) = srows s \<union> srows t"
  and skeys_SPlus [simp]: "skeys (SPlus s t) = skeys s \<union> skeys t"
  unfolding SPlus_def
  using split_consistent_Un [OF split_basis_consistent [of s] split_basis_consistent [of t]]
  by simp_all

lemma srows_SMaybe [simp]: "srows (SMaybe t) = {}"
  and skeys_SMaybe [simp]: "skeys (SMaybe t) = skeys t"
  unfolding SMaybe_def by simp_all

lemma srows_SOpen [simp]: "srows (SOpen a) = {a}"
  and skeys_SOpen [simp]: "skeys (SOpen a) = {compact_bot}"
  unfolding SOpen_def by (simp_all add: split_consistent_def)

lemma srows_SKey [simp]: "srows (SKey k) = {}"
  and skeys_SKey [simp]: "skeys (SKey k) = {k}"
  unfolding SKey_def by simp_all

lemma SPlus_split_mono: "\<lbrakk>split_le s t; split_le u v\<rbrakk> \<Longrightarrow> split_le (SPlus s u) (SPlus t v)"
  unfolding split_le_def by (simp add: hoare_le_Un smyth_le_Un)

lemma SMaybe_split_mono: "split_le s t \<Longrightarrow> split_le (SMaybe s) (SMaybe t)"
  unfolding split_le_def by simp

lemma SOpen_split_mono: "a \<sqsubseteq> b \<Longrightarrow> split_le (SOpen a) (SOpen b)"
  unfolding split_le_def hoare_le_def by simp

lemma SKey_split_mono: "k \<sqsubseteq> l \<Longrightarrow> split_le (SKey k) (SKey l)"
  unfolding split_le_def smyth_le_def by simp

lemma SMaybe_split_le: "split_le (SMaybe t) t"
  unfolding split_le_def by simp

lemma SMaybe_split_le_SEmpty: "split_le (SMaybe t) SEmpty"
  unfolding split_le_def by simp


subsection \<open>Empty, plus, maybe, the open unit and the maybe-unit\<close>

definition split_empty :: "('r, 'k) split_pd" where
  "split_empty = split_principal SEmpty"

definition split_plus :: "('r, 'k) split_pd \<rightarrow> ('r, 'k) split_pd \<rightarrow> ('r, 'k) split_pd" where
  "split_plus = split_pd.extension (\<lambda>t. split_pd.extension (\<lambda>u. split_principal (SPlus t u)))"

abbreviation split_add :: "('r, 'k) split_pd \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> ('r, 'k) split_pd"
    (infixl \<open>\<union>\<^sub>s\<close> 65) where
  "xs \<union>\<^sub>s ys \<equiv> split_plus\<cdot>xs\<cdot>ys"

definition split_maybe :: "('r, 'k) split_pd \<rightarrow> ('r, 'k) split_pd" where
  "split_maybe = split_pd.extension (\<lambda>t. split_principal (SMaybe t))"

definition split_open_unit :: "'r \<rightarrow> ('r, 'k) split_pd" where
  "split_open_unit = compact_basis.extension (\<lambda>a. split_principal (SOpen a))"

definition split_maybe_unit :: "'k \<rightarrow> ('r, 'k) split_pd" where
  "split_maybe_unit = compact_basis.extension (\<lambda>k. split_principal (SKey k))"

lemma split_plus_principal [simp]:
  "split_principal t \<union>\<^sub>s split_principal u = split_principal (SPlus t u)"
  unfolding split_plus_def
  by (simp add: split_pd.extension_principal split_pd.extension_mono SPlus_split_mono)

lemma split_maybe_principal [simp]:
  "split_maybe\<cdot>(split_principal t) = split_principal (SMaybe t)"
  unfolding split_maybe_def
  by (simp add: split_pd.extension_principal SMaybe_split_mono)

lemma split_open_unit_Rep_compact_basis [simp]:
  "split_open_unit\<cdot>(Rep_compact_basis a) = split_principal (SOpen a)"
  unfolding split_open_unit_def
  by (simp add: compact_basis.extension_principal SOpen_split_mono)

lemma split_maybe_unit_Rep_compact_basis [simp]:
  "split_maybe_unit\<cdot>(Rep_compact_basis k) = split_principal (SKey k)"
  unfolding split_maybe_unit_def
  by (simp add: compact_basis.extension_principal SKey_split_mono)

interpretation split_add: semilattice_neutr split_add split_empty
proof
  fix xs ys zs :: "('r, 'k) split_pd"
  show "(xs \<union>\<^sub>s ys) \<union>\<^sub>s zs = xs \<union>\<^sub>s (ys \<union>\<^sub>s zs)"
    apply (induct xs rule: split_pd.principal_induct, simp)
    apply (induct ys rule: split_pd.principal_induct, simp)
    apply (induct zs rule: split_pd.principal_induct, simp)
    apply (simp, rule split_principal_eqI, simp_all add: Un_assoc)
    done
  show "xs \<union>\<^sub>s ys = ys \<union>\<^sub>s xs"
    apply (induct xs rule: split_pd.principal_induct, simp)
    apply (induct ys rule: split_pd.principal_induct, simp)
    apply (simp, rule split_principal_eqI, simp_all add: Un_commute)
    done
  show "xs \<union>\<^sub>s xs = xs"
    apply (induct xs rule: split_pd.principal_induct, simp)
    apply (simp, rule split_principal_eqI, simp_all)
    done
  show "xs \<union>\<^sub>s split_empty = xs"
    apply (induct xs rule: split_pd.principal_induct, simp)
    apply (simp add: split_empty_def, rule split_principal_eqI, simp_all)
    done
qed

lemmas split_plus_assoc = split_add.assoc
lemmas split_plus_commute = split_add.commute
lemmas split_plus_absorb = split_add.idem
lemmas split_plus_left_commute = split_add.left_commute
lemmas split_plus_left_absorb = split_add.left_idem
lemmas split_plus_empty1 [simp] = split_add.left_neutral
lemmas split_plus_empty2 [simp] = split_add.right_neutral

lemmas split_plus_ac = split_plus_assoc split_plus_commute split_plus_left_commute
lemmas split_plus_aci = split_plus_ac split_plus_absorb split_plus_left_absorb

lemma split_maybe_plus [simp]: "split_maybe\<cdot>(xs \<union>\<^sub>s ys) = split_maybe\<cdot>xs \<union>\<^sub>s split_maybe\<cdot>ys"
  apply (induct xs rule: split_pd.principal_induct, simp)
  apply (induct ys rule: split_pd.principal_induct, simp)
  apply (simp, rule split_principal_eqI, simp_all)
  done

lemma split_maybe_maybe [simp]: "split_maybe\<cdot>(split_maybe\<cdot>xs) = split_maybe\<cdot>xs"
  apply (induct xs rule: split_pd.principal_induct, simp)
  apply (simp, rule split_principal_eqI, simp_all)
  done

lemma split_maybe_empty [simp]: "split_maybe\<cdot>split_empty = split_empty"
  by (simp add: split_empty_def, rule split_principal_eqI, simp_all)

lemma split_plus_maybe_absorb [simp]: "xs \<union>\<^sub>s split_maybe\<cdot>xs = xs"
  apply (induct xs rule: split_pd.principal_induct, simp)
  apply (simp, rule split_principal_eqI, simp_all)
  done

lemma split_maybe_below: "split_maybe\<cdot>xs \<sqsubseteq> xs"
  apply (induct xs rule: split_pd.principal_induct, simp)
  apply (simp add: SMaybe_split_le)
  done

lemma split_maybe_below_empty: "split_maybe\<cdot>xs \<sqsubseteq> split_empty"
  apply (induct xs rule: split_pd.principal_induct, simp)
  apply (simp add: split_empty_def SMaybe_split_le_SEmpty)
  done

lemma split_open_unit_below_iff [simp]: "split_open_unit\<cdot>x \<sqsubseteq> split_open_unit\<cdot>y \<longleftrightarrow> x \<sqsubseteq> y"
  apply (induct x rule: compact_basis.principal_induct, simp)
  apply (induct y rule: compact_basis.principal_induct, simp)
  apply (simp add: split_le_def hoare_le_def)
  done

lemma split_maybe_unit_below_iff [simp]: "split_maybe_unit\<cdot>k \<sqsubseteq> split_maybe_unit\<cdot>l \<longleftrightarrow> k \<sqsubseteq> l"
  apply (induct k rule: compact_basis.principal_induct, simp)
  apply (induct l rule: compact_basis.principal_induct, simp)
  apply (simp add: split_le_def smyth_le_def)
  done

text \<open>The bottom is the maybe-unit at the bottom key, and the weakening of the open unit.\<close>

lemma split_bottom_maybe_unit: "\<bottom> = split_maybe_unit\<cdot>\<bottom>"
proof -
  have "split_maybe_unit\<cdot>(Rep_compact_basis compact_bot) = split_principal SBot"
    by (simp only: split_maybe_unit_Rep_compact_basis, rule split_principal_eqI, simp_all)
  then show ?thesis unfolding Rep_compact_bot inst_split_pd_pcpo by (rule sym)
qed

lemma split_bottom_maybe_open_unit: "\<bottom> = split_maybe\<cdot>(split_open_unit\<cdot>x)"
proof (induct x rule: compact_basis.principal_induct)
  show "adm (\<lambda>x. \<bottom> = split_maybe\<cdot>(split_open_unit\<cdot>x))" by simp
  fix a :: "'a compact_basis"
  show "\<bottom> = split_maybe\<cdot>(split_open_unit\<cdot>(Rep_compact_basis a))"
    unfolding inst_split_pd_pcpo split_open_unit_Rep_compact_basis split_maybe_principal
    by (rule split_principal_eqI) simp_all
qed

lemma split_maybe_strict [simp]: "split_maybe\<cdot>\<bottom> = \<bottom>"
  by (subst (1 2) split_bottom_maybe_open_unit [of \<bottom>]) (rule split_maybe_maybe)

lemma compact_split_plus [simp]: "\<lbrakk>compact xs; compact ys\<rbrakk> \<Longrightarrow> compact (xs \<union>\<^sub>s ys)"
  by (auto dest!: split_pd.compact_imp_principal)

lemma compact_split_maybe [simp]: "compact xs \<Longrightarrow> compact (split_maybe\<cdot>xs)"
  by (auto dest!: split_pd.compact_imp_principal)

lemma compact_split_empty [simp]: "compact split_empty"
  by (simp add: split_empty_def)

lemma compact_split_open_unit: "compact x \<Longrightarrow> compact (split_open_unit\<cdot>x)"
  by (auto dest!: compact_basis.compact_imp_principal)

lemma compact_split_maybe_unit: "compact k \<Longrightarrow> compact (split_maybe_unit\<cdot>k)"
  by (auto dest!: compact_basis.compact_imp_principal)


subsection \<open>The unit\<close>

text \<open>The unit of a row has the row as its definite row and the row's key as its only possible
  key.  The key of a compact row need not be compact, so the unit of a compact row is the limit
  of the basis elements with the row and an approximation of its key, along an approximation
  chain of the key type.\<close>

definition split_approx :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where
  "split_approx = (SOME a. approx_chain a)"

lemma approx_chain_split_approx: "approx_chain split_approx"
  unfolding split_approx_def by (rule someI_ex [OF bifinite])

interpretation split_approx: approx_chain split_approx
  by (rule approx_chain_split_approx)

definition SUnit :: "'r compact_basis \<Rightarrow> nat \<Rightarrow> ('r, 'k) split_basis" where
  "SUnit a i = SplitB {a} {Abs_compact_basis (split_approx i\<cdot>(row_key\<cdot>(Rep_compact_basis a)))}"

lemma srows_SUnit [simp]: "srows (SUnit a i :: ('r, 'k) split_basis) = {a}"
  and skeys_SUnit [simp]:
    "skeys (SUnit a i :: ('r, 'k) split_basis)
      = {Abs_compact_basis (split_approx i\<cdot>(row_key\<cdot>(Rep_compact_basis a) :: 'k))}"
proof -
  have "split_consistent {a} {Abs_compact_basis (split_approx i\<cdot>(row_key\<cdot>(Rep_compact_basis a) :: 'k))}"
    by (simp add: split_consistent_def split_approx.approx_below)
  then show "srows (SUnit a i :: ('r, 'k) split_basis) = {a}"
    and "skeys (SUnit a i :: ('r, 'k) split_basis)
      = {Abs_compact_basis (split_approx i\<cdot>(row_key\<cdot>(Rep_compact_basis a) :: 'k))}"
    unfolding SUnit_def by simp_all
qed

lemma SUnit_split_mono:
  assumes ab: "a \<sqsubseteq> b" and ij: "i \<le> j"
  shows "split_le (SUnit a i :: ('r, 'k) split_basis) (SUnit b j)"
proof -
  have "split_approx i \<sqsubseteq> (split_approx j :: 'k \<rightarrow> 'k)"
    by (rule chain_mono [OF split_approx.chain_approx ij])
  moreover have "row_key\<cdot>(Rep_compact_basis a) \<sqsubseteq> (row_key\<cdot>(Rep_compact_basis b) :: 'k)"
    by (rule monofun_cfun_arg) (use ab in \<open>simp only: compact_le_def\<close>)
  ultimately have "split_approx i\<cdot>(row_key\<cdot>(Rep_compact_basis a)) \<sqsubseteq> (split_approx j\<cdot>(row_key\<cdot>(Rep_compact_basis b)) :: 'k)"
    by (rule monofun_cfun)
  then have "Abs_compact_basis (split_approx i\<cdot>(row_key\<cdot>(Rep_compact_basis a)))
      \<sqsubseteq> (Abs_compact_basis (split_approx j\<cdot>(row_key\<cdot>(Rep_compact_basis b))) :: 'k compact_basis)"
    by (simp only: compact_le_def Abs_compact_basis_inverse' split_approx.compact_approx)
  then show ?thesis using ab unfolding split_le_def hoare_le_def smyth_le_def srows_SUnit skeys_SUnit by simp
qed

definition split_unit_basis :: "'r compact_basis \<Rightarrow> ('r, 'k) split_pd" where
  "split_unit_basis a = (\<Squnion>i. split_principal (SUnit a i))"

lemma chain_split_unit_basis: "chain (\<lambda>i. split_principal (SUnit a i) :: ('r, 'k) split_pd)"
  by (rule chainI, rule split_pd.principal_mono, rule SUnit_split_mono) simp_all

lemma split_unit_basis_mono: "a \<sqsubseteq> b \<Longrightarrow> split_unit_basis a \<sqsubseteq> (split_unit_basis b :: ('r, 'k) split_pd)"
  unfolding split_unit_basis_def
  by (rule lub_mono [OF chain_split_unit_basis chain_split_unit_basis],
      rule split_pd.principal_mono, rule SUnit_split_mono) simp_all

definition split_unit :: "'r \<rightarrow> ('r, 'k) split_pd" where
  "split_unit = compact_basis.extension split_unit_basis"

lemma split_unit_Rep_compact_basis [simp]:
  "split_unit\<cdot>(Rep_compact_basis a) = (\<Squnion>i. split_principal (SUnit a i))"
  unfolding split_unit_def
  by (simp add: compact_basis.extension_principal split_unit_basis_mono, simp add: split_unit_basis_def)

text \<open>The open unit is below the unit: it forgets the row's key.\<close>

lemma split_open_unit_below_unit:
  "split_open_unit\<cdot>x \<sqsubseteq> (split_unit\<cdot>x :: ('r, 'k) split_pd)"
proof (induct x rule: compact_basis.principal_induct)
  show "adm (\<lambda>x. split_open_unit\<cdot>x \<sqsubseteq> (split_unit\<cdot>x :: ('r, 'k) split_pd))" by simp
  fix a :: "'r compact_basis"
  have "split_principal (SOpen a) \<sqsubseteq> (split_principal (SUnit a 0) :: ('r, 'k) split_pd)"
    by (rule split_pd.principal_mono) (simp add: split_le_def hoare_le_def smyth_le_def)
  also have "\<dots> \<sqsubseteq> (\<Squnion>i. split_principal (SUnit a i))"
    by (rule is_ub_thelub [OF chain_split_unit_basis])
  finally show "split_open_unit\<cdot>(Rep_compact_basis a) \<sqsubseteq> (split_unit\<cdot>(Rep_compact_basis a) :: ('r, 'k) split_pd)"
    by simp
qed

lemma split_maybe_unit_bottom_below: "split_maybe_unit\<cdot>k \<sqsubseteq> split_empty"
proof (induct k rule: compact_basis.principal_induct)
  show "adm (\<lambda>k. split_maybe_unit\<cdot>k \<sqsubseteq> split_empty)" by simp
qed (simp add: split_empty_def split_le_def)


subsection \<open>The definite rows\<close>

text \<open>HOLCF's lower powerdomain has no empty set: its bottom is the one row \<open>\<bottom>\<close>, which says that
  some row exists.  The definite rows of a dataset are therefore a \<^emph>\<open>lifted\<close> lower powerdomain,
  whose bottom is no rows.  Union is lifted non-strictly: no rows is its unit.\<close>

definition lower_union_fun :: "'a lower_pd u \<Rightarrow> 'a lower_pd u \<Rightarrow> 'a lower_pd u" where
  "lower_union_fun X Y = (if X = \<bottom> \<and> Y = \<bottom> then \<bottom> else up\<cdot>(fup\<cdot>ID\<cdot>X \<union>\<flat> fup\<cdot>ID\<cdot>Y))"

lemma lower_plus_bottom_right: "xs \<union>\<flat> \<bottom> = xs"
  by (rule below_antisym [OF lower_plus_least [OF below_refl minimal] lower_plus_below1])

lemma lower_plus_bottom_left: "\<bottom> \<union>\<flat> xs = xs"
  by (rule below_antisym [OF lower_plus_least [OF minimal below_refl] lower_plus_below2])

lemma lower_union_fun_bottom1: "lower_union_fun \<bottom> Y = Y"
  by (cases Y) (simp_all add: lower_union_fun_def lower_plus_bottom_left)

lemma lower_union_fun_bottom2: "lower_union_fun X \<bottom> = X"
  by (cases X) (simp_all add: lower_union_fun_def lower_plus_bottom_right)

lemma lower_union_fun_up: "lower_union_fun (up\<cdot>x) (up\<cdot>y) = up\<cdot>(x \<union>\<flat> y)"
  by (simp add: lower_union_fun_def)

lemma cont_lower_union_fun1: "cont (\<lambda>X. lower_union_fun X Y)"
proof (cases Y)
  case bottom
  then show ?thesis by (simp add: lower_union_fun_bottom2)
next
  case (up y)
  then show ?thesis by (simp add: lower_union_fun_def)
qed

lemma cont_lower_union_fun2: "cont (\<lambda>Y. lower_union_fun X Y)"
proof (cases X)
  case bottom
  then show ?thesis by (simp add: lower_union_fun_bottom1)
next
  case (up x)
  then show ?thesis by (simp add: lower_union_fun_def)
qed

definition lower_union :: "'a lower_pd u \<rightarrow> 'a lower_pd u \<rightarrow> 'a lower_pd u" where
  "lower_union = (\<Lambda> X Y. lower_union_fun X Y)"

lemma lower_union_beta: "lower_union\<cdot>X\<cdot>Y = lower_union_fun X Y"
  unfolding lower_union_def by (simp add: cont2cont_LAM cont_lower_union_fun1 cont_lower_union_fun2)

lemma lower_union_bottom1 [simp]: "lower_union\<cdot>\<bottom>\<cdot>Y = Y"
  and lower_union_bottom2 [simp]: "lower_union\<cdot>X\<cdot>\<bottom> = X"
  and lower_union_up [simp]: "lower_union\<cdot>(up\<cdot>x)\<cdot>(up\<cdot>y) = up\<cdot>(x \<union>\<flat> y)"
  by (simp_all add: lower_union_beta lower_union_fun_bottom1 lower_union_fun_bottom2 lower_union_fun_up)

definition srows_lower :: "('r, 'k) split_basis \<Rightarrow> 'r lower_pd u" where
  "srows_lower t = (if srows t = {} then \<bottom> else up\<cdot>(lower_principal (Abs_pd_basis (srows t))))"

lemma srows_lower_mono: "split_le s t \<Longrightarrow> srows_lower s \<sqsubseteq> srows_lower t"
proof -
  assume st: "split_le s t"
  show ?thesis
  proof (cases "srows s = {}")
    case False
    then have t: "srows t \<noteq> {}" using st by (auto simp: split_le_def hoare_le_def)
    have "Abs_pd_basis (srows s) \<le>\<flat> Abs_pd_basis (srows t)"
      using st False t by (simp add: lower_le_def split_le_def hoare_le_def Abs_pd_basis_inverse pd_basis_def)
    then show ?thesis using False t unfolding srows_lower_def by (simp add: lower_pd.principal_mono)
  qed (simp add: srows_lower_def)
qed

definition split_rows :: "('r, 'k) split_pd \<rightarrow> 'r lower_pd u" where
  "split_rows = split_pd.extension srows_lower"

lemma split_rows_principal [simp]: "split_rows\<cdot>(split_principal t) = srows_lower t"
  unfolding split_rows_def by (simp add: split_pd.extension_principal srows_lower_mono)

lemma split_rows_open_unit [simp]: "split_rows\<cdot>(split_open_unit\<cdot>x) = up\<cdot>(lower_unit\<cdot>x)"
proof (induct x rule: compact_basis.principal_induct)
  show "adm (\<lambda>x. split_rows\<cdot>(split_open_unit\<cdot>x) = up\<cdot>(lower_unit\<cdot>x))" by simp
qed (simp add: srows_lower_def PDUnit_def)

lemma split_rows_unit [simp]: "split_rows\<cdot>(split_unit\<cdot>x :: ('r, 'k) split_pd) = up\<cdot>(lower_unit\<cdot>x)"
proof (induct x rule: compact_basis.principal_induct)
  show "adm (\<lambda>x. split_rows\<cdot>(split_unit\<cdot>x :: ('r, 'k) split_pd) = up\<cdot>(lower_unit\<cdot>x))" by simp
  fix a :: "'r compact_basis"
  have "split_rows\<cdot>(\<Squnion>i. split_principal (SUnit a i) :: ('r, 'k) split_pd) = (\<Squnion>i. srows_lower (SUnit a i :: ('r, 'k) split_basis))"
    by (simp add: contlub_cfun_arg [OF chain_split_unit_basis])
  also have "\<dots> = up\<cdot>(lower_unit\<cdot>(Rep_compact_basis a))"
    by (simp add: srows_lower_def PDUnit_def)
  finally show "split_rows\<cdot>(split_unit\<cdot>(Rep_compact_basis a) :: ('r, 'k) split_pd) = up\<cdot>(lower_unit\<cdot>(Rep_compact_basis a))"
    by simp
qed

lemma split_rows_maybe [simp]: "split_rows\<cdot>(split_maybe\<cdot>xs) = \<bottom>"
  by (induct xs rule: split_pd.principal_induct, simp, simp add: srows_lower_def)

lemma split_rows_empty [simp]: "split_rows\<cdot>split_empty = \<bottom>"
  by (simp add: split_empty_def srows_lower_def)

lemma split_rows_strict [simp]: "split_rows\<cdot>\<bottom> = \<bottom>"
  by (simp add: inst_split_pd_pcpo srows_lower_def)

lemma split_rows_plus [simp]: "split_rows\<cdot>(xs \<union>\<^sub>s ys) = lower_union\<cdot>(split_rows\<cdot>xs)\<cdot>(split_rows\<cdot>ys)"
proof (induct xs rule: split_pd.principal_induct)
  fix s
  show "split_rows\<cdot>(split_principal s \<union>\<^sub>s ys) = lower_union\<cdot>(split_rows\<cdot>(split_principal s))\<cdot>(split_rows\<cdot>ys)"
  proof (induct ys rule: split_pd.principal_induct)
    fix t
    show "split_rows\<cdot>(split_principal s \<union>\<^sub>s split_principal t)
        = lower_union\<cdot>(split_rows\<cdot>(split_principal s))\<cdot>(split_rows\<cdot>(split_principal t))"
      by (cases "srows s = {}"; cases "srows t = {}")
        (simp_all add: srows_lower_def PDPlus_def Abs_pd_basis_inverse pd_basis_def)
  qed simp
qed simp

text \<open>A dataset has no definite rows exactly when it has no definite row \<open>\<bottom>\<close>.\<close>

lemma split_rows_bottom_principal: "split_rows\<cdot>(split_principal t) = \<bottom> \<longleftrightarrow> srows t = {}"
  by (simp add: srows_lower_def)


subsection \<open>Opening\<close>

text \<open>Opening a dataset forgets its possible keys: the definite rows are kept and any key is
  possible.  The open unit is the opened unit.\<close>

definition SOpenB :: "('r, 'k) split_basis \<Rightarrow> ('r, 'k) split_basis" where
  "SOpenB t = SplitB (srows t) {compact_bot}"

lemma srows_SOpenB [simp]: "srows (SOpenB t) = srows t"
  and skeys_SOpenB [simp]: "skeys (SOpenB t) = {compact_bot}"
  unfolding SOpenB_def by (simp_all add: split_consistent_def)

lemma SOpenB_split_mono: "split_le s t \<Longrightarrow> split_le (SOpenB s) (SOpenB t)"
  unfolding split_le_def by (simp add: smyth_le_def)

definition split_open :: "('r, 'k) split_pd \<rightarrow> ('r, 'k) split_pd" where
  "split_open = split_pd.extension (\<lambda>t. split_principal (SOpenB t))"

lemma split_open_principal [simp]: "split_open\<cdot>(split_principal t) = split_principal (SOpenB t)"
  unfolding split_open_def by (simp add: split_pd.extension_principal SOpenB_split_mono)

lemma split_open_below: "split_open\<cdot>xs \<sqsubseteq> xs"
  by (induct xs rule: split_pd.principal_induct, simp, simp add: split_le_def smyth_le_def)

lemma split_open_open [simp]: "split_open\<cdot>(split_open\<cdot>xs) = split_open\<cdot>xs"
  by (induct xs rule: split_pd.principal_induct, simp, simp, rule split_principal_eqI, simp_all)

lemma split_open_plus [simp]: "split_open\<cdot>(xs \<union>\<^sub>s ys) = split_open\<cdot>xs \<union>\<^sub>s split_open\<cdot>ys"
  apply (induct xs rule: split_pd.principal_induct, simp)
  apply (induct ys rule: split_pd.principal_induct, simp)
  apply (simp, rule split_principal_eqI, simp_all)
  done

lemma split_open_maybe [simp]: "split_open\<cdot>(split_maybe\<cdot>xs) = \<bottom>"
  by (induct xs rule: split_pd.principal_induct, simp,
      simp add: inst_split_pd_pcpo, rule split_principal_eqI, simp_all)

lemma split_maybe_open [simp]: "split_maybe\<cdot>(split_open\<cdot>xs) = \<bottom>"
  by (induct xs rule: split_pd.principal_induct, simp,
      simp add: inst_split_pd_pcpo, rule split_principal_eqI, simp_all)

lemma split_open_empty [simp]: "split_open\<cdot>split_empty = \<bottom>"
  by (simp add: split_empty_def inst_split_pd_pcpo, rule split_principal_eqI, simp_all)

lemma split_open_strict [simp]: "split_open\<cdot>\<bottom> = \<bottom>"
  by (simp add: inst_split_pd_pcpo, rule split_principal_eqI, simp_all)

lemma split_open_unit_open: "split_open\<cdot>(split_unit\<cdot>x) = (split_open_unit\<cdot>x :: ('r, 'k) split_pd)"
proof (induct x rule: compact_basis.principal_induct)
  show "adm (\<lambda>x. split_open\<cdot>(split_unit\<cdot>x) = (split_open_unit\<cdot>x :: ('r, 'k) split_pd))" by simp
  fix a :: "'r compact_basis"
  have eq: "split_principal (SOpenB (SUnit a i)) = (split_principal (SOpen a) :: ('r, 'k) split_pd)" for i
    by (rule split_principal_eqI) simp_all
  have "split_open\<cdot>(\<Squnion>i. split_principal (SUnit a i) :: ('r, 'k) split_pd) = (\<Squnion>i. split_open\<cdot>(split_principal (SUnit a i)))"
    by (rule contlub_cfun_arg [OF chain_split_unit_basis])
  also have "\<dots> = split_principal (SOpen a)"
    by (simp only: split_open_principal eq lub_const)
  finally have "split_open\<cdot>(\<Squnion>i. split_principal (SUnit a i) :: ('r, 'k) split_pd) = split_principal (SOpen a)" .
  then show "split_open\<cdot>(split_unit\<cdot>(Rep_compact_basis a)) = (split_open_unit\<cdot>(Rep_compact_basis a) :: ('r, 'k) split_pd)"
    by simp
qed

lemma split_open_open_unit [simp]: "split_open\<cdot>(split_open_unit\<cdot>x) = split_open_unit\<cdot>x"
  by (induct x rule: compact_basis.principal_induct, simp, simp, rule split_principal_eqI, simp_all)


subsection \<open>The possible keys\<close>

text \<open>The possible keys of a dataset, as an upper powerdomain with a top adjoined: no possible
  keys (definitely no rows) is the top.\<close>

lemma Abs_pd_basis_singleton: "Abs_pd_basis {a} = PDUnit a"
  by (simp add: PDUnit_def)

definition skeys_upper :: "('r, 'k) split_basis \<Rightarrow> 'k upper_pd top" where
  "skeys_upper t = (if skeys t = {} then Top else down\<cdot>(upper_principal (Abs_pd_basis (skeys t))))"

lemma skeys_upper_mono: "split_le s t \<Longrightarrow> skeys_upper s \<sqsubseteq> skeys_upper t"
proof -
  assume st: "split_le s t"
  show ?thesis
  proof (cases "skeys t = {}")
    case False
    then have s: "skeys s \<noteq> {}" using st by (auto simp: split_le_def smyth_le_def)
    have "Abs_pd_basis (skeys s) \<le>\<sharp> Abs_pd_basis (skeys t)"
      using st False s by (simp add: upper_le_def split_le_def smyth_le_def Abs_pd_basis_inverse pd_basis_def)
    then show ?thesis using False s unfolding skeys_upper_def by (simp add: down_below_iff upper_pd.principal_mono)
  qed (simp add: skeys_upper_def)
qed

definition split_keys :: "('r, 'k) split_pd \<rightarrow> 'k upper_pd top" where
  "split_keys = split_pd.extension skeys_upper"

lemma split_keys_principal [simp]: "split_keys\<cdot>(split_principal t) = skeys_upper t"
  unfolding split_keys_def by (simp add: split_pd.extension_principal skeys_upper_mono)

lemma split_keys_empty [simp]: "split_keys\<cdot>split_empty = Top"
  by (simp add: split_empty_def skeys_upper_def)

lemma split_keys_strict [simp]: "split_keys\<cdot>\<bottom> = down\<cdot>\<bottom>"
  by (simp add: inst_split_pd_pcpo skeys_upper_def Abs_pd_basis_singleton inst_upper_pd_pcpo)

lemma split_keys_maybe [simp]: "split_keys\<cdot>(split_maybe\<cdot>xs) = split_keys\<cdot>xs"
  by (induct xs rule: split_pd.principal_induct, simp, simp add: skeys_upper_def)

lemma split_keys_open [simp]: "split_keys\<cdot>(split_open\<cdot>xs) = down\<cdot>\<bottom>"
  by (induct xs rule: split_pd.principal_induct, simp,
      simp add: skeys_upper_def Abs_pd_basis_singleton inst_upper_pd_pcpo)

lemma split_keys_maybe_unit [simp]: "split_keys\<cdot>(split_maybe_unit\<cdot>k :: ('r, 'k) split_pd) = down\<cdot>(upper_unit\<cdot>k)"
proof (induct k rule: compact_basis.principal_induct)
  show "adm (\<lambda>k. split_keys\<cdot>(split_maybe_unit\<cdot>k :: ('r, 'k) split_pd) = down\<cdot>(upper_unit\<cdot>k))"
    by simp
qed (simp add: skeys_upper_def Abs_pd_basis_singleton)

lemma split_keys_unit [simp]:
  "split_keys\<cdot>(split_unit\<cdot>x :: ('r, 'k) split_pd) = down\<cdot>(upper_unit\<cdot>(row_key\<cdot>x :: 'k))"
proof (induct x rule: compact_basis.principal_induct)
  show "adm (\<lambda>x. split_keys\<cdot>(split_unit\<cdot>x :: ('r, 'k) split_pd) = down\<cdot>(upper_unit\<cdot>(row_key\<cdot>x :: 'k)))"
    by simp
  fix a :: "'r compact_basis"
  let ?k = "row_key\<cdot>(Rep_compact_basis a) :: 'k"
  have "split_keys\<cdot>(\<Squnion>i. split_principal (SUnit a i) :: ('r, 'k) split_pd)
      = (\<Squnion>i. down\<cdot>(upper_unit\<cdot>(split_approx i\<cdot>?k)))"
  proof -
    have u: "upper_principal (PDUnit (Abs_compact_basis (split_approx i\<cdot>?k))) = upper_unit\<cdot>(split_approx i\<cdot>?k)" for i
      by (simp only: upper_unit_Rep_compact_basis [symmetric] Abs_compact_basis_inverse' [OF split_approx.compact_approx])
    show ?thesis
      by (simp add: contlub_cfun_arg [OF chain_split_unit_basis] skeys_upper_def Abs_pd_basis_singleton u)
  qed
  also have "\<dots> = down\<cdot>(upper_unit\<cdot>(\<Squnion>i. split_approx i\<cdot>?k))"
    by (simp add: contlub_cfun_arg contlub_cfun_fun)
  also have "\<dots> = down\<cdot>(upper_unit\<cdot>?k)"
    by (simp add: contlub_cfun_fun [symmetric])
  finally show "split_keys\<cdot>(split_unit\<cdot>(Rep_compact_basis a) :: ('r, 'k) split_pd) = down\<cdot>(upper_unit\<cdot>?k)"
    by simp
qed

lemma split_keys_open_unit [simp]: "split_keys\<cdot>(split_open_unit\<cdot>x :: ('r, 'k) split_pd) = down\<cdot>\<bottom>"
  by (simp only: split_open_unit_open [symmetric] split_keys_open)


subsection \<open>Inclusion and presence\<close>

text \<open>A dataset is \<^emph>\<open>included\<close> in another when adding it changes nothing: everything definite in
  it is definite in the other, and every key possible in the other is possible in it.  Three
  tests read presence off a dataset: a row is \<^emph>\<open>definite\<close> when its open unit is below the dataset
  (monotone), the dataset is \<^emph>\<open>confined\<close> above a key when the maybe-unit of the key is below it
  (monotone), and a key is \<^emph>\<open>possible\<close> when its maybe-unit is included in the dataset.\<close>

definition split_incl :: "('r, 'k) split_pd \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> bool" (infix \<open>\<subseteq>\<^sub>s\<close> 50) where
  "xs \<subseteq>\<^sub>s ys \<longleftrightarrow> ys \<union>\<^sub>s xs = ys"

lemma split_incl_refl [simp]: "xs \<subseteq>\<^sub>s xs"
  unfolding split_incl_def by simp

lemma split_incl_trans: "xs \<subseteq>\<^sub>s ys \<Longrightarrow> ys \<subseteq>\<^sub>s zs \<Longrightarrow> xs \<subseteq>\<^sub>s zs"
  unfolding split_incl_def by (metis split_plus_assoc)

lemma split_incl_antisym: "xs \<subseteq>\<^sub>s ys \<Longrightarrow> ys \<subseteq>\<^sub>s xs \<Longrightarrow> xs = ys"
  unfolding split_incl_def by (metis split_plus_commute)

lemma split_incl_plus1: "xs \<subseteq>\<^sub>s xs \<union>\<^sub>s ys" and split_incl_plus2: "ys \<subseteq>\<^sub>s xs \<union>\<^sub>s ys"
  unfolding split_incl_def by (simp_all add: split_plus_aci)

lemma split_empty_incl [simp]: "split_empty \<subseteq>\<^sub>s xs"
  unfolding split_incl_def by simp

lemma split_incl_principal:
  "split_principal s \<subseteq>\<^sub>s split_principal t \<longleftrightarrow> hoare_le (srows s) (srows t) \<and> smyth_le (skeys t) (skeys s)"
proof -
  have "split_principal t \<union>\<^sub>s split_principal s = split_principal t \<longleftrightarrow> split_le (SPlus t s) t \<and> split_le t (SPlus t s)"
    by (simp only: split_plus_principal split_pd.principal_eq_iff)
  also have "\<dots> \<longleftrightarrow> hoare_le (srows s) (srows t) \<and> smyth_le (skeys t) (skeys s)"
    unfolding split_le_def hoare_le_def smyth_le_def by auto
  finally show ?thesis unfolding split_incl_def .
qed

definition split_definite :: "'r \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> bool" where
  "split_definite x xs \<longleftrightarrow> split_open_unit\<cdot>x \<sqsubseteq> xs"

definition split_confined :: "'k \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> bool" where
  "split_confined k xs \<longleftrightarrow> split_maybe_unit\<cdot>k \<sqsubseteq> xs"

definition split_possible :: "'k \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> bool" where
  "split_possible k xs \<longleftrightarrow> split_maybe_unit\<cdot>k \<subseteq>\<^sub>s xs"

lemma split_definite_mono: "split_definite x xs \<Longrightarrow> xs \<sqsubseteq> ys \<Longrightarrow> split_definite x ys"
  and split_confined_mono: "split_confined k xs \<Longrightarrow> xs \<sqsubseteq> ys \<Longrightarrow> split_confined k ys"
  unfolding split_definite_def split_confined_def by (erule (1) below_trans)+

lemma split_definite_principal:
  "split_definite (Rep_compact_basis a) (split_principal t :: ('r, 'k) split_pd) \<longleftrightarrow> (\<exists>x\<in>srows t. a \<sqsubseteq> x)"
  unfolding split_definite_def by (simp add: split_le_def hoare_le_def smyth_le_def)

lemma split_confined_principal:
  "split_confined (Rep_compact_basis k) (split_principal t :: ('r, 'k) split_pd) \<longleftrightarrow> (\<forall>v\<in>skeys t. k \<sqsubseteq> v)"
  unfolding split_confined_def by (simp add: split_le_def smyth_le_def)

lemma split_possible_principal:
  "split_possible (Rep_compact_basis k) (split_principal t :: ('r, 'k) split_pd) \<longleftrightarrow> (\<exists>u\<in>skeys t. u \<sqsubseteq> k)"
  unfolding split_possible_def split_maybe_unit_Rep_compact_basis split_incl_principal
  by (simp add: hoare_le_def smyth_le_def)

text \<open>Possibility is read off the possible keys: a key is possible when the Smyth set of possible
  keys lies below its unit, that is, when it belongs to the set the Smyth set represents.  So
  possibility is upward closed.\<close>

lemma split_keys_plus_below: "split_keys\<cdot>(xs \<union>\<^sub>s ys) \<sqsubseteq> split_keys\<cdot>ys"
proof (induct xs rule: split_pd.principal_induct)
  case (2 s)
  show ?case
  proof (induct ys rule: split_pd.principal_induct)
    case (2 t)
    show ?case
    proof (cases "skeys t = {}")
      case False
      have "Abs_pd_basis (skeys s \<union> skeys t) \<le>\<sharp> Abs_pd_basis (skeys t)"
        using False by (simp add: upper_le_def Abs_pd_basis_inverse pd_basis_def) blast
      then show ?thesis using False by (simp add: skeys_upper_def upper_pd.principal_mono)
    qed (simp add: skeys_upper_def)
  qed simp
qed simp

lemma split_possible_keys: "split_possible (k::'k) (xs :: ('r, 'k) split_pd) \<longleftrightarrow> split_keys\<cdot>xs \<sqsubseteq> down\<cdot>{k}\<sharp>"
proof
  assume "split_possible k xs"
  then have "split_keys\<cdot>xs = split_keys\<cdot>(xs \<union>\<^sub>s split_maybe_unit\<cdot>k)" by (simp add: split_possible_def split_incl_def)
  also have "\<dots> \<sqsubseteq> down\<cdot>{k}\<sharp>" by (rule below_trans [OF split_keys_plus_below]) simp
  finally show "split_keys\<cdot>xs \<sqsubseteq> down\<cdot>{k}\<sharp>" .
next
  assume K: "split_keys\<cdot>xs \<sqsubseteq> down\<cdot>{k}\<sharp>"
  have kc: "chain (\<lambda>i. split_approx i\<cdot>k)" by (rule ch2ch_Rep_cfunL [OF split_approx.chain_approx])
  have kl: "(\<Squnion>i. split_approx i\<cdot>k) = k"
    by (simp add: contlub_cfun_fun [OF split_approx.chain_approx, symmetric])
  have le: "xs \<union>\<^sub>s split_maybe_unit\<cdot>k \<sqsubseteq> xs"
    using monofun_cfun_arg [OF split_maybe_unit_bottom_below [of k], of "split_plus\<cdot>xs"] by simp
  have "split_keys\<cdot>ys \<sqsubseteq> down\<cdot>{k}\<sharp> \<longrightarrow> ys \<sqsubseteq> ys \<union>\<^sub>s split_maybe_unit\<cdot>k" for ys :: "('r, 'k) split_pd"
  proof (induct ys rule: split_pd.principal_induct)
    case 1
    show ?case by (intro adm_imp adm_not_below adm_below) simp_all
  next
    case (2 s)
    show ?case
    proof
      assume "split_keys\<cdot>(split_principal s) \<sqsubseteq> down\<cdot>{k}\<sharp>"
      then have ne: "skeys s \<noteq> {}" and "upper_principal (Abs_pd_basis (skeys s)) \<sqsubseteq> {k}\<sharp>"
        by (auto simp: skeys_upper_def split: if_splits)
      then obtain u where u: "u \<in> skeys s" "Rep_compact_basis u \<sqsubseteq> k"
        by (auto simp: upper_principal_below_unit_iff Abs_pd_basis_inverse pd_basis_def)
      have "Rep_compact_basis u \<sqsubseteq> (\<Squnion>i. split_approx i\<cdot>k)" unfolding kl by (rule u(2))
      then obtain i where i: "Rep_compact_basis u \<sqsubseteq> split_approx i\<cdot>k"
        using compact_below_lub_iff [OF Rep_compact_basis' kc] by blast
      let ?a = "Abs_compact_basis (split_approx i\<cdot>k)"
      have a: "Rep_compact_basis ?a = split_approx i\<cdot>k" by (rule Abs_compact_basis_inverse' [OF split_approx.compact_approx])
      have ua: "u \<sqsubseteq> ?a" unfolding compact_le_def a by (rule i)
      have "split_le s (SPlus s (SKey ?a))"
        unfolding split_le_def hoare_le_def smyth_le_def using u(1) ua by auto
      then have "split_principal s \<sqsubseteq> split_principal (SPlus s (SKey ?a))" by (rule split_pd.principal_mono)
      also have "\<dots> = split_principal s \<union>\<^sub>s split_maybe_unit\<cdot>(split_approx i\<cdot>k)"
      proof -
        have "split_maybe_unit\<cdot>(split_approx i\<cdot>k) = (split_principal (SKey ?a) :: ('r, 'k) split_pd)"
          using split_maybe_unit_Rep_compact_basis [of ?a] unfolding a .
        then show ?thesis by (simp only: split_plus_principal)
      qed
      also have "\<dots> \<sqsubseteq> split_principal s \<union>\<^sub>s split_maybe_unit\<cdot>k"
        by (intro monofun_cfun_arg split_approx.approx_below)
      finally show "split_principal s \<sqsubseteq> split_principal s \<union>\<^sub>s split_maybe_unit\<cdot>k" .
    qed
  qed
  then have "xs \<sqsubseteq> xs \<union>\<^sub>s split_maybe_unit\<cdot>k" using K by blast
  then show "split_possible k xs" unfolding split_possible_def split_incl_def by (rule below_antisym [OF le])
qed

lemma split_possible_upper_set:
  "split_keys\<cdot>xs = down\<cdot>U \<Longrightarrow> split_possible k xs \<longleftrightarrow> k \<in> upper_set U"
  "split_keys\<cdot>xs = Top \<Longrightarrow> \<not> split_possible k xs"
  by (simp_all add: split_possible_keys upper_set_def)

lemma split_possible_up: "split_possible u xs \<Longrightarrow> u \<sqsubseteq> v \<Longrightarrow> split_possible v xs"
  unfolding split_possible_keys by (erule below_trans) (simp add: monofun_cfun_arg)


text \<open>\<^emph>\<open>Rigid presence\<close>: a row is present when its exact unit is included in the dataset, so
  adding the row changes nothing.  This is neither monotone nor antitone.  It says that the row is
  definite and its key possible; on compact data the two together are equivalent to it.\<close>

definition split_present :: "'r \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> bool" where
  "split_present x xs \<longleftrightarrow> split_unit\<cdot>x \<subseteq>\<^sub>s xs"

lemma split_open_below_plus: "split_open\<cdot>ys \<sqsubseteq> xs \<union>\<^sub>s ys"
  apply (induct xs rule: split_pd.principal_induct, simp)
  apply (induct ys rule: split_pd.principal_induct, simp)
  apply (simp add: split_le_def hoare_le_def smyth_le_def, blast)
  done

lemma split_incl_maybe: "ys \<subseteq>\<^sub>s xs \<Longrightarrow> split_maybe\<cdot>ys \<subseteq>\<^sub>s xs"
proof -
  assume "ys \<subseteq>\<^sub>s xs"
  then have xy: "xs \<union>\<^sub>s ys = xs" unfolding split_incl_def .
  have "xs \<union>\<^sub>s split_maybe\<cdot>ys = (xs \<union>\<^sub>s ys) \<union>\<^sub>s split_maybe\<cdot>ys" by (simp only: xy)
  also have "\<dots> = xs \<union>\<^sub>s ys" by (simp only: split_plus_assoc split_plus_maybe_absorb)
  finally show ?thesis unfolding split_incl_def xy .
qed

lemma split_present_definite: "split_present x xs \<Longrightarrow> split_definite x xs"
proof -
  assume "split_present x xs"
  then have "xs \<union>\<^sub>s split_unit\<cdot>x = xs" unfolding split_present_def split_incl_def .
  moreover have "split_open\<cdot>(split_unit\<cdot>x) \<sqsubseteq> xs \<union>\<^sub>s split_unit\<cdot>x" by (rule split_open_below_plus)
  ultimately show ?thesis unfolding split_definite_def by (simp add: split_open_unit_open)
qed

text \<open>On compact data, rigid presence reads off the generators: some definite row is above the
  row, and some possible key below the row's key.\<close>

lemma split_present_principal:
  "split_present (Rep_compact_basis a) (split_principal t :: ('r, 'k) split_pd) \<longleftrightarrow>
    (\<exists>x\<in>srows t. a \<sqsubseteq> x) \<and> (\<exists>u\<in>skeys t. Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis a))"
proof -
  let ?k = "row_key\<cdot>(Rep_compact_basis a) :: 'k"
  let ?C = "\<lambda>i. split_principal (SPlus t (SUnit a i)) :: ('r, 'k) split_pd"
  have C: "chain ?C"
    by (rule chainI, rule split_pd.principal_mono, rule SPlus_split_mono, simp, rule SUnit_split_mono) simp_all
  have lub: "split_principal t \<union>\<^sub>s split_unit\<cdot>(Rep_compact_basis a) = (\<Squnion>i. ?C i)"
    by (simp add: contlub_cfun_arg [OF chain_split_unit_basis])
  have kc: "chain (\<lambda>i. split_approx i\<cdot>?k)" by (rule ch2ch_Rep_cfunL [OF split_approx.chain_approx])
  have kl: "(\<Squnion>i. split_approx i\<cdot>?k) = ?k"
    by (simp add: contlub_cfun_fun [OF split_approx.chain_approx, symmetric])
  have Ab: "u \<sqsubseteq> Abs_compact_basis (split_approx i\<cdot>?k) \<longleftrightarrow> Rep_compact_basis u \<sqsubseteq> split_approx i\<cdot>?k" for u i
    unfolding compact_le_def by (simp only: Abs_compact_basis_inverse' [OF split_approx.compact_approx])
  show ?thesis
  proof
    assume "split_present (Rep_compact_basis a) (split_principal t :: ('r, 'k) split_pd)"
    then have eq: "(\<Squnion>i. ?C i) = split_principal t" unfolding split_present_def split_incl_def lub .
    have "?C 0 \<sqsubseteq> split_principal t" unfolding eq [symmetric] by (rule is_ub_thelub [OF C])
    then have rows: "\<exists>x\<in>srows t. a \<sqsubseteq> x" by (simp add: split_le_def hoare_le_def)
    have "split_principal t \<sqsubseteq> (\<Squnion>i. ?C i)" unfolding eq ..
    then obtain i where "split_principal t \<sqsubseteq> ?C i"
      using compact_below_lub_iff [OF split_pd.compact_principal C] by blast
    then obtain u where u: "u \<in> skeys t" and "Rep_compact_basis u \<sqsubseteq> split_approx i\<cdot>?k"
      by (auto simp: split_le_def smyth_le_def Ab)
    then have "Rep_compact_basis u \<sqsubseteq> ?k" by (blast intro: below_trans split_approx.approx_below)
    with rows u show "(\<exists>x\<in>srows t. a \<sqsubseteq> x) \<and> (\<exists>u\<in>skeys t. Rep_compact_basis u \<sqsubseteq> ?k)" by blast
  next
    assume "(\<exists>x\<in>srows t. a \<sqsubseteq> x) \<and> (\<exists>u\<in>skeys t. Rep_compact_basis u \<sqsubseteq> ?k)"
    then obtain x u where x: "x \<in> srows t" "a \<sqsubseteq> x" and u: "u \<in> skeys t" "Rep_compact_basis u \<sqsubseteq> ?k" by blast
    have "Rep_compact_basis u \<sqsubseteq> (\<Squnion>i. split_approx i\<cdot>?k)" unfolding kl by (rule u(2))
    then obtain i0 where i0: "Rep_compact_basis u \<sqsubseteq> split_approx i0\<cdot>?k"
      using compact_below_lub_iff [OF Rep_compact_basis' kc] by blast
    have Ci: "?C (i + i0) = split_principal t" for i
    proof -
      have "split_approx i0\<cdot>?k \<sqsubseteq> split_approx (i + i0)\<cdot>?k"
        by (rule monofun_cfun_fun, rule chain_mono [OF split_approx.chain_approx]) simp
      then have "Rep_compact_basis u \<sqsubseteq> split_approx (i + i0)\<cdot>?k" by (rule below_trans [OF i0])
      then show ?thesis
        unfolding split_pd.principal_eq_iff using x u(1)
        by (auto simp: split_le_def hoare_le_def smyth_le_def Ab)
    qed
    have "(\<Squnion>i. ?C i) = (\<Squnion>i. ?C (i + i0))" by (rule lub_range_shift [OF C, symmetric])
    also have "\<dots> = split_principal t" by (simp only: Ci lub_const)
    finally show "split_present (Rep_compact_basis a) (split_principal t :: ('r, 'k) split_pd)"
      unfolding split_present_def split_incl_def lub .
  qed
qed


subsection \<open>Views act on datasets\<close>

text \<open>For keyed rows, a view acts on datasets: it
  sections the rows to the view's columns and the support of its key part, and projects the
  possible keys to the key part.  This is a deflation.\<close>

locale split_keyed = keyed
begin

definition vrow :: "('r, 'k) view \<Rightarrow> 'r compact_basis \<Rightarrow> 'r compact_basis" where
  "vrow v x = Abs_compact_basis (Rep_compact_basis x \<downharpoonright> (fst v \<squnion> csupp (snd v)))"

definition vkeyb :: "('r, 'k) view \<Rightarrow> 'k compact_basis \<Rightarrow> 'k compact_basis" where
  "vkeyb v u = Abs_compact_basis (proj (snd v)\<cdot>(Rep_compact_basis u))"

lemma Rep_vrow [simp]: "Rep_compact_basis (vrow v x) = Rep_compact_basis x \<downharpoonright> (fst v \<squnion> csupp (snd v))"
  unfolding vrow_def by (simp add: compact_proj_compact)

lemma Rep_vkeyb [simp]: "Rep_compact_basis (vkeyb v u) = proj (snd v)\<cdot>(Rep_compact_basis u)"
  unfolding vkeyb_def by (simp add: compact_proj_compact)

lemma vview_consistent: "split_consistent (vrow v ` srows t) (vkeyb v ` skeys t)"
  unfolding split_consistent_def
proof
  fix x' assume "x' \<in> vrow v ` srows t"
  then obtain x where x: "x \<in> srows t" and x': "x' = vrow v x" by blast
  obtain u where u: "u \<in> skeys t" and ux: "Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x)"
    using split_basis_consistentD [OF x] by blast
  let ?s = "fst v \<squnion> csupp (snd v)" and ?a = "snd v"
  have "proj ?a\<cdot>(Rep_compact_basis u) \<sqsubseteq> rproj ?a (Rep_compact_basis x)"
    using ux by (rule monofun_cfun_arg)
  also have "\<dots> = rproj ?a (Rep_compact_basis x \<downharpoonright> ?s)"
    by (rule rproj_section [symmetric]) (rule lattice_join_ge2)
  also have "\<dots> \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x \<downharpoonright> ?s)"
    by (rule deflation.below [OF proj_defl])
  finally show "\<exists>w\<in>vkeyb v ` skeys t. Rep_compact_basis w \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x')"
    using u unfolding x' by auto
qed

definition SView :: "('r, 'k) view \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> ('r, 'k) split_basis" where
  "SView v t = SplitB (vrow v ` srows t) (vkeyb v ` skeys t)"

lemma srows_SView [simp]: "srows (SView v t) = vrow v ` srows t"
  and skeys_SView [simp]: "skeys (SView v t) = vkeyb v ` skeys t"
  unfolding SView_def by (simp_all add: vview_consistent)

lemma vrow_mono: "x \<sqsubseteq> y \<Longrightarrow> vrow v x \<sqsubseteq> vrow v y"
  and vkeyb_mono: "u \<sqsubseteq> w \<Longrightarrow> vkeyb v u \<sqsubseteq> vkeyb v w"
  unfolding compact_le_def by (simp_all add: monofun_cfun_arg)

lemma SView_split_mono: "split_le s t \<Longrightarrow> split_le (SView v s) (SView v t)"
  unfolding split_le_def hoare_le_def smyth_le_def by auto (meson vrow_mono vkeyb_mono)+

definition split_view :: "('r, 'k) view \<Rightarrow> ('r, 'k) split_pd \<rightarrow> ('r, 'k) split_pd" where
  "split_view v = split_pd.extension (\<lambda>t. split_principal (SView v t))"

lemma split_view_principal [simp]: "split_view v\<cdot>(split_principal t) = split_principal (SView v t)"
  unfolding split_view_def by (simp add: split_pd.extension_principal SView_split_mono)

lemma vrow_below: "vrow v x \<sqsubseteq> x" and vkeyb_below: "vkeyb v u \<sqsubseteq> u"
  unfolding compact_le_def by (simp_all add: deflation.below [OF proj_defl])

lemma vrow_idem [simp]: "vrow v (vrow v x) = vrow v x" and vkeyb_idem [simp]: "vkeyb v (vkeyb v u) = vkeyb v u"
  by (simp_all add: Rep_compact_basis_inject [symmetric] deflation.idem [OF proj_defl])

lemma deflation_split_view: "deflation (split_view v)"
proof
  fix xs :: "('r, 'k) split_pd"
  show "split_view v\<cdot>(split_view v\<cdot>xs) = split_view v\<cdot>xs"
    by (induct xs rule: split_pd.principal_induct, simp, simp,
        rule split_principal_eqI, simp_all add: image_image)
  show "split_view v\<cdot>xs \<sqsubseteq> xs"
    by (induct xs rule: split_pd.principal_induct, simp,
        simp add: split_le_def hoare_le_def smyth_le_def, use vrow_below vkeyb_below in blast)
qed

lemma split_view_plus [simp]: "split_view v\<cdot>(xs \<union>\<^sub>s ys) = split_view v\<cdot>xs \<union>\<^sub>s split_view v\<cdot>ys"
  apply (induct xs rule: split_pd.principal_induct, simp)
  apply (induct ys rule: split_pd.principal_induct, simp)
  apply (simp, rule split_principal_eqI, simp_all add: image_Un)
  done

lemma split_view_maybe [simp]: "split_view v\<cdot>(split_maybe\<cdot>xs) = split_maybe\<cdot>(split_view v\<cdot>xs)"
  by (induct xs rule: split_pd.principal_induct, simp, simp, rule split_principal_eqI, simp_all)

lemma split_view_empty [simp]: "split_view v\<cdot>split_empty = split_empty"
  by (simp add: split_empty_def, rule split_principal_eqI, simp_all)

lemma split_view_strict [simp]: "split_view v\<cdot>\<bottom> = \<bottom>"
proof -
  have b: "proj (snd v)\<cdot>\<bottom> = \<bottom>" by (rule bottomI, rule deflation.below [OF proj_defl])
  have "split_view v\<cdot>(split_principal SBot) = split_principal SBot"
    by (simp only: split_view_principal, rule split_principal_eqI) (simp_all add: vkeyb_def compact_bot_def b)
  then show ?thesis by (simp only: inst_split_pd_pcpo)
qed

end

end
