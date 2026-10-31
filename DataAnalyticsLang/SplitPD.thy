theory SplitPD
  imports HOLCF
begin

section \<open>The split powerdomain\<close>

text \<open>A dataset in the split powerdomain has two parts in different types: \<^emph>\<open>definite rows\<close>,
  ordered as in the lower (Hoare) powerdomain over the row type, and \<^emph>\<open>possible keys\<close>, ordered
  as in the upper (Smyth) powerdomain over the key type.  The two are tied through the key of a
  row, @{text split_key}: every definite row has its key above some possible key.  Like HOLCF's
  powerdomains and the mixed powerdomain (the case where the key of a row is the row itself), it
  is the ideal completion of a preordered basis of pairs of finite sets of compact elements, and
  the consistency condition is stated on the generators of a basis element: on Hoare closures it
  would force the bottom key.  Both parts may be empty: no definite rows is the Hoare bottom, no
  possible keys the Smyth top (definitely no rows), which consistency forces to come with no
  definite rows.

  The key of a row is a constant, left unspecified: instances give it for particular row and key
  types.  The split powerdomain is pointed; it is bifinite only for suitable keys (spectral ones),
  so no generic bifinite instance is given.\<close>

consts split_key :: "'r::bifinite \<rightarrow> 'k::bifinite"


subsection \<open>The basis\<close>

definition split_consistent :: "'r::bifinite compact_basis set \<Rightarrow> 'k::bifinite compact_basis set \<Rightarrow> bool" where
  "split_consistent X U \<longleftrightarrow> (\<forall>x\<in>X. \<exists>u\<in>U. Rep_compact_basis u \<sqsubseteq> split_key\<cdot>(Rep_compact_basis x))"

lemma split_consistent_empty [simp]: "split_consistent {} U"
  by (simp add: split_consistent_def)

lemma split_consistent_Un:
  "split_consistent X U \<Longrightarrow> split_consistent Y V \<Longrightarrow> split_consistent (X \<union> Y) (U \<union> V)"
  unfolding split_consistent_def by blast

typedef (overloaded) ('r::bifinite, 'k::bifinite) split_basis =
  "{(X, U). finite X \<and> finite U \<and> split_consistent X U} :: ('r compact_basis set \<times> 'k compact_basis set) set"
  by (rule exI [of _ "({}, {})"]) simp

definition srows :: "('r::bifinite, 'k::bifinite) split_basis \<Rightarrow> 'r compact_basis set" where
  "srows t = fst (Rep_split_basis t)"

definition skeys :: "('r::bifinite, 'k::bifinite) split_basis \<Rightarrow> 'k compact_basis set" where
  "skeys t = snd (Rep_split_basis t)"

definition SplitB :: "'r::bifinite compact_basis set \<Rightarrow> 'k::bifinite compact_basis set \<Rightarrow> ('r, 'k) split_basis" where
  "SplitB X U = Abs_split_basis (X, U)"

lemma finite_srows [simp]: "finite (srows t)"
  and finite_skeys [simp]: "finite (skeys t)"
  and split_basis_consistent: "split_consistent (srows t) (skeys t)"
  using Rep_split_basis [of t] by (auto simp: srows_def skeys_def split: prod.splits)

lemma split_basis_consistentD:
  "x \<in> srows t \<Longrightarrow> \<exists>u\<in>skeys t. Rep_compact_basis u \<sqsubseteq> split_key\<cdot>(Rep_compact_basis x)"
  using split_basis_consistent [of t] unfolding split_consistent_def by blast

lemma split_basis_eqI: "\<lbrakk>srows s = srows t; skeys s = skeys t\<rbrakk> \<Longrightarrow> s = t"
  by (simp add: srows_def skeys_def Rep_split_basis_inject [symmetric] prod_eq_iff)

lemma srows_SplitB [simp]: "\<lbrakk>finite X; finite U; split_consistent X U\<rbrakk> \<Longrightarrow> srows (SplitB X U) = X"
  and skeys_SplitB [simp]: "\<lbrakk>finite X; finite U; split_consistent X U\<rbrakk> \<Longrightarrow> skeys (SplitB X U) = U"
  by (simp_all add: srows_def skeys_def SplitB_def Abs_split_basis_inverse)

lemma split_basis_countable: "\<exists>f::('r::bifinite, 'k::bifinite) split_basis \<Rightarrow> nat. inj f"
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

definition split_le :: "('r::bifinite, 'k::bifinite) split_basis \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> bool" where
  "split_le s t \<longleftrightarrow> hoare_le (srows s) (srows t) \<and> smyth_le (skeys s) (skeys t)"

lemma split_le_refl [simp]: "split_le t t"
  unfolding split_le_def by simp

lemma split_le_trans: "\<lbrakk>split_le s t; split_le t u\<rbrakk> \<Longrightarrow> split_le s u"
  unfolding split_le_def by (blast intro: hoare_le_trans smyth_le_trans)

interpretation split_le: preorder split_le
  by (rule preorder.intro, rule split_le_refl, rule split_le_trans)


subsection \<open>Type definition\<close>

typedef (overloaded) ('r::bifinite, 'k::bifinite) split_pd =
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

definition split_principal :: "('r::bifinite, 'k::bifinite) split_basis \<Rightarrow> ('r, 'k) split_pd" where
  "split_principal t = Abs_split_pd {u. split_le u t}"

interpretation split_pd: ideal_completion split_le split_principal Rep_split_pd
  using type_definition_split_pd below_split_pd_def
  using split_principal_def split_basis_countable
  by (rule split_le.typedef_ideal_completion)

text \<open>The least element has no definite rows and the possible key \<open>\<bottom>\<close>: the open world.\<close>

definition SBot :: "('r::bifinite, 'k::bifinite) split_basis" where
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

definition SEmpty :: "('r::bifinite, 'k::bifinite) split_basis" where
  "SEmpty = SplitB {} {}"

definition SPlus :: "('r::bifinite, 'k::bifinite) split_basis \<Rightarrow> ('r, 'k) split_basis \<Rightarrow> ('r, 'k) split_basis" where
  "SPlus s t = SplitB (srows s \<union> srows t) (skeys s \<union> skeys t)"

definition SMaybe :: "('r::bifinite, 'k::bifinite) split_basis \<Rightarrow> ('r, 'k) split_basis" where
  "SMaybe t = SplitB {} (skeys t)"

definition SOpen :: "'r::bifinite compact_basis \<Rightarrow> ('r, 'k::bifinite) split_basis" where
  "SOpen a = SplitB {a} {compact_bot}"

definition SKey :: "'k::bifinite compact_basis \<Rightarrow> ('r::bifinite, 'k) split_basis" where
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

definition split_empty :: "('r::bifinite, 'k::bifinite) split_pd" where
  "split_empty = split_principal SEmpty"

definition split_plus :: "('r::bifinite, 'k::bifinite) split_pd \<rightarrow> ('r, 'k) split_pd \<rightarrow> ('r, 'k) split_pd" where
  "split_plus = split_pd.extension (\<lambda>t. split_pd.extension (\<lambda>u. split_principal (SPlus t u)))"

abbreviation split_add :: "('r::bifinite, 'k::bifinite) split_pd \<Rightarrow> ('r, 'k) split_pd \<Rightarrow> ('r, 'k) split_pd"
    (infixl \<open>\<union>\<^sub>s\<close> 65) where
  "xs \<union>\<^sub>s ys \<equiv> split_plus\<cdot>xs\<cdot>ys"

definition split_maybe :: "('r::bifinite, 'k::bifinite) split_pd \<rightarrow> ('r, 'k) split_pd" where
  "split_maybe = split_pd.extension (\<lambda>t. split_principal (SMaybe t))"

definition split_open_unit :: "'r::bifinite \<rightarrow> ('r, 'k::bifinite) split_pd" where
  "split_open_unit = compact_basis.extension (\<lambda>a. split_principal (SOpen a))"

definition split_maybe_unit :: "'k::bifinite \<rightarrow> ('r::bifinite, 'k) split_pd" where
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
  fix xs ys zs :: "('r::bifinite, 'k::bifinite) split_pd"
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

definition split_approx :: "nat \<Rightarrow> 'a::bifinite \<rightarrow> 'a" where
  "split_approx = (SOME a. approx_chain a)"

lemma approx_chain_split_approx: "approx_chain split_approx"
  unfolding split_approx_def by (rule someI_ex [OF bifinite])

interpretation split_approx: approx_chain split_approx
  by (rule approx_chain_split_approx)

definition SUnit :: "'r::bifinite compact_basis \<Rightarrow> nat \<Rightarrow> ('r, 'k::bifinite) split_basis" where
  "SUnit a i = SplitB {a} {Abs_compact_basis (split_approx i\<cdot>(split_key\<cdot>(Rep_compact_basis a)))}"

lemma srows_SUnit [simp]: "srows (SUnit a i :: ('r::bifinite, 'k::bifinite) split_basis) = {a}"
  and skeys_SUnit [simp]:
    "skeys (SUnit a i :: ('r::bifinite, 'k::bifinite) split_basis)
      = {Abs_compact_basis (split_approx i\<cdot>(split_key\<cdot>(Rep_compact_basis a) :: 'k))}"
proof -
  have "split_consistent {a} {Abs_compact_basis (split_approx i\<cdot>(split_key\<cdot>(Rep_compact_basis a) :: 'k))}"
    by (simp add: split_consistent_def split_approx.approx_below)
  then show "srows (SUnit a i :: ('r, 'k) split_basis) = {a}"
    and "skeys (SUnit a i :: ('r, 'k) split_basis)
      = {Abs_compact_basis (split_approx i\<cdot>(split_key\<cdot>(Rep_compact_basis a) :: 'k))}"
    unfolding SUnit_def by simp_all
qed

lemma SUnit_split_mono:
  assumes ab: "a \<sqsubseteq> b" and ij: "i \<le> j"
  shows "split_le (SUnit a i :: ('r::bifinite, 'k::bifinite) split_basis) (SUnit b j)"
proof -
  have "split_approx i \<sqsubseteq> (split_approx j :: 'k \<rightarrow> 'k)"
    by (rule chain_mono [OF split_approx.chain_approx ij])
  moreover have "split_key\<cdot>(Rep_compact_basis a) \<sqsubseteq> (split_key\<cdot>(Rep_compact_basis b) :: 'k)"
    by (rule monofun_cfun_arg) (use ab in \<open>simp only: compact_le_def\<close>)
  ultimately have "split_approx i\<cdot>(split_key\<cdot>(Rep_compact_basis a)) \<sqsubseteq> (split_approx j\<cdot>(split_key\<cdot>(Rep_compact_basis b)) :: 'k)"
    by (rule monofun_cfun)
  then have "Abs_compact_basis (split_approx i\<cdot>(split_key\<cdot>(Rep_compact_basis a)))
      \<sqsubseteq> (Abs_compact_basis (split_approx j\<cdot>(split_key\<cdot>(Rep_compact_basis b))) :: 'k compact_basis)"
    by (simp only: compact_le_def Abs_compact_basis_inverse' split_approx.compact_approx)
  then show ?thesis using ab unfolding split_le_def hoare_le_def smyth_le_def srows_SUnit skeys_SUnit by simp
qed

definition split_unit_basis :: "'r::bifinite compact_basis \<Rightarrow> ('r, 'k::bifinite) split_pd" where
  "split_unit_basis a = (\<Squnion>i. split_principal (SUnit a i))"

lemma chain_split_unit_basis: "chain (\<lambda>i. split_principal (SUnit a i) :: ('r::bifinite, 'k::bifinite) split_pd)"
  by (rule chainI, rule split_pd.principal_mono, rule SUnit_split_mono) simp_all

lemma split_unit_basis_mono: "a \<sqsubseteq> b \<Longrightarrow> split_unit_basis a \<sqsubseteq> (split_unit_basis b :: ('r::bifinite, 'k::bifinite) split_pd)"
  unfolding split_unit_basis_def
  by (rule lub_mono [OF chain_split_unit_basis chain_split_unit_basis],
      rule split_pd.principal_mono, rule SUnit_split_mono) simp_all

definition split_unit :: "'r::bifinite \<rightarrow> ('r, 'k::bifinite) split_pd" where
  "split_unit = compact_basis.extension split_unit_basis"

lemma split_unit_Rep_compact_basis [simp]:
  "split_unit\<cdot>(Rep_compact_basis a) = (\<Squnion>i. split_principal (SUnit a i))"
  unfolding split_unit_def
  by (simp add: compact_basis.extension_principal split_unit_basis_mono, simp add: split_unit_basis_def)

text \<open>The open unit is below the unit: it forgets the row's key.\<close>

lemma split_open_unit_below_unit:
  "split_open_unit\<cdot>x \<sqsubseteq> (split_unit\<cdot>x :: ('r::bifinite, 'k::bifinite) split_pd)"
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

text \<open>The definite rows of a dataset, as a lower powerdomain: no definite rows is its bottom.\<close>

definition srows_lower :: "('r::bifinite, 'k::bifinite) split_basis \<Rightarrow> 'r lower_pd" where
  "srows_lower t = (if srows t = {} then \<bottom> else lower_principal (Abs_pd_basis (srows t)))"

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

definition split_rows :: "('r::bifinite, 'k::bifinite) split_pd \<rightarrow> 'r lower_pd" where
  "split_rows = split_pd.extension srows_lower"

lemma split_rows_principal [simp]: "split_rows\<cdot>(split_principal t) = srows_lower t"
  unfolding split_rows_def by (simp add: split_pd.extension_principal srows_lower_mono)

lemma split_rows_open_unit [simp]: "split_rows\<cdot>(split_open_unit\<cdot>x) = lower_unit\<cdot>x"
proof (induct x rule: compact_basis.principal_induct)
  show "adm (\<lambda>x. split_rows\<cdot>(split_open_unit\<cdot>x) = lower_unit\<cdot>x)" by simp
qed (simp add: srows_lower_def PDUnit_def)

lemma split_rows_unit [simp]: "split_rows\<cdot>(split_unit\<cdot>x :: ('r::bifinite, 'k::bifinite) split_pd) = lower_unit\<cdot>x"
proof (induct x rule: compact_basis.principal_induct)
  show "adm (\<lambda>x. split_rows\<cdot>(split_unit\<cdot>x :: ('r, 'k) split_pd) = lower_unit\<cdot>x)" by simp
  fix a :: "'r compact_basis"
  have "split_rows\<cdot>(\<Squnion>i. split_principal (SUnit a i) :: ('r, 'k) split_pd) = (\<Squnion>i. srows_lower (SUnit a i :: ('r, 'k) split_basis))"
    by (simp add: contlub_cfun_arg [OF chain_split_unit_basis])
  also have "\<dots> = lower_unit\<cdot>(Rep_compact_basis a)"
    by (simp add: srows_lower_def PDUnit_def)
  finally show "split_rows\<cdot>(split_unit\<cdot>(Rep_compact_basis a) :: ('r, 'k) split_pd) = lower_unit\<cdot>(Rep_compact_basis a)"
    by simp
qed

lemma split_rows_maybe [simp]: "split_rows\<cdot>(split_maybe\<cdot>xs) = \<bottom>"
  by (induct xs rule: split_pd.principal_induct, simp, simp add: srows_lower_def)

lemma split_rows_empty [simp]: "split_rows\<cdot>split_empty = \<bottom>"
  by (simp add: split_empty_def srows_lower_def)

lemma split_rows_strict [simp]: "split_rows\<cdot>\<bottom> = \<bottom>"
  by (simp add: inst_split_pd_pcpo srows_lower_def)

lemma split_rows_plus [simp]: "split_rows\<cdot>(xs \<union>\<^sub>s ys) = split_rows\<cdot>xs \<union>\<flat> split_rows\<cdot>ys"
proof (induct xs rule: split_pd.principal_induct)
  fix s
  show "split_rows\<cdot>(split_principal s \<union>\<^sub>s ys) = split_rows\<cdot>(split_principal s) \<union>\<flat> split_rows\<cdot>ys"
  proof (induct ys rule: split_pd.principal_induct)
    fix t
    show "split_rows\<cdot>(split_principal s \<union>\<^sub>s split_principal t)
        = split_rows\<cdot>(split_principal s) \<union>\<flat> split_rows\<cdot>(split_principal t)"
      by (cases "srows s = {}"; cases "srows t = {}")
        (simp_all add: srows_lower_def PDPlus_def Abs_pd_basis_inverse pd_basis_def)
  qed simp
qed simp

end
