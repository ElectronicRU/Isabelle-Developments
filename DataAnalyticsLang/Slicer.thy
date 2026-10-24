theory Slicer
  imports ValsetBase Congruence LOD "HOL-Library.FSet"
begin

default_sort type

section \<open>Levels of detail as syntactic dimension sets\<close>

text \<open>
  Dimensions are drawn from a (countable, nominal) label set \<^typ>\<open>'d\<close>; each label is
  evaluated on rows by a continuous row-level expression into a value domain.  Two labels may
  share an expression: they are then functionally dependent, but distinct.  The key of a row is
  the tuple of all its dimensions' values; a level of detail then cuts it.

  The image of a row under the cut key need \<^emph>\<open>not\<close> be a stable subdomain of the tuple domain
  (with an expression dimension \<open>c \<approx> a + b\<close> the allowable sub-rows are not closed under existing
  joins), and we never require it to be: the domain stays the source rows, and functional
  dependence is stated relationally via kernel orders.
\<close>

locale dim_eval =
  fixes deval :: "'d \<Rightarrow> ('r::pcpo \<rightarrow> 'v::pcpo)" (\<open>\<lbrakk>_\<rbrakk>\<close>)
begin

definition keyof :: "'r \<rightarrow> ('d, 'v) tuple" where
  "keyof = (\<Lambda> r. Abs_tuple (\<lambda>d. \<lbrakk>d\<rbrakk>\<cdot>r))"

lemma keyof_beta: "keyof\<cdot>r = Abs_tuple (\<lambda>d. \<lbrakk>d\<rbrakk>\<cdot>r)"
  unfolding keyof_def by (simp add: cont_Abs_tuple)

lemma keyof_tget [simp]: "(keyof\<cdot>r)\<langle>d\<rangle> = \<lbrakk>d\<rbrakk>\<cdot>r"
  by (simp add: keyof_beta Abs_tuple_inverse')

subsection \<open>Kernel orders and functional dependence\<close>

text \<open>The kernel order of a projection \<open>p\<close> on keys (in practice a deflation, such as an LOD's):
  rows compared by what \<open>p\<close> keeps of their keys.\<close>

definition kern :: "(('d, 'v) tuple \<rightarrow> ('d, 'v) tuple) \<Rightarrow> 'r \<Rightarrow> 'r \<Rightarrow> bool" where
  "kern p x y \<longleftrightarrow> p\<cdot>(keyof\<cdot>x) \<sqsubseteq> p\<cdot>(keyof\<cdot>y)"

lemma is_cong_kern: "is_cong (kern p)"
  unfolding kern_def by unfold_locales (auto intro: below_trans monofun_cfun_arg)

lemma kern_bot: "kern \<bottom> x y"
  by (simp add: kern_def)

lemma kern_below:
  assumes "deflation p" "deflation q" "p \<sqsubseteq> q" and "kern q x y"
  shows "kern p x y"
proof -
  have "p\<cdot>(q\<cdot>(keyof\<cdot>x)) \<sqsubseteq> p\<cdot>(q\<cdot>(keyof\<cdot>y))" using assms(4) unfolding kern_def by (rule monofun_cfun_arg)
  then show ?thesis unfolding kern_def by (simp add: deflation_below_comp1[OF assms(1-3)])
qed

text \<open>Functional dependence of \<open>p\<close> on \<open>q\<close>, relative to a support predicate \<^term>\<open>S\<close> on source
  rows: rows that \<open>q\<close> cannot tell apart (in the kernel order), \<open>p\<close> cannot either.  Taking
  \<^term>\<open>S\<close> true everywhere gives schema-level dependence; taking \<^term>\<open>S\<close> to be what a filter
  selects gives the data-level one.\<close>

definition fdep :: "('r \<Rightarrow> bool) \<Rightarrow> (('d, 'v) tuple \<rightarrow> ('d, 'v) tuple) \<Rightarrow> (('d, 'v) tuple \<rightarrow> ('d, 'v) tuple) \<Rightarrow> bool" where
  "fdep S p q \<longleftrightarrow> (\<forall>x y. S x \<longrightarrow> S y \<longrightarrow> kern q x y \<longrightarrow> kern p x y)"

lemma fdep_refl: "fdep S p p"
  by (simp add: fdep_def)

lemma fdep_trans: "fdep S p q \<Longrightarrow> fdep S q r \<Longrightarrow> fdep S p r"
  unfolding fdep_def by blast

lemma fdep_below: "deflation p \<Longrightarrow> deflation q \<Longrightarrow> p \<sqsubseteq> q \<Longrightarrow> fdep S p q"
  unfolding fdep_def by (blast intro: kern_below)

lemma fdep_support_mono: "(\<And>x. S' x \<Longrightarrow> S x) \<Longrightarrow> fdep S p q \<Longrightarrow> fdep S' p q"
  unfolding fdep_def by blast

end

section \<open>Filters\<close>

text \<open>A filter is a continuous predicate into \<^typ>\<open>one\<close> (Sierpinski space): a row \<^emph>\<open>passes\<close> it
  when it maps to \<^term>\<open>ONE\<close>, a Scott-open predicate.  Several filters are combined by
  continuous conjunction.\<close>

definition passes :: "('r::pcpo \<rightarrow> one) \<Rightarrow> 'r \<Rightarrow> bool" where
  "passes \<phi> r \<longleftrightarrow> \<phi>\<cdot>r = ONE"

lemma passes_up: "passes \<phi> x \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> passes \<phi> y"
  unfolding passes_def by (cases "\<phi>\<cdot>y") (auto dest: monofun_cfun_arg[of x y \<phi>])

lemma passes_open: "adm (\<lambda>r. \<not> passes \<phi> r)"
proof -
  have "\<not> passes \<phi> r \<longleftrightarrow> \<phi>\<cdot>r \<sqsubseteq> \<bottom>" for r
    unfolding passes_def by (cases "\<phi>\<cdot>r") simp_all
  then show ?thesis by simp
qed

definition fconj :: "('r::pcpo \<rightarrow> one) \<Rightarrow> ('r \<rightarrow> one) \<Rightarrow> ('r \<rightarrow> one)" where
  "fconj \<phi> \<psi> = (\<Lambda> r. seq\<cdot>(\<phi>\<cdot>r)\<cdot>(\<psi>\<cdot>r))"

lemma passes_fconj [simp]: "passes (fconj \<phi> \<psi>) r \<longleftrightarrow> passes \<phi> r \<and> passes \<psi> r"
  unfolding passes_def fconj_def by (auto simp: seq_conv_if split: if_splits)

lemma passes_ftrue [simp]: "passes (\<Lambda> _. ONE) r"
  by (simp add: passes_def)

section \<open>Datasets\<close>

text \<open>A dataset is a Scott-closed set \<^term>\<open>S\<close> of rows whose \<^emph>\<open>maximal\<close> elements are the
  actual data points; the rest are their partial approximations (sub-rows).  These need not be
  maximal in the row \<^emph>\<open>type\<close>.  Restricting to a predicate keeps the data points satisfying it and
  everything below them.  The result is generally \<^emph>\<open>not\<close> a stable subdomain (it need not be
  closed under joins of compatible sub-rows), but it is again a dataset, with exactly those
  points as its maximal elements.  We assume finitely many data points, which also makes
  closedness automatic.\<close>

definition pts :: "'r::pcpo set \<Rightarrow> 'r set" where
  "pts S = {m \<in> S. \<forall>y\<in>S. m \<sqsubseteq> y \<longrightarrow> y = m}"

definition filtered :: "'r::pcpo set \<Rightarrow> ('r \<Rightarrow> bool) \<Rightarrow> 'r set" where
  "filtered S P = {x. \<exists>m \<in> pts S. P m \<and> x \<sqsubseteq> m}"

lemma adm_below_finite: "finite P \<Longrightarrow> adm (\<lambda>x. \<exists>m\<in>P. x \<sqsubseteq> m)"
  by (induct rule: finite_induct) simp_all

locale dataset =
  fixes S :: "'r::pcpo set"
  assumes downward: "y \<in> S \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> x \<in> S"
    and max_above: "x \<in> S \<Longrightarrow> \<exists>m\<in>pts S. x \<sqsubseteq> m"
    and finite_pts: "finite (pts S)"
begin

lemma S_eq: "S = {x. \<exists>m\<in>pts S. x \<sqsubseteq> m}"
  using max_above downward unfolding pts_def by blast

lemma closed: "adm (\<lambda>x. x \<in> S)"
  by (subst S_eq) (simp add: adm_below_finite finite_pts)

lemma filtered_subset: "filtered S P \<subseteq> S"
  unfolding filtered_def pts_def using downward by blast

lemma pts_filtered: "pts (filtered S P) = {m \<in> pts S. P m}"
  using filtered_subset unfolding filtered_def pts_def by (auto 6 3)

lemma dataset_filtered: "dataset (filtered S P)"
proof
  show "y \<in> filtered S P \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> x \<in> filtered S P" for x y
    unfolding filtered_def by (blast intro: below_trans)
  show "x \<in> filtered S P \<Longrightarrow> \<exists>m\<in>pts (filtered S P). x \<sqsubseteq> m" for x
    unfolding pts_filtered by (auto simp: filtered_def)
  show "finite (pts (filtered S P))"
    unfolding pts_filtered using finite_pts by simp
qed

lemma filtered_filtered: "filtered (filtered S P) Q = filtered S (\<lambda>x. P x \<and> Q x)"
  unfolding filtered_def[of "filtered S P"] pts_filtered
  by (auto simp: filtered_def)

lemma filtered_top: "filtered S (\<lambda>_. True) = S"
  by (subst (2) S_eq) (simp add: filtered_def)

end

section \<open>Slicers\<close>

subsection \<open>Selections\<close>

text \<open>What slices select: Scott-open predicates, i.e.\ upward closed with an admissible
  complement.  These correspond one-to-one to filters \<^typ>\<open>'r \<rightarrow> one\<close>, and form a distributive
  bounded lattice under the pointwise operations.\<close>

typedef 'r sel = "{P :: 'r::pcpo \<Rightarrow> bool. (\<forall>x y. P x \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> P y) \<and> adm (\<lambda>x. \<not> P x)}"
  morphisms selects Abs_sel
  by (rule exI[of _ "\<lambda>_. True"]) simp

setup_lifting type_definition_sel

lemma selects_up: "selects s x \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> selects s y"
  using selects[of s] by blast

lemma selects_open: "adm (\<lambda>x. \<not> selects s x)"
  using selects[of s] by blast

lemma sel_eqI: "(\<And>x. selects a x \<longleftrightarrow> selects b x) \<Longrightarrow> a = b"
  by (simp add: selects_inject[symmetric] fun_eq_iff)

lift_definition sel_of :: "('r::pcpo \<rightarrow> one) \<Rightarrow> 'r sel" is passes
  using passes_up passes_open by blast

instantiation sel :: (pcpo) "{distrib_lattice, bounded_lattice}"
begin

lift_definition less_eq_sel :: "'a sel \<Rightarrow> 'a sel \<Rightarrow> bool" is "(\<le>)" .
lift_definition less_sel :: "'a sel \<Rightarrow> 'a sel \<Rightarrow> bool" is "(<)" .
lift_definition inf_sel :: "'a sel \<Rightarrow> 'a sel \<Rightarrow> 'a sel" is inf
  by (auto intro!: adm_disj)
lift_definition sup_sel :: "'a sel \<Rightarrow> 'a sel \<Rightarrow> 'a sel" is sup
  by (auto intro!: adm_conj)
lift_definition bot_sel :: "'a sel" is bot by simp
lift_definition top_sel :: "'a sel" is top by simp

instance proof
  fix x y z :: "'a sel"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" by transfer (rule less_le_not_le)
  show "x \<le> x" by transfer (rule order_refl)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by transfer (erule (1) order_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by transfer (erule (1) antisym)
  show "inf x y \<le> x" by transfer (rule inf_le1)
  show "inf x y \<le> y" by transfer (rule inf_le2)
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> inf y z" by transfer (erule (1) le_infI)
  show "x \<le> sup x y" by transfer (rule sup_ge1)
  show "y \<le> sup x y" by transfer (rule sup_ge2)
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> sup y z \<le> x" by transfer (erule (1) le_supI)
  show "sup x (inf y z) = inf (sup x y) (sup x z)" by transfer (rule sup_inf_distrib1)
  show "bot \<le> x" by transfer (rule bot_least)
  show "x \<le> top" by transfer (rule top_greatest)
qed

end

lemma selects_inf [simp]: "selects (inf a b) x \<longleftrightarrow> selects a x \<and> selects b x"
  by (simp add: inf_sel.rep_eq)

lemma selects_top [simp]: "selects top x"
  by (simp add: top_sel.rep_eq)

subsection \<open>Semilattice homomorphisms\<close>

text \<open>Slices are an algebra given by laws (e.g.\ a quotient of syntax), not a type class:
  conjunction alone is assumed to form a semilattice with unit.  Their selections, their
  dimensions and their coarsening are all homomorphisms of such, into different targets.\<close>

locale semilattice_hom = src: semilattice_neutr f z + tgt: semilattice_neutr g w
  for f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and z :: 'a and g :: "'b \<Rightarrow> 'b \<Rightarrow> 'b" and w :: 'b +
  fixes h :: "'a \<Rightarrow> 'b"
  assumes hom_f: "h (f a b) = g (h a) (h b)"
    and hom_z: "h z = w"

subsection \<open>Slice evaluation\<close>

text \<open>Slices are given by their conjunction \<open>\<^bold>*\<close> and its unit \<open>\<^bold>1\<close>, nothing more: the slicer
  constructs only conjoin.  The order is the one conjunction induces.  Slices act on keys, which
  carry levels of detail (semi-factors of the keys, compact ones for LODs).  Each slice comes with the LOD it is written
  at, \<open>slod\<close>: what it \<^emph>\<open>looks at\<close>, not what it selects (an upper bound, not the least one).  Its
  meaning \<open>sopen\<close> is a Scott-open predicate on keys, and a meet-semilattice homomorphism.  A slice
  reads a key only through its truncation to the slice's LOD, so it applies to keys finer than its
  LOD as well.  \<open>holds\<close> is the plain predicate.\<close>

text \<open>The slicer interface is a record of operations.  Besides evaluation, a slicer
  \<^emph>\<open>coarsens\<close> slices to a given LOD and \<^emph>\<open>pins\<close> keys; their laws are explained below.\<close>

record ('f, 'k) slicer_ops =
  sl_conj :: "'f \<Rightarrow> 'f \<Rightarrow> 'f"
  sl_unit :: 'f
  sl_lod :: "'f \<Rightarrow> 'k semi_factor"
  sl_open :: "'f \<Rightarrow> 'k sel"
  sl_coarsen :: "'k semi_factor \<Rightarrow> 'f \<Rightarrow> 'f"
  sl_pin :: "'k \<Rightarrow> 'f"

hide_const (open) slicer_ops.truncate

locale slicer = conj: semilattice_neutr "sl_conj slicing" "sl_unit slicing" +
  slod: semilattice_hom "sl_conj slicing" "sl_unit slicing" "(\<squnion>)" \<bottom> "sl_lod slicing" +
  sopen: semilattice_hom "sl_conj slicing" "sl_unit slicing" inf top "sl_open slicing"
  for slicing :: "('f, 'k::{dI, locally_finitely_detailed}) slicer_ops" +
  assumes sopen_lod: "selects (sl_open slicing f) (proj (sl_lod slicing f)\<cdot>k) \<longleftrightarrow> selects (sl_open slicing f) k"
    and slod_compact: "compact (sl_lod slicing f)"
    and coarsen_conj: "sl_coarsen slicing A (sl_conj slicing a b) =
      sl_conj slicing (sl_coarsen slicing A a) (sl_coarsen slicing A b)"
    and coarsen_inside: "sl_lod slicing f \<sqsubseteq> A \<Longrightarrow> sl_coarsen slicing A f = f"
    and slod_coarsen: "sl_lod slicing (sl_coarsen slicing A f) \<sqsubseteq> sl_lod slicing f \<sqinter> A"
    and coarsen_cut: "selects (sl_open slicing f) k \<Longrightarrow>
      selects (sl_open slicing (sl_coarsen slicing A f)) (proj A\<cdot>k)"
    and coarsen_slod: "sl_coarsen slicing A f = sl_coarsen slicing (A \<sqinter> sl_lod slicing f) f"
    and coarsen_coarsen: "sl_coarsen slicing A (sl_coarsen slicing B f) = sl_coarsen slicing (A \<sqinter> B) f"
    and sopen_spin: "compact K \<Longrightarrow> selects (sl_open slicing (sl_pin slicing K)) k \<longleftrightarrow> K \<sqsubseteq> k"
    and coarsen_spin: "compact K \<Longrightarrow> sl_coarsen slicing A (sl_pin slicing K) = sl_pin slicing (proj A\<cdot>K)"
    and spin_join: "compact K1 \<Longrightarrow> compact K2 \<Longrightarrow> K1 \<Up> K2 \<Longrightarrow>
      sl_pin slicing (K1 \<squnion> K2) = sl_conj slicing (sl_pin slicing K1) (sl_pin slicing K2)"
begin

abbreviation conj :: "'f \<Rightarrow> 'f \<Rightarrow> 'f" (infixl \<open>\<^bold>*\<close> 70) where "conj \<equiv> sl_conj slicing"
abbreviation sunit :: 'f (\<open>\<^bold>1\<close>) where "sunit \<equiv> sl_unit slicing"
abbreviation slod :: "'f \<Rightarrow> 'k semi_factor" where "slod \<equiv> sl_lod slicing"
abbreviation sopen :: "'f \<Rightarrow> 'k sel" where "sopen \<equiv> sl_open slicing"
abbreviation coarsen :: "'k semi_factor \<Rightarrow> 'f \<Rightarrow> 'f" where "coarsen \<equiv> sl_coarsen slicing"
abbreviation spin :: "'k \<Rightarrow> 'f" where "spin \<equiv> sl_pin slicing"

lemmas slod_conj [simp] = slod.hom_f and slod_unit [simp] = slod.hom_z

definition sle :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix \<open>\<^bold>\<le>\<close> 50) where
  "a \<^bold>\<le> b \<longleftrightarrow> a = a \<^bold>* b"

definition slt :: "'f \<Rightarrow> 'f \<Rightarrow> bool" (infix \<open>\<^bold><\<close> 50) where
  "a \<^bold>< b \<longleftrightarrow> a \<^bold>\<le> b \<and> a \<noteq> b"

sublocale sord: semilattice_neutr_order conj sunit sle slt
  by unfold_locales (simp_all add: sle_def slt_def)

lemma sopen_mono: "a \<^bold>\<le> b \<Longrightarrow> sopen a \<le> sopen b"
  unfolding sle_def by (metis sopen.hom_f inf.orderI)

definition holds :: "'f \<Rightarrow> 'k \<Rightarrow> bool" where
  "holds f = selects (sopen f)"

lemma holds_conj [simp]: "holds (a \<^bold>* b) k \<longleftrightarrow> holds a k \<and> holds b k"
  by (simp add: holds_def sopen.hom_f)

lemma holds_unit [simp]: "holds \<^bold>1 k"
  by (simp add: holds_def sopen.hom_z)

lemma holds_up: "holds f k \<Longrightarrow> k \<sqsubseteq> k' \<Longrightarrow> holds f k'"
  unfolding holds_def by (rule selects_up)

lemma holds_open: "adm (\<lambda>k. \<not> holds f k)"
  unfolding holds_def by (rule selects_open)

lemma holds_mono: "a \<^bold>\<le> b \<Longrightarrow> holds a k \<Longrightarrow> holds b k"
  unfolding sle_def by (metis holds_conj)

lemma holds_lod: "holds f (proj (slod f)\<cdot>k) \<longleftrightarrow> holds f k"
  by (simp add: holds_def sopen_lod)

text \<open>Truncating to any LOD the slice is written within does not change whether it holds.\<close>

lemma holds_proj: "slod f \<sqsubseteq> c \<Longrightarrow> holds f (proj c\<cdot>k) \<longleftrightarrow> holds f k"
  by (metis holds_lod proj_le)

lemma holds_bot_lod:
  assumes "slod f = \<bottom>" shows "holds f k \<longleftrightarrow> holds f \<bottom>"
  using holds_lod[of f k] by (simp add: assms proj_bot)

subsection \<open>Coarsening\<close>

text \<open>A slicer adds \<^emph>\<open>coarsening\<close> of a slice to a given LOD.  \<open>GROUP BY ONLY\<close> coarsens to the new
  frame LOD; \<open>FOR\<close> coarsens to the slice's own LOD with dimensions dropped by a transformer.
  Coarsening distributes over conjunction, leaves slices written inside the target alone, keeps
  only what the target looks at, holds at the truncation of every key the original holds at, and
  coarsening twice is coarsening once, to the meet of the targets.
  It only depends on the part of the target the slice is written at: coarsening is about what is
  cut away.
  It is \<^emph>\<open>not\<close> extensional: coarsening \<open>b = 2 \<and> b \<noteq> 2\<close> away from \<open>b\<close> gives \<open>True\<close>, coarsening
  \<open>False\<close> gives \<open>False\<close>.\<close>


lemma holds_coarsen_cut: "holds f k \<Longrightarrow> holds (coarsen A f) (proj A\<cdot>k)"
  unfolding holds_def by (rule coarsen_cut)

lemma coarsen_unit [simp]: "coarsen A \<^bold>1 = \<^bold>1"
  by (rule coarsen_inside) simp

lemma coarsen_hom: "semilattice_hom conj sunit conj sunit (coarsen A)"
  by unfold_locales (fact coarsen_conj coarsen_unit)+

lemma coarsen_mono: "a \<^bold>\<le> b \<Longrightarrow> coarsen A a \<^bold>\<le> coarsen A b"
  unfolding sle_def by (metis coarsen_conj)

lemma slod_coarsen_target: "slod (coarsen A f) \<sqsubseteq> A"
  using slod_coarsen[of A f] by (rule below_trans[OF _ lattice_meet_le2])

lemma holds_coarsen: "holds f k \<Longrightarrow> holds (coarsen A f) k"
  using holds_coarsen_cut proj_below by (rule holds_up)

lemma holds_coarsen_reads: "holds (coarsen A f) (proj A\<cdot>k) \<longleftrightarrow> holds (coarsen A f) k"
  by (rule holds_proj[OF slod_coarsen_target])

text \<open>A slice written entirely outside the target coarsens to a constant, which is true as soon
  as the slice holds anywhere.  Syntactically this fails: \<open>False \<and> a = 1\<close> coarsens to \<open>False\<close>
  away from \<open>a\<close>.\<close>

lemma coarsen_outside:
  assumes "slod f \<sqinter> A = \<bottom>" and "holds f t"
  shows "holds (coarsen A f) k"
proof -
  have lod: "slod (coarsen A f) = \<bottom>"
    using slod_coarsen[of A f] assms(1) by simp
  have "holds (coarsen A f) (proj A\<cdot>t)" using assms(2) by (rule holds_coarsen_cut)
  then have "holds (coarsen A f) \<bottom>" using holds_bot_lod[OF lod, of "proj A\<cdot>t"] by blast
  then show ?thesis by (rule holds_up) simp
qed

text \<open>Coarsening to less is weaker.\<close>

lemma holds_coarsen_le:
  assumes "A \<sqsubseteq> B" and "holds (coarsen B f) k" shows "holds (coarsen A f) k"
proof -
  have "coarsen A f = coarsen A (coarsen B f)" by (simp add: coarsen_coarsen lattice_meet_absorb1[OF assms(1)])
  then show ?thesis using holds_coarsen[OF assms(2)] by simp
qed

lemma coarsen_top [simp]: "coarsen lattice_top f = f"
  by (rule coarsen_inside) simp

subsection \<open>Pins\<close>

text \<open>\<open>spin K\<close> is the slice pinning the key \<open>K\<close>: on keys, the principal upset of \<open>K\<close>.  It is only
  specified for compact keys, whose upsets are open.  The slicer picks the LOD a pin is written
  at; nothing is assumed about it, but it is always one the key lives at.  Pins coarsen by
  truncating the key, and compatible pins conjoin to the pin of the join.\<close>


lemma holds_spin: "compact K \<Longrightarrow> holds (spin K) k \<longleftrightarrow> K \<sqsubseteq> k"
  unfolding holds_def by (rule sopen_spin)

lemma slod_spin_lives:
  assumes "compact K" shows "proj (slod (spin K))\<cdot>K = K"
proof -
  have "holds (spin K) K" by (simp add: holds_spin[OF assms])
  then have "holds (spin K) (proj (slod (spin K))\<cdot>K)" by (simp only: holds_lod)
  then have "K \<sqsubseteq> proj (slod (spin K))\<cdot>K" by (simp only: holds_spin[OF assms])
  then show ?thesis using proj_below by (rule below_antisym[rotated])
qed

text \<open>A slice below a pin only holds above the pinned key.\<close>

lemma holds_pinned:
  assumes "compact K" and "f \<^bold>\<le> spin K" and "holds f k"
  shows "K \<sqsubseteq> k"
proof -
  have "holds (spin K) k" using assms(2,3) by (rule holds_mono)
  then show ?thesis by (simp only: holds_spin[OF assms(1)])
qed

end

subsection \<open>Rows versus keys\<close>

text \<open>A row predicate reading only what a projection \<open>p\<close> keeps of the key is the same thing as a
  key predicate: its up-image is open (when the projected keys are compact), and its preimage
  gives back the row predicate.
  Preimages of open key predicates are open for any \<open>p\<close>.\<close>

context dim_eval
begin

definition keyup :: "(('d, 'v) tuple \<rightarrow> ('d, 'v) tuple) \<Rightarrow> ('r \<Rightarrow> bool) \<Rightarrow> ('d, 'v) tuple \<Rightarrow> bool" where
  "keyup p V t \<longleftrightarrow> (\<exists>r. V r \<and> p\<cdot>(keyof\<cdot>r) \<sqsubseteq> t)"

definition rowpre :: "(('d, 'v) tuple \<rightarrow> ('d, 'v) tuple) \<Rightarrow> (('d, 'v) tuple \<Rightarrow> bool) \<Rightarrow> 'r \<Rightarrow> bool" where
  "rowpre p U r \<longleftrightarrow> U (p\<cdot>(keyof\<cdot>r))"

lemma keyup_up: "keyup p V t \<Longrightarrow> t \<sqsubseteq> t' \<Longrightarrow> keyup p V t'"
  unfolding keyup_def by (blast intro: below_trans)

lemma rowpre_keyup:
  assumes "\<And>x y. kern p x y \<Longrightarrow> V x \<Longrightarrow> V y"
  shows "rowpre p (keyup p V) = V"
  using assms unfolding fun_eq_iff rowpre_def keyup_def kern_def by blast

lemma rowpre_up: "(\<And>t t'. U t \<Longrightarrow> t \<sqsubseteq> t' \<Longrightarrow> U t') \<Longrightarrow> rowpre p U r \<Longrightarrow> r \<sqsubseteq> r' \<Longrightarrow> rowpre p U r'"
  unfolding rowpre_def by (blast intro: monofun_cfun_arg)

lemma rowpre_open: "adm (\<lambda>t. \<not> U t) \<Longrightarrow> adm (\<lambda>r. \<not> rowpre p U r)"
  unfolding rowpre_def using adm_subst[of "\<lambda>r. p\<cdot>(keyof\<cdot>r)" "\<lambda>t. \<not> U t"] by simp

lemma keyup_open:
  assumes "\<And>r. compact (p\<cdot>(keyof\<cdot>r))"
  shows "adm (\<lambda>t. \<not> keyup p V t)"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> ('d, 'v) tuple"
  assume Y: "chain Y" "\<forall>i. \<not> keyup p V (Y i)"
  show "\<not> keyup p V (\<Squnion>i. Y i)"
  proof
    assume "keyup p V (\<Squnion>i. Y i)"
    then obtain r where "V r" "p\<cdot>(keyof\<cdot>r) \<sqsubseteq> (\<Squnion>i. Y i)" by (auto simp: keyup_def)
    then obtain i where "p\<cdot>(keyof\<cdot>r) \<sqsubseteq> Y i" using Y(1) assms compact_below_lub_iff by blast
    with \<open>V r\<close> Y(2) show False by (auto simp: keyup_def)
  qed
qed

end

end
