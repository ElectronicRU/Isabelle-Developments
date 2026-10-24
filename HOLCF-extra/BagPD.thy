theory BagPD
  imports HOLCF "HOL-Library.Extended_Nat"
begin

section \<open>The bag powerdomain\<close>

text \<open>Finite bags of compact elements with multiplicities in @{typ enat}, where @{term "\<infinity>::enat"}
  stands for an open-ended (countable) number of copies. A bag @{text u} is above a bag @{text t}
  when every copy of @{text t} goes to exactly one copy of @{text u} above it and every copy of
  @{text u} is hit: copies may merge but never split. Formally the order is witnessed by an
  @{typ enat}-labelled plan between the supports (a transport plan with exact row sums and
  covered column sums, cf.\ Jones's splitting lemma with the column inequality reversed).
  The powerdomain is the ideal completion of this preorder, built like HOLCF's own
  powerdomains.\<close>

subsection \<open>Splitting plans\<close>

text \<open>The splitting lemmas are plain HOL, over arbitrary types.\<close>

default_sort type

text \<open>A plan from @{text a} on @{text A} to @{text b} on @{text B}: row sums exactly @{text a},
  column sums at least @{text b}, entries only towards nonzero demands.\<close>

definition split_plan ::
    "'i set \<Rightarrow> 'j set \<Rightarrow> ('i \<Rightarrow> 'v::ordered_comm_monoid_add) \<Rightarrow> ('j \<Rightarrow> 'v) \<Rightarrow> ('i \<Rightarrow> 'j \<Rightarrow> 'v) \<Rightarrow> bool"
  where "split_plan A B a b m \<longleftrightarrow>
    (\<forall>x\<in>A. sum (m x) B = a x) \<and> (\<forall>z\<in>B. b z \<le> (\<Sum>x\<in>A. m x z)) \<and>
    (\<forall>x z. m x z \<noteq> 0 \<longrightarrow> x \<in> A \<and> z \<in> B \<and> b z \<noteq> 0)"

lemma sum_nonzero_ex:
  fixes f :: "'i \<Rightarrow> 'v::comm_monoid_add"
  assumes "sum f A \<noteq> 0"
  shows "\<exists>x\<in>A. f x \<noteq> 0"
  using assms by (blast elim: sum.not_neutral_contains_not_neutral)

lemma enat_sum_infty:
  fixes f :: "'i \<Rightarrow> enat"
  shows "finite A \<Longrightarrow> x \<in> A \<Longrightarrow> f x = \<infinity> \<Longrightarrow> sum f A = \<infinity>"
  using member_le_sum[of x A f] by simp

lemma sum_enat_of_nat: "(\<Sum>i\<in>I. enat (f i)) = enat (sum f I)"
  by (induct I rule: infinite_finite_induct) (simp_all add: zero_enat_def)

lemma sum_update_add:
  fixes f :: "'i \<Rightarrow> 'v::comm_monoid_add"
  assumes "finite A" and "x \<in> A"
  shows "sum (f(x := f x + c)) A = sum f A + c"
  using sum.remove[OF assms, of "f(x := f x + c)"] sum.remove[OF assms, of f]
  by (simp add: add_ac)

text \<open>One more unit in row @{text x}, sent to column @{text w}.\<close>

lemma split_plan_bump:
  fixes a :: "'i \<Rightarrow> nat" and b :: "'j \<Rightarrow> nat"
  assumes plan: "split_plan A B a' b' m" and fin: "finite A" "finite B"
    and xw: "x \<in> A" "w \<in> B" "b w \<noteq> 0"
    and a: "a = a'(x := a' x + 1)"
    and bw: "b w \<le> b' w + 1" and bz: "\<And>z. z \<in> B \<Longrightarrow> z \<noteq> w \<Longrightarrow> b z \<le> b' z"
    and bnz: "\<And>z. b' z \<noteq> 0 \<Longrightarrow> b z \<noteq> 0"
  shows "split_plan A B a b (m(x := (m x)(w := m x w + 1)))"
proof -
  let ?m = "m(x := (m x)(w := m x w + 1))"
  have row: "sum (?m y) B = a y" if "y \<in> A" for y
    using plan that sum_update_add[OF fin(2) xw(2), of "m x" 1]
    by (cases "y = x") (simp_all add: split_plan_def a)
  have col: "b z \<le> (\<Sum>y\<in>A. ?m y z)" if "z \<in> B" for z
  proof -
    have "(\<lambda>y. ?m y z) = (\<lambda>y. m y z)(x := m x z + (if z = w then 1 else 0))"
      by auto
    then have "(\<Sum>y\<in>A. ?m y z) = (\<Sum>y\<in>A. m y z) + (if z = w then 1 else 0)"
      by (simp only: sum_update_add[OF fin(1) xw(1), of "\<lambda>y. m y z"])
    then show ?thesis
      using plan that bw bz[of z] unfolding split_plan_def by (cases "z = w") auto
  qed
  show ?thesis
    using row col plan xw bnz unfolding split_plan_def by auto
qed

lemma nat_split_plan:
  fixes a :: "'i \<Rightarrow> nat" and b :: "'j \<Rightarrow> nat"
  assumes fin: "finite A" "finite B"
    and le: "sum b B \<le> sum a A" and nz: "sum a A \<noteq> 0 \<Longrightarrow> \<exists>z\<in>B. b z \<noteq> 0"
  shows "\<exists>m. split_plan A B a b m"
  using le nz
proof (induct "sum a A" arbitrary: a b)
  case 0
  then show ?case
    using fin by (intro exI[of _ "\<lambda>_ _. 0"]) (simp add: split_plan_def)
next
  case (Suc n)
  text \<open>Take one unit off a nonempty row @{text x} and send it to a demanded column
    @{text w}; the demand at @{text w} drops by one when the total demand is tight.\<close>
  obtain x where x: "x \<in> A" "a x \<noteq> 0"
    using sum_nonzero_ex[of a A] Suc.hyps(2) by fastforce
  obtain w where w: "w \<in> B" "b w \<noteq> 0"
    using Suc.prems(2) Suc.hyps(2) by fastforce
  define a' where "a' = a(x := a x - 1)"
  define b' where "b' = (if sum b B \<le> n then b else b(w := b w - 1))"
  have a: "a = a'(x := a' x + 1)"
    using x(2) by (auto simp: a'_def)
  have "n = sum a' A"
    using sum_update_add[OF fin(1) x(1), of a' 1] Suc.hyps(2) a by simp
  moreover have "sum b' B \<le> n \<and> (n \<noteq> 0 \<longrightarrow> (\<exists>z\<in>B. b' z \<noteq> 0))"
  proof (cases "sum b B \<le> n")
    case True
    then show ?thesis
      using w by (auto simp: b'_def)
  next
    case False
    then have "b = b'(w := b' w + 1)"
      using w(2) by (auto simp: b'_def)
    then have "sum b' B = n"
      using sum_update_add[OF fin(2) w(1), of b' 1] False Suc.prems(1) Suc.hyps(2) by simp
    then show ?thesis
      using sum_nonzero_ex[of b' B] by auto
  qed
  ultimately obtain m where "split_plan A B a' b' m"
    using Suc.hyps(1) by blast
  then have "split_plan A B a b (m(x := (m x)(w := m x w + 1)))"
    by (rule split_plan_bump[where b = b, OF _ fin x(1) w a])
      (auto simp: b'_def split: if_split_asm)
  then show ?case
    by blast
qed

lemma enat_split_plan:
  fixes a :: "'i \<Rightarrow> enat" and b :: "'j \<Rightarrow> enat"
  assumes fin: "finite A" "finite B"
    and le: "sum b B \<le> sum a A" and nz: "sum a A \<noteq> 0 \<Longrightarrow> \<exists>z\<in>B. b z \<noteq> 0"
  shows "\<exists>m. split_plan A B a b m"
proof (cases "\<exists>x\<in>A. a x = \<infinity>")
  case True
  text \<open>An infinite row covers every demanded column; the finite rows all go to one of them.\<close>
  then obtain xi where xi: "xi \<in> A" "a xi = \<infinity>"
    by blast
  then obtain z0 where z0: "z0 \<in> B" "b z0 \<noteq> 0"
    using nz enat_sum_infty[OF fin(1)] by fastforce
  define m where "m x z = (if x \<in> A \<and> z \<in> B \<and> b z \<noteq> 0
    then (if a x = \<infinity> then \<infinity> else if z = z0 then a x else 0) else 0)" for x z
  have r: "sum (m x) B = a x" if "x \<in> A" for x
  proof (cases "a x = \<infinity>")
    case True
    then show ?thesis
      using that z0 by (simp add: enat_sum_infty[OF fin(2) z0(1)] m_def)
  next
    case False
    have "sum (m x) B = sum (\<lambda>z. if z = z0 then a x else 0) B"
      by (rule sum.cong) (auto simp: m_def that False z0)
    then show ?thesis
      using z0(1) fin(2) by simp
  qed
  have c: "b z \<le> (\<Sum>x\<in>A. m x z)" if "z \<in> B" for z
    using that xi by (cases "b z = 0") (simp_all add: enat_sum_infty[OF fin(1) xi(1)] m_def)
  have s: "m x z \<noteq> 0 \<longrightarrow> x \<in> A \<and> z \<in> B \<and> b z \<noteq> 0" for x z
    by (simp add: m_def)
  show ?thesis
    unfolding split_plan_def using r c s by blast
next
  case False
  text \<open>All rows are finite, hence so are all demands: reduce to @{typ nat}.\<close>
  define a' where "a' x = the_enat (a x)" for x
  define b' where "b' z = the_enat (b z)" for z
  have a: "a x = enat (a' x)" if "x \<in> A" for x
    using False that by (cases "a x") (auto simp: a'_def)
  then have sa: "sum a A = enat (sum a' A)"
    by (simp add: sum_enat_of_nat[symmetric])
  have b: "b z = enat (b' z)" if "z \<in> B" for z
  proof -
    have "b z \<le> sum b B"
      by (rule member_le_sum[OF that _ fin(2)]) simp
    then have "b z \<le> enat (sum a' A)"
      using le sa by simp
    then show ?thesis
      by (cases "b z") (auto simp: b'_def)
  qed
  then have sb: "sum b B = enat (sum b' B)"
    by (simp add: sum_enat_of_nat[symmetric])
  have "\<exists>m. split_plan A B a' b' m"
    by (rule nat_split_plan[OF fin]) (use le nz sa sb b in \<open>auto simp: zero_enat_def\<close>)
  then obtain m where m: "split_plan A B a' b' m"
    by blast
  have "split_plan A B a b (\<lambda>x z. enat (m x z))"
    using m a b by (auto simp: split_plan_def sum_enat_of_nat zero_enat_def)
  then show ?thesis
    by blast
qed

default_sort bifinite

subsection \<open>The basis\<close>

text \<open>A basis element is a nonempty finite-support multiplicity function on compact
  elements.\<close>

definition "bag_basis =
  {f :: 'a compact_basis \<Rightarrow> enat. finite {x. f x \<noteq> 0} \<and> {x. f x \<noteq> 0} \<noteq> {}}"

typedef 'a bag_basis = "bag_basis :: ('a compact_basis \<Rightarrow> enat) set"
  morphisms bmult Abs_bag_basis
  by (rule exI[of _ "\<lambda>x. if x = compact_bot then 1 else 0"]) (simp add: bag_basis_def)

definition bsupp :: "'a bag_basis \<Rightarrow> 'a compact_basis set"
  where "bsupp t = {x. bmult t x \<noteq> 0}"

lemma bsupp_iff: "x \<in> bsupp t \<longleftrightarrow> bmult t x \<noteq> 0"
  by (simp add: bsupp_def)

lemma finite_bsupp [simp]: "finite (bsupp t)"
  using bmult [of t] by (simp add: bag_basis_def bsupp_def)

lemma bsupp_nonempty [simp]: "bsupp t \<noteq> {}"
  using bmult [of t] by (simp add: bag_basis_def bsupp_def)

lemma Abs_bag_basis_inverse':
  "finite {x. f x \<noteq> 0} \<Longrightarrow> {x. f x \<noteq> 0} \<noteq> {} \<Longrightarrow> bmult (Abs_bag_basis f) = f"
  by (simp add: Abs_bag_basis_inverse bag_basis_def)

lemma bag_basis_eqI: "(\<And>x. bmult t x = bmult u x) \<Longrightarrow> t = u"
  by (simp add: bmult_inject [symmetric] fun_eq_iff)

text \<open>The basis is countable: encode the graph of the multiplicity function on its support.\<close>

lemma bag_basis_countable: "\<exists>f::'a bag_basis \<Rightarrow> nat. inj f"
proof -
  obtain g :: "'a compact_basis \<Rightarrow> nat" where g: "inj g"
    using compact_basis.countable ..
  define G where "G t = (\<lambda>x. to_nat (g x, bmult t x)) ` bsupp t" for t :: "'a bag_basis"
  have half: "bmult u x = bmult t x" if "G t = G u" and "x \<in> bsupp t" for t u x
  proof -
    have "to_nat (g x, bmult t x) \<in> G t"
      using that(2) unfolding G_def by (rule imageI)
    then have "to_nat (g x, bmult t x) \<in> G u"
      using that(1) by simp
    then obtain x' where "x' \<in> bsupp u" "g x' = g x" "bmult u x' = bmult t x"
      by (auto simp: G_def)
    then show ?thesis
      using g by (auto dest: injD)
  qed
  have "inj (\<lambda>t. set_encode (G t))"
  proof (rule injI)
    fix t u
    assume "set_encode (G t) = set_encode (G u)"
    then have "G t = G u"
      by (simp add: set_encode_eq G_def)
    then show "t = u"
      using half[of t u] half[of u t] by (intro bag_basis_eqI) (metis bsupp_iff)
  qed
  then show ?thesis
    by blast
qed

subsection \<open>Basis constructors\<close>

definition BUnit :: "'a compact_basis \<Rightarrow> 'a bag_basis"
  where "BUnit a = Abs_bag_basis (\<lambda>x. if x = a then 1 else 0)"

definition BPlus :: "'a bag_basis \<Rightarrow> 'a bag_basis \<Rightarrow> 'a bag_basis"
  where "BPlus t u = Abs_bag_basis (\<lambda>x. bmult t x + bmult u x)"

definition BOmega :: "'a bag_basis \<Rightarrow> 'a bag_basis"
  where "BOmega t = Abs_bag_basis (\<lambda>x. if bmult t x = 0 then 0 else \<infinity>)"

lemma bmult_BUnit: "bmult (BUnit a) x = (if x = a then 1 else 0)"
  unfolding BUnit_def by (subst Abs_bag_basis_inverse') simp_all

lemma bmult_BPlus [simp]: "bmult (BPlus t u) x = bmult t x + bmult u x"
proof -
  have "{x. bmult t x + bmult u x \<noteq> 0} = bsupp t \<union> bsupp u"
    by (auto simp: bsupp_def)
  then show ?thesis
    unfolding BPlus_def by (subst Abs_bag_basis_inverse') simp_all
qed

lemma bmult_BOmega: "bmult (BOmega t) x = (if bmult t x = 0 then 0 else \<infinity>)"
proof -
  have "{x. (if bmult t x = 0 then 0 else \<infinity>) \<noteq> (0::enat)} = bsupp t"
    by (auto simp: bsupp_def)
  then show ?thesis
    unfolding BOmega_def by (subst Abs_bag_basis_inverse') simp_all
qed

lemma bsupp_BUnit [simp]: "bsupp (BUnit a) = {a}"
  by (auto simp: bsupp_def bmult_BUnit)

lemma bsupp_BPlus [simp]: "bsupp (BPlus t u) = bsupp t \<union> bsupp u"
  by (auto simp: bsupp_def)

lemma bsupp_BOmega [simp]: "bsupp (BOmega t) = bsupp t"
  by (auto simp: bsupp_def bmult_BOmega)

lemma BPlus_assoc: "BPlus (BPlus t u) v = BPlus t (BPlus u v)"
  by (rule bag_basis_eqI) (simp add: add.assoc)

lemma BPlus_commute: "BPlus t u = BPlus u t"
  by (rule bag_basis_eqI) (simp add: add.commute)

lemma BOmega_BOmega: "BOmega (BOmega t) = BOmega t"
  by (rule bag_basis_eqI) (simp add: bmult_BOmega)

lemma BOmega_BPlus: "BOmega (BPlus t u) = BPlus (BOmega t) (BOmega u)"
  by (rule bag_basis_eqI) (simp add: bmult_BOmega)

lemma BPlus_BOmega_absorb: "BPlus (BOmega t) t = BOmega t"
  by (rule bag_basis_eqI) (simp add: bmult_BOmega)

lemma BPlus_BOmega_idem: "BPlus (BOmega t) (BOmega t) = BOmega t"
  by (rule bag_basis_eqI) (simp add: bmult_BOmega)

subsection \<open>Basis preorder\<close>

text \<open>A plan from @{text t} to @{text u}: a splitting plan between the supports whose entries
  only connect comparable elements.\<close>

definition bag_plan ::
    "'a bag_basis \<Rightarrow> 'a bag_basis \<Rightarrow> ('a compact_basis \<Rightarrow> 'a compact_basis \<Rightarrow> enat) \<Rightarrow> bool"
  where "bag_plan t u a \<longleftrightarrow>
    (\<forall>x y. a x y \<noteq> 0 \<longrightarrow> x \<sqsubseteq> y) \<and> split_plan (bsupp t) (bsupp u) (bmult t) (bmult u) a"

definition bag_le :: "'a bag_basis \<Rightarrow> 'a bag_basis \<Rightarrow> bool" (infix \<open>\<le>\<^sub>b\<close> 50)
  where "t \<le>\<^sub>b u \<longleftrightarrow> (\<exists>a. bag_plan t u a)"

lemma bag_planI:
  assumes "\<And>x y. a x y \<noteq> 0 \<Longrightarrow> x \<sqsubseteq> y \<and> x \<in> bsupp t \<and> y \<in> bsupp u"
    and "\<And>x. x \<in> bsupp t \<Longrightarrow> sum (a x) (bsupp u) = bmult t x"
    and "\<And>y. y \<in> bsupp u \<Longrightarrow> bmult u y \<le> (\<Sum>x\<in>bsupp t. a x y)"
  shows "bag_plan t u a"
  using assms by (auto simp: bag_plan_def split_plan_def bsupp_iff)

lemmas bag_leI = bag_planI [THEN bag_le_def [THEN iffD2, OF exI]]

lemma bag_planD:
  assumes "bag_plan t u a"
  shows bag_plan_below: "a x y \<noteq> 0 \<Longrightarrow> x \<sqsubseteq> y"
    and bag_plan_supp: "a x y \<noteq> 0 \<Longrightarrow> x \<in> bsupp t \<and> y \<in> bsupp u"
    and bag_plan_row: "sum (a x) (bsupp u) = bmult t x"
    and bag_plan_col: "bmult u y \<le> (\<Sum>x\<in>bsupp t. a x y)"
proof -
  from assms show "a x y \<noteq> 0 \<Longrightarrow> x \<sqsubseteq> y" "a x y \<noteq> 0 \<Longrightarrow> x \<in> bsupp t \<and> y \<in> bsupp u"
    by (auto simp: bag_plan_def split_plan_def)
  from assms show "sum (a x) (bsupp u) = bmult t x"
    by (cases "x \<in> bsupp t")
      (auto simp: bag_plan_def split_plan_def bsupp_iff intro: sum.neutral)
  from assms show "bmult u y \<le> (\<Sum>x\<in>bsupp t. a x y)"
    by (cases "y \<in> bsupp u") (auto simp: bag_plan_def split_plan_def bsupp_iff)
qed

text \<open>Row and column sums may be taken over any finite superset of the supports.\<close>

lemma bag_plan_row_on:
  assumes "bag_plan t u a" and "finite Y" and "bsupp u \<subseteq> Y"
  shows "sum (a x) Y = bmult t x"
proof -
  have "sum (a x) Y = sum (a x) (bsupp u)"
    using assms bag_plan_supp[OF assms(1)] by (intro sum.mono_neutral_right) auto
  then show ?thesis
    using bag_plan_row[OF assms(1)] by simp
qed

lemma bag_plan_col_on:
  assumes "bag_plan t u a" and "finite X" and "bsupp t \<subseteq> X"
  shows "bmult u y \<le> (\<Sum>x\<in>X. a x y)"
proof -
  have "(\<Sum>x\<in>X. a x y) = (\<Sum>x\<in>bsupp t. a x y)"
    using assms bag_plan_supp[OF assms(1)] by (intro sum.mono_neutral_right) auto
  then show ?thesis
    using bag_plan_col[OF assms(1)] by simp
qed

text \<open>Every element of either support takes part in the plan.\<close>

lemma bag_plan_row_ex:
  assumes "bag_plan t u a" and "x \<in> bsupp t"
  obtains y where "y \<in> bsupp u" and "a x y \<noteq> 0"
  using sum_nonzero_ex[of "a x" "bsupp u"] bag_plan_row[OF assms(1), of x] assms(2)
  by (auto simp: bsupp_iff)

lemma bag_plan_col_ex:
  assumes "bag_plan t u a" and "y \<in> bsupp u"
  obtains x where "x \<in> bsupp t" and "a x y \<noteq> 0"
proof -
  have "(\<Sum>x\<in>bsupp t. a x y) \<noteq> 0"
    using bag_plan_col[OF assms(1), of y] assms(2) by (metis bsupp_iff le_zero_eq)
  then show ?thesis
    using sum_nonzero_ex that by blast
qed

lemma bag_le_refl [simp]: "t \<le>\<^sub>b t"
  by (rule bag_leI[where a = "\<lambda>x y. if x = y then bmult t x else 0"])
    (auto simp: bsupp_iff split: if_split_asm)

text \<open>Transitivity: split the copies flowing through each middle element @{text y} along its
  outgoing row, and add up the pieces.\<close>

lemma bag_le_trans:
  assumes "t \<le>\<^sub>b u" and "u \<le>\<^sub>b v"
  shows "t \<le>\<^sub>b v"
proof -
  from assms obtain a b where a: "bag_plan t u a" and b: "bag_plan u v b"
    unfolding bag_le_def by blast
  have "\<exists>m. split_plan (bsupp t) (bsupp v) (\<lambda>x. a x y) (b y) m" if "y \<in> bsupp u" for y
  proof (rule enat_split_plan)
    show "sum (b y) (bsupp v) \<le> (\<Sum>x\<in>bsupp t. a x y)"
      using bag_plan_row[OF b] bag_plan_col[OF a] by simp
    show "\<exists>z\<in>bsupp v. b y z \<noteq> 0"
      using bag_plan_row_ex[OF b that] by blast
  qed simp_all
  then obtain M where "\<And>y. y \<in> bsupp u \<Longrightarrow> split_plan (bsupp t) (bsupp v) (\<lambda>x. a x y) (b y) (M y)"
    by metis
  then have Mrow: "\<And>x y. y \<in> bsupp u \<Longrightarrow> x \<in> bsupp t \<Longrightarrow> sum (M y x) (bsupp v) = a x y"
    and Mcol: "\<And>y z. y \<in> bsupp u \<Longrightarrow> z \<in> bsupp v \<Longrightarrow> b y z \<le> (\<Sum>x\<in>bsupp t. M y x z)"
    and Msupp: "\<And>x y z. y \<in> bsupp u \<Longrightarrow> M y x z \<noteq> 0 \<Longrightarrow> x \<in> bsupp t \<and> z \<in> bsupp v \<and> b y z \<noteq> 0"
    unfolding split_plan_def by blast+
  define c where "c x z = (\<Sum>y\<in>bsupp u. M y x z)" for x z
  show ?thesis
  proof (rule bag_leI[of c])
    fix x z
    assume "c x z \<noteq> 0"
    then obtain y where y: "y \<in> bsupp u" "M y x z \<noteq> 0"
      using sum_nonzero_ex unfolding c_def by blast
    then have xz: "x \<in> bsupp t" "z \<in> bsupp v" "b y z \<noteq> 0"
      using Msupp by blast+
    have "a x y \<noteq> 0"
      using Mrow[OF y(1) xz(1)] y(2) xz(2) by auto
    then have "x \<sqsubseteq> y"
      by (rule bag_plan_below[OF a])
    also have "y \<sqsubseteq> z"
      using xz(3) by (rule bag_plan_below[OF b])
    finally show "x \<sqsubseteq> z \<and> x \<in> bsupp t \<and> z \<in> bsupp v"
      using xz by blast
  next
    fix x
    assume x: "x \<in> bsupp t"
    have "sum (c x) (bsupp v) = (\<Sum>y\<in>bsupp u. sum (M y x) (bsupp v))"
      unfolding c_def by (rule sum.swap)
    also have "\<dots> = bmult t x"
      using Mrow x bag_plan_row[OF a] by simp
    finally show "sum (c x) (bsupp v) = bmult t x" .
  next
    fix z
    assume z: "z \<in> bsupp v"
    have "bmult v z \<le> (\<Sum>y\<in>bsupp u. b y z)"
      by (rule bag_plan_col[OF b])
    also have "\<dots> \<le> (\<Sum>y\<in>bsupp u. \<Sum>x\<in>bsupp t. M y x z)"
      using Mcol z by (intro sum_mono) simp
    also have "\<dots> = (\<Sum>x\<in>bsupp t. c x z)"
      unfolding c_def by (rule sum.swap)
    finally show "bmult v z \<le> (\<Sum>x\<in>bsupp t. c x z)" .
  qed
qed

interpretation bag_le: preorder bag_le
  by (rule preorder.intro, rule bag_le_refl, rule bag_le_trans)

subsection \<open>Basic plans\<close>

text \<open>Below a bag, the supports are related in the Egli-Milner order.\<close>

lemma bag_le_supp:
  assumes "t \<le>\<^sub>b u"
  shows bag_le_lower: "x \<in> bsupp t \<Longrightarrow> \<exists>y\<in>bsupp u. x \<sqsubseteq> y"
    and bag_le_upper: "y \<in> bsupp u \<Longrightarrow> \<exists>x\<in>bsupp t. x \<sqsubseteq> y"
proof -
  obtain a where a: "bag_plan t u a"
    using assms unfolding bag_le_def by blast
  show "x \<in> bsupp t \<Longrightarrow> \<exists>y\<in>bsupp u. x \<sqsubseteq> y"
    by (metis a bag_plan_row_ex bag_plan_below)
  show "y \<in> bsupp u \<Longrightarrow> \<exists>x\<in>bsupp t. x \<sqsubseteq> y"
    by (metis a bag_plan_col_ex bag_plan_below)
qed

text \<open>Conversely, a bag with only infinite multiplicities is below every bag whose support is
  Egli-Milner above its own: all entries of the plan can be infinite.\<close>

lemma bag_le_omegaI:
  assumes inf: "\<And>x. x \<in> bsupp t \<Longrightarrow> bmult t x = \<infinity>"
    and lower: "\<And>x. x \<in> bsupp t \<Longrightarrow> \<exists>y\<in>bsupp u. x \<sqsubseteq> y"
    and upper: "\<And>y. y \<in> bsupp u \<Longrightarrow> \<exists>x\<in>bsupp t. x \<sqsubseteq> y"
  shows "t \<le>\<^sub>b u"
proof -
  define p where "p x y = (if x \<in> bsupp t \<and> y \<in> bsupp u \<and> x \<sqsubseteq> y then \<infinity> else 0 :: enat)"
    for x y
  show ?thesis
  proof (rule bag_leI[of p])
    fix x
    assume x: "x \<in> bsupp t"
    then obtain y where "y \<in> bsupp u" "x \<sqsubseteq> y"
      using lower by blast
    then show "sum (p x) (bsupp u) = bmult t x"
      using x inf by (simp add: enat_sum_infty[where x = y] p_def)
  next
    fix y
    assume y: "y \<in> bsupp u"
    then obtain x where "x \<in> bsupp t" "x \<sqsubseteq> y"
      using upper by blast
    then show "bmult u y \<le> (\<Sum>x\<in>bsupp t. p x y)"
      using y by (simp add: enat_sum_infty[where x = x] p_def)
  qed (simp add: p_def split: if_split_asm)
qed

lemma bag_le_minimal [simp]: "BOmega (BUnit compact_bot) \<le>\<^sub>b t"
  by (rule bag_le_omegaI) (auto simp: bmult_BOmega bmult_BUnit ex_in_conv)

lemma BUnit_mono: "a \<sqsubseteq> b \<Longrightarrow> BUnit a \<le>\<^sub>b BUnit b"
  by (rule bag_leI[where a = "\<lambda>x y. if x = a \<and> y = b then 1 else 0"])
    (simp_all add: bmult_BUnit split: if_split_asm)

lemma BUnit_le_iff [simp]: "BUnit a \<le>\<^sub>b BUnit b \<longleftrightarrow> a \<sqsubseteq> b"
  using bag_le_upper[of "BUnit a" "BUnit b" b] BUnit_mono by auto

lemma BPlus_mono:
  assumes "s \<le>\<^sub>b t" and "u \<le>\<^sub>b v"
  shows "BPlus s u \<le>\<^sub>b BPlus t v"
proof -
  from assms obtain a b where a: "bag_plan s t a" and b: "bag_plan u v b"
    unfolding bag_le_def by blast
  show ?thesis
  proof (rule bag_leI[where a = "\<lambda>x y. a x y + b x y"])
    fix x y
    assume "a x y + b x y \<noteq> 0"
    then show "x \<sqsubseteq> y \<and> x \<in> bsupp (BPlus s u) \<and> y \<in> bsupp (BPlus t v)"
      using bag_planD(1,2)[OF a] bag_planD(1,2)[OF b] by auto
  next
    fix x
    show "sum (\<lambda>y. a x y + b x y) (bsupp (BPlus t v)) = bmult (BPlus s u) x"
      using bag_plan_row_on[OF a] bag_plan_row_on[OF b] by (simp add: sum.distrib)
  next
    fix y
    show "bmult (BPlus t v) y \<le> (\<Sum>x\<in>bsupp (BPlus s u). a x y + b x y)"
      using bag_plan_col_on[OF a] bag_plan_col_on[OF b] by (simp add: sum.distrib add_mono)
  qed
qed

lemma BOmega_mono: "t \<le>\<^sub>b u \<Longrightarrow> BOmega t \<le>\<^sub>b BOmega u"
  by (rule bag_le_omegaI) (auto simp: bmult_BOmega bsupp_iff dest: bag_le_supp)

lemma BPlus_contract: "BPlus t t \<le>\<^sub>b t"
  by (rule bag_leI[where a = "\<lambda>x y. if x = y then bmult t x + bmult t x else 0"])
    (auto simp: bsupp_iff split: if_split_asm)

lemma BOmega_le: "BOmega t \<le>\<^sub>b t"
  by (rule bag_le_omegaI) (auto simp: bmult_BOmega bsupp_iff)

subsection \<open>Labelled families\<close>

text \<open>A finite family of compact elements with multiplicities, collapsed to a bag. A plan
  between the index sets pushes forward to a plan between the bags, so operations that emit
  one element per index (maps, joins) can be shown monotone on indices.\<close>

definition BFamily ::
    "'i::type set \<Rightarrow> ('i \<Rightarrow> 'a compact_basis) \<Rightarrow> ('i \<Rightarrow> enat) \<Rightarrow> 'a bag_basis"
  where "BFamily I f m = Abs_bag_basis (\<lambda>x. \<Sum>i\<in>{i\<in>I. f i = x}. m i)"

lemma bmult_BFamily:
  assumes "finite I" and "\<exists>i\<in>I. m i \<noteq> 0"
  shows "bmult (BFamily I f m) x = (\<Sum>i\<in>{i\<in>I. f i = x}. m i)"
proof -
  have "{x. (\<Sum>i\<in>{i\<in>I. f i = x}. m i) \<noteq> 0} = f ` {i\<in>I. m i \<noteq> 0}"
    using assms(1) by auto
  then show ?thesis
    unfolding BFamily_def using assms by (subst Abs_bag_basis_inverse') auto
qed

lemma bsupp_BFamily:
  assumes "finite I" and "\<exists>i\<in>I. m i \<noteq> 0"
  shows "bsupp (BFamily I f m) = f ` {i\<in>I. m i \<noteq> 0}"
  unfolding bsupp_def bmult_BFamily[OF assms] using assms(1) by auto

text \<open>Indices of multiplicity zero, and the naming of indices, do not matter.\<close>

lemma BFamily_nonzero: "finite I \<Longrightarrow> BFamily {i\<in>I. m i \<noteq> 0} f m = BFamily I f m"
  unfolding BFamily_def by (rule arg_cong[where f = Abs_bag_basis], rule ext, rule sum.mono_neutral_left) auto

lemma BFamily_reindex:
  assumes "bij_betw h I J"
  shows "BFamily I (\<lambda>i. f (h i)) (\<lambda>i. m (h i)) = BFamily J f m"
proof -
  have "bij_betw h {i\<in>I. f (h i) = x} {j\<in>J. f j = x}" for x
    using assms unfolding bij_betw_def inj_on_def by auto
  then have "(\<Sum>i\<in>{i\<in>I. f (h i) = x}. m (h i)) = (\<Sum>j\<in>{j\<in>J. f j = x}. m j)" for x
    by (rule sum.reindex_bij_betw)
  then show ?thesis
    unfolding BFamily_def by simp
qed

text \<open>Pushing an exact plan between index sets of nonzero multiplicity forward along the labels.\<close>

lemma BFamily_le_exact:
  fixes f :: "'i::type \<Rightarrow> 'a compact_basis" and g :: "'j::type \<Rightarrow> 'a compact_basis"
  assumes fin: "finite I" "finite J" and ne: "I \<noteq> {}"
    and nzI: "\<And>i. i \<in> I \<Longrightarrow> m i \<noteq> 0" and nzJ: "\<And>j. j \<in> J \<Longrightarrow> n j \<noteq> 0"
    and below: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> J \<Longrightarrow> q i j \<noteq> 0 \<Longrightarrow> f i \<sqsubseteq> g j"
    and row: "\<And>i. i \<in> I \<Longrightarrow> sum (q i) J = m i"
    and col: "\<And>j. j \<in> J \<Longrightarrow> n j \<le> (\<Sum>i\<in>I. q i j)"
  shows "BFamily I f m \<le>\<^sub>b BFamily J g n"
proof -
  have neI: "\<exists>i\<in>I. m i \<noteq> 0"
    using ne nzI by blast
  have neJ: "\<exists>j\<in>J. n j \<noteq> 0"
    by (metis nzJ row neI sum_nonzero_ex)
  define a where "a x y = (\<Sum>i\<in>{i\<in>I. f i = x}. \<Sum>j\<in>{j\<in>J. g j = y}. q i j)" for x y
  have sI: "bsupp (BFamily I f m) = f ` I"
    using bsupp_BFamily[OF fin(1) neI] nzI by auto
  have sJ: "bsupp (BFamily J g n) = g ` J"
    using bsupp_BFamily[OF fin(2) neJ] nzJ by auto
  show ?thesis
  proof (rule bag_leI[of a])
    fix x y
    assume "a x y \<noteq> 0"
    then obtain i j where "i \<in> I" "f i = x" "j \<in> J" "g j = y" "q i j \<noteq> 0"
      unfolding a_def by (blast dest: sum_nonzero_ex)
    then show "x \<sqsubseteq> y \<and> x \<in> bsupp (BFamily I f m) \<and> y \<in> bsupp (BFamily J g n)"
      using below sI sJ by blast
  next
    fix x
    have "sum (a x) (g ` J) = (\<Sum>i\<in>{i\<in>I. f i = x}. \<Sum>y\<in>g ` J. \<Sum>j\<in>{j\<in>J. g j = y}. q i j)"
      unfolding a_def by (rule sum.swap)
    also have "\<dots> = (\<Sum>i\<in>{i\<in>I. f i = x}. sum (q i) J)"
      using fin by (simp add: sum.group)
    also have "\<dots> = bmult (BFamily I f m) x"
      using row fin neI by (simp add: bmult_BFamily)
    finally show "sum (a x) (bsupp (BFamily J g n)) = bmult (BFamily I f m) x"
      by (simp add: sJ)
  next
    fix y
    have "bmult (BFamily J g n) y \<le> (\<Sum>j\<in>{j\<in>J. g j = y}. \<Sum>i\<in>I. q i j)"
      unfolding bmult_BFamily[OF fin(2) neJ] using col by (intro sum_mono) blast
    also have "\<dots> = (\<Sum>i\<in>I. \<Sum>j\<in>{j\<in>J. g j = y}. q i j)"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>x\<in>f ` I. a x y)"
      unfolding a_def using fin by (simp add: sum.group)
    finally show "bmult (BFamily J g n) y \<le> (\<Sum>x\<in>bsupp (BFamily I f m). a x y)"
      by (simp add: sI)
  qed
qed

lemma enat_add_diff_le: "a \<le> b \<Longrightarrow> a + (b - a) = (b::enat)"
  by (cases a; cases b) simp_all

text \<open>The general form: the plan may send less than a source holds, provided every source has
  somewhere to go (the Hoare half), and may touch indices of multiplicity zero.\<close>

lemma BFamily_le:
  fixes f :: "'i::type \<Rightarrow> 'a compact_basis" and g :: "'j::type \<Rightarrow> 'a compact_basis"
  assumes fin: "finite I" "finite J" and ne: "\<exists>i\<in>I. m i \<noteq> 0"
    and below: "\<And>i j. i \<in> I \<Longrightarrow> j \<in> J \<Longrightarrow> p i j \<noteq> 0 \<Longrightarrow> f i \<sqsubseteq> g j"
    and row: "\<And>i. i \<in> I \<Longrightarrow> sum (p i) J \<le> m i"
    and col: "\<And>j. j \<in> J \<Longrightarrow> n j \<le> (\<Sum>i\<in>I. p i j)"
    and lower: "\<And>i. i \<in> I \<Longrightarrow> m i \<noteq> 0 \<Longrightarrow> \<exists>j\<in>J. n j \<noteq> 0 \<and> f i \<sqsubseteq> g j"
  shows "BFamily I f m \<le>\<^sub>b BFamily J g n"
proof -
  define I' where "I' = {i\<in>I. m i \<noteq> 0}"
  define J' where "J' = {j\<in>J. n j \<noteq> 0}"
  obtain s where s: "\<And>i. i \<in> I' \<Longrightarrow> s i \<in> J' \<and> f i \<sqsubseteq> g (s i)"
    using lower unfolding I'_def J'_def by (metis (mono_tags, lifting) mem_Collect_eq)
  define q where "q i j = p i j + (if j = s i then m i - sum (p i) J' else 0)" for i j
  have fin': "finite I'" "finite J'"
    using fin by (simp_all add: I'_def J'_def)
  have pJ': "sum (p i) J' \<le> m i" if "i \<in> I" for i
    using row[OF that] sum_mono2[OF fin(2), of J' "p i"] by (auto simp: J'_def)
  have p0: "p i j = 0" if "i \<in> I" "j \<in> J" "m i = 0" for i j
    using row[OF that(1)] member_le_sum[OF that(2), of "p i"] fin(2) that(3) by simp
  have "BFamily I' f m \<le>\<^sub>b BFamily J' g n"
  proof (rule BFamily_le_exact[where q = q])
    fix i
    assume i: "i \<in> I'"
    have "sum (q i) J' = sum (p i) J' + (m i - sum (p i) J')"
      using s[OF i] fin' by (simp add: q_def sum.distrib)
    also have "\<dots> = m i"
      using pJ' i by (simp add: I'_def enat_add_diff_le)
    finally show "sum (q i) J' = m i" .
  next
    fix i j
    assume "i \<in> I'" "j \<in> J'" "q i j \<noteq> 0"
    then show "f i \<sqsubseteq> g j"
      using below s by (auto simp: q_def I'_def J'_def split: if_split_asm)
  next
    fix j
    assume j: "j \<in> J'"
    have "n j \<le> (\<Sum>i\<in>I. p i j)"
      using col j by (simp add: J'_def)
    also have "\<dots> = (\<Sum>i\<in>I'. p i j)"
      using fin j p0 by (intro sum.mono_neutral_right) (auto simp: I'_def J'_def)
    also have "\<dots> \<le> (\<Sum>i\<in>I'. q i j)"
      by (intro sum_mono) (simp add: q_def)
    finally show "n j \<le> (\<Sum>i\<in>I'. q i j)" .
  qed (use fin' ne in \<open>auto simp: I'_def J'_def\<close>)
  then show ?thesis
    using fin by (simp add: I'_def J'_def BFamily_nonzero)
qed

text \<open>The mass of a bag on a predicate. Refinement moves mass upwards, so the mass on an upward
  region can only shrink, measured against the mass on any region that contains everything
  below it.\<close>

definition bag_mass :: "'a bag_basis \<Rightarrow> ('a compact_basis \<Rightarrow> bool) \<Rightarrow> enat"
  where "bag_mass t P = (\<Sum>x\<in>{x\<in>bsupp t. P x}. bmult t x)"

lemma bag_mass_nonzero_iff: "bag_mass t P \<noteq> 0 \<longleftrightarrow> (\<exists>x\<in>bsupp t. P x)"
proof -
  have "bag_mass t P = 0 \<longleftrightarrow> (\<forall>x\<in>{x\<in>bsupp t. P x}. bmult t x = 0)"
    unfolding bag_mass_def by (rule sum_eq_0_iff) simp
  then show ?thesis
    by (auto simp: bsupp_iff)
qed

lemma bag_mass_BUnit: "bag_mass (BUnit a) P = (if P a then 1 else 0)"
proof -
  have "{x\<in>bsupp (BUnit a). P x} = (if P a then {a} else {})"
    by auto
  then show ?thesis
    by (simp add: bag_mass_def bmult_BUnit)
qed

lemma bmult_BFamily_sum:
  "finite I \<Longrightarrow> \<exists>i\<in>I. m i \<noteq> 0 \<Longrightarrow> bmult (BFamily I f m) x = (\<Sum>i\<in>I. if f i = x then m i else 0)"
  by (simp add: bmult_BFamily sum.inter_filter)

lemma bag_mass_cong: "(\<And>x. x \<in> bsupp t \<Longrightarrow> P x = Q x) \<Longrightarrow> bag_mass t P = bag_mass t Q"
  unfolding bag_mass_def by (rule sum.cong) auto

lemma bag_mass_disj:
  "(\<And>x. P x \<Longrightarrow> Q x \<Longrightarrow> False) \<Longrightarrow> bag_mass t (\<lambda>x. P x \<or> Q x) = bag_mass t P + bag_mass t Q"
  unfolding bag_mass_def by (subst sum.union_disjoint[symmetric]) (auto intro: sum.cong)

lemma bag_le_mass:
  assumes "t \<le>\<^sub>b t'" and down: "\<And>x x'. x \<sqsubseteq> x' \<Longrightarrow> Q' x' \<Longrightarrow> Q x"
  shows "bag_mass t' Q' \<le> bag_mass t Q"
proof -
  obtain a where a: "bag_plan t t' a"
    using assms(1) unfolding bag_le_def by blast
  let ?S' = "{x'\<in>bsupp t'. Q' x'}"
  have "bag_mass t' Q' \<le> (\<Sum>x'\<in>?S'. \<Sum>x\<in>bsupp t. a x x')"
    unfolding bag_mass_def by (intro sum_mono bag_plan_col[OF a])
  also have "\<dots> = (\<Sum>x\<in>bsupp t. \<Sum>x'\<in>?S'. a x x')"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>x\<in>{x\<in>bsupp t. Q x}. \<Sum>x'\<in>?S'. a x x')"
    by (rule sum.mono_neutral_right) (auto intro!: sum.neutral dest: bag_plan_below[OF a] down)
  also have "\<dots> \<le> (\<Sum>x\<in>{x\<in>bsupp t. Q x}. \<Sum>x'\<in>bsupp t'. a x x')"
    by (intro sum_mono sum_mono2) auto
  also have "\<dots> = bag_mass t Q"
    unfolding bag_mass_def using bag_plan_row[OF a] by simp
  finally show ?thesis .
qed

text \<open>A plain congruence for families.\<close>

lemma BFamily_cong:
  "(\<And>i. i \<in> I \<Longrightarrow> f i = f' i) \<Longrightarrow> (\<And>i. i \<in> I \<Longrightarrow> m i = m' i) \<Longrightarrow> BFamily I f m = BFamily I f' m'"
  unfolding BFamily_def by (rule arg_cong[where f = Abs_bag_basis], rule ext, rule sum.cong) auto

subsection \<open>Type definition\<close>

typedef 'a bag_pd = "{S::'a bag_basis set. bag_le.ideal S}"
  by (rule bag_le.ex_ideal)

instantiation bag_pd :: (bifinite) below
begin

definition
  "x \<sqsubseteq> y \<longleftrightarrow> Rep_bag_pd x \<subseteq> Rep_bag_pd y"

instance ..
end

instance bag_pd :: (bifinite) po
  using type_definition_bag_pd below_bag_pd_def
  by (rule bag_le.typedef_ideal_po)

instance bag_pd :: (bifinite) cpo
  using type_definition_bag_pd below_bag_pd_def
  by (rule bag_le.typedef_ideal_cpo)

definition bag_principal :: "'a bag_basis \<Rightarrow> 'a bag_pd"
  where "bag_principal t = Abs_bag_pd {u. u \<le>\<^sub>b t}"

interpretation bag_pd: ideal_completion bag_le bag_principal Rep_bag_pd
  using type_definition_bag_pd below_bag_pd_def
  using bag_principal_def bag_basis_countable
  by (rule bag_le.typedef_ideal_completion)

text \<open>The bag powerdomain is pointed: the bottom is an open-ended number of unknown rows.\<close>

lemma bag_pd_minimal: "bag_principal (BOmega (BUnit compact_bot)) \<sqsubseteq> ys"
  by (induct ys rule: bag_pd.principal_induct) simp_all

instance bag_pd :: (bifinite) pcpo
  by intro_classes (fast intro: bag_pd_minimal)

lemma inst_bag_pd_pcpo: "\<bottom> = bag_principal (BOmega (BUnit compact_bot))"
  by (rule bag_pd_minimal [THEN bottomI, symmetric])

subsection \<open>Unit, plus and omega\<close>

definition bag_unit :: "'a \<rightarrow> 'a bag_pd"
  where "bag_unit = compact_basis.extension (\<lambda>a. bag_principal (BUnit a))"

definition bag_plus :: "'a bag_pd \<rightarrow> 'a bag_pd \<rightarrow> 'a bag_pd"
  where "bag_plus = bag_pd.extension (\<lambda>t. bag_pd.extension (\<lambda>u. bag_principal (BPlus t u)))"

definition bag_omega :: "'a bag_pd \<rightarrow> 'a bag_pd"
  where "bag_omega = bag_pd.extension (\<lambda>t. bag_principal (BOmega t))"

abbreviation bag_add :: "'a bag_pd \<Rightarrow> 'a bag_pd \<Rightarrow> 'a bag_pd" (infixl \<open>\<union>\<^sub>b\<close> 65)
  where "xs \<union>\<^sub>b ys == bag_plus\<cdot>xs\<cdot>ys"

lemma bag_unit_Rep_compact_basis [simp]: "bag_unit\<cdot>(Rep_compact_basis a) = bag_principal (BUnit a)"
  unfolding bag_unit_def by (simp add: compact_basis.extension_principal BUnit_mono)

lemma bag_plus_principal [simp]:
  "bag_principal t \<union>\<^sub>b bag_principal u = bag_principal (BPlus t u)"
  unfolding bag_plus_def
  by (simp add: bag_pd.extension_principal bag_pd.extension_mono BPlus_mono)

lemma bag_omega_principal [simp]: "bag_omega\<cdot>(bag_principal t) = bag_principal (BOmega t)"
  unfolding bag_omega_def by (simp add: bag_pd.extension_principal BOmega_mono)

interpretation bag_add: abel_semigroup bag_add
proof
  fix xs ys zs :: "'a bag_pd"
  show "(xs \<union>\<^sub>b ys) \<union>\<^sub>b zs = xs \<union>\<^sub>b (ys \<union>\<^sub>b zs)"
    apply (induct xs rule: bag_pd.principal_induct, simp)
    apply (induct ys rule: bag_pd.principal_induct, simp)
    apply (induct zs rule: bag_pd.principal_induct, simp)
    apply (simp add: BPlus_assoc)
    done
  show "xs \<union>\<^sub>b ys = ys \<union>\<^sub>b xs"
    apply (induct xs rule: bag_pd.principal_induct, simp)
    apply (induct ys rule: bag_pd.principal_induct, simp)
    apply (simp add: BPlus_commute)
    done
qed

lemmas bag_plus_assoc = bag_add.assoc
lemmas bag_plus_commute = bag_add.commute
lemmas bag_plus_left_commute = bag_add.left_commute

text \<open>Useful for \<open>simp add: bag_plus_ac\<close>\<close>
lemmas bag_plus_ac = bag_plus_assoc bag_plus_commute bag_plus_left_commute

lemma bag_plus_contract: "xs \<union>\<^sub>b xs \<sqsubseteq> xs"
  by (induct xs rule: bag_pd.principal_induct) (simp_all add: BPlus_contract)

lemma bag_omega_below: "bag_omega\<cdot>xs \<sqsubseteq> xs"
  by (induct xs rule: bag_pd.principal_induct) (simp_all add: BOmega_le)

lemma bag_omega_omega [simp]: "bag_omega\<cdot>(bag_omega\<cdot>xs) = bag_omega\<cdot>xs"
  by (induct xs rule: bag_pd.principal_induct) (simp_all add: BOmega_BOmega)

lemma bag_omega_plus [simp]: "bag_omega\<cdot>(xs \<union>\<^sub>b ys) = bag_omega\<cdot>xs \<union>\<^sub>b bag_omega\<cdot>ys"
  apply (induct xs rule: bag_pd.principal_induct, simp)
  apply (induct ys rule: bag_pd.principal_induct, simp)
  apply (simp add: BOmega_BPlus)
  done

lemma bag_plus_omega_absorb [simp]: "bag_omega\<cdot>xs \<union>\<^sub>b xs = bag_omega\<cdot>xs"
  by (induct xs rule: bag_pd.principal_induct) (simp_all add: BPlus_BOmega_absorb)

lemma bag_plus_omega_idem [simp]: "bag_omega\<cdot>xs \<union>\<^sub>b bag_omega\<cdot>xs = bag_omega\<cdot>xs"
  by (induct xs rule: bag_pd.principal_induct) (simp_all add: BPlus_BOmega_idem)

lemma bag_unit_below_iff [simp]: "bag_unit\<cdot>x \<sqsubseteq> bag_unit\<cdot>y \<longleftrightarrow> x \<sqsubseteq> y"
  apply (induct x rule: compact_basis.principal_induct, simp)
  apply (induct y rule: compact_basis.principal_induct, simp)
  apply simp
  done

lemma bag_unit_eq_iff [simp]: "bag_unit\<cdot>x = bag_unit\<cdot>y \<longleftrightarrow> x = y"
  unfolding po_eq_conv by simp

lemma bag_omega_unit_bottom: "bag_omega\<cdot>(bag_unit\<cdot>(\<bottom>::'a)) = \<bottom>"
proof -
  have "bag_unit\<cdot>(\<bottom>::'a) = bag_principal (BUnit compact_bot)"
    using bag_unit_Rep_compact_basis [of "compact_bot::'a compact_basis"] by simp
  then show ?thesis
    by (simp add: inst_bag_pd_pcpo)
qed

text \<open>@{text Extended_Nat} brings the topological @{text compact} into scope; the domain-theoretic
  one is @{const Cpo.compact}.\<close>

lemma compact_bag_unit: "Cpo.compact x \<Longrightarrow> Cpo.compact (bag_unit\<cdot>x)"
  by (auto dest!: compact_basis.compact_imp_principal)

lemma compact_bag_plus [simp]: "\<lbrakk>Cpo.compact xs; Cpo.compact ys\<rbrakk> \<Longrightarrow> Cpo.compact (xs \<union>\<^sub>b ys)"
  by (auto dest!: bag_pd.compact_imp_principal)

lemma compact_bag_omega [simp]: "Cpo.compact xs \<Longrightarrow> Cpo.compact (bag_omega\<cdot>xs)"
  by (auto dest!: bag_pd.compact_imp_principal)

subsection \<open>Embedding-projection pair with the convex powerdomain\<close>

text \<open>Forgetting multiplicities projects a bag onto its support in the convex powerdomain;
  giving every element multiplicity @{text \<omega>} embeds a convex set back. The composite is
  @{const bag_omega}, so the multiplicity-free part of the bag powerdomain is a copy of the
  convex powerdomain.\<close>

definition BSet :: "'a pd_basis \<Rightarrow> 'a bag_basis"
  where "BSet S = Abs_bag_basis (\<lambda>x. if x \<in> Rep_pd_basis S then \<infinity> else 0)"

lemma bmult_BSet: "bmult (BSet S) x = (if x \<in> Rep_pd_basis S then \<infinity> else 0)"
proof -
  have "{x. (if x \<in> Rep_pd_basis S then \<infinity> else 0) \<noteq> (0::enat)} = Rep_pd_basis S"
    by auto
  then show ?thesis
    unfolding BSet_def by (subst Abs_bag_basis_inverse') simp_all
qed

lemma bsupp_BSet [simp]: "bsupp (BSet S) = Rep_pd_basis S"
  by (auto simp: bsupp_def bmult_BSet)

definition bag_pdb :: "'a bag_basis \<Rightarrow> 'a pd_basis"
  where "bag_pdb t = Abs_pd_basis (bsupp t)"

lemma Rep_bag_pdb [simp]: "Rep_pd_basis (bag_pdb t) = bsupp t"
  unfolding bag_pdb_def by (rule Abs_pd_basis_inverse) (simp add: pd_basis_def)

lemma bag_pdb_mono: "t \<le>\<^sub>b u \<Longrightarrow> bag_pdb t \<le>\<natural> bag_pdb u"
  unfolding convex_le_def upper_le_def lower_le_def by (simp add: bag_le_supp)

lemma BSet_mono: "S \<le>\<natural> T \<Longrightarrow> BSet S \<le>\<^sub>b BSet T"
  unfolding convex_le_def upper_le_def lower_le_def
  by (rule bag_le_omegaI) (auto simp: bmult_BSet)

lemma bag_pdb_BSet [simp]: "bag_pdb (BSet S) = S"
  by (simp add: bag_pdb_def Rep_pd_basis_inverse)

lemma BSet_bag_pdb: "BSet (bag_pdb t) = BOmega t"
  by (rule bag_basis_eqI) (simp add: bmult_BSet bmult_BOmega bsupp_iff)

lemma bag_pdb_BUnit [simp]: "bag_pdb (BUnit a) = PDUnit a"
  by (simp add: Rep_pd_basis_inject [symmetric] Rep_PDUnit)

lemma bag_pdb_BPlus [simp]: "bag_pdb (BPlus t u) = PDPlus (bag_pdb t) (bag_pdb u)"
  by (simp add: Rep_pd_basis_inject [symmetric] Rep_PDPlus)

lemma bag_pdb_BOmega [simp]: "bag_pdb (BOmega t) = bag_pdb t"
  by (simp add: Rep_pd_basis_inject [symmetric])

lemma BSet_PDUnit: "BSet (PDUnit a) = BOmega (BUnit a)"
  by (rule bag_basis_eqI) (simp add: bmult_BSet bmult_BOmega bmult_BUnit Rep_PDUnit)

lemma BSet_PDPlus: "BSet (PDPlus S T) = BPlus (BSet S) (BSet T)"
  by (rule bag_basis_eqI) (simp add: bmult_BSet Rep_PDPlus)

definition bag_to_convex :: "'a bag_pd \<rightarrow> 'a convex_pd"
  where "bag_to_convex = bag_pd.extension (\<lambda>t. convex_principal (bag_pdb t))"

definition convex_to_bag :: "'a convex_pd \<rightarrow> 'a bag_pd"
  where "convex_to_bag = convex_pd.extension (\<lambda>S. bag_principal (BSet S))"

lemma bag_to_convex_principal [simp]:
  "bag_to_convex\<cdot>(bag_principal t) = convex_principal (bag_pdb t)"
  unfolding bag_to_convex_def by (simp add: bag_pd.extension_principal bag_pdb_mono)

lemma convex_to_bag_principal [simp]:
  "convex_to_bag\<cdot>(convex_principal S) = bag_principal (BSet S)"
  unfolding convex_to_bag_def by (simp add: convex_pd.extension_principal BSet_mono)

lemma ep_pair_convex_to_bag: "ep_pair convex_to_bag bag_to_convex"
proof
  fix x :: "'a convex_pd"
  show "bag_to_convex\<cdot>(convex_to_bag\<cdot>x) = x"
    by (induct x rule: convex_pd.principal_induct) simp_all
next
  fix y :: "'a bag_pd"
  show "convex_to_bag\<cdot>(bag_to_convex\<cdot>y) \<sqsubseteq> y"
    by (induct y rule: bag_pd.principal_induct) (simp_all add: BSet_bag_pdb BOmega_le)
qed

lemma bag_omega_eq: "bag_omega\<cdot>xs = convex_to_bag\<cdot>(bag_to_convex\<cdot>xs)"
  by (induct xs rule: bag_pd.principal_induct) (simp_all add: BSet_bag_pdb)

lemma bag_to_convex_unit [simp]: "bag_to_convex\<cdot>(bag_unit\<cdot>x) = convex_unit\<cdot>x"
  by (induct x rule: compact_basis.principal_induct) simp_all

lemma bag_to_convex_plus [simp]:
  "bag_to_convex\<cdot>(xs \<union>\<^sub>b ys) = bag_to_convex\<cdot>xs \<union>\<natural> bag_to_convex\<cdot>ys"
  apply (induct xs rule: bag_pd.principal_induct, simp)
  apply (induct ys rule: bag_pd.principal_induct, simp)
  apply simp
  done

lemma bag_to_convex_omega [simp]: "bag_to_convex\<cdot>(bag_omega\<cdot>xs) = bag_to_convex\<cdot>xs"
  by (induct xs rule: bag_pd.principal_induct) simp_all

lemma convex_to_bag_unit [simp]: "convex_to_bag\<cdot>(convex_unit\<cdot>x) = bag_omega\<cdot>(bag_unit\<cdot>x)"
  by (induct x rule: compact_basis.principal_induct) (simp_all add: BSet_PDUnit)

lemma convex_to_bag_plus [simp]:
  "convex_to_bag\<cdot>(xs \<union>\<natural> ys) = convex_to_bag\<cdot>xs \<union>\<^sub>b convex_to_bag\<cdot>ys"
  apply (induct xs rule: convex_pd.principal_induct, simp)
  apply (induct ys rule: convex_pd.principal_induct, simp)
  apply (simp add: BSet_PDPlus)
  done

text \<open>Below @{text \<omega>} multiplicities are invisible: the @{text \<omega>}-images are ordered exactly
  as in the convex (Egli-Milner) order.\<close>

lemma bag_omega_below_iff:
  "bag_omega\<cdot>xs \<sqsubseteq> bag_omega\<cdot>ys \<longleftrightarrow> bag_to_convex\<cdot>xs \<sqsubseteq> bag_to_convex\<cdot>ys"
  by (simp add: bag_omega_eq ep_pair.e_below_iff [OF ep_pair_convex_to_bag])

subsection \<open>Mapping\<close>

text \<open>A continuous map on elements acts on bags, continuously in the map as well. Its values on
  compact elements need not be compact, so the basis map reads them through a fixed approximation
  chain, and the bag map is the limit along the chain.\<close>

definition chosen_approx :: "nat \<Rightarrow> 'a \<rightarrow> 'a"
  where "chosen_approx = (SOME a. approx_chain a)"

lemma approx_chain_chosen_approx: "approx_chain chosen_approx"
  unfolding chosen_approx_def using bifinite by (rule someI_ex)

interpretation chosen_approx: approx_chain chosen_approx
  by (rule approx_chain_chosen_approx)

lemma chain_chosen_approx_app [simp]: "chain (\<lambda>i. chosen_approx i\<cdot>x)"
  by (rule ch2ch_Rep_cfunL[OF chosen_approx.chain_approx])

lemma lub_chosen_approx_app: "(\<Squnion>i. chosen_approx i\<cdot>x) = x"
  using contlub_cfun_fun[OF chosen_approx.chain_approx, of x] by simp

lemma compact_below_iff: "x \<sqsubseteq> y \<longleftrightarrow> Rep_compact_basis x \<sqsubseteq> Rep_compact_basis y"
  unfolding compact_le_def ..

definition approx_basis :: "nat \<Rightarrow> 'a \<Rightarrow> 'a compact_basis"
  where "approx_basis i x = Abs_compact_basis (chosen_approx i\<cdot>x)"

lemma Rep_approx_basis [simp]: "Rep_compact_basis (approx_basis i x) = chosen_approx i\<cdot>x"
  by (simp add: approx_basis_def)

lemma approx_basis_mono: "i \<le> j \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> approx_basis i x \<sqsubseteq> approx_basis j y"
  unfolding compact_le_def Rep_approx_basis
  by (rule below_trans[OF monofun_cfun_fun[OF chain_mono[OF chosen_approx.chain_approx]] monofun_cfun_arg])

text \<open>Finitely many eventual properties hold together eventually.\<close>

lemma finite_eventually:
  fixes P :: "'x::type \<Rightarrow> nat \<Rightarrow> bool"
  assumes "finite S" and "\<And>x. x \<in> S \<Longrightarrow> \<exists>n. \<forall>m\<ge>n. P x m"
  shows "\<exists>N. \<forall>x\<in>S. P x N"
proof -
  obtain nf where nf: "\<And>x. x \<in> S \<Longrightarrow> \<forall>m\<ge>nf x. P x m"
    using assms(2) by metis
  have "P x (Max (insert 0 (nf ` S)))" if "x \<in> S" for x
    using nf[OF that] Max_ge[of "insert 0 (nf ` S)" "nf x"] assms(1) that by simp
  then show ?thesis
    by blast
qed

text \<open>Families over the same indices with pointwise larger labels are larger.\<close>

lemma BFamily_le_labels:
  assumes "finite I" and "\<exists>i\<in>I. m i \<noteq> 0" and "\<And>i. i \<in> I \<Longrightarrow> f i \<sqsubseteq> g i"
  shows "BFamily I f m \<le>\<^sub>b BFamily I g m"
  by (rule BFamily_le[where p = "\<lambda>i j. if i = j then m i else 0"]) (use assms in \<open>auto split: if_split_asm\<close>)

definition BMap :: "('a \<rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'a bag_basis \<Rightarrow> 'b bag_basis"
  where "BMap f i t = BFamily (bsupp t) (\<lambda>x. approx_basis i (f\<cdot>(Rep_compact_basis x))) (bmult t)"

lemma bsupp_ex_nonzero: "\<exists>x\<in>bsupp t. bmult t x \<noteq> 0"
  using bsupp_nonempty[of t] unfolding bsupp_iff [symmetric] by blast

lemma BMap_mono:
  assumes fg: "f \<sqsubseteq> g" and ij: "i \<le> j" and tu: "t \<le>\<^sub>b u"
  shows "BMap f i t \<le>\<^sub>b BMap g j u"
proof -
  obtain P where P: "bag_plan t u P"
    using tu unfolding bag_le_def by blast
  have lab: "approx_basis i (f\<cdot>(Rep_compact_basis x)) \<sqsubseteq> approx_basis j (g\<cdot>(Rep_compact_basis y))"
    if "x \<sqsubseteq> y" for x y
    by (rule approx_basis_mono[OF ij monofun_cfun[OF fg compact_below_iff [THEN iffD1, OF that]]])
  show ?thesis
    unfolding BMap_def
  proof (rule BFamily_le[where p = P])
    fix x
    assume "x \<in> bsupp t" and "bmult t x \<noteq> 0"
    then obtain y where y: "y \<in> bsupp u" "P x y \<noteq> 0"
      using bag_plan_row_ex[OF P] by blast
    then show "\<exists>y\<in>bsupp u. bmult u y \<noteq> 0 \<and>
        approx_basis i (f\<cdot>(Rep_compact_basis x)) \<sqsubseteq> approx_basis j (g\<cdot>(Rep_compact_basis y))"
      using lab[OF bag_plan_below[OF P y(2)]] bsupp_iff by blast
  qed (auto simp: bsupp_ex_nonzero bag_plan_row[OF P] bag_plan_col[OF P] intro: lab bag_plan_below[OF P])
qed

text \<open>Along a chain of maps, the approximation at a fixed level is eventually reached on the
  finitely many elements of a basis bag.\<close>

lemma BMap_lub:
  assumes Y: "chain Y"
  shows "\<exists>N. BMap (\<Squnion>n. Y n) i t \<le>\<^sub>b BMap (Y N) i t"
proof -
  have "\<exists>N. \<forall>x\<in>bsupp t.
      approx_basis i ((\<Squnion>n. Y n)\<cdot>(Rep_compact_basis x)) \<sqsubseteq> approx_basis i (Y N\<cdot>(Rep_compact_basis x))"
  proof (rule finite_eventually[OF finite_bsupp])
    fix x
    let ?a = "\<lambda>n. chosen_approx i\<cdot>(Y n\<cdot>(Rep_compact_basis x))"
    have ch: "chain ?a"
      using Y by (intro ch2ch_Rep_cfunR ch2ch_Rep_cfunL)
    have "chosen_approx i\<cdot>((\<Squnion>n. Y n)\<cdot>(Rep_compact_basis x)) = (\<Squnion>n. ?a n)"
      using Y by (simp add: contlub_cfun_fun contlub_cfun_arg ch2ch_Rep_cfunL)
    then have "chosen_approx i\<cdot>((\<Squnion>n. Y n)\<cdot>(Rep_compact_basis x)) \<sqsubseteq> (\<Squnion>n. ?a n)"
      by simp
    then obtain n where n: "chosen_approx i\<cdot>((\<Squnion>n. Y n)\<cdot>(Rep_compact_basis x)) \<sqsubseteq> ?a n"
      using compact_below_lub_iff[OF chosen_approx.compact_approx[of i "(\<Squnion>n. Y n)\<cdot>(Rep_compact_basis x)"] ch]
      by blast
    have "\<forall>m\<ge>n. approx_basis i ((\<Squnion>n. Y n)\<cdot>(Rep_compact_basis x)) \<sqsubseteq> approx_basis i (Y m\<cdot>(Rep_compact_basis x))"
      using n chain_mono[OF ch] unfolding compact_below_iff Rep_approx_basis by (blast intro: below_trans)
    then show "\<exists>n. \<forall>m\<ge>n.
        approx_basis i ((\<Squnion>n. Y n)\<cdot>(Rep_compact_basis x)) \<sqsubseteq> approx_basis i (Y m\<cdot>(Rep_compact_basis x))"
      by blast
  qed
  then show ?thesis
    unfolding BMap_def by (blast intro: BFamily_le_labels finite_bsupp bsupp_ex_nonzero)
qed

lemma chain_BMap: "chain (\<lambda>i. bag_principal (BMap f i t))"
  by (rule chainI, rule bag_pd.principal_mono, rule BMap_mono) simp_all

lemma lub_BMap_mono:
  "f \<sqsubseteq> g \<Longrightarrow> t \<le>\<^sub>b u \<Longrightarrow> (\<Squnion>i. bag_principal (BMap f i t)) \<sqsubseteq> (\<Squnion>i. bag_principal (BMap g i u))"
  by (rule lub_mono[OF chain_BMap chain_BMap], rule bag_pd.principal_mono, erule (1) BMap_mono[OF _ order_refl])

lemma cont_bag_map: "cont (\<lambda>f. bag_pd.extension (\<lambda>t. \<Squnion>i. bag_principal (BMap f i t)))"
proof (rule contI2)
  let ?F = "\<lambda>f t. \<Squnion>i. bag_principal (BMap f i t)"
  show mono: "monofun (\<lambda>f. bag_pd.extension (?F f))"
    by (rule monofunI, rule bag_pd.extension_mono) (simp_all add: lub_BMap_mono)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'b"
  assume Y: "chain Y" and chY: "chain (\<lambda>n. bag_pd.extension (?F (Y n)))"
  have chF: "chain (\<lambda>n. ?F (Y n) t)" for t
    using Y by (intro chainI lub_BMap_mono) (simp_all add: chainE)
  show "bag_pd.extension (?F (\<Squnion>n. Y n)) \<sqsubseteq> (\<Squnion>n. bag_pd.extension (?F (Y n)))"
  proof (rule cfun_belowI)
    fix xs
    show "bag_pd.extension (?F (\<Squnion>n. Y n))\<cdot>xs \<sqsubseteq> (\<Squnion>n. bag_pd.extension (?F (Y n)))\<cdot>xs"
    proof (induct xs rule: bag_pd.principal_induct)
      fix t
      have "?F (\<Squnion>n. Y n) t \<sqsubseteq> (\<Squnion>n. ?F (Y n) t)"
      proof (rule lub_below[OF chain_BMap])
        fix i
        obtain N where "BMap (\<Squnion>n. Y n) i t \<le>\<^sub>b BMap (Y N) i t"
          using BMap_lub[OF Y] by blast
        then have "bag_principal (BMap (\<Squnion>n. Y n) i t) \<sqsubseteq> ?F (Y N) t"
          by (blast intro: below_trans bag_pd.principal_mono is_ub_thelub[OF chain_BMap])
        also have "\<dots> \<sqsubseteq> (\<Squnion>n. ?F (Y n) t)"
          by (rule is_ub_thelub[OF chF])
        finally show "bag_principal (BMap (\<Squnion>n. Y n) i t) \<sqsubseteq> (\<Squnion>n. ?F (Y n) t)" .
      qed
      then show "bag_pd.extension (?F (\<Squnion>n. Y n))\<cdot>(bag_principal t) \<sqsubseteq>
          (\<Squnion>n. bag_pd.extension (?F (Y n)))\<cdot>(bag_principal t)"
        by (simp add: contlub_cfun_fun[OF chY] bag_pd.extension_principal lub_BMap_mono)
    qed simp
  qed
qed

definition bag_map :: "('a \<rightarrow> 'b) \<rightarrow> 'a bag_pd \<rightarrow> 'b bag_pd"
  where "bag_map = (\<Lambda> f. bag_pd.extension (\<lambda>t. \<Squnion>i. bag_principal (BMap f i t)))"

lemma bag_map_principal: "bag_map\<cdot>f\<cdot>(bag_principal t) = (\<Squnion>i. bag_principal (BMap f i t))"
  unfolding bag_map_def by (simp add: cont_bag_map bag_pd.extension_principal lub_BMap_mono)

lemma BMap_BUnit: "BMap f i (BUnit a) = BUnit (approx_basis i (f\<cdot>(Rep_compact_basis a)))"
  by (rule bag_basis_eqI) (auto simp: BMap_def bmult_BFamily_sum bmult_BUnit)

lemma bag_map_unit [simp]:
  fixes f :: "'a \<rightarrow> 'b"
  shows "bag_map\<cdot>f\<cdot>(bag_unit\<cdot>x) = bag_unit\<cdot>(f\<cdot>x)"
proof (induct x rule: compact_basis.principal_induct)
  fix a
  have u: "bag_principal (BUnit (approx_basis i y)) = bag_unit\<cdot>(chosen_approx i\<cdot>y)"
    for i and y :: 'b
    using bag_unit_Rep_compact_basis[of "approx_basis i y"] by simp
  show "bag_map\<cdot>f\<cdot>(bag_unit\<cdot>(Rep_compact_basis a)) = bag_unit\<cdot>(f\<cdot>(Rep_compact_basis a))"
    by (simp add: bag_map_principal BMap_BUnit u contlub_cfun_arg[symmetric] lub_chosen_approx_app)
qed simp

text \<open>The identity map: the approximations are eventually exact on the compact elements of a basis
  bag.\<close>

lemma BFamily_bsupp: "BFamily (bsupp t) (\<lambda>x. x) (bmult t) = t"
proof (rule bag_basis_eqI)
  fix z
  have "{x\<in>bsupp t. x = z} = (if z \<in> bsupp t then {z} else {})"
    by auto
  then show "bmult (BFamily (bsupp t) (\<lambda>x. x) (bmult t)) z = bmult t z"
    by (simp add: bmult_BFamily[OF finite_bsupp bsupp_ex_nonzero] bsupp_iff)
qed

lemma bag_map_ID [simp]: "bag_map\<cdot>ID = (ID :: 'a bag_pd \<rightarrow> 'a bag_pd)"
proof (rule cfun_eqI)
  fix xs :: "'a bag_pd"
  show "bag_map\<cdot>ID\<cdot>xs = ID\<cdot>xs"
  proof (induct xs rule: bag_pd.principal_induct)
    fix t :: "'a bag_basis"
    have "\<exists>N. \<forall>x\<in>bsupp t. approx_basis N (Rep_compact_basis x) = x"
    proof (rule finite_eventually[OF finite_bsupp, where P = "\<lambda>x N. approx_basis N (Rep_compact_basis x) = x"])
      fix x :: "'a compact_basis"
      obtain n where n: "chosen_approx n\<cdot>(Rep_compact_basis x) = Rep_compact_basis x"
        using chosen_approx.compact_eq_approx[OF Rep_compact_basis'] by blast
      have "chosen_approx m\<cdot>(Rep_compact_basis x) = Rep_compact_basis x" if "n \<le> m" for m
        by (rule below_antisym[OF chosen_approx.approx_below])
          (metis n monofun_cfun_fun[OF chain_mono[OF chosen_approx.chain_approx that]])
      then show "\<exists>n. \<forall>m\<ge>n. approx_basis m (Rep_compact_basis x) = x"
        by (auto simp: Rep_compact_basis_inject [symmetric])
    qed
    then obtain N where N: "\<And>x. x \<in> bsupp t \<Longrightarrow> approx_basis N (Rep_compact_basis x) = x"
      by blast
    have below: "bag_principal (BMap ID i t) \<sqsubseteq> bag_principal t" for i
    proof (rule bag_pd.principal_mono)
      have "BMap ID i t \<le>\<^sub>b BFamily (bsupp t) (\<lambda>x. x) (bmult t)"
        unfolding BMap_def
        by (rule BFamily_le_labels) (simp_all add: bsupp_ex_nonzero compact_below_iff chosen_approx.approx_below)
      then show "BMap ID i t \<le>\<^sub>b t"
        by (simp add: BFamily_bsupp)
    qed
    have "BMap ID N t = t"
      unfolding BMap_def by (subst BFamily_cong[where f' = "\<lambda>x. x" and m' = "bmult t"]) (simp_all add: N BFamily_bsupp)
    then have "bag_principal t \<sqsubseteq> (\<Squnion>i. bag_principal (BMap ID i t))"
      using is_ub_thelub[OF chain_BMap, of ID N t] by simp
    then show "bag_map\<cdot>ID\<cdot>(bag_principal t) = ID\<cdot>(bag_principal t)"
      by (simp add: bag_map_principal below_antisym lub_below[OF chain_BMap below])
  qed simp
qed

lemma bmult_BMap:
  "bmult (BMap f i t) z = (\<Sum>x\<in>bsupp t. if approx_basis i (f\<cdot>(Rep_compact_basis x)) = z then bmult t x else 0)"
  by (simp only: BMap_def bmult_BFamily_sum[OF finite_bsupp bsupp_ex_nonzero])

lemma BMap_BPlus: "BMap f i (BPlus t u) = BPlus (BMap f i t) (BMap f i u)"
proof (rule bag_basis_eqI)
  fix z
  let ?l = "\<lambda>x. approx_basis i (f\<cdot>(Rep_compact_basis x))"
  let ?f = "\<lambda>v x. if ?l x = z then bmult v x else 0"
  have ext: "sum (?f v) (bsupp t \<union> bsupp u) = sum (?f v) (bsupp v)" if "bsupp v \<subseteq> bsupp t \<union> bsupp u" for v
    using that by (intro sum.mono_neutral_right) (auto simp: bsupp_iff)
  have "bmult (BMap f i (BPlus t u)) z = (\<Sum>x\<in>bsupp t \<union> bsupp u. ?f t x + ?f u x)"
    unfolding bmult_BMap by (rule sum.cong) simp_all
  also have "\<dots> = bmult (BMap f i t) z + bmult (BMap f i u) z"
    unfolding sum.distrib bmult_BMap by (simp add: ext)
  finally show "bmult (BMap f i (BPlus t u)) z = bmult (BPlus (BMap f i t) (BMap f i u)) z"
    by simp
qed

lemma BMap_BOmega: "BMap f i (BOmega t) = BOmega (BMap f i t)"
proof (rule bag_basis_eqI)
  fix z
  let ?l = "\<lambda>x. approx_basis i (f\<cdot>(Rep_compact_basis x))"
  show "bmult (BMap f i (BOmega t)) z = bmult (BOmega (BMap f i t)) z"
  proof (cases "\<exists>x\<in>bsupp t. ?l x = z")
    case True
    then obtain x where x: "x \<in> bsupp t" "?l x = z"
      by blast
    have "bmult (BMap f i (BOmega t)) z = \<infinity>"
      unfolding bmult_BMap using x by (intro enat_sum_infty[where x = x]) (simp_all add: bmult_BOmega bsupp_iff)
    moreover have "bmult (BMap f i t) z \<noteq> 0"
      unfolding bmult_BMap using x by (subst sum_eq_0_iff) (auto simp: bsupp_iff)
    ultimately show ?thesis
      by (simp add: bmult_BOmega)
  next
    case False
    then show ?thesis
      by (simp add: bmult_BMap bmult_BOmega)
  qed
qed

lemma bag_map_plus [simp]:
  fixes f :: "'a \<rightarrow> 'b"
  shows "bag_map\<cdot>f\<cdot>(xs \<union>\<^sub>b ys) = bag_map\<cdot>f\<cdot>xs \<union>\<^sub>b bag_map\<cdot>f\<cdot>ys"
proof (induct xs rule: bag_pd.principal_induct)
  fix t
  show "bag_map\<cdot>f\<cdot>(bag_principal t \<union>\<^sub>b ys) = bag_map\<cdot>f\<cdot>(bag_principal t) \<union>\<^sub>b bag_map\<cdot>f\<cdot>ys"
  proof (induct ys rule: bag_pd.principal_induct)
    fix u
    have lubplus: "(\<Squnion>i. P i \<union>\<^sub>b Q i) = (\<Squnion>i. P i) \<union>\<^sub>b (\<Squnion>i. Q i)"
      if "chain P" "chain Q" for P Q :: "nat \<Rightarrow> 'b bag_pd"
      using lub_APP[OF ch2ch_Rep_cfunR[OF that(1)] that(2)] contlub_cfun_arg[OF that(1), of bag_plus]
      by simp
    have "bag_map\<cdot>f\<cdot>(bag_principal t \<union>\<^sub>b bag_principal u) =
        (\<Squnion>i. bag_principal (BMap f i t) \<union>\<^sub>b bag_principal (BMap f i u))"
      by (simp add: bag_map_principal BMap_BPlus)
    then show "bag_map\<cdot>f\<cdot>(bag_principal t \<union>\<^sub>b bag_principal u) =
        bag_map\<cdot>f\<cdot>(bag_principal t) \<union>\<^sub>b bag_map\<cdot>f\<cdot>(bag_principal u)"
      by (simp add: lubplus chain_BMap bag_map_principal del: bag_plus_principal)
  qed simp
qed simp

lemma bag_map_omega [simp]: "bag_map\<cdot>f\<cdot>(bag_omega\<cdot>xs) = bag_omega\<cdot>(bag_map\<cdot>f\<cdot>xs)"
  by (induct xs rule: bag_pd.principal_induct)
    (simp_all add: bag_map_principal BMap_BOmega contlub_cfun_arg[OF chain_BMap])

end
