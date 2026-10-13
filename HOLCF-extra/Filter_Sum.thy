theory Filter_Sum imports Distributive begin


section \<open>Filter sums\<close>

text \<open>A pcpo is a \<^emph>\<open>filter sum\<close> when any two nonbottom elements with a common upper bound also
  have a common nonbottom lower bound.  In a bounded-complete pcpo this says that joinable
  nonbottom elements have a nonbottom meet (@{text filter_sum_meet} below).  Equivalently, every
  connected component of the punctured space \<open>D - {\<bottom>}\<close> is a filter, i.e. \<open>D \<cong> (\<Sigma>\<^sub>i F\<^sub>i)\<^sub>\<bottom>\<close>.  This
  is what keeps the smash product distributive.  (When every component has a least element, \<open>D\<close>
  is a \<^emph>\<open>separated sum\<close>, the lifted disjoint sum of pointed domains.)\<close>

class filter_sum = pcpo +
  assumes filter_sum: "x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> x \<sqsubseteq> u \<Longrightarrow> y \<sqsubseteq> u \<Longrightarrow> \<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"

text \<open>Bounded-above nonbottom elements have nonbottom lower bounds with any third element
  together: if \<open>z\<close> has one with \<open>y\<close>, it has one with \<open>x\<close>.  No lattice operations needed.\<close>

lemma filter_sum_lower_cong:
  fixes x y z :: "'a::filter_sum"
  assumes x: "x \<noteq> \<bottom>" and xu: "x \<sqsubseteq> u" and yu: "y \<sqsubseteq> u"
    and w: "w \<noteq> \<bottom>" "w \<sqsubseteq> z" "w \<sqsubseteq> y"
  shows "\<exists>v. v \<noteq> \<bottom> \<and> v \<sqsubseteq> z \<and> v \<sqsubseteq> x"
proof -
  have "w \<sqsubseteq> u" using \<open>w \<sqsubseteq> y\<close> yu by (rule below_trans)
  from filter_sum[OF \<open>w \<noteq> \<bottom>\<close> x this xu] obtain v where "v \<noteq> \<bottom>" "v \<sqsubseteq> w" "v \<sqsubseteq> x" by fast
  with \<open>w \<sqsubseteq> z\<close> show ?thesis by (fast dest: below_trans)
qed

text \<open>Separation through any chain of maps with lub \<open>ID\<close> (e.g. the \<open>take\<close> functions of a domain):
  it suffices to separate approximants \<open>t n\<cdot>x\<close> from arbitrary \<open>y\<close>.  A nonbottom \<open>x\<close> has a
  nonbottom approximant, and a witness below it lies below \<open>x\<close>.\<close>

lemma filter_sum_chainI:
  fixes t :: "nat \<Rightarrow> 'a::pcpo \<rightarrow> 'a"
  assumes t: "chain t" "(\<Squnion>i. t i) = ID"
    and sep: "\<And>n x y u. t n\<cdot>x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> t n\<cdot>x \<sqsubseteq> u \<Longrightarrow> y \<sqsubseteq> u \<Longrightarrow>
      \<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> t n\<cdot>x \<and> l \<sqsubseteq> y"
  shows "OFCLASS('a, filter_sum_class)"
proof
  fix x y u :: 'a assume "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" "x \<sqsubseteq> u" "y \<sqsubseteq> u"
  have chx: "chain (\<lambda>n. t n\<cdot>x)" by (rule ch2ch_Rep_cfunL[OF t(1)])
  have reach: "(\<Squnion>n. t n\<cdot>x) = x" by (simp add: contlub_cfun_fun[OF t(1), symmetric] t(2))
  have below: "t n\<cdot>x \<sqsubseteq> x" for n using is_ub_thelub[OF chx, of n] by (simp add: reach)
  have "\<exists>n. t n\<cdot>x \<noteq> \<bottom>" using \<open>x \<noteq> \<bottom>\<close> lub_eq_bottom_iff[OF chx] by (simp add: reach)
  then obtain n :: nat where n: "t n\<cdot>x \<noteq> \<bottom>" by (elim exE)
  have "t n\<cdot>x \<sqsubseteq> u" using below \<open>x \<sqsubseteq> u\<close> by (rule below_trans)
  from sep[OF n \<open>y \<noteq> \<bottom>\<close> this \<open>y \<sqsubseteq> u\<close>] obtain l :: 'a where l: "l \<noteq> \<bottom>" "l \<sqsubseteq> t n\<cdot>x" "l \<sqsubseteq> y"
    by (elim exE conjE)
  from l(2) below have "l \<sqsubseteq> x" by (rule below_trans)
  with l(1,3) show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y" by (intro exI[of _ l]) simp
qed

subsection \<open>The meet form, in bounded-complete pcpos\<close>

text \<open>A nonbottom meet is the same as a nonbottom common lower bound; through this, the
  lattice-free statements above become statements about meets.\<close>

lemma nonbot_meet_iff:
  fixes x y :: "'a::bounded_complete"
  shows "x \<sqinter> y \<noteq> \<bottom> \<longleftrightarrow> (\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y)"
proof
  assume "x \<sqinter> y \<noteq> \<bottom>"
  then show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
    by (intro exI[of _ "x \<sqinter> y"] conjI meet_below1 meet_below2)
next
  assume "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
  then obtain l :: 'a where "l \<noteq> \<bottom>" "l \<sqsubseteq> x" "l \<sqsubseteq> y" by (elim exE conjE)
  then show "x \<sqinter> y \<noteq> \<bottom>" by (metis bottomI meet_greatest)
qed

lemma filter_sum_meet:
  fixes x y :: "'a::{filter_sum, bounded_complete}"
  assumes "x \<Up> y" "x \<sqinter> y = \<bottom>" shows "x = \<bottom> \<or> y = \<bottom>"
proof -
  from \<open>x \<Up> y\<close> obtain u :: 'a where "x \<sqsubseteq> u" "y \<sqsubseteq> u" unfolding joinable_def by (elim exE conjE)
  with filter_sum[of x y u] \<open>x \<sqinter> y = \<bottom>\<close> show ?thesis
    by (auto simp: nonbot_meet_iff[symmetric])
qed

text \<open>Joinable nonbottom elements meet any third element to \<open>\<bottom>\<close> together.\<close>

lemma filter_sum_meet_bottom_cong:
  fixes x y z :: "'a::{filter_sum, bounded_complete}"
  assumes "x \<Up> y" "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" "z \<sqinter> x = \<bottom>" shows "z \<sqinter> y = \<bottom>"
proof (rule ccontr)
  assume "z \<sqinter> y \<noteq> \<bottom>"
  then obtain w :: 'a where w: "w \<noteq> \<bottom>" "w \<sqsubseteq> z" "w \<sqsubseteq> y"
    unfolding nonbot_meet_iff by (elim exE conjE)
  from \<open>x \<Up> y\<close> obtain u :: 'a where u: "x \<sqsubseteq> u" "y \<sqsubseteq> u" unfolding joinable_def by (elim exE conjE)
  have "\<exists>v. v \<noteq> \<bottom> \<and> v \<sqsubseteq> z \<and> v \<sqsubseteq> x"
    using filter_sum_lower_cong[of x u y w z] \<open>x \<noteq> \<bottom>\<close> u w by simp
  then have "z \<sqinter> x \<noteq> \<bottom>" by (simp add: nonbot_meet_iff)
  with \<open>z \<sqinter> x = \<bottom>\<close> show False by simp
qed

subsection \<open>Instances\<close>

(*TODO move to bounded_complete and use there too? *)

lemma (in flat) flat_joinableE: assumes "a \<Up> b" obtains "a = \<bottom>" | "b = \<bottom>" | "a = b"
  by (metis ax_flat joinableD assms)

instance flat \<subseteq> filter_sum
proof
  fix x y u :: 'a assume "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" "x \<sqsubseteq> u" "y \<sqsubseteq> u"
  then have "x = y" by (metis ax_flat)
  with \<open>x \<noteq> \<bottom>\<close> show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y" by (intro exI[of _ x]) simp
qed

text \<open>Lifting needs no assumption on the argument beyond pointedness: \<open>up\<cdot>\<bottom>\<close> lies below every
  nonbottom element.\<close>

instance u :: (pcpo) filter_sum
proof
  fix x y u :: "'a u" assume "x \<noteq> \<bottom>" "y \<noteq> \<bottom>"
  then show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
    by (intro exI[of _ "up\<cdot>\<bottom>"]) (cases x; cases y; simp)
qed

text \<open>A common upper bound forces both elements into the same summand; separate there.\<close>

instance ssum :: ("{pcpo, filter_sum}", "{pcpo, filter_sum}") filter_sum
proof
  fix x y u :: "'a \<oplus> 'b" assume nb: "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" and le: "x \<sqsubseteq> u" "y \<sqsubseteq> u"
  have L: "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> (sinl\<cdot>a :: 'a \<oplus> 'b) \<and> l \<sqsubseteq> sinl\<cdot>b"
    if "a \<noteq> \<bottom>" "b \<noteq> \<bottom>" "a \<sqsubseteq> c" "b \<sqsubseteq> c" for a b c :: 'a
  proof -
    from filter_sum[OF that] obtain l :: 'a where "l \<noteq> \<bottom>" "l \<sqsubseteq> a" "l \<sqsubseteq> b"
      by (elim exE conjE)
    then show ?thesis by (intro exI[of _ "sinl\<cdot>l"]) simp
  qed
  have R: "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> (sinr\<cdot>a :: 'a \<oplus> 'b) \<and> l \<sqsubseteq> sinr\<cdot>b"
    if "a \<noteq> \<bottom>" "b \<noteq> \<bottom>" "a \<sqsubseteq> c" "b \<sqsubseteq> c" for a b c :: 'b
  proof -
    from filter_sum[OF that] obtain l :: 'b where "l \<noteq> \<bottom>" "l \<sqsubseteq> a" "l \<sqsubseteq> b"
      by (elim exE conjE)
    then show ?thesis by (intro exI[of _ "sinr\<cdot>l"]) simp
  qed
  show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
  proof (cases x)
    case bottom with nb show ?thesis by simp
  next
    case (sinl a)
    from le(1) sinl obtain c where u: "u = sinl\<cdot>c" and ac: "a \<sqsubseteq> c" by (cases u) auto
    from le(2) nb(2) u obtain b where y: "y = sinl\<cdot>b" "b \<noteq> \<bottom>" and bc: "b \<sqsubseteq> c" by (cases y) auto
    from L[OF sinl(2) y(2) ac bc] show ?thesis by (simp only: sinl(1) y(1))
  next
    case (sinr a)
    from le(1) sinr obtain c where u: "u = sinr\<cdot>c" and ac: "a \<sqsubseteq> c" by (cases u) auto
    from le(2) nb(2) u obtain b where y: "y = sinr\<cdot>b" "b \<noteq> \<bottom>" and bc: "b \<sqsubseteq> c" by (cases y) auto
    from R[OF sinr(2) y(2) ac bc] show ?thesis by (simp only: sinr(1) y(1))
  qed
qed

text \<open>Componentwise: the pair of the two components' witnesses.\<close>

instance sprod :: ("{pcpo, filter_sum}", "{pcpo, filter_sum}") filter_sum
proof
  fix x y u :: "'a \<otimes> 'b" assume nb: "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" and le: "x \<sqsubseteq> u" "y \<sqsubseteq> u"
  have S: "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> (:a, b:) \<and> l \<sqsubseteq> (:a', b':)"
    if "a \<noteq> \<bottom>" "b \<noteq> \<bottom>" "a' \<noteq> \<bottom>" "b' \<noteq> \<bottom>" "a \<sqsubseteq> c" "a' \<sqsubseteq> c" "b \<sqsubseteq> d" "b' \<sqsubseteq> d"
    for a a' c :: 'a and b b' d :: 'b
  proof -
    from filter_sum[OF \<open>a \<noteq> \<bottom>\<close> \<open>a' \<noteq> \<bottom>\<close> \<open>a \<sqsubseteq> c\<close> \<open>a' \<sqsubseteq> c\<close>]
    obtain la :: 'a where "la \<noteq> \<bottom>" "la \<sqsubseteq> a" "la \<sqsubseteq> a'" by (elim exE conjE)
    moreover from filter_sum[OF \<open>b \<noteq> \<bottom>\<close> \<open>b' \<noteq> \<bottom>\<close> \<open>b \<sqsubseteq> d\<close> \<open>b' \<sqsubseteq> d\<close>]
    obtain lb :: 'b where "lb \<noteq> \<bottom>" "lb \<sqsubseteq> b" "lb \<sqsubseteq> b'" by (elim exE conjE)
    ultimately show ?thesis using that
      by (intro exI[of _ "(:la, lb:)"] conjI) (simp_all only: spair_below spair_bottom_iff simp_thms)
  qed
  obtain x1 x2 where x: "x = (:x1, x2:)" "x1 \<noteq> \<bottom>" "x2 \<noteq> \<bottom>" using nb(1) by (cases x) auto
  obtain y1 y2 where y: "y = (:y1, y2:)" "y1 \<noteq> \<bottom>" "y2 \<noteq> \<bottom>" using nb(2) by (cases y) auto
  obtain u1 u2 where u: "u = (:u1, u2:)" using le(1) x by (cases u) auto
  have "x1 \<sqsubseteq> u1" "x2 \<sqsubseteq> u2" "y1 \<sqsubseteq> u1" "y2 \<sqsubseteq> u2"
    using le(1)[unfolded x(1) u] le(2)[unfolded y(1) u]
    by (simp_all only: spair_below x(2,3) y(2,3) simp_thms)
  from S[OF x(2,3) y(2,3) this(1,3,2,4)] show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
    by (simp only: x(1) y(1))
qed

section \<open>Separated sums\<close>

text \<open>An \<^emph>\<open>atom\<close> is a minimal nonbottom element.  A pcpo is a \<^emph>\<open>separated sum\<close> when any two
  nonbottom elements with a common upper bound lie above a common atom: atomicity and
  separation in one statement.  Equivalently every component of the punctured space
  \<open>D - {\<bottom>}\<close> has a least element, i.e.\ \<open>D \<cong> (\<Sigma>\<^sub>i C\<^sub>i)\<^sub>\<bottom>\<close> for pointed \<open>C\<^sub>i\<close>, the separated sum of
  the \<open>C\<^sub>i\<close>; that least element is the component's unique atom.\<close>

definition atom :: "'a::pcpo \<Rightarrow> bool" where
  "atom l \<longleftrightarrow> l \<noteq> \<bottom> \<and> (\<forall>z. z \<sqsubseteq> l \<longrightarrow> z = \<bottom> \<or> z = l)"

lemma atomI: "l \<noteq> \<bottom> \<Longrightarrow> (\<And>z. z \<sqsubseteq> l \<Longrightarrow> z = \<bottom> \<or> z = l) \<Longrightarrow> atom l"
  by (simp add: atom_def)

lemma atom_nonbottom: "atom l \<Longrightarrow> l \<noteq> \<bottom>"
  by (simp add: atom_def)

lemma atomD: "atom l \<Longrightarrow> z \<sqsubseteq> l \<Longrightarrow> z = \<bottom> \<or> z = l"
  by (simp add: atom_def)

class separated_sum = pcpo +
  assumes separated_sum: "x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> x \<sqsubseteq> u \<Longrightarrow> y \<sqsubseteq> u \<Longrightarrow> \<exists>l. atom l \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"

instance separated_sum \<subseteq> filter_sum
proof
  fix x y u :: 'a assume "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" "x \<sqsubseteq> u" "y \<sqsubseteq> u"
  from separated_sum[OF this] show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
    by (blast dest: atom_nonbottom)
qed

lemma atom_below:
  fixes x :: "'a::separated_sum"
  assumes "x \<noteq> \<bottom>" obtains l where "atom l" "l \<sqsubseteq> x"
  using separated_sum[OF assms assms below_refl below_refl] by blast

text \<open>Two atoms with a common upper bound are equal.\<close>

lemma atom_unique:
  fixes a b :: "'a::separated_sum"
  assumes a: "atom a" and b: "atom b" and "a \<sqsubseteq> u" "b \<sqsubseteq> u" shows "a = b"
proof -
  from separated_sum[OF atom_nonbottom[OF a] atom_nonbottom[OF b] assms(3,4)]
  obtain l where l: "atom l" "l \<sqsubseteq> a" "l \<sqsubseteq> b" by blast
  have "l = a" using atomD[OF a l(2)] atom_nonbottom[OF l(1)] by blast
  moreover have "l = b" using atomD[OF b l(3)] atom_nonbottom[OF l(1)] by blast
  ultimately show ?thesis by simp
qed

text \<open>In an algebraic domain atoms are compact: some compact approximant is nonbottom, and
  lies below the atom.\<close>

lemma atom_compact:
  fixes a :: "'a::bifinite" assumes a: "atom a" shows "compact a"
proof -
  obtain C where C: "chain C" "\<forall>i. compact (C i)" "a = (\<Squnion>i. C i)" by (rule obtain_compact_chain)
  have "\<exists>i. C i \<noteq> \<bottom>" using C(1,3) atom_nonbottom[OF a] lub_eq_bottom_iff by blast
  then obtain i where i: "C i \<noteq> \<bottom>" by blast
  have "C i \<sqsubseteq> a" using is_ub_thelub[OF C(1)] C(3) by simp
  with atomD[OF a] i have "C i = a" by blast
  with C(2) show ?thesis by metis
qed

subsection \<open>Atoms of the domain constructions\<close>

lemma atom_up_bottom: "atom (up\<cdot>(\<bottom>::'a::pcpo))"
proof (rule atomI)
  fix z :: "'a u" assume "z \<sqsubseteq> up\<cdot>\<bottom>"
  then show "z = \<bottom> \<or> z = up\<cdot>\<bottom>" by (cases z) simp_all
qed simp

lemma atom_sinl_iff: "atom (sinl\<cdot>x :: 'a::pcpo \<oplus> 'b::pcpo) \<longleftrightarrow> atom x"
proof
  assume a: "atom (sinl\<cdot>x :: 'a \<oplus> 'b)"
  show "atom x"
  proof (rule atomI)
    show "x \<noteq> \<bottom>" using atom_nonbottom[OF a] by auto
    fix z assume "z \<sqsubseteq> x"
    then have "(sinl\<cdot>z :: 'a \<oplus> 'b) \<sqsubseteq> sinl\<cdot>x" by simp
    from atomD[OF a this] show "z = \<bottom> \<or> z = x" by simp
  qed
next
  assume a: "atom x"
  show "atom (sinl\<cdot>x :: 'a \<oplus> 'b)"
  proof (rule atomI)
    show "(sinl\<cdot>x :: 'a \<oplus> 'b) \<noteq> \<bottom>" using atom_nonbottom[OF a] by simp
    fix z :: "'a \<oplus> 'b" assume z: "z \<sqsubseteq> sinl\<cdot>x"
    show "z = \<bottom> \<or> z = sinl\<cdot>x"
    proof (cases z)
      case (sinl z') with z atomD[OF a, of z'] show ?thesis by auto
    qed (use z in auto)
  qed
qed

lemma atom_sinr_iff: "atom (sinr\<cdot>x :: 'a::pcpo \<oplus> 'b::pcpo) \<longleftrightarrow> atom x"
proof
  assume a: "atom (sinr\<cdot>x :: 'a \<oplus> 'b)"
  show "atom x"
  proof (rule atomI)
    show "x \<noteq> \<bottom>" using atom_nonbottom[OF a] by auto
    fix z assume "z \<sqsubseteq> x"
    then have "(sinr\<cdot>z :: 'a \<oplus> 'b) \<sqsubseteq> sinr\<cdot>x" by simp
    from atomD[OF a this] show "z = \<bottom> \<or> z = x" by simp
  qed
next
  assume a: "atom x"
  show "atom (sinr\<cdot>x :: 'a \<oplus> 'b)"
  proof (rule atomI)
    show "(sinr\<cdot>x :: 'a \<oplus> 'b) \<noteq> \<bottom>" using atom_nonbottom[OF a] by simp
    fix z :: "'a \<oplus> 'b" assume z: "z \<sqsubseteq> sinr\<cdot>x"
    show "z = \<bottom> \<or> z = sinr\<cdot>x"
    proof (cases z)
      case (sinr z') with z atomD[OF a, of z'] show ?thesis by auto
    qed (use z in auto)
  qed
qed

lemma atom_spair:
  assumes a: "atom (a::'a::pcpo)" and b: "atom (b::'b::pcpo)" shows "atom (:a, b:)"
proof (rule atomI)
  show "(:a, b:) \<noteq> \<bottom>" using atom_nonbottom[OF a] atom_nonbottom[OF b] by simp
  fix z assume z: "z \<sqsubseteq> (:a, b:)"
  show "z = \<bottom> \<or> z = (:a, b:)"
  proof (cases z)
    case (spair z1 z2)
    with z atom_nonbottom[OF a] atom_nonbottom[OF b] have "z1 \<sqsubseteq> a" "z2 \<sqsubseteq> b"
      by (simp_all add: spair_below)
    with atomD[OF a] atomD[OF b] spair show ?thesis by auto
  qed simp
qed

subsection \<open>Instances\<close>

instance flat \<subseteq> separated_sum
proof
  fix x y u :: 'a assume "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" "x \<sqsubseteq> u" "y \<sqsubseteq> u"
  then have "x = y" by (metis ax_flat)
  moreover have "atom x" by (rule atomI[OF \<open>x \<noteq> \<bottom>\<close>]) (metis ax_flat)
  ultimately show "\<exists>l. atom l \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y" by blast
qed

instance u :: (pcpo) separated_sum
proof
  fix x y u :: "'a u" assume "x \<noteq> \<bottom>" "y \<noteq> \<bottom>"
  then show "\<exists>l. atom l \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
    by (intro exI[of _ "up\<cdot>\<bottom>"]) (cases x; cases y; simp add: atom_up_bottom)
qed

instance ssum :: (separated_sum, separated_sum) separated_sum
proof
  fix x y u :: "'a \<oplus> 'b" assume nb: "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" and le: "x \<sqsubseteq> u" "y \<sqsubseteq> u"
  show "\<exists>l. atom l \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
  proof (cases x)
    case bottom with nb show ?thesis by simp
  next
    case (sinl a)
    from le(1) sinl obtain c where u: "u = sinl\<cdot>c" and ac: "a \<sqsubseteq> c" by (cases u) auto
    from le(2) nb(2) u obtain b where y: "y = sinl\<cdot>b" "b \<noteq> \<bottom>" and bc: "b \<sqsubseteq> c" by (cases y) auto
    from separated_sum[OF sinl(2) y(2) ac bc] obtain l where "atom l" "l \<sqsubseteq> a" "l \<sqsubseteq> b" by blast
    with sinl y show ?thesis by (intro exI[of _ "sinl\<cdot>l"]) (simp add: atom_sinl_iff)
  next
    case (sinr a)
    from le(1) sinr obtain c where u: "u = sinr\<cdot>c" and ac: "a \<sqsubseteq> c" by (cases u) auto
    from le(2) nb(2) u obtain b where y: "y = sinr\<cdot>b" "b \<noteq> \<bottom>" and bc: "b \<sqsubseteq> c" by (cases y) auto
    from separated_sum[OF sinr(2) y(2) ac bc] obtain l where "atom l" "l \<sqsubseteq> a" "l \<sqsubseteq> b" by blast
    with sinr y show ?thesis by (intro exI[of _ "sinr\<cdot>l"]) (simp add: atom_sinr_iff)
  qed
qed

instance sprod :: (separated_sum, separated_sum) separated_sum
proof
  fix x y u :: "'a \<otimes> 'b" assume nb: "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" and le: "x \<sqsubseteq> u" "y \<sqsubseteq> u"
  obtain x1 x2 where x: "x = (:x1, x2:)" "x1 \<noteq> \<bottom>" "x2 \<noteq> \<bottom>" using nb(1) by (cases x) auto
  obtain y1 y2 where y: "y = (:y1, y2:)" "y1 \<noteq> \<bottom>" "y2 \<noteq> \<bottom>" using nb(2) by (cases y) auto
  obtain u1 u2 where u: "u = (:u1, u2:)" using le(1) x by (cases u) auto
  have "x1 \<sqsubseteq> u1" "x2 \<sqsubseteq> u2" "y1 \<sqsubseteq> u1" "y2 \<sqsubseteq> u2"
    using le(1)[unfolded x(1) u] le(2)[unfolded y(1) u]
    by (simp_all only: spair_below x(2,3) y(2,3) simp_thms)
  then obtain l1 l2 where "atom l1" "l1 \<sqsubseteq> x1" "l1 \<sqsubseteq> y1" "atom l2" "l2 \<sqsubseteq> x2" "l2 \<sqsubseteq> y2"
    using separated_sum[OF x(2) y(2)] separated_sum[OF x(3) y(3)] by meson
  then show "\<exists>l. atom l \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
    using x y by (intro exI[of _ "(:l1, l2:)"])
      (simp add: atom_spair spair_below atom_nonbottom)
qed

section \<open>Distributivity of smash products\<close>

text \<open>Separation of both components keeps \<open>\<otimes>\<close> distributive: joinable nonbottom pairs meet a third
  pair to \<open>\<bottom>\<close> together, so either both sides collapse or everything is componentwise.\<close>

instance sprod :: ("{filter_sum, distributive_cpo}", "{filter_sum, distributive_cpo}")
  distributive_cpo
proof
  fix a b c :: "'a \<otimes> 'b" assume "a \<Up> b"
  show "c \<sqinter> (a \<squnion> b) = c \<sqinter> a \<squnion> c \<sqinter> b"
  proof (cases "a = \<bottom> \<or> b = \<bottom> \<or> c = \<bottom>")
    case True then show ?thesis by (elim disjE) simp_all
  next
    case False
    then obtain a1 a2 b1 b2 c1 c2 where
      ab: "a = (:a1, a2:)" "b = (:b1, b2:)" "c = (:c1, c2:)" and
      nb: "a1 \<noteq> \<bottom>" "a2 \<noteq> \<bottom>" "b1 \<noteq> \<bottom>" "b2 \<noteq> \<bottom>" "c1 \<noteq> \<bottom>" "c2 \<noteq> \<bottom>"
      by (cases a; cases b; cases c) auto
    from \<open>a \<Up> b\<close> have j: "a1 \<Up> b1" "a2 \<Up> b2" by (simp_all add: ab nb spair_joinable_iff)
    have cong: "c1 \<sqinter> a1 = \<bottom> \<longleftrightarrow> c1 \<sqinter> b1 = \<bottom>" "c2 \<sqinter> a2 = \<bottom> \<longleftrightarrow> c2 \<sqinter> b2 = \<bottom>"
      using filter_sum_meet_bottom_cong[OF j(1) nb(1,3)] filter_sum_meet_bottom_cong[OF j(2) nb(2,4)]
        filter_sum_meet_bottom_cong[OF joinable_sym[THEN iffD1, OF j(1)] nb(3,1)]
        filter_sum_meet_bottom_cong[OF joinable_sym[THEN iffD1, OF j(2)] nb(4,2)]
      by blast+
    have mj: "x \<sqinter> y \<Up> x \<sqinter> z" for x y z :: "'c::bounded_complete"
      by (rule joinableI[OF meet_below1 meet_below1])
    have lhs: "c \<sqinter> (a \<squnion> b) = (:c1 \<sqinter> a1 \<squnion> c1 \<sqinter> b1, c2 \<sqinter> a2 \<squnion> c2 \<sqinter> b2:)"
      by (simp only: ab spair_join[OF nb(1,2,3,4) j] spair_meet meet_join_distrib[OF j(1)]
        meet_join_distrib[OF j(2)])
    have rhs: "c \<sqinter> a \<squnion> c \<sqinter> b = (:c1 \<sqinter> a1, c2 \<sqinter> a2:) \<squnion> (:c1 \<sqinter> b1, c2 \<sqinter> b2:)"
      by (simp only: ab spair_meet)
    show ?thesis
    proof (cases "c1 \<sqinter> a1 = \<bottom> \<or> c2 \<sqinter> a2 = \<bottom>")
      case True
      with cong show ?thesis unfolding lhs rhs by auto
    next
      case False
      with cong have "c1 \<sqinter> a1 \<noteq> \<bottom>" "c2 \<sqinter> a2 \<noteq> \<bottom>" "c1 \<sqinter> b1 \<noteq> \<bottom>" "c2 \<sqinter> b2 \<noteq> \<bottom>" by simp_all
      then show ?thesis unfolding lhs rhs by (simp add: spair_join mj)
    qed
  qed
qed

text \<open>If one component is flat, the other needs no separation: joinable nonbottom elements of a
  flat type are equal, so that component contributes no proper joins.  These cannot be
  instances (they would conflict with the arity above), so they are stated as the class law.\<close>

lemma sprod_flat_left_distrib:
  fixes a b c :: "'a::flat \<otimes> 'b::distributive_cpo"
  assumes "a \<Up> b" shows "c \<sqinter> (a \<squnion> b) = c \<sqinter> a \<squnion> c \<sqinter> b"
proof (cases "a = \<bottom> \<or> b = \<bottom> \<or> c = \<bottom>")
  case True then show ?thesis by (elim disjE) simp_all
next
  case False
  then obtain a1 a2 b1 b2 c1 c2 where
    ab: "a = (:a1, a2:)" "b = (:b1, b2:)" "c = (:c1, c2:)" and
    nb: "a1 \<noteq> \<bottom>" "a2 \<noteq> \<bottom>" "b1 \<noteq> \<bottom>" "b2 \<noteq> \<bottom>" "c1 \<noteq> \<bottom>" "c2 \<noteq> \<bottom>"
    by (cases a; cases b; cases c) auto
  from \<open>a \<Up> b\<close> have j: "a1 \<Up> b1" "a2 \<Up> b2" by (simp_all add: ab nb spair_joinable_iff)
  from j(1) nb(1,3) have "a1 = b1" by (blast elim: flat_joinableE)
  with ab(2) have b: "b = (:a1, b2:)" by simp
  have mj: "x \<sqinter> y \<Up> x \<sqinter> z" for x y z :: "'c::bounded_complete"
    by (rule joinableI[OF meet_below1 meet_below1])
  have lhs: "c \<sqinter> (a \<squnion> b) = (:c1 \<sqinter> a1, c2 \<sqinter> a2 \<squnion> c2 \<sqinter> b2:)"
    by (simp only: ab(1,3) b spair_join[OF nb(1,2,1,4) joinable_refl j(2)] spair_meet join_idem
      meet_join_distrib[OF j(2)])
  have rhs: "c \<sqinter> a \<squnion> c \<sqinter> b = (:c1 \<sqinter> a1, c2 \<sqinter> a2:) \<squnion> (:c1 \<sqinter> a1, c2 \<sqinter> b2:)"
    by (simp only: ab(1,3) b spair_meet)
  show ?thesis
  proof (cases "c1 \<sqinter> a1 = \<bottom> \<or> c2 \<sqinter> a2 = \<bottom> \<or> c2 \<sqinter> b2 = \<bottom>")
    case True then show ?thesis unfolding lhs rhs by (elim disjE) simp_all
  next    case False then show ?thesis unfolding lhs rhs by (simp add: spair_join mj)
  qed
qed

global_interpretation sprod_flat_left: distributive_cpo
  "below :: ('a::flat \<otimes> 'b::distributive_cpo) \<Rightarrow> _ \<Rightarrow> bool"
  rewrites "po.is_ub (\<sqsubseteq>) = ((<|) :: ('a \<otimes> 'b) set \<Rightarrow> _)"
    and "po.is_lub (\<sqsubseteq>) = ((<<|) :: ('a \<otimes> 'b) set \<Rightarrow> _)"
    and "po.lub (\<sqsubseteq>) = (lub :: ('a \<otimes> 'b) set \<Rightarrow> _)"
    and "po.is_glb (\<sqsubseteq>) = (is_glb :: ('a \<otimes> 'b) set \<Rightarrow> _)"
    and "po.glb (\<sqsubseteq>) = (glb :: ('a \<otimes> 'b) set \<Rightarrow> _)"
    and "po.meet (\<sqsubseteq>) = ((\<sqinter>) :: 'a \<otimes> 'b \<Rightarrow> _)"
    and "po.join (\<sqsubseteq>) = ((\<squnion>) :: 'a \<otimes> 'b \<Rightarrow> _)"
    and "bounded_complete.joinable (\<sqsubseteq>) = ((\<Up>) :: 'a \<otimes> 'b \<Rightarrow> _)"
  by unfold_locales (simp_all only: class_locale_eqs sprod_flat_left_distrib)

lemma sprod_flat_right_distrib:
  fixes a b c :: "'a::distributive_cpo \<otimes> 'b::flat"
  assumes "a \<Up> b" shows "c \<sqinter> (a \<squnion> b) = c \<sqinter> a \<squnion> c \<sqinter> b"
proof (cases "a = \<bottom> \<or> b = \<bottom> \<or> c = \<bottom>")
  case True then show ?thesis by (elim disjE) simp_all
next
  case False
  then obtain a1 a2 b1 b2 c1 c2 where
    ab: "a = (:a1, a2:)" "b = (:b1, b2:)" "c = (:c1, c2:)" and
    nb: "a1 \<noteq> \<bottom>" "a2 \<noteq> \<bottom>" "b1 \<noteq> \<bottom>" "b2 \<noteq> \<bottom>" "c1 \<noteq> \<bottom>" "c2 \<noteq> \<bottom>"
    by (cases a; cases b; cases c) auto
  from \<open>a \<Up> b\<close> have j: "a1 \<Up> b1" "a2 \<Up> b2" by (simp_all add: ab nb spair_joinable_iff)
  from j(2) nb(2,4) have "a2 = b2" by (blast elim: flat_joinableE)
  with ab(2) have b: "b = (:b1, a2:)" by simp
  have mj: "x \<sqinter> y \<Up> x \<sqinter> z" for x y z :: "'c::bounded_complete"
    by (rule joinableI[OF meet_below1 meet_below1])
  have lhs: "c \<sqinter> (a \<squnion> b) = (:c1 \<sqinter> a1 \<squnion> c1 \<sqinter> b1, c2 \<sqinter> a2:)"
    by (simp only: ab(1,3) b spair_join[OF nb(1,2,3,2) j(1) joinable_refl] spair_meet join_idem
      meet_join_distrib[OF j(1)])
  have rhs: "c \<sqinter> a \<squnion> c \<sqinter> b = (:c1 \<sqinter> a1, c2 \<sqinter> a2:) \<squnion> (:c1 \<sqinter> b1, c2 \<sqinter> a2:)"
    by (simp only: ab(1,3) b spair_meet)
  show ?thesis
  proof (cases "c2 \<sqinter> a2 = \<bottom> \<or> c1 \<sqinter> a1 = \<bottom> \<or> c1 \<sqinter> b1 = \<bottom>")
    case True then show ?thesis unfolding lhs rhs by (elim disjE) simp_all
  next
    case False then show ?thesis unfolding lhs rhs by (simp add: spair_join mj)
  qed
qed

global_interpretation sprod_flat_right: distributive_cpo
  "below :: ('a::distributive_cpo \<otimes> 'b::flat) \<Rightarrow> _ \<Rightarrow> bool"
  rewrites "po.is_ub (\<sqsubseteq>) = ((<|) :: ('a \<otimes> 'b) set \<Rightarrow> _)"
    and "po.is_lub (\<sqsubseteq>) = ((<<|) :: ('a \<otimes> 'b) set \<Rightarrow> _)"
    and "po.lub (\<sqsubseteq>) = (lub :: ('a \<otimes> 'b) set \<Rightarrow> _)"
    and "po.is_glb (\<sqsubseteq>) = (is_glb :: ('a \<otimes> 'b) set \<Rightarrow> _)"
    and "po.glb (\<sqsubseteq>) = (glb :: ('a \<otimes> 'b) set \<Rightarrow> _)"
    and "po.meet (\<sqsubseteq>) = ((\<sqinter>) :: 'a \<otimes> 'b \<Rightarrow> _)"
    and "po.join (\<sqsubseteq>) = ((\<squnion>) :: 'a \<otimes> 'b \<Rightarrow> _)"
    and "bounded_complete.joinable (\<sqsubseteq>) = ((\<Up>) :: 'a \<otimes> 'b \<Rightarrow> _)"
  by unfold_locales (simp_all only: class_locale_eqs sprod_flat_right_distrib)

end

