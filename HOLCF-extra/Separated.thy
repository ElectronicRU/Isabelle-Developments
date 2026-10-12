theory Separated imports Distributive begin


section \<open>Separated partial orders\<close>

text \<open>A partial order is \<^emph>\<open>separated\<close> when any two non-least elements with a common upper bound
  also have a common non-least lower bound.  No pointedness or bounded completeness is assumed;
  in a bounded-complete pcpo this says that joinable nonbottom elements have a nonbottom meet
  (@{text separated_meet} below).  Equivalently, every connected component of the punctured
  space \<open>D - {\<bottom>}\<close> is a filter, i.e. \<open>D \<cong> (\<Sigma>\<^sub>i F\<^sub>i)\<^sub>\<bottom>\<close>.  Separation is what keeps the smash product
  distributive.\<close>

class separated_po = po +
  assumes separated: "\<not> is_bot x \<Longrightarrow> \<not> is_bot y \<Longrightarrow> x \<sqsubseteq> u \<Longrightarrow> y \<sqsubseteq> u \<Longrightarrow>
    \<exists>l. \<not> is_bot l \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"

text \<open>Bounded-above non-least elements have non-least lower bounds with any third element
  together: if \<open>z\<close> has one with \<open>y\<close>, it has one with \<open>x\<close>.  No lattice operations needed.\<close>

lemma separated_lower_cong:
  fixes x y z :: "'a::separated_po"
  assumes x: "\<not> is_bot x" and xu: "x \<sqsubseteq> u" and yu: "y \<sqsubseteq> u"
    and w: "\<not> is_bot w" "w \<sqsubseteq> z" "w \<sqsubseteq> y"
  shows "\<exists>v. \<not> is_bot v \<and> v \<sqsubseteq> z \<and> v \<sqsubseteq> x"
proof -
  have "w \<sqsubseteq> u" using \<open>w \<sqsubseteq> y\<close> yu by (rule below_trans)
  from separated[OF \<open>\<not> is_bot w\<close> x this xu] obtain v where "\<not> is_bot v" "v \<sqsubseteq> w" "v \<sqsubseteq> x" by fast
  with \<open>w \<sqsubseteq> z\<close> show ?thesis by (fast dest: below_trans)
qed

subsection \<open>In pointed cpos\<close>

text \<open>In a pcpo the class axiom in simp normal form (\<open>\<noteq> \<bottom>\<close> instead of @{const is_bot}), as a
  destruction rule and as an introduction rule for instances.\<close>

lemma separated_pcpo:
  fixes x y u :: "'a::{pcpo, separated_po}"
  shows "x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> x \<sqsubseteq> u \<Longrightarrow> y \<sqsubseteq> u \<Longrightarrow> \<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
  using separated[of x y u] by simp

lemma separated_poI:
  assumes "\<And>x y u::'a::pcpo. x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> x \<sqsubseteq> u \<Longrightarrow> y \<sqsubseteq> u \<Longrightarrow> \<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
  shows "OFCLASS('a, separated_po_class)"
  by intro_classes (simp add: assms)

text \<open>Separation through any chain of maps with lub \<open>ID\<close> (e.g. the \<open>take\<close> functions of a domain):
  it suffices to separate approximants \<open>t n\<cdot>x\<close> from arbitrary \<open>y\<close>.  A nonbottom \<open>x\<close> has a
  nonbottom approximant, and a witness below it lies below \<open>x\<close>.\<close>

lemma separated_po_chainI:
  fixes t :: "nat \<Rightarrow> 'a::pcpo \<rightarrow> 'a"
  assumes t: "chain t" "(\<Squnion>i. t i) = ID"
    and sep: "\<And>n x y u. t n\<cdot>x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> t n\<cdot>x \<sqsubseteq> u \<Longrightarrow> y \<sqsubseteq> u \<Longrightarrow>
      \<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> t n\<cdot>x \<and> l \<sqsubseteq> y"
  shows "OFCLASS('a, separated_po_class)"
proof (rule separated_poI)
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

lemma separated_meet:
  fixes x y :: "'a::{separated_po, bounded_complete}"
  assumes "x \<Up> y" "x \<sqinter> y = \<bottom>" shows "x = \<bottom> \<or> y = \<bottom>"
proof -
  from \<open>x \<Up> y\<close> obtain u :: 'a where "x \<sqsubseteq> u" "y \<sqsubseteq> u" unfolding joinable_def by (elim exE conjE)
  with separated_pcpo[of x y u] \<open>x \<sqinter> y = \<bottom>\<close> show ?thesis
    by (auto simp: nonbot_meet_iff[symmetric])
qed

text \<open>Joinable nonbottom elements meet any third element to \<open>\<bottom>\<close> together.\<close>

lemma separated_meet_bottom_cong:
  fixes x y z :: "'a::{separated_po, bounded_complete}"
  assumes "x \<Up> y" "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" "z \<sqinter> x = \<bottom>" shows "z \<sqinter> y = \<bottom>"
proof (rule ccontr)
  assume "z \<sqinter> y \<noteq> \<bottom>"
  then obtain w :: 'a where w: "w \<noteq> \<bottom>" "w \<sqsubseteq> z" "w \<sqsubseteq> y"
    unfolding nonbot_meet_iff by (elim exE conjE)
  from \<open>x \<Up> y\<close> obtain u :: 'a where u: "x \<sqsubseteq> u" "y \<sqsubseteq> u" unfolding joinable_def by (elim exE conjE)
  have "\<exists>v. v \<noteq> \<bottom> \<and> v \<sqsubseteq> z \<and> v \<sqsubseteq> x"
    using separated_lower_cong[of x u y w z] \<open>x \<noteq> \<bottom>\<close> u w by simp
  then have "z \<sqinter> x \<noteq> \<bottom>" by (simp add: nonbot_meet_iff)
  with \<open>z \<sqinter> x = \<bottom>\<close> show False by simp
qed

subsection \<open>Instances\<close>

(*TODO move to bounded_complete and use there too? *)

lemma (in flat) flat_joinableE: assumes "a \<Up> b" obtains "a = \<bottom>" | "b = \<bottom>" | "a = b"
  by (metis ax_flat joinableD assms)

instance flat \<subseteq> separated_po
proof (rule separated_poI)
  fix x y u :: 'a assume "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" "x \<sqsubseteq> u" "y \<sqsubseteq> u"
  then have "x = y" by (metis ax_flat)
  with \<open>x \<noteq> \<bottom>\<close> show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y" by (intro exI[of _ x]) simp
qed

text \<open>Lifting needs no assumption on the argument beyond pointedness: \<open>up\<cdot>\<bottom>\<close> lies below every
  nonbottom element.\<close>

instance u :: (pcpo) separated_po
proof (rule separated_poI)
  fix x y u :: "'a u" assume "x \<noteq> \<bottom>" "y \<noteq> \<bottom>"
  then show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
    by (intro exI[of _ "up\<cdot>\<bottom>"]) (cases x; cases y; simp)
qed

text \<open>A common upper bound forces both elements into the same summand; separate there.\<close>

instance ssum :: ("{pcpo, separated_po}", "{pcpo, separated_po}") separated_po
proof (rule separated_poI)
  fix x y u :: "'a \<oplus> 'b" assume nb: "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" and le: "x \<sqsubseteq> u" "y \<sqsubseteq> u"
  have L: "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> (sinl\<cdot>a :: 'a \<oplus> 'b) \<and> l \<sqsubseteq> sinl\<cdot>b"
    if "a \<noteq> \<bottom>" "b \<noteq> \<bottom>" "a \<sqsubseteq> c" "b \<sqsubseteq> c" for a b c :: 'a
  proof -
    from separated_pcpo[OF that] obtain l :: 'a where "l \<noteq> \<bottom>" "l \<sqsubseteq> a" "l \<sqsubseteq> b"
      by (elim exE conjE)
    then show ?thesis by (intro exI[of _ "sinl\<cdot>l"]) simp
  qed
  have R: "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> (sinr\<cdot>a :: 'a \<oplus> 'b) \<and> l \<sqsubseteq> sinr\<cdot>b"
    if "a \<noteq> \<bottom>" "b \<noteq> \<bottom>" "a \<sqsubseteq> c" "b \<sqsubseteq> c" for a b c :: 'b
  proof -
    from separated_pcpo[OF that] obtain l :: 'b where "l \<noteq> \<bottom>" "l \<sqsubseteq> a" "l \<sqsubseteq> b"
      by (elim exE conjE)
    then show ?thesis by (intro exI[of _ "sinr\<cdot>l"]) simp
  qed
  show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
    using nb le by (cases x; cases y; cases u) (auto intro: L R)
qed

text \<open>Componentwise: the pair of the two components' witnesses.\<close>

instance sprod :: ("{pcpo, separated_po}", "{pcpo, separated_po}") separated_po
proof (rule separated_poI)
  fix x y u :: "'a \<otimes> 'b" assume nb: "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" and le: "x \<sqsubseteq> u" "y \<sqsubseteq> u"
  have S: "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> (:a, b:) \<and> l \<sqsubseteq> (:a', b':)"
    if "a \<noteq> \<bottom>" "b \<noteq> \<bottom>" "a' \<noteq> \<bottom>" "b' \<noteq> \<bottom>" "a \<sqsubseteq> c" "a' \<sqsubseteq> c" "b \<sqsubseteq> d" "b' \<sqsubseteq> d"
    for a a' c :: 'a and b b' d :: 'b
  proof -
    from separated_pcpo[OF \<open>a \<noteq> \<bottom>\<close> \<open>a' \<noteq> \<bottom>\<close> \<open>a \<sqsubseteq> c\<close> \<open>a' \<sqsubseteq> c\<close>]
    obtain la :: 'a where "la \<noteq> \<bottom>" "la \<sqsubseteq> a" "la \<sqsubseteq> a'" by (elim exE conjE)
    moreover from separated_pcpo[OF \<open>b \<noteq> \<bottom>\<close> \<open>b' \<noteq> \<bottom>\<close> \<open>b \<sqsubseteq> d\<close> \<open>b' \<sqsubseteq> d\<close>]
    obtain lb :: 'b where "lb \<noteq> \<bottom>" "lb \<sqsubseteq> b" "lb \<sqsubseteq> b'" by (elim exE conjE)
    ultimately show ?thesis using that by (intro exI[of _ "(:la, lb:)"]) (simp add: spair_below)
  qed
  show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
    using nb le by (cases x; cases y; cases u) (auto simp: spair_below intro: S)
qed

section \<open>Distributivity of smash products\<close>

text \<open>Separation of both components keeps \<open>\<otimes>\<close> distributive: joinable nonbottom pairs meet a third
  pair to \<open>\<bottom>\<close> together, so either both sides collapse or everything is componentwise.\<close>

instance sprod :: ("{separated_po, distributive_cpo}", "{separated_po, distributive_cpo}")
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
      using separated_meet_bottom_cong[OF j(1) nb(1,3)] separated_meet_bottom_cong[OF j(2) nb(2,4)]
        separated_meet_bottom_cong[OF joinable_sym[THEN iffD1, OF j(1)] nb(3,1)]
        separated_meet_bottom_cong[OF joinable_sym[THEN iffD1, OF j(2)] nb(4,2)]
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

