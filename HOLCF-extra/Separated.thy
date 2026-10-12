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

end

