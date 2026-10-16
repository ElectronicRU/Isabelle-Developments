theory DI imports Filter_Sum begin

section \<open>dI-domains\<close>

text \<open>A \<^emph>\<open>dI-domain\<close> (Berry) is a distributive bifinite domain with property I: every compact
  element has finitely many elements below it.  Everything below a compact element is then
  compact itself.\<close>

class dI = bifinite + distributive_cpo +
  assumes finite_below_compact: "compact k \<Longrightarrow> finite {x. x \<sqsubseteq> k}"

lemma compact_below_compact:
  fixes x :: "'a::dI"
  assumes k: "compact k" and xk: "x \<sqsubseteq> k"
  shows "compact x"
proof -
  obtain a :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where a: "approx_chain a" using bifinite by blast
  interpret approx_chain a by (fact a)
  let ?Y = "\<lambda>i. a i\<cdot>x"
  have ch: "chain ?Y" by (rule ch2ch_Rep_cfunL[OF chain_approx])
  have "range ?Y \<subseteq> {y. y \<sqsubseteq> k}" using approx_below xk by (blast intro: below_trans)
  then have "finite (range ?Y)" by (rule finite_subset) (rule finite_below_compact[OF k])
  then obtain i where "max_in_chain i ?Y"
    using finite_range_imp_finch[OF ch] unfolding finite_chain_def by blast
  then have l: "(\<Squnion>j. ?Y j) = ?Y i" using maxinch_is_thelub[OF ch] by blast
  have "(\<Squnion>j. ?Y j) = x" by (simp add: contlub_cfun_fun[OF chain_approx, symmetric])
  with l have "x = a i\<cdot>x" by simp
  then show ?thesis by (metis compact_approx)
qed

subsection \<open>Transfer along isomorphisms\<close>

text \<open>Domain types are dI-domains when their representation is: the derivation machinery for
  map functions does not apply, since property I is not preserved by recursion.\<close>

lemma dI_iso:
  fixes abs :: "'r::dI \<rightarrow> 't::{bifinite, distributive_cpo}" and rep
  assumes "iso abs rep" shows "OFCLASS('t, dI_class)"
proof (intro_classes)
  fix k :: 't assume "compact k"
  then have c: "compact (rep\<cdot>k)" by (rule iso.compact_rep[OF assms])
  have "{x. x \<sqsubseteq> k} \<subseteq> (\<lambda>y. abs\<cdot>y) ` {y. y \<sqsubseteq> rep\<cdot>k}"
  proof
    fix x assume "x \<in> {x. x \<sqsubseteq> k}"
    then have "rep\<cdot>x \<sqsubseteq> rep\<cdot>k" by (simp add: monofun_cfun_arg)
    moreover have "x = abs\<cdot>(rep\<cdot>x)" by (simp add: iso.rep_iso[OF assms])
    ultimately show "x \<in> (\<lambda>y. abs\<cdot>y) ` {y. y \<sqsubseteq> rep\<cdot>k}" by blast
  qed
  then show "finite {x. x \<sqsubseteq> k}"
    by (rule finite_subset) (rule finite_imageI[OF finite_below_compact[OF c]])
qed

subsection \<open>Instances\<close>

text \<open>Flat domains have at most two elements below anything.\<close>

instance lift :: (countable) dI
proof
  fix k :: "'a lift"
  show "finite {x. x \<sqsubseteq> k}"
    by (rule finite_subset[of _ "{\<bottom>, k}"]) (auto dest: flat_eq)
qed

text \<open>Lifting adds one element below everything.\<close>

instance u :: (dI) dI
proof
  fix k :: "'a u" assume k: "compact k"
  show "finite {x. x \<sqsubseteq> k}"
  proof (cases k rule: upE)
    case bottom
    then show ?thesis by simp
  next
    case (up a)
    with k have a: "compact a" by simp
    have "{x. x \<sqsubseteq> k} \<subseteq> insert \<bottom> ((\<lambda>z. up\<cdot>z) ` {z. z \<sqsubseteq> a})"
    proof
      fix x assume "x \<in> {x. x \<sqsubseteq> k}"
      with up show "x \<in> insert \<bottom> ((\<lambda>z. up\<cdot>z) ` {z. z \<sqsubseteq> a})" by (cases x rule: upE) auto
    qed
    then show ?thesis
      by (rule finite_subset) (simp add: finite_below_compact[OF a])
  qed
qed

text \<open>Below an injection lie the injections of what lies below its argument.\<close>

instance ssum :: (dI, dI) dI
proof
  fix k :: "'a \<oplus> 'b" assume k: "compact k"
  show "finite {x. x \<sqsubseteq> k}"
  proof (cases k rule: ssumE)
    case bottom
    then show ?thesis by simp
  next
    case (sinl a)
    with k have a: "compact a" by simp
    have "{x. x \<sqsubseteq> k} \<subseteq> (\<lambda>z. sinl\<cdot>z) ` {z. z \<sqsubseteq> a}"
    proof
      fix x assume "x \<in> {x. x \<sqsubseteq> k}"
      with sinl show "x \<in> (\<lambda>z. sinl\<cdot>z) ` {z. z \<sqsubseteq> a}"
        by (cases x rule: ssumE) (auto intro: image_eqI[where x = \<bottom>])
    qed
    then show ?thesis by (rule finite_subset) (simp add: finite_below_compact[OF a])
  next
    case (sinr b)
    with k have b: "compact b" by simp
    have "{x. x \<sqsubseteq> k} \<subseteq> (\<lambda>z. sinr\<cdot>z) ` {z. z \<sqsubseteq> b}"
    proof
      fix x assume "x \<in> {x. x \<sqsubseteq> k}"
      with sinr show "x \<in> (\<lambda>z. sinr\<cdot>z) ` {z. z \<sqsubseteq> b}"
        by (cases x rule: ssumE) (auto intro: image_eqI[where x = \<bottom>])
    qed
    then show ?thesis by (rule finite_subset) (simp add: finite_below_compact[OF b])
  qed
qed

text \<open>Below a pair lie the pairs of what lies below its components.\<close>

instance prod :: (dI, dI) dI
proof
  fix k :: "'a \<times> 'b" assume k: "compact k"
  obtain a b where ab: "k = (a, b)" by (cases k)
  with k have a: "compact a" and b: "compact b" by simp_all
  have "{x. x \<sqsubseteq> k} \<subseteq> {z. z \<sqsubseteq> a} \<times> {z. z \<sqsubseteq> b}"
    using ab by (auto simp: below_prod_def)
  then show "finite {x. x \<sqsubseteq> k}"
    by (rule finite_subset) (simp add: finite_below_compact[OF a] finite_below_compact[OF b])
qed

text \<open>Strict products are distributive over filter-sum factors (see \<open>Filter_Sum\<close>).\<close>

instance sprod :: ("{filter_sum, dI}", "{filter_sum, dI}") dI
proof
  fix k :: "'a \<otimes> 'b" assume k: "compact k"
  show "finite {x. x \<sqsubseteq> k}"
  proof (cases k rule: sprodE)
    case bottom
    then show ?thesis by simp
  next
    case (spair a b)
    with k have a: "compact a" and b: "compact b" by (simp_all add: compact_spair_iff)
    have "{x. x \<sqsubseteq> k} \<subseteq> (\<lambda>(y, z). (:y, z:)) ` ({y. y \<sqsubseteq> a} \<times> {z. z \<sqsubseteq> b})"
    proof
      fix x assume x: "x \<in> {x. x \<sqsubseteq> k}"
      show "x \<in> (\<lambda>(y, z). (:y, z:)) ` ({y. y \<sqsubseteq> a} \<times> {z. z \<sqsubseteq> b})"
      proof (cases x rule: sprodE)
        case bottom
        then show ?thesis
          by (intro image_eqI[where x = "(\<bottom> :: 'a, \<bottom> :: 'b)"]) (simp_all add: mem_Times_iff)
      next
        case (spair c d)
        with x \<open>k = (:a, b:)\<close> have "c \<sqsubseteq> a" "d \<sqsubseteq> b" by (simp_all add: spair_below)
        with spair show ?thesis by (intro image_eqI[where x = "(c, d)"]) simp_all
      qed
    qed
    then show ?thesis
      by (rule finite_subset) (simp add: finite_below_compact[OF a] finite_below_compact[OF b])
  qed
qed

end
