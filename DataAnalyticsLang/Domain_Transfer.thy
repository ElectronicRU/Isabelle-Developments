theory Domain_Transfer
  imports LOD_Factor "HOLCF-extra.Domain_Order"
begin

section \<open>Transferring the classes along domain isomorphisms\<close>

text \<open>The domain package presents each domain as isomorphic, through \<open>abs\<close> and \<open>rep\<close> satisfying
  the laws of @{locale iso}, to a combination of its constructor arguments.  The order-theoretic
  transfer (bounds, lubs, meets; @{text bounded_complete_iso}, @{text distributive_cpo_iso}) is in
  \<open>HOLCF-extra.Domain_Order\<close>; here, compactness and semi-factors, so that the level-of-detail
  classes transfer as well.\<close>


subsection \<open>Levels of detail\<close>

text \<open>The image of a semi-factor under the isomorphism is a semi-factor, with projection
  \<open>abs \<circ> p \<circ> rep\<close>; it is finitary, and faithful, when the original is.\<close>

lemma semi_factor_subdomain_iso:
  fixes abs :: "'r::{bifinite, distributive_cpo} \<rightarrow> 't::{bifinite, distributive_cpo}" and rep
  assumes "iso abs rep" "semi_factor_subdomain S"
  shows "semi_factor_subdomain {y. abs\<cdot>(stable_subdomain.p S\<cdot>(rep\<cdot>y)) = y}"
proof -
  interpret iso abs rep by fact
  note ss = semi_factor_subdomain.axioms(1)[OF assms(2)]
  let ?D = "abs oo stable_subdomain.p S oo rep"
  have fixD: "?D\<cdot>y = y \<longleftrightarrow> rep\<cdot>y \<in> S" for y
    using stable_subdomain.p_fixed_iff[OF ss, of "rep\<cdot>y"] by (metis abs_iso rep_iso cfcomp2)
  have "semi_factor_subdomain {y. ?D\<cdot>y = y}"
  proof (rule semi_factor_subdomain_deflationI)
    show "deflation ?D"
      by (rule deflation_abs_rep[OF abs_iso rep_iso stable_subdomain.deflation_p[OF ss]])
  next
    fix x y assume "?D\<cdot>y = y" "x \<sqsubseteq> y"
    then show "?D\<cdot>x = x"
      unfolding fixD by (auto simp: rep_below intro: stable_subdomain.downward[OF ss])
  next
    fix x y assume y: "?D\<cdot>y = y" and le: "?D\<cdot>x \<sqsubseteq> y"
    have "rep\<cdot>(?D\<cdot>x) \<sqsubseteq> rep\<cdot>y" using le by (rule monofun_cfun_arg)
    then have "stable_subdomain.p S\<cdot>(rep\<cdot>x) \<sqsubseteq> rep\<cdot>y" by simp
    with y have "rep\<cdot>x \<Up> rep\<cdot>y" unfolding fixD by (rule semi_factor_subdomain.slide_rule[OF assms(2)])
    then show "x \<Up> y" by (simp add: iso_rep_joinable_iff[OF assms(1)])
  qed
  then show ?thesis by simp
qed

lemma iso_home:
  fixes abs :: "'r::{bifinite, distributive_cpo} \<rightarrow> 't::{bifinite, distributive_cpo}" and rep
  assumes iso: "iso abs rep" and S: "semi_factor_subdomain S" "\<forall>x\<in>S. compact x"
  defines "H \<equiv> {y. abs\<cdot>(stable_subdomain.p S\<cdot>(rep\<cdot>y)) = y}"
  shows "semi_factor_subdomain H" "\<forall>y\<in>H. compact y" "rep\<cdot>k \<in> S \<Longrightarrow> k \<in> H"
    "faithful S \<Longrightarrow> faithful H"
proof -
  interpret iso abs rep by fact
  note ss = semi_factor_subdomain.axioms(1)[OF S(1)]
  let ?D = "abs oo stable_subdomain.p S oo rep"
  have mem: "y \<in> H \<longleftrightarrow> rep\<cdot>y \<in> S" for y
  proof -
    have "abs\<cdot>(stable_subdomain.p S\<cdot>(rep\<cdot>y)) = y \<longleftrightarrow> stable_subdomain.p S\<cdot>(rep\<cdot>y) = rep\<cdot>y"
      by (subst eq_commute, subst iso_swap, rule eq_commute)
    then show ?thesis unfolding H_def by (simp add: stable_subdomain.p_fixed_iff[OF ss])
  qed
  have Hd: "H = {y. ?D\<cdot>y = y}" by (simp add: H_def)
  show sH: "semi_factor_subdomain H" unfolding H_def by (rule semi_factor_subdomain_iso[OF iso S(1)])
  show "\<forall>y\<in>H. compact y" using S(2) mem compact_rep_rev by blast
  show "rep\<cdot>k \<in> S \<Longrightarrow> k \<in> H" by (simp add: mem)
  assume fS: "faithful S"
  have pH: "stable_subdomain.p H = ?D"
  proof -
    have "stable_subdomain {y. ?D\<cdot>y = y}" using semi_factor_subdomain.axioms(1)[OF sH] by (simp add: Hd)
    with deflation_abs_rep[OF abs_iso rep_iso stable_subdomain.deflation_p[OF ss]]
    have "?D = stable_subdomain.p {y. ?D\<cdot>y = y}" by (rule stable_subdomain_deflation)
    then show ?thesis unfolding Hd by (rule sym)
  qed
  show "faithful H" unfolding faithful_def pH
  proof (intro allI impI)
    fix b assume "?D\<cdot>b = \<bottom>"
    then have "stable_subdomain.p S\<cdot>(rep\<cdot>b) = \<bottom>" by (simp add: abs_bottom_iff)
    with fS have "rep\<cdot>b = \<bottom>" unfolding faithful_def by blast
    then show "b = \<bottom>" by (simp add: rep_bottom_iff)
  qed
qed

lemma locally_finitely_detailed_iso:
  fixes abs :: "'r::locally_finitely_detailed \<rightarrow> 't::{bifinite, distributive_cpo}" and rep
  assumes "iso abs rep" shows "OFCLASS('t, locally_finitely_detailed_class)"
proof intro_classes
  interpret iso abs rep by fact
  fix k :: 't assume "compact k"
  then have "compact (rep\<cdot>k)" by (rule compact_rep)
  from compact_home_set[OF this]
  obtain S :: "'r set" where S: "semi_factor_subdomain S" "\<forall>x\<in>S. compact x" "rep\<cdot>k \<in> S"
    by (elim exE conjE) (rule that)
  show "\<exists>S. semi_factor_subdomain S \<and> (\<forall>x\<in>S. compact x) \<and> k \<in> S"
    using iso_home(1,2)[OF assms S(1,2)] iso_home(3)[OF assms S(1,2) S(3)] by blast
qed

lemma faithfully_finitely_detailed_iso:
  fixes abs :: "'r::faithfully_finitely_detailed \<rightarrow> 't::{bifinite, distributive_cpo}" and rep
  assumes "iso abs rep" shows "OFCLASS('t, faithfully_finitely_detailed_class)"
proof (rule faithfully_finitely_detailedI)
  interpret iso abs rep by fact
  fix k :: 't assume "compact k"
  then have "compact (rep\<cdot>k)" by (rule compact_rep)
  from compact_faithful_home[OF this]
  obtain S :: "'r set"
    where S: "semi_factor_subdomain S" "\<forall>x\<in>S. compact x" "faithful S" "rep\<cdot>k \<in> S"
    by (elim exE conjE) (rule that)
  show "\<exists>S. semi_factor_subdomain S \<and> (\<forall>x\<in>S. compact x) \<and> faithful S \<and> k \<in> S"
    using iso_home(1,2)[OF assms S(1,2)] iso_home(3)[OF assms S(1,2) S(4)]
      iso_home(4)[OF assms S(1,2) S(3)] by blast
qed

section \<open>Example: a non-recursive domain\<close>

text \<open>A lazy binary sum is represented by \<open>'a u \<oplus> 'b u\<close>; every class transfers from the
  combinator instances.\<close>

domain ('a::"domain", 'b::"domain") either = L (lazy 'a) | R (lazy 'b)

lemma either_iso: "iso either_abs either_rep"
  by unfold_locales (rule either.abs_iso, rule either.rep_iso)

instance either :: ("{domain, bounded_complete}", "{domain, bounded_complete}") bounded_complete
  by (rule bounded_complete_iso[OF either_iso])

instance either :: ("{domain, distributive_cpo}", "{domain, distributive_cpo}") distributive_cpo
  by (rule distributive_cpo_iso[OF either_iso])

instance either :: ("{domain, locally_finitely_detailed}", "{domain, locally_finitely_detailed}")
  faithfully_finitely_detailed
  by (rule faithfully_finitely_detailed_iso[OF either_iso])

end
