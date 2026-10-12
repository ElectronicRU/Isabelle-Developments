theory Domain_Transfer
  imports LOD_Factor
begin

section \<open>Transferring the classes along domain isomorphisms\<close>

text \<open>The domain package presents each domain as isomorphic, through \<open>abs\<close> and \<open>rep\<close> satisfying
  the laws of @{locale iso}, to a combination of its constructor arguments.  An isomorphism of
  pointed cpos is an order isomorphism, so it preserves bounds, lubs and meets, compactness and
  semi-factors; all our classes transfer along it.\<close>

subsection \<open>Order-theoretic transfer\<close>

lemma iso_is_ub_iff:
  fixes abs :: "'r::pcpo \<rightarrow> 't::pcpo" and rep
  assumes "iso abs rep" shows "(\<lambda>x. rep\<cdot>x) ` A <| l \<longleftrightarrow> A <| abs\<cdot>l"
proof -
  interpret iso abs rep by fact
  have "x \<sqsubseteq> abs\<cdot>l \<longleftrightarrow> rep\<cdot>x \<sqsubseteq> l" for x by (subst rep_below[symmetric]) simp
  then show ?thesis unfolding is_ub_def by auto
qed

lemma iso_is_lub_iff:
  fixes abs :: "'r::pcpo \<rightarrow> 't::pcpo" and rep
  assumes "iso abs rep" shows "(\<lambda>x. rep\<cdot>x) ` A <<| l \<longleftrightarrow> A <<| abs\<cdot>l"
proof -
  interpret iso abs rep by fact
  note ub = iso_is_ub_iff[OF assms]
  show ?thesis
  proof
    assume l: "(\<lambda>x. rep\<cdot>x) ` A <<| l"
    show "A <<| abs\<cdot>l"
    proof (rule is_lubI)
      show "A <| abs\<cdot>l" using is_lubD1[OF l] ub by blast
      fix u assume "A <| u"
      then have "(\<lambda>x. rep\<cdot>x) ` A <| rep\<cdot>u" using ub[of A "rep\<cdot>u"] by simp
      with l have "l \<sqsubseteq> rep\<cdot>u" by (rule is_lubD2)
      then have "abs\<cdot>l \<sqsubseteq> abs\<cdot>(rep\<cdot>u)" by (rule monofun_cfun_arg)
      then show "abs\<cdot>l \<sqsubseteq> u" by simp
    qed
  next
    assume l: "A <<| abs\<cdot>l"
    show "(\<lambda>x. rep\<cdot>x) ` A <<| l"
    proof (rule is_lubI)
      show "(\<lambda>x. rep\<cdot>x) ` A <| l" using is_lubD1[OF l] ub by blast
      fix v assume "(\<lambda>x. rep\<cdot>x) ` A <| v"
      then have "A <| abs\<cdot>v" using ub by blast
      with l have "abs\<cdot>l \<sqsubseteq> abs\<cdot>v" by (rule is_lubD2)
      then show "l \<sqsubseteq> v" by (simp add: abs_below)
    qed
  qed
qed

subsection \<open>Bounded completeness and distributivity\<close>

lemma bounded_complete_iso:
  fixes abs :: "'r::bounded_complete \<rightarrow> 't::pcpo" and rep
  assumes "iso abs rep" shows "OFCLASS('t, bounded_complete_class)"
proof intro_classes
  interpret iso abs rep by fact
  fix A :: "'t set" and b assume ne: "A \<noteq> {}" and ub: "A <| b"
  from ub have "(\<lambda>x. rep\<cdot>x) ` A <| rep\<cdot>b" using iso_is_ub_iff[OF assms, of A "rep\<cdot>b"] by simp
  with ne obtain l where "(\<lambda>x. rep\<cdot>x) ` A <<| l" using ex_bound_ne_ex_lub by blast
  then have "A <<| abs\<cdot>l" using iso_is_lub_iff[OF assms] by blast
  then show "\<exists>a. A <<| a" ..
qed

lemma iso_rep_meet:
  fixes abs :: "'r::bounded_complete \<rightarrow> 't::bounded_complete" and rep
  assumes "iso abs rep" shows "rep\<cdot>(x \<sqinter> y) = rep\<cdot>x \<sqinter> rep\<cdot>y"
proof (rule below_antisym)
  interpret iso abs rep by fact
  show "rep\<cdot>(x \<sqinter> y) \<sqsubseteq> rep\<cdot>x \<sqinter> rep\<cdot>y"
    by (intro meet_greatest monofun_cfun_arg meet_below1 meet_below2)
  have "abs\<cdot>(rep\<cdot>x \<sqinter> rep\<cdot>y) \<sqsubseteq> abs\<cdot>(rep\<cdot>x)" "abs\<cdot>(rep\<cdot>x \<sqinter> rep\<cdot>y) \<sqsubseteq> abs\<cdot>(rep\<cdot>y)"
    by (intro monofun_cfun_arg meet_below1 meet_below2)+
  then have "abs\<cdot>(rep\<cdot>x \<sqinter> rep\<cdot>y) \<sqsubseteq> x \<sqinter> y" by (simp add: meet_greatest)
  then show "rep\<cdot>x \<sqinter> rep\<cdot>y \<sqsubseteq> rep\<cdot>(x \<sqinter> y)" by (simp add: iso_swap[symmetric] abs_below[symmetric])
qed

lemma iso_rep_joinable_iff:
  fixes abs :: "'r::bounded_complete \<rightarrow> 't::bounded_complete" and rep
  assumes "iso abs rep" shows "rep\<cdot>x \<Up> rep\<cdot>y \<longleftrightarrow> x \<Up> y"
proof
  interpret iso abs rep by fact
  assume "rep\<cdot>x \<Up> rep\<cdot>y"
  then obtain z where zx: "rep\<cdot>x \<sqsubseteq> z" and zy: "rep\<cdot>y \<sqsubseteq> z" unfolding joinable_def by blast
  have "abs\<cdot>(rep\<cdot>x) \<sqsubseteq> abs\<cdot>z" using zx by (rule monofun_cfun_arg)
  moreover have "abs\<cdot>(rep\<cdot>y) \<sqsubseteq> abs\<cdot>z" using zy by (rule monofun_cfun_arg)
  ultimately show "x \<Up> y" by (simp add: joinableI)
next
  interpret iso abs rep by fact
  assume "x \<Up> y"
  then obtain z where "x \<sqsubseteq> z" "y \<sqsubseteq> z" unfolding joinable_def by blast
  then have "rep\<cdot>x \<sqsubseteq> rep\<cdot>z" "rep\<cdot>y \<sqsubseteq> rep\<cdot>z" by (simp_all add: monofun_cfun_arg)
  then show "rep\<cdot>x \<Up> rep\<cdot>y" by (rule joinableI)
qed

lemma iso_rep_join:
  fixes abs :: "'r::bounded_complete \<rightarrow> 't::bounded_complete" and rep
  assumes "iso abs rep" "x \<Up> y" shows "rep\<cdot>(x \<squnion> y) = rep\<cdot>x \<squnion> rep\<cdot>y"
proof (rule below_antisym)
  interpret iso abs rep by fact
  have j: "rep\<cdot>x \<Up> rep\<cdot>y" using iso_rep_joinable_iff[OF assms(1)] assms(2) by simp
  have "abs\<cdot>(rep\<cdot>x) \<sqsubseteq> abs\<cdot>(rep\<cdot>x \<squnion> rep\<cdot>y)" "abs\<cdot>(rep\<cdot>y) \<sqsubseteq> abs\<cdot>(rep\<cdot>x \<squnion> rep\<cdot>y)"
    by (rule monofun_cfun_arg[OF joinableD(1)[OF j]], rule monofun_cfun_arg[OF joinableD(2)[OF j]])
  then have "x \<squnion> y \<sqsubseteq> abs\<cdot>(rep\<cdot>x \<squnion> rep\<cdot>y)" by (simp add: join_belowI)
  then show "rep\<cdot>(x \<squnion> y) \<sqsubseteq> rep\<cdot>x \<squnion> rep\<cdot>y" by (simp add: iso_swap[symmetric] rep_below[symmetric])
  have "rep\<cdot>x \<sqsubseteq> rep\<cdot>(x \<squnion> y)" "rep\<cdot>y \<sqsubseteq> rep\<cdot>(x \<squnion> y)"
    by (rule monofun_cfun_arg[OF joinableD(1)[OF assms(2)]],
        rule monofun_cfun_arg[OF joinableD(2)[OF assms(2)]])
  then show "rep\<cdot>x \<squnion> rep\<cdot>y \<sqsubseteq> rep\<cdot>(x \<squnion> y)" by (rule join_belowI)
qed

lemma distributive_cpo_iso:
  fixes abs :: "'r::distributive_cpo \<rightarrow> 't::bounded_complete" and rep
  assumes "iso abs rep" shows "OFCLASS('t, distributive_cpo_class)"
proof intro_classes
  interpret iso abs rep by fact
  fix a b c :: 't assume ab: "a \<Up> b"
  have cab: "c \<sqinter> a \<Up> c \<sqinter> b" by (rule joinableI[OF meet_below1 meet_below1])
  have "rep\<cdot>(c \<sqinter> (a \<squnion> b)) = rep\<cdot>c \<sqinter> (rep\<cdot>a \<squnion> rep\<cdot>b)"
    by (simp add: iso_rep_meet[OF assms] iso_rep_join[OF assms ab])
  also have "\<dots> = (rep\<cdot>c \<sqinter> rep\<cdot>a) \<squnion> (rep\<cdot>c \<sqinter> rep\<cdot>b)"
    using ab by (simp add: meet_join_distrib iso_rep_joinable_iff[OF assms])
  also have "\<dots> = rep\<cdot>(c \<sqinter> a \<squnion> (c \<sqinter> b))"
    by (simp add: iso_rep_meet[OF assms] iso_rep_join[OF assms cab])
  finally show "c \<sqinter> (a \<squnion> b) = c \<sqinter> a \<squnion> (c \<sqinter> b)" by (simp add: rep_eq)
qed

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
