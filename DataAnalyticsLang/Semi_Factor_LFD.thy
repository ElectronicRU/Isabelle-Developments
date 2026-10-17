theory Semi_Factor_LFD
  imports Semi_Factor_DI LOD_Factor
begin

section \<open>Compact semi-factors over locally finitely detailed dI keys\<close>

text \<open>Over a dI-domain every compact semi-factor is a finite join of principals of compacts
  (@{thm [source] compact_semi_factor_finite_join}).  If the domain is moreover locally finitely
  detailed, the principal of a compact lies below a finitary semi-factor containing it, hence is
  finitary itself; and finite joins of finitary semi-factors are finitary.  So compact
  semi-factors project every key to a compact one.  (Without local finite detail this fails: in
  the separated sum of the powerset of the naturals and a point, the principal of the point is
  the whole domain.)\<close>

lemma compact_finite_lub:
  fixes u :: "'a::cpo"
  assumes fin: "finite C" and comp: "\<And>c. c \<in> C \<Longrightarrow> compact c" and lub: "C <<| u"
  shows "compact u"
proof (rule compactI2)
  fix Y :: "nat \<Rightarrow> 'a" assume Y: "chain Y" and uY: "u \<sqsubseteq> (\<Squnion>i. Y i)"
  have "\<exists>i. c \<sqsubseteq> Y i" if "c \<in> C" for c
    by (rule compactD2[OF comp[OF that] Y])
      (rule below_trans[OF is_ubD[OF is_lubD1[OF lub] that] uY])
  then obtain f where f: "\<And>c. c \<in> C \<Longrightarrow> c \<sqsubseteq> Y (f c)" by metis
  let ?n = "Max (insert 0 (f ` C))"
  have "c \<sqsubseteq> Y ?n" if "c \<in> C" for c
    by (rule below_trans[OF f[OF that] chain_mono[OF Y]]) (simp add: fin that)
  then have "u \<sqsubseteq> Y ?n" by (intro is_lubD2[OF lub] is_ubI)
  then show "\<exists>i. u \<sqsubseteq> Y i" by blast
qed

lemma finitary_semi_factor_below:
  "F \<sqsubseteq> G \<Longrightarrow> finitary_semi_factor G \<Longrightarrow> finitary_semi_factor F"
  unfolding finitary_semi_factor_def finitary_def
  by (metis semi_factor_p_mono stable_defl.lower_fixed[OF stable_defl_semi_factor_p])

lemma finitary_semi_factor_lub:
  assumes "finite \<A>" and "\<And>F. F \<in> \<A> \<Longrightarrow> finitary_semi_factor F"
  shows "finitary_semi_factor (lub \<A>)"
  unfolding finitary_semi_factor_def finitary_def
proof
  fix x
  show "compact (semi_factor_p (lub \<A>)\<cdot>x)"
    by (rule compact_finite_lub[OF _ _ semi_factor_p_lub_is_lub])
      (use assms in \<open>auto simp: finitary_semi_factor_def finitary_def\<close>)
qed

lemma finitary_semi_factor_principal:
  fixes k :: "'a::{dI, locally_finitely_detailed}"
  assumes "compact k"
  shows "finitary_semi_factor (semi_factor_principal k)"
proof -
  obtain F where "finitary_semi_factor F" "k \<downharpoonright> F = k" using compact_level[OF assms] by blast
  then show ?thesis
    by (blast intro: finitary_semi_factor_below semi_factor_principal_below_iff[THEN iffD2])
qed

theorem compact_finitary_semi_factor:
  fixes K :: "'a::{dI, locally_finitely_detailed} semi_factor"
  assumes "compact K"
  shows "finitary_semi_factor K"
proof -
  obtain A where A: "finite A" "A \<subseteq> {k. compact k}" "K = lub (semi_factor_principal ` A)"
    using compact_semi_factor_finite_join[OF assms] by blast
  show ?thesis unfolding A(3)
    by (rule finitary_semi_factor_lub) (use A(1,2) in \<open>auto intro: finitary_semi_factor_principal\<close>)
qed

text \<open>Projections onto compact semi-factors give compact keys; projections of compact keys are
  compact in any dI-domain, everything below a compact element being compact.\<close>

corollary compact_semi_factor_proj:
  fixes K :: "'a::{dI, locally_finitely_detailed} semi_factor"
  shows "compact K \<Longrightarrow> compact (x \<downharpoonright> K)"
  using compact_finitary_semi_factor unfolding finitary_semi_factor_def finitary_def by blast

lemma compact_proj_compact: "compact k \<Longrightarrow> compact (k \<downharpoonright> (F :: 'a::dI semi_factor))"
  by (rule compact_below_compact[OF _ deflation.below[OF deflation_semi_factor_p]])

end
