theory LOD_Factor
  imports LOD
begin

section \<open>Finitary semi-factors as levels of detail\<close>

text \<open>A semi-factor is \<^emph>\<open>finitary\<close> when all its elements are compact (equivalently, as a
  subdomain it has finite height): its projection takes every element, however large, to a
  compact one.  Finitary semi-factors are closed under meets (intersection), joins (pointwise
  joins of compacts) and contain the bottom semi-factor.\<close>

lemma compact_join:
  fixes x y :: "'a::bounded_complete"
  assumes x: "compact x" and y: "compact y" and xy: "x \<Up> y"
  shows "compact (x \<squnion> y)"
proof (rule compactI2)
  fix Y :: "nat \<Rightarrow> 'a" assume Y: "chain Y" and le: "x \<squnion> y \<sqsubseteq> (\<Squnion>i. Y i)"
  from le joinableD[OF xy] have "x \<sqsubseteq> (\<Squnion>i. Y i)" "y \<sqsubseteq> (\<Squnion>i. Y i)"
    by (blast intro: below_trans)+
  then obtain i j where "x \<sqsubseteq> Y i" "y \<sqsubseteq> Y j"
    using compactD2[OF x Y] compactD2[OF y Y] by blast
  then have "x \<sqsubseteq> Y (max i j)" "y \<sqsubseteq> Y (max i j)"
    using chain_mono[OF Y] by (blast intro: below_trans max.cobounded1 max.cobounded2)+
  then show "\<exists>i. x \<squnion> y \<sqsubseteq> Y i" by (blast intro: join_belowI)
qed

default_sort "{bifinite, distributive_cpo}"

definition finitary :: "'a semi_factor \<Rightarrow> bool" where
  "finitary F \<longleftrightarrow> (\<forall>x \<in> set_of_factor F. compact x)"

lemma finitary_bot: "finitary bot"
  unfolding finitary_def by (auto dest!: semi_factor.p_fixed[where A=bot] simp: semi_factor_p_bot)

lemma finitary_inf: "finitary F \<Longrightarrow> finitary (inf F G)"
  unfolding finitary_def
proof (intro ballI)
  fix x assume F: "\<forall>x \<in> set_of_factor F. compact x" and x: "x \<in> set_of_factor (inf F G)"
  have "x \<downharpoonright> F = x \<downharpoonright> inf F G \<downharpoonright> F" by (simp only: semi_factor.p_fixed[OF x])
  also have "\<dots> = x \<downharpoonright> inf F G" by (simp only: semi_factor_proj_comp inf.absorb1[OF inf.cobounded1])
  also have "\<dots> = x" by (rule semi_factor.p_fixed[OF x])
  finally show "compact x" using F semi_factor.p_fixed_iff by blast
qed

lemma finitary_sup: "finitary F \<Longrightarrow> finitary G \<Longrightarrow> finitary (sup F G)"
  unfolding finitary_def
proof (intro ballI)
  fix x assume F: "\<forall>x \<in> set_of_factor F. compact x" and G: "\<forall>x \<in> set_of_factor G. compact x"
    and x: "x \<in> set_of_factor (sup F G)"
  have "x = x \<downharpoonright> F \<squnion> x \<downharpoonright> G"
    using semi_factor.p_fixed[OF x] by (simp add: semi_factor_p_sup)
  moreover have "x \<downharpoonright> F \<Up> x \<downharpoonright> G"
    by (rule joinableI) (rule semi_factor.proj_below[unfolded semi_factor.p_beta[symmetric]])+
  ultimately show "compact x"
    using F G semi_factor.p_in_S by (metis compact_join)
qed

text \<open>A domain is \<^emph>\<open>locally finitely detailed\<close> when every compact element lives at some finite
  level of detail, i.e.\ lies in a finitary semi-factor: every finite piece of information has a
  finite, self-contained home.  This is the semi-factor analogue of property I of dI-domains
  (for stable subdomains the least home of a compact \<open>k\<close> is \<open>\<down>k\<close>, and a distributive lattice of
  finite height is finite), and strictly stronger.  (Compare also Libkin's requirement that the
  compact elements -- the storable objects -- form an ideal.)\<close>

default_sort type

class locally_finitely_detailed = bifinite + distributive_cpo +
  assumes compact_home_set: "compact k \<Longrightarrow> \<exists>S. semi_factor_subdomain S \<and> (\<forall>x\<in>S. compact x) \<and> k \<in> S"

lemma compact_home:
  fixes k :: "'a::locally_finitely_detailed"
  assumes "compact k"
  obtains F :: "'a semi_factor" where "finitary F" "k \<in> set_of_factor F"
proof -
  from compact_home_set[OF assms] obtain S
    where S: "semi_factor_subdomain S" "\<forall>x\<in>S. compact x" "k \<in> S" by blast
  let ?A = "subdom_of_set S"
  have A: "set_of_subdom ?A = S"
    using semi_factor_subdomain.axioms(1)[OF S(1)] by (simp add: stable_subdom.subdom_of_set_inverse)
  with S(1) have "is_semi_factor ?A" by (simp add: is_semi_factor_def)
  then have "set_of_factor (factor_of_subdom ?A) = S"
    by (simp add: set_of_factor.abs_eq eq_onp_same_args A)
  with S show thesis by (intro that[of "factor_of_subdom ?A"]) (simp_all add: finitary_def)
qed

typedef (overloaded) 'a lod = "{F :: 'a::{bifinite, distributive_cpo} semi_factor. finitary F}"
  morphisms factor_of_lod lod_of_factor
  using finitary_bot by blast

setup_lifting type_definition_lod

instantiation lod :: ("{bifinite, distributive_cpo}") "{distrib_lattice, bounded_lattice_bot}"
begin

lift_definition less_eq_lod :: "'a lod \<Rightarrow> 'a lod \<Rightarrow> bool" is "(\<le>)" .
lift_definition less_lod :: "'a lod \<Rightarrow> 'a lod \<Rightarrow> bool" is "(<)" .
lift_definition inf_lod :: "'a lod \<Rightarrow> 'a lod \<Rightarrow> 'a lod" is inf by (rule finitary_inf)
lift_definition sup_lod :: "'a lod \<Rightarrow> 'a lod \<Rightarrow> 'a lod" is sup by (rule finitary_sup)
lift_definition bot_lod :: "'a lod" is bot by (rule finitary_bot)

instance
  apply (standard; transfer; simp add: less_le_not_le)
  apply (standard; transfer)
  apply (simp_all add: less_le_not_le)
  by (rule sup_inf_distrib1)

end

interpretation lod: lod_space "\<lambda>F. semi_factor_p (factor_of_lod F) :: 'a::locally_finitely_detailed \<rightarrow> 'a"
proof unfold_locales
  fix a b :: "'a lod" and k x y :: 'a
  show "k \<downharpoonright> factor_of_lod (inf a b) = k \<downharpoonright> factor_of_lod b \<downharpoonright> factor_of_lod a"
    by (simp add: inf_lod.rep_eq semi_factor_proj_comp inf_commute)
  show "k \<downharpoonright> factor_of_lod (sup a b) = k \<downharpoonright> factor_of_lod a \<squnion> k \<downharpoonright> factor_of_lod b"
    by (simp add: sup_lod.rep_eq semi_factor_p_sup)
  show "semi_factor_p (factor_of_lod bot) = \<bottom>"
    by (simp add: bot_lod.rep_eq semi_factor_p_bot)
  show "x \<Up> y" if "y \<downharpoonright> factor_of_lod a = y" "x \<downharpoonright> factor_of_lod a \<sqsubseteq> y"
    using that by (simp add: semi_factor.p_fixed_iff semi_factor.slide_rule)
  show "compact (k \<downharpoonright> factor_of_lod a)"
    using factor_of_lod[of a] semi_factor.p_in_S by (simp add: finitary_def)
next
  fix k :: 'a assume "compact k"
  then obtain F where F: "finitary F" "k \<in> set_of_factor F" by (rule compact_home)
  then show "\<exists>c. k \<downharpoonright> factor_of_lod c = k"
    by (intro exI[of _ "lod_of_factor F"]) (simp add: lod_of_factor_inverse semi_factor.p_fixed)
qed

section \<open>Locally finitely detailed domains\<close>

subsection \<open>Generic constructions\<close>

lemma semi_factor_subdomain_UNIV: "semi_factor_subdomain (UNIV :: 'a::{bifinite, distributive_cpo} set)"
  using is_semi_factor_top unfolding is_semi_factor_def by (simp add: top_stable_subdom.rep_eq)

text \<open>A semi-factor from a deflation: downward closure of its fixed points and the slide rule.\<close>

lemma semi_factor_subdomain_deflationI:
  fixes D :: "'a::{bifinite, distributive_cpo} \<rightarrow> 'a"
  assumes D: "deflation D"
    and down: "\<And>x y. D\<cdot>y = y \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> D\<cdot>x = x"
    and slide: "\<And>x y. D\<cdot>y = y \<Longrightarrow> D\<cdot>x \<sqsubseteq> y \<Longrightarrow> x \<Up> y"
  shows "semi_factor_subdomain {x. D\<cdot>x = x}"
proof -
  have st: "stable_subdomain {x. D\<cdot>x = x}" using D down by (rule deflation_stable_subdomainI)
  have "stable_subdomain.p {x. D\<cdot>x = x} = D"
    using stable_subdomain_deflation[OF D st] by simp
  with st slide show ?thesis
    by (intro semi_factor_subdomain.intro semi_factor_subdomain_axioms.intro) auto
qed

subsection \<open>Lifting\<close>

text \<open>Lifting adds a single new bottom below everything, so the home of \<open>up\<cdot>k\<close> is the lifted
  home of \<open>k\<close>.\<close>

lemma semi_factor_subdomain_u:
  fixes S :: "'a::{bifinite, distributive_cpo} set"
  assumes S: "semi_factor_subdomain S"
  shows "semi_factor_subdomain {u :: 'a u. u_map\<cdot>(stable_subdomain.p S)\<cdot>u = u}"
proof -
  have ss: "stable_subdomain S" using S by (rule semi_factor_subdomain.axioms(1))
  note p = stable_subdomain.p_fixed_iff[OF ss]
  show ?thesis
  proof (rule semi_factor_subdomain_deflationI)
    show "deflation (u_map\<cdot>(stable_subdomain.p S))"
      by (rule deflation_u_map[OF stable_subdomain.deflation_p[OF ss]])
  next
    fix x y :: "'a u"
    assume "u_map\<cdot>(stable_subdomain.p S)\<cdot>y = y" "x \<sqsubseteq> y"
    then show "u_map\<cdot>(stable_subdomain.p S)\<cdot>x = x"
      by (cases x; cases y) (auto simp: p intro: stable_subdomain.downward[OF ss])
  next
    fix x y :: "'a u"
    assume "u_map\<cdot>(stable_subdomain.p S)\<cdot>y = y" "u_map\<cdot>(stable_subdomain.p S)\<cdot>x \<sqsubseteq> y"
    then show "x \<Up> y"
      by (cases x; cases y) (auto simp: p intro: semi_factor_subdomain.slide_rule[OF S])
  qed
qed

instance u :: (locally_finitely_detailed) locally_finitely_detailed
proof
  fix k :: "'a u" assume k: "compact k"
  show "\<exists>S. semi_factor_subdomain S \<and> (\<forall>x\<in>S. compact x) \<and> k \<in> S"
  proof (cases k)
    case bottom
    then show ?thesis using semi_factor_subdomain_bot by auto
  next
    case (up k')
    with k obtain S where S: "semi_factor_subdomain S" "\<forall>x\<in>S. compact x" "k' \<in> S"
      using compact_home_set by auto
    have ss: "stable_subdomain S" using S(1) by (rule semi_factor_subdomain.axioms(1))
    let ?H = "{u :: 'a u. u_map\<cdot>(stable_subdomain.p S)\<cdot>u = u}"
    have "\<forall>x\<in>?H. compact x"
    proof
      fix x assume "x \<in> ?H"
      with S(2) show "compact x"
        by (cases x) (auto simp: stable_subdomain.p_fixed_iff[OF ss])
    qed
    with S up show ?thesis
      by (intro exI[of _ ?H]) (simp add: semi_factor_subdomain_u stable_subdomain.p_fixed[OF ss])
  qed
qed

subsection \<open>Faithfully finitely detailed domains\<close>

text \<open>A domain is \<^emph>\<open>faithfully\<close> finitely detailed when, in addition, some finite level of detail
  sees every nonbottom element: its projection reflects \<open>\<bottom>\<close>.  This is what strict sums need: a
  home for \<open>sinl\<cdot>t\<close> must not collapse any nonbottom \<open>sinr\<cdot>b\<close> to \<open>\<bottom>\<close>, or the slide rule would make
  the two joinable.  Lifting always provides it, via the level \<open>{\<bottom>, up\<cdot>\<bottom>}\<close>.\<close>

definition faithful :: "'a::{bifinite, distributive_cpo} set \<Rightarrow> bool" where
  "faithful S \<longleftrightarrow> (\<forall>b. stable_subdomain.p S\<cdot>b = \<bottom> \<longrightarrow> b = \<bottom>)"

class faithfully_finitely_detailed = locally_finitely_detailed +
  assumes faithful_home: "\<exists>S. semi_factor_subdomain S \<and> (\<forall>x\<in>S. compact x) \<and> faithful S"

lemma faithful_mono:
  assumes "stable_subdomain A" "stable_subdomain B" "A \<subseteq> B" "faithful A" shows "faithful B"
  unfolding faithful_def
proof (intro allI impI)
  fix b assume "stable_subdomain.p B\<cdot>b = \<bottom>"
  with proj_mono_subdomain[OF assms(1-3), of b] have "stable_subdomain.p A\<cdot>b = \<bottom>"
    by (simp add: stable_subdomain.p_beta[OF assms(1)] stable_subdomain.p_beta[OF assms(2)] bottomI)
  with assms(4) show "b = \<bottom>" unfolding faithful_def by blast
qed

text \<open>Joining a home with a faithful finite level of detail gives a faithful home.\<close>

lemma compact_faithful_home:
  fixes k :: "'a::faithfully_finitely_detailed"
  assumes "compact k"
  shows "\<exists>S. semi_factor_subdomain S \<and> (\<forall>x\<in>S. compact x) \<and> faithful S \<and> k \<in> S"
proof -
  obtain H where H: "semi_factor_subdomain H" "\<forall>x\<in>H. compact x" "k \<in> H"
    using compact_home_set[OF assms] by blast
  obtain F :: "'a set" where F: "semi_factor_subdomain F" "\<forall>x\<in>F. compact x" "faithful F"
    using faithful_home by (elim exE conjE) (rule that)
  note ssH = semi_factor_subdomain.axioms(1)[OF H(1)]
  note ssF = semi_factor_subdomain.axioms(1)[OF F(1)]
  let ?J = "{a \<squnion> b |a b. a \<in> H \<and> b \<in> F \<and> a \<Up> b}"
  have J: "semi_factor_subdomain ?J" using H(1) F(1) by (rule semi_factor_subdomain_join)
  have "\<forall>x\<in>?J. compact x" using H(2) F(2) by (auto intro: compact_join)
  moreover have "F \<subseteq> ?J"
  proof
    fix b assume "b \<in> F"
    with stable_subdomain.bot_in_S[OF ssH] show "b \<in> ?J"
      by (intro CollectI exI[of _ "\<bottom>"] exI[of _ b]) simp
  qed
  then have "faithful ?J"
    using faithful_mono[OF ssF semi_factor_subdomain.axioms(1)[OF J] _ F(3)] by blast
  moreover have "k \<in> ?J"
    using H(3) stable_subdomain.bot_in_S[OF ssF] by (intro CollectI exI[of _ k] exI[of _ "\<bottom>"]) simp
  ultimately show ?thesis using J by blast
qed

text \<open>Conversely, a finitary faithful home for every compact element gives both class axioms
  (the home of \<open>\<bottom>\<close> is the faithful level).\<close>

lemma faithfully_finitely_detailedI:
  assumes "\<And>k::'a::{bifinite, distributive_cpo}. compact k \<Longrightarrow>
    \<exists>S. semi_factor_subdomain S \<and> (\<forall>x\<in>S. compact x) \<and> faithful S \<and> k \<in> S"
  shows "OFCLASS('a, faithfully_finitely_detailed_class)"
proof intro_classes
  fix k :: 'a assume "compact k"
  from assms[OF this] show "\<exists>S. semi_factor_subdomain S \<and> (\<forall>x\<in>S. compact x) \<and> k \<in> S"
    by (elim exE conjE) (intro exI conjI)
next
  from assms[OF compact_bottom]
  show "\<exists>S :: 'a set. semi_factor_subdomain S \<and> (\<forall>x\<in>S. compact x) \<and> faithful S"
    by (elim exE conjE) (intro exI conjI)
qed


instance u :: (locally_finitely_detailed) faithfully_finitely_detailed
proof
  let ?D = "u_map\<cdot>(stable_subdomain.p {\<bottom>}) :: 'a u \<rightarrow> 'a u"
  have p: "stable_subdomain.p {\<bottom>}\<cdot>x = \<bottom>" for x :: 'a by (rule p_bot)
  have S: "semi_factor_subdomain {u. ?D\<cdot>u = u}"
    by (rule semi_factor_subdomain_u[OF semi_factor_subdomain_bot])
  have pD: "stable_subdomain.p {u. ?D\<cdot>u = u} = ?D"
    using stable_subdomain_deflation[OF deflation_u_map[OF stable_subdomain.deflation_p[OF
      stable_subdomain_bot]] semi_factor_subdomain.axioms(1)[OF S]] by simp
  have "\<forall>x\<in>{u. ?D\<cdot>u = u}. compact x"
  proof
    fix x assume "x \<in> {u. ?D\<cdot>u = u}"
    then show "compact x" by (cases x) (simp_all add: p)
  qed
  moreover have "faithful {u. ?D\<cdot>u = u}"
    unfolding faithful_def pD
  proof (intro allI impI)
    fix b assume "?D\<cdot>b = \<bottom>"
    then show "b = \<bottom>" by (cases b) (simp_all add: p)
  qed
  ultimately show "\<exists>S :: 'a u set. semi_factor_subdomain S \<and> (\<forall>x\<in>S. compact x) \<and> faithful S"
    using S by blast
qed

subsection \<open>Strict sums\<close>

text \<open>A sum of two faithful finitary levels is a level of the strict sum: faithfulness is exactly
  what closes the cross case of the slide rule (a left element is never projected to \<open>\<bottom>\<close> below a
  right one).\<close>

lemma semi_factor_subdomain_ssum:
  fixes S :: "'a::{bifinite, distributive_cpo} set" and T :: "'b::{bifinite, distributive_cpo} set"
  assumes S: "semi_factor_subdomain S" and T: "semi_factor_subdomain T"
    and fS: "faithful S" and fT: "faithful T"
  shows "semi_factor_subdomain
    {u :: 'a \<oplus> 'b. ssum_map\<cdot>(stable_subdomain.p S)\<cdot>(stable_subdomain.p T)\<cdot>u = u}"
proof -
  note ssS = semi_factor_subdomain.axioms(1)[OF S] and ssT = semi_factor_subdomain.axioms(1)[OF T]
  have strict: "stable_subdomain.p S\<cdot>\<bottom> = \<bottom>" "stable_subdomain.p T\<cdot>\<bottom> = \<bottom>"
    by (simp_all add: stable_subdomain.p_fixed stable_subdomain.bot_in_S ssS ssT)
  note simps = ssum_map_sinl'[OF strict(1)] ssum_map_sinr'[OF strict(2)]
    stable_subdomain.p_fixed_iff[OF ssS] stable_subdomain.p_fixed_iff[OF ssT]
  show ?thesis
  proof (rule semi_factor_subdomain_deflationI)
    show "deflation (ssum_map\<cdot>(stable_subdomain.p S)\<cdot>(stable_subdomain.p T))"
      by (intro deflation_ssum_map stable_subdomain.deflation_p ssS ssT)
  next
    fix x y :: "'a \<oplus> 'b"
    assume "ssum_map\<cdot>(stable_subdomain.p S)\<cdot>(stable_subdomain.p T)\<cdot>y = y" "x \<sqsubseteq> y"
    then show "ssum_map\<cdot>(stable_subdomain.p S)\<cdot>(stable_subdomain.p T)\<cdot>x = x"
      by (cases x; cases y)
        (auto simp: simps intro: stable_subdomain.downward[OF ssS] stable_subdomain.downward[OF ssT])
  next
    fix x y :: "'a \<oplus> 'b"
    assume "ssum_map\<cdot>(stable_subdomain.p S)\<cdot>(stable_subdomain.p T)\<cdot>y = y"
      "ssum_map\<cdot>(stable_subdomain.p S)\<cdot>(stable_subdomain.p T)\<cdot>x \<sqsubseteq> y"
    then show "x \<Up> y"
      using fS fT unfolding faithful_def
      by (cases x; cases y)
        (auto simp: simps intro: semi_factor_subdomain.slide_rule[OF S] semi_factor_subdomain.slide_rule[OF T])
  qed
qed

instance ssum :: (faithfully_finitely_detailed, faithfully_finitely_detailed)
  faithfully_finitely_detailed
proof (rule faithfully_finitely_detailedI)
  fix k :: "'a \<oplus> 'b" assume k: "compact k"
  have home: "\<exists>U. semi_factor_subdomain U \<and> (\<forall>x\<in>U. compact x) \<and> faithful U \<and> k \<in> U"
    if a: "compact a" and b: "compact b"
      and kD: "\<And>S T. stable_subdomain S \<Longrightarrow> stable_subdomain T \<Longrightarrow> a \<in> S \<Longrightarrow> b \<in> T \<Longrightarrow>
        ssum_map\<cdot>(stable_subdomain.p S)\<cdot>(stable_subdomain.p T)\<cdot>k = k"
    for a :: 'a and b :: 'b
  proof -
    obtain S where S: "semi_factor_subdomain S" "\<forall>x\<in>S. compact x" "faithful S" "a \<in> S"
      using compact_faithful_home[OF a] by (elim exE conjE) (rule that)
    obtain T where T: "semi_factor_subdomain T" "\<forall>x\<in>T. compact x" "faithful T" "b \<in> T"
      using compact_faithful_home[OF b] by (elim exE conjE) (rule that)
    note ssS = semi_factor_subdomain.axioms(1)[OF S(1)] and ssT = semi_factor_subdomain.axioms(1)[OF T(1)]
    let ?D = "ssum_map\<cdot>(stable_subdomain.p S)\<cdot>(stable_subdomain.p T)"
    have strict: "stable_subdomain.p S\<cdot>\<bottom> = \<bottom>" "stable_subdomain.p T\<cdot>\<bottom> = \<bottom>"
      by (simp_all add: stable_subdomain.p_fixed stable_subdomain.bot_in_S ssS ssT)
    note simps = ssum_map_sinl'[OF strict(1)] ssum_map_sinr'[OF strict(2)]
      stable_subdomain.p_fixed_iff[OF ssS] stable_subdomain.p_fixed_iff[OF ssT]
    have U: "semi_factor_subdomain {u. ?D\<cdot>u = u}"
      by (rule semi_factor_subdomain_ssum[OF S(1) T(1) S(3) T(3)])
    have pD: "stable_subdomain.p {u. ?D\<cdot>u = u} = ?D"
      using stable_subdomain_deflation[OF deflation_ssum_map[OF stable_subdomain.deflation_p[OF ssS]
        stable_subdomain.deflation_p[OF ssT]] semi_factor_subdomain.axioms(1)[OF U]] by simp
    have "\<forall>x\<in>{u. ?D\<cdot>u = u}. compact x"
    proof
      fix x assume "x \<in> {u. ?D\<cdot>u = u}"
      with S(2) T(2) show "compact x" by (cases x) (auto simp: simps)
    qed
    moreover have "faithful {u. ?D\<cdot>u = u}"
      unfolding faithful_def pD
    proof (intro allI impI)
      fix x assume "?D\<cdot>x = \<bottom>"
      with S(3) T(3) show "x = \<bottom>" unfolding faithful_def by (cases x) (auto simp: simps)
    qed
    moreover have "k \<in> {u. ?D\<cdot>u = u}" using kD[OF ssS ssT S(4) T(4)] by simp
    ultimately show ?thesis using U by blast
  qed
  show "\<exists>U. semi_factor_subdomain U \<and> (\<forall>x\<in>U. compact x) \<and> faithful U \<and> k \<in> U"
  proof (cases k)
    case bottom then show ?thesis by (intro home[of \<bottom> \<bottom>]) simp_all
  next
    case (sinl a)
    with k show ?thesis
      by (intro home[of a \<bottom>]) (simp_all add: stable_subdomain.p_fixed)
  next
    case (sinr b)
    with k show ?thesis
      by (intro home[of \<bottom> b]) (simp_all add: stable_subdomain.p_fixed)
  qed
qed

subsection \<open>Finite height and flat domains\<close>

text \<open>With finite height the whole domain is a finitary level of detail, and it is trivially
  faithful.\<close>

lemma chfin_faithful_home:
  fixes k :: "'a::{bifinite, distributive_cpo, chfin}"
  shows "\<exists>S. semi_factor_subdomain S \<and> (\<forall>x\<in>S. compact x) \<and> faithful S \<and> k \<in> S"
proof (intro exI conjI)
  show "faithful (UNIV :: 'a set)" by (simp add: faithful_def p_UNIV)
qed (simp_all add: semi_factor_subdomain_UNIV compact_chfin)

instance lift :: (countable) faithfully_finitely_detailed
  by (rule faithfully_finitely_detailedI) (rule chfin_faithful_home)

subsection \<open>Tuples\<close>

text \<open>A compact tuple has finite support and compact components.  Its finitary home is the
  product of finitary homes of the components on its support (and of \<open>{\<bottom>}\<close> elsewhere).\<close>

definition tmap :: "('d \<Rightarrow> 'v::pcpo \<rightarrow> 'v) \<Rightarrow> ('d, 'v) tuple \<rightarrow> ('d, 'v) tuple" where
  "tmap f = (\<Lambda> t. Abs_tuple (\<lambda>d. f d\<cdot>(t\<langle>d\<rangle>)))"

lemma tmap_tget [simp]: "(tmap f\<cdot>t)\<langle>d\<rangle> = f d\<cdot>(t\<langle>d\<rangle>)"
  unfolding tmap_def
  by (subst beta_cfun)
    (simp_all add: cont_Abs_tuple cont2cont_lambda cont2cont_fun cont_tget Abs_tuple_inverse')

lemma tuple_below_iff: "x \<sqsubseteq> y \<longleftrightarrow> (\<forall>d. x\<langle>d\<rangle> \<sqsubseteq> y\<langle>d\<rangle>)"
  by (simp add: below_tuple_def fun_below_iff)

lemma tuple_joinableI:
  fixes x y :: "('d, 'v::bounded_complete) tuple"
  assumes "\<And>d. x\<langle>d\<rangle> \<Up> y\<langle>d\<rangle>"
  shows "x \<Up> y"
proof (rule joinableI)
  let ?z = "Abs_tuple (\<lambda>d. x\<langle>d\<rangle> \<squnion> y\<langle>d\<rangle>) :: ('d, 'v) tuple"
  show "x \<sqsubseteq> ?z" "y \<sqsubseteq> ?z"
    using joinableD[OF assms] by (simp_all add: tuple_below_iff Abs_tuple_inverse')
qed

text \<open>A component of a compact tuple is compact: a chain approximating the component, placed
  into the tuple, approximates the whole tuple.\<close>

lemma compact_tget:
  fixes K :: "('d, 'v::pcpo) tuple"
  assumes "compact K" shows "compact (K\<langle>d\<rangle>)"
proof (rule compactI2)
  fix Y :: "nat \<Rightarrow> 'v" assume Y: "chain Y" and le: "K\<langle>d\<rangle> \<sqsubseteq> (\<Squnion>i. Y i)"
  define Z where "Z i = Abs_tuple ((tget K)(d := Y i))" for i
  have Zd: "(Z i)\<langle>e\<rangle> = (if e = d then Y i else K\<langle>e\<rangle>)" for i e
    by (simp add: Z_def Abs_tuple_inverse')
  have Z: "chain Z"
    using Y by (simp add: chain_def tuple_below_iff Zd)
  have "K \<sqsubseteq> (\<Squnion>i. Z i)"
    using le by (simp add: tuple_below_iff tget_lub[OF Z] Zd Y)
  then obtain i where "K \<sqsubseteq> Z i" using compactD2[OF assms Z] by blast
  then have "K\<langle>d\<rangle> \<sqsubseteq> (Z i)\<langle>d\<rangle>" by (simp add: tuple_below_iff)
  then show "\<exists>i. K\<langle>d\<rangle> \<sqsubseteq> Y i" by (auto simp: Zd)
qed

lemma compact_tupleI:
  fixes K :: "('d, 'v::pcpo) tuple"
  assumes "finite (tsupp K)" and "\<And>d. compact (K\<langle>d\<rangle>)"
  shows "compact K"
proof (rule compactI)
  have "(\<not> K \<sqsubseteq> u) \<longleftrightarrow> (\<exists>d\<in>tsupp K. \<not> K\<langle>d\<rangle> \<sqsubseteq> u\<langle>d\<rangle>)" for u
    by (auto simp: tuple_below_iff tsupp_def)
  moreover have "adm (\<lambda>u. \<exists>d\<in>tsupp K. \<not> K\<langle>d\<rangle> \<sqsubseteq> u\<langle>d\<rangle>)"
    using assms(1) proof (rule adm_finite_bex)
    show "adm (\<lambda>u. \<not> K\<langle>d\<rangle> \<sqsubseteq> u\<langle>d\<rangle>)" for d
      by (rule adm_compact_not_below[OF assms(2)]) (simp add: cont2cont_fun cont_tget)
  qed
  ultimately show "adm (\<lambda>u. \<not> K \<sqsubseteq> u)" by simp
qed

lemma tuple_eq_iff: "x = y \<longleftrightarrow> (\<forall>d. x\<langle>d\<rangle> = y\<langle>d\<rangle>)"
  by (auto simp: po_eq_conv tuple_below_iff)

text \<open>A product of semi-factors, one per dimension, is a semi-factor: its projection acts
  componentwise, and the slide rule holds componentwise.\<close>

lemma semi_factor_subdomain_tprod:
  fixes S :: "'d::countable \<Rightarrow> 'v::{bifinite, distributive_cpo} set"
  assumes S: "\<And>d. semi_factor_subdomain (S d)"
  shows "semi_factor_subdomain {t :: ('d, 'v) tuple. \<forall>d. t\<langle>d\<rangle> \<in> S d}"
proof -
  have ss: "stable_subdomain (S d)" for d using S semi_factor_subdomain.axioms(1) by blast
  define D where "D = (tmap (\<lambda>d. stable_subdomain.p (S d)) :: ('d, 'v) tuple \<rightarrow> _)"
  have fix_iff: "D\<cdot>t = t \<longleftrightarrow> (\<forall>d. t\<langle>d\<rangle> \<in> S d)" for t
    by (simp add: D_def tuple_eq_iff stable_subdomain.p_fixed_iff[OF ss])
  have defl: "deflation D"
    by (rule deflation.intro)
      (simp_all add: D_def tuple_eq_iff tuple_below_iff stable_subdomain.p_fixed[OF ss]
        stable_subdomain.p_in_S[OF ss] stable_subdomain.p_below[OF ss])
  have set_eq: "{t. \<forall>d. t\<langle>d\<rangle> \<in> S d} = {t. D\<cdot>t = t}" using fix_iff by blast
  have st: "stable_subdomain {t. D\<cdot>t = t}"
  proof (rule deflation_stable_subdomainI[OF defl])
    fix x y :: "('d, 'v) tuple" assume "D\<cdot>y = y" "x \<sqsubseteq> y"
    then show "D\<cdot>x = x"
      unfolding fix_iff tuple_below_iff by (blast intro: stable_subdomain.downward[OF ss])
  qed
  have pD: "stable_subdomain.p {t. D\<cdot>t = t} = D"
    using stable_subdomain_deflation[OF defl st] by simp
  show ?thesis unfolding set_eq
  proof (rule semi_factor_subdomain.intro[OF st], unfold_locales, unfold pD)
    fix y x :: "('d, 'v) tuple" assume y: "y \<in> {t. D\<cdot>t = t}" and le: "D\<cdot>x \<sqsubseteq> y"
    show "x \<Up> y"
    proof (rule tuple_joinableI)
      fix d
      from y have yd: "y\<langle>d\<rangle> \<in> S d" by (simp add: fix_iff)
      from le have "stable_subdomain.p (S d)\<cdot>(x\<langle>d\<rangle>) \<sqsubseteq> y\<langle>d\<rangle>" by (simp add: D_def tuple_below_iff)
      with yd show "x\<langle>d\<rangle> \<Up> y\<langle>d\<rangle>" by (rule semi_factor_subdomain.slide_rule[OF S])
    qed
  qed
qed

instance tuple :: (countable, locally_finitely_detailed) locally_finitely_detailed
proof
  fix K :: "('a, 'b) tuple" assume K: "compact K"
  define H where "H d = (if d \<in> tsupp K
      then (SOME S. semi_factor_subdomain S \<and> (\<forall>x\<in>S. compact x) \<and> K\<langle>d\<rangle> \<in> S) else {\<bottom>})" for d
  have H: "semi_factor_subdomain (H d) \<and> (\<forall>x\<in>H d. compact x) \<and> K\<langle>d\<rangle> \<in> H d" for d
  proof (cases "d \<in> tsupp K")
    case True
    then show ?thesis
      using someI_ex[OF compact_home_set[OF compact_tget[OF K, of d]]] by (simp add: H_def)
  next
    case False
    then show ?thesis using semi_factor_subdomain_bot by (simp add: H_def tsupp_def)
  qed
  let ?S = "{t :: ('a, 'b) tuple. \<forall>d. t\<langle>d\<rangle> \<in> H d}"
  have "semi_factor_subdomain ?S" using H by (blast intro: semi_factor_subdomain_tprod)
  moreover have "compact t" if t: "t \<in> ?S" for t
  proof (rule compact_tupleI)
    have "tsupp t \<subseteq> tsupp K"
      using t by (auto simp: tsupp_def H_def split: if_splits)
    then show "finite (tsupp t)" using compact_finite_tsupp[OF K] by (rule finite_subset)
    show "compact (t\<langle>d\<rangle>)" for d using t H by blast
  qed
  moreover have "K \<in> ?S" using H by blast
  ultimately show "\<exists>S. semi_factor_subdomain S \<and> (\<forall>x\<in>S. compact x) \<and> K \<in> S" by blast
qed
end

