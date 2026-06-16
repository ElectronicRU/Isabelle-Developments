theory Subdomain 
  imports HOLCF "HOLCF-extra.Directed" "HOLCF-extra.Bounded_Complete" begin

default_sort "{bifinite, distributive_cpo}"

text \<open>\<^cite>\<open>buneman91\<close>\<close>

lemma compact_directedD:
  fixes x :: "'a::bifinite"
  assumes D: "directed D" "D \<noteq> {}" and x: "compact x"
  shows "x \<sqsubseteq> lub D \<longleftrightarrow> (\<exists>y \<in> D. x \<sqsubseteq> y)"
proof (safe)
  assume "x \<sqsubseteq> lub D"
  from obtain_directed_chain[OF D]
  obtain C where "chain C" "\<forall>i. C i \<in> D" "(\<Squnion>i. C i) = lub D" .
  with x \<open>x \<sqsubseteq> lub D\<close> have "\<exists>i. x \<sqsubseteq> C i"
    by (auto intro: compactD2[of x C])
  with \<open>\<forall>i. C i \<in> D\<close> show "\<exists>y \<in> D. x \<sqsubseteq> y" by fast
next
  fix y assume "y \<in> D"
  with directed_lub[OF D(1)] is_lubD1 is_ubD have "y \<sqsubseteq> lub D" by blast
  moreover assume "x \<sqsubseteq> y"
  ultimately show "x \<sqsubseteq> lub D" by order
qed

lemma directed_approximants:
  fixes D :: "('a::bifinite) set"
  assumes "directed D" "D \<noteq> {}"
  shows "approximants (lub D) = (\<Union>x \<in> D. approximants x)"
  unfolding approximants_def
  using compact_directedD[OF assms] by auto

locale stable_subdomain =
  fixes S :: "'a set" (structure)
  assumes strong_closed:  "T \<subseteq> S \<Longrightarrow> T <<| t \<Longrightarrow> t \<in> S"
  assumes downward: "y \<in> S \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> x \<in> S"
begin
definition "proj a = lub {x \<in> S. x \<sqsubseteq> a}"

lemma proj_set_directed: "directed {x \<in> S. x \<sqsubseteq> a}"
proof (rule directedI, safe)
  fix x y assume S: "x \<in> S" "y \<in> S"
  assume a: "x \<sqsubseteq> a" "y \<sqsubseteq> a"
  then have lub: "{x, y} <<| (x \<squnion> y)" by (rule join_is_lub)
  from strong_closed[OF _ this] S have lubS: "x \<squnion> y \<in> S"
    by blast
  from lub have le: "x \<sqsubseteq> x \<squnion> y" "y \<sqsubseteq> x \<squnion> y" by (auto dest: is_lubD1 is_ubD)
  moreover from a have "x \<squnion> y \<sqsubseteq> a"
    using is_lubD2[OF lub, of a] by auto
  ultimately show "\<exists>z \<in> {x \<in> S. x \<sqsubseteq> a}. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
    using lubS by blast
qed

lemma bot_in_S: "\<bottom> \<in> S"
  using strong_closed[of "{}" "\<bottom>"] by simp

lemma proj_set_ne: "{x \<in> S. x \<sqsubseteq> a} \<noteq> {}"
proof -
  have "\<bottom> \<in> {x \<in> S. x \<sqsubseteq> a}" using bot_in_S by simp
  then show ?thesis by auto
qed

corollary proj_is_lub: "{x \<in> S. x \<sqsubseteq> a} <<| proj a"
  unfolding proj_def using proj_set_directed by (rule directed_lub)

corollary proj_in_S: "proj a \<in> S"
  using strong_closed[OF _ proj_is_lub] by blast

lemma proj_below: "proj a \<sqsubseteq> a"
  by (blast intro: proj_is_lub[THEN is_lubD2, of a a] is_ubI)

corollary proj_fixed: "a \<in> S \<Longrightarrow> proj a = a"
proof (rule below_antisym)
  show "proj a \<sqsubseteq> a" by (fact proj_below)
  assume "a \<in> S"
  then have "a \<in> {x \<in> S. x \<sqsubseteq> a}" by simp
  with proj_is_lub[THEN is_lubD1, THEN is_ubD] show "a \<sqsubseteq> proj a" .
qed

corollary proj_fixed_iff: "proj a = a \<longleftrightarrow> a \<in> S"
  using proj_in_S proj_fixed by metis

corollary below_set_is_down_set:
  "{x \<in> S. x \<sqsubseteq> a} = {x. x \<sqsubseteq> proj a}"
proof (intro subset_antisym subsetI; safe)
  fix x assume "x \<in> S" "x \<sqsubseteq> a"
  with proj_is_lub[THEN is_lubD1, THEN is_ubD]
  show "x \<sqsubseteq> proj a" by blast
next
  fix x assume *: "x \<sqsubseteq> proj a"
  from below_trans[OF * proj_below]
  show "x \<sqsubseteq> a" .
  from downward[OF proj_in_S *]
  show "x \<in> S" .
qed

lemma approximants_proj:
  "approximants (proj a) = {x \<in> approximants a. Rep_compact_basis x \<in> S}"
  unfolding approximants_def
  using below_set_is_down_set by blast

lemma proj_mono: "monofun proj"
proof (rule monofunI)
  fix x y :: 'a assume "x \<sqsubseteq> y"
  then have "{z \<in> S. z \<sqsubseteq> x} \<subseteq> {z \<in> S. z \<sqsubseteq> y}"
    using below_trans by blast
  with proj_is_lub proj_is_lub show "proj x \<sqsubseteq> proj y"
    by (rule lub_subset_mono)
qed

lemma proj_cont: "cont proj"
proof (rule contI2)
  show "monofun proj" by (fact proj_mono)
  fix Y :: "nat \<Rightarrow> 'a" assume Y: "chain Y"
  assume pY: "chain (\<lambda>i. proj (Y i))"
  from Y have 1: "approximants (\<Squnion>i. Y i) = (\<Union>i. approximants (Y i))"
    by (rule compact_basis.rep_lub)
  from pY have 2: "approximants (\<Squnion>i. proj(Y i)) = (\<Union>i. approximants (proj (Y i)))"
    by (rule compact_basis.rep_lub)
  from 1 2 approximants_proj
  have "approximants (proj (\<Squnion>i. Y i)) \<subseteq> approximants (\<Squnion>i. proj(Y i))"
    by auto
  then show "proj (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. proj(Y i))"
    by (rule compact_basis.belowI)
qed

definition "p \<equiv> \<Lambda> a. proj a"

lemma p_beta[simp]: "p\<cdot>x = proj x"
  unfolding p_def
  by (simp add: proj_cont)

sublocale deflation p
proof
  show "p\<cdot>(p\<cdot>x) = p\<cdot>x" for x
    using proj_in_S proj_fixed
    by simp
  show "p\<cdot>x \<sqsubseteq> x" for x
    using proj_below by simp
qed

lemma p_fixes: "{x. p\<cdot>x = x} = S"
  by (simp add: proj_fixed_iff)

lemma p_range: "range (\<lambda>x. p\<cdot>x) = S"
  by (simp only: p_fixes range_eq_fixes)

end

locale strong_subdomain = stable_subdomain +
  assumes slide_rule: "y \<in> S \<Longrightarrow> p\<cdot>x \<sqsubseteq> y \<Longrightarrow> x \<Up> y"

lemma stable_subdomain_deflation:
  fixes p assumes p: "deflation p" and ss: "stable_subdomain {x. p\<cdot>x = x}"
  shows "p = stable_subdomain.p {x. p\<cdot>x = x}"
proof -
  interpret p: deflation p by (rule p)
  interpret S: stable_subdomain "{x. p\<cdot>x = x}" by (rule ss)
  show ?thesis
  proof (intro below_antisym)
    show "p \<sqsubseteq> S.p"
    proof (rule p.belowI)
      fix x assume "p\<cdot>x = x"
      then show "S.p\<cdot>x = x"
        by (metis (mono_tags, lifting) S.p_fixes mem_Collect_eq)
    qed
    show "S.p \<sqsubseteq> p"
    proof (rule S.belowI)
      fix x assume "S.p\<cdot>x = x"
      then show "p\<cdot>x = x"
        by (metis (mono_tags, lifting) S.p_fixes mem_Collect_eq)
    qed
  qed
qed
text \<open>The range of any deflation is automatically closed under lubs of bounded
  subsets: only downward closure distinguishes a stable-subdomain projection from a
  general deflation.\<close>

lemma deflation_strong_closed:
  assumes d: "deflation d" and T: "T \<subseteq> {x. d\<cdot>x = x}" and lub: "T <<| t"
  shows "d\<cdot>t = t"
proof -
  interpret deflation d by (rule d)
  have "T <| d\<cdot>t"
  proof (rule is_ubI)
    fix x assume x: "x \<in> T"
    with T have "d\<cdot>x = x" by auto
    moreover from is_lubD1[OF lub] x have "x \<sqsubseteq> t" by (rule is_ubD)
    ultimately show "x \<sqsubseteq> d\<cdot>t" by (metis monofun_cfun_arg)
  qed
  from is_lubD2[OF lub this] have "t \<sqsubseteq> d\<cdot>t" .
  with below show "d\<cdot>t = t" by (rule below_antisym)
qed

lemma deflation_stable_subdomainI:
  assumes d: "deflation d"
    and dc: "\<And>x y. d\<cdot>y = y \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> d\<cdot>x = x"
  shows "stable_subdomain {x. d\<cdot>x = x}"
proof
  fix y x assume "y \<in> {x. d\<cdot>x = x}" "x \<sqsubseteq> y"
  with dc show "x \<in> {x. d\<cdot>x = x}" by simp
next
  fix T t assume "T \<subseteq> {x. d\<cdot>x = x}" "T <<| t"
  with deflation_strong_closed[OF d] show "t \<in> {x. d\<cdot>x = x}" by simp
qed

subsection \<open>Stable subdomains as a type of deflations\<close>

text \<open>A continuous function is a \<^emph>\<open>stable projection\<close> when it is a deflation whose
  fixed-point set is downward closed; equivalently, a deflation whose range is a
  stable subdomain.\<close>

definition dc_defl :: "'a defl \<Rightarrow> bool"
  where "dc_defl d \<longleftrightarrow> (\<forall>x y. cast\<cdot>d\<cdot>y = y \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> cast\<cdot>d\<cdot>x = x)"

lemma dc_deflI:
  assumes "\<And>x y. cast\<cdot>d\<cdot>y = y \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> cast\<cdot>d\<cdot>x = x"
  shows "dc_defl d"
  using assms unfolding dc_defl_def by blast

lemma dc_deflD:
  assumes "dc_defl d" "cast\<cdot>d\<cdot>y = y" "x \<sqsubseteq> y"
  shows "cast\<cdot>d\<cdot>x = x"
  using assms unfolding dc_defl_def by blast

lemma dc_defl_stable_subdomain:
  assumes "dc_defl d"
  shows "stable_subdomain {x. cast\<cdot>d\<cdot>x = x}"
  by (rule deflation_stable_subdomainI[OF deflation_cast])
    (rule dc_deflD[OF assms])

lemma dc_defl_bottom: "dc_defl \<bottom>"
proof (rule dc_deflI)
  fix x y :: 'a assume a: "cast\<cdot>\<bottom>\<cdot>y = y" and b: "x \<sqsubseteq> y"
  from a have "y = \<bottom>" by (simp add: cast_strict1)
  with b have "x = \<bottom>" by (simp add: bottomI)
  then show "cast\<cdot>\<bottom>\<cdot>x = x" by (simp add: cast_strict1)
qed

lemma adm_dc_defl: "adm (dc_defl :: 'a defl \<Rightarrow> bool)"
proof (rule admI)
  fix D :: "nat \<Rightarrow> 'a defl"
  assume chain: "chain D" and H: "\<forall>i. dc_defl (D i)"
  show "dc_defl (\<Squnion>i. D i)"
  proof (rule dc_deflI)
    fix x y assume fy: "cast\<cdot>(\<Squnion>i. D i)\<cdot>y = y" and xy: "x \<sqsubseteq> y"
    define p where "p = cast\<cdot>(\<Squnion>i. D i)"
    have cchain: "chain (\<lambda>i. cast\<cdot>(D i))" by (intro ch2ch_Rep_cfunR chain)
    have plub: "p = (\<Squnion>i. cast\<cdot>(D i))" unfolding p_def by (rule contlub_cfun_arg[OF chain])
    have defl: "deflation p" unfolding p_def by (rule deflation_cast)
    obtain C where C: "chain C" "\<forall>i. compact (C i)" "x = (\<Squnion>i. C i)"
      by (rule obtain_compact_chain)
    have fixed: "p\<cdot>(C i) = C i" for i
    proof -
      have "C i \<sqsubseteq> x" using is_ub_thelub[OF C(1)] C(3) by metis
      then have Ciy: "C i \<sqsubseteq> y" using xy by (rule below_trans)
      have "C i \<sqsubseteq> p\<cdot>y" using Ciy fy by (simp add: p_def)
      also have "p\<cdot>y = (\<Squnion>j. cast\<cdot>(D j)\<cdot>y)" unfolding plub by (rule contlub_cfun_fun[OF cchain])
      finally have Cilub: "C i \<sqsubseteq> (\<Squnion>j. cast\<cdot>(D j)\<cdot>y)" .
      have chy: "chain (\<lambda>j. cast\<cdot>(D j)\<cdot>y)" by (intro ch2ch_Rep_cfunL cchain)
      from compactD2[OF C(2)[rule_format] chy Cilub]
      obtain j where j: "C i \<sqsubseteq> cast\<cdot>(D j)\<cdot>y" by blast
      have idem: "cast\<cdot>(D j)\<cdot>(cast\<cdot>(D j)\<cdot>y) = cast\<cdot>(D j)\<cdot>y" by (rule cast.idem)
      have CiFix: "cast\<cdot>(D j)\<cdot>(C i) = C i" by (rule dc_deflD[OF H[rule_format] idem j])
      have "cast\<cdot>(D j) \<sqsubseteq> p" unfolding plub by (rule is_ub_thelub[OF cchain])
      from monofun_cfun_fun[OF this] CiFix have "C i \<sqsubseteq> p\<cdot>(C i)" by metis
      then show "p\<cdot>(C i) = C i" by (rule below_antisym[OF deflation.below[OF defl]])
    qed
    have rcx: "range C <<| x" using cpo_lubI[OF C(1)] C(3) by simp
    have "range C \<subseteq> {z. p\<cdot>z = z}" using fixed by auto
    from deflation_strong_closed[OF defl this rcx]
    show "cast\<cdot>(\<Squnion>i. D i)\<cdot>x = x" by (simp add: p_def)
  qed
qed

pcpodef 'a stable_dom = "{d::'a defl. dc_defl d}"
  using dc_defl_bottom adm_dc_defl by auto

text \<open>A pcpo carved from a bounded-complete type by a typedef whose set is closed
  under lubs of bounded subsets is again bounded complete. The order on the subtype
  must be the one induced by @{term Rep}, as supplied by @{command pcpodef}.\<close>

lemma bounded_complete_subtypeI:
  fixes Rep :: "'b::pcpo \<Rightarrow> 'a::bounded_complete"
  assumes type: "type_definition Rep Abs Q"
    and below: "\<And>x y. (x \<sqsubseteq> y) = (Rep x \<sqsubseteq> Rep y)"
    and Q_strong_closed: "\<And>A a. A \<subseteq> Q \<Longrightarrow> A <<| a \<Longrightarrow> a \<in> Q"
  shows "OFCLASS('b, bounded_complete_class)"
proof
  interpret type_definition Rep Abs Q by (rule type)
  fix A :: "'b set" and b :: 'b
  assume "A \<noteq> {}" and Ab: "A <| b"
  have RepAb: "Rep ` A <| Rep b"
  proof (rule is_ubI)
    fix y assume "y \<in> Rep ` A"
    then obtain x where x: "x \<in> A" "y = Rep x" by auto
    from is_ubD[OF Ab x(1)] have "Rep x \<sqsubseteq> Rep b" using below by simp
    with x(2) show "y \<sqsubseteq> Rep b" by simp
  qed
  then obtain l where l: "Rep ` A <<| l" using ex_bound_ex_lub by blast
  have "Rep ` A \<subseteq> Q" using Rep by auto
  from Q_strong_closed[OF this l] have lQ: "l \<in> Q" .
  have "A <<| Abs l"
  proof (rule is_lubI)
    show "A <| Abs l"
    proof (rule is_ubI)
      fix x assume "x \<in> A"
      from is_ubD[OF is_lubD1[OF l]] this have "Rep x \<sqsubseteq> l" by auto
      then show "x \<sqsubseteq> Abs l" using below Abs_inverse[OF lQ] by simp
    qed
  next
    fix u assume "A <| u"
    have "Rep ` A <| Rep u"
    proof (rule is_ubI)
      fix y assume "y \<in> Rep ` A"
      then obtain x where x: "x \<in> A" "y = Rep x" by auto
      from is_ubD[OF \<open>A <| u\<close> x(1)] have "Rep x \<sqsubseteq> Rep u" using below by simp
      with x(2) show "y \<sqsubseteq> Rep u" by simp
    qed
    with l have "l \<sqsubseteq> Rep u" by (rule is_lubD2)
    then show "Abs l \<sqsubseteq> u" using below Abs_inverse[OF lQ] by simp
  qed
  then show "\<exists>z. A <<| z" ..
qed


subsection \<open>Continuity of binary meet\<close>

text \<open>In a bifinite bounded-complete domain binary meet is continuous: this is the
  \<open>approximants\<close> observation — a compact below @{term \<open>(\<Squnion>i. X i) \<sqinter> y\<close>} already lies
  below some @{term \<open>X i \<sqinter> y\<close>}.\<close>

lemma approximants_meet: "approximants ((x::'a) \<sqinter> y) = approximants x \<inter> approximants y"
  unfolding approximants_def by (auto simp add: meet_below_iff)

lemma cont_meet_arg: "cont (\<lambda>(x::'a). x \<sqinter> y)"
proof -
  have mono: "monofun (\<lambda>x. x \<sqinter> y)"
  proof (rule monofunI)
    fix a b :: 'a assume "a \<sqsubseteq> b"
    have "a \<sqinter> y \<sqsubseteq> b" using meet_below1[of a y] \<open>a \<sqsubseteq> b\<close> by (rule below_trans)
    moreover have "a \<sqinter> y \<sqsubseteq> y" by (rule meet_below2)
    ultimately show "a \<sqinter> y \<sqsubseteq> b \<sqinter> y" by (rule meet_greatest)
  qed
  show ?thesis
  proof (rule contI2[OF mono])
    fix X :: "nat \<Rightarrow> 'a" assume X: "chain X"
    assume chXy: "chain (\<lambda>i. X i \<sqinter> y)"
    show "(\<Squnion>i. X i) \<sqinter> y \<sqsubseteq> (\<Squnion>i. X i \<sqinter> y)"
      by (rule compact_basis.belowI)
       (simp add:
         compact_basis.rep_lub X chXy approximants_meet)
  qed
qed

lemma cont_meet_arg2: "cont (\<lambda>y::'a. x \<sqinter> y)"
  using cont_meet_arg[of x] by (simp add: meet_sym)

lemma cont2cont_meet [simp, cont2cont]:
  fixes f g :: "'b::cpo \<Rightarrow> 'a"
  assumes contf: "cont f" and contg: "cont g" shows "cont (\<lambda>x. f x \<sqinter> g x)"
  by (rule cont_apply [OF contg cont_meet_arg2 cont_compose [OF cont_meet_arg contf]])


subsection \<open>Meet of two deflations\<close>

text \<open>The meet of two deflations in the deflation order (the projection onto
  @{term \<open>{x. f\<cdot>x = x} \<inter> {x. g\<cdot>x = x}\<close>}) is the glb of the descending chain of
  composition-iterates of the cfun meet @{term \<open>f \<sqinter> g\<close>} (which is below @{term ID}
  but in general not idempotent).\<close>

definition defl_meet :: "('a \<rightarrow> 'a) \<Rightarrow> ('a \<rightarrow> 'a) \<Rightarrow> ('a \<rightarrow> 'a)" where
  "defl_meet f g = glb (range (\<lambda>n. iterate n\<cdot>(f \<sqinter> g)))"

lemma defl_meet_is_glb: "is_glb (range (\<lambda>n. iterate n\<cdot>(f \<sqinter> g))) (defl_meet f g)"
  unfolding defl_meet_def by (rule glb) auto

lemma defl_meet_below_iterate: "defl_meet f g \<sqsubseteq> iterate n\<cdot>(f \<sqinter> g)"
  using defl_meet_is_glb is_glb_below by blast

lemma defl_meet_greatest: "(\<And>n. b \<sqsubseteq> iterate n\<cdot>(f \<sqinter> g)) \<Longrightarrow> b \<sqsubseteq> defl_meet f g"
  using defl_meet_is_glb is_glb_greatest by blast

lemma iterate_0_ID: "iterate 0\<cdot>F = ID"
  by (simp add: cfun_eq_iff iterate_0)

lemma defl_meet_below_ID: "defl_meet f g \<sqsubseteq> ID"
  using defl_meet_below_iterate[where n=0] by (simp add: iterate_0_ID)

lemma defl_meet_idem_below:
  "defl_meet f g oo defl_meet f g \<sqsubseteq> defl_meet f g"
proof (rule defl_meet_greatest)
  fix n
  have "defl_meet f g oo defl_meet f g \<sqsubseteq> iterate n\<cdot>(f \<sqinter> g) oo ID"
    by (intro monofun_cfun monofun_cfun_arg defl_meet_below_iterate defl_meet_below_ID)
  then show "defl_meet f g oo defl_meet f g \<sqsubseteq> iterate n\<cdot>(f \<sqinter> g)" by simp
qed

lemma defl_meet_idem:
  assumes f: "deflation f"
  shows "defl_meet f g oo defl_meet f g = defl_meet f g"
proof (rule below_antisym[OF defl_meet_idem_below])
  show "defl_meet f g \<sqsubseteq> defl_meet f g oo defl_meet f g"
    sorry
qed


section \<open>Stable subdomains as a lattice of sets\<close>

text \<open>Stable subdomains form a closure system: they contain @{term UNIV} and are
  closed under arbitrary intersection. Hence they form a complete lattice under
  inclusion, with meet given by intersection.\<close>

lemma stable_subdomain_UNIV: "stable_subdomain UNIV"
  by unfold_locales auto

lemma stable_subdomain_bot: "stable_subdomain {\<bottom>::'a}"
proof
  fix t :: 'a and T :: "'a set" assume "T \<subseteq> {\<bottom>}"
  then have "T = {} \<or> T = {\<bottom>}" by fast
  then have "T <<| \<bottom>" by auto
  moreover assume "T <<| t"
  ultimately have "t = \<bottom>" by (rule is_lub_unique[symmetric])
  then show "t \<in> {\<bottom>}" ..
qed auto

lemma stable_subdomain_Inter:
  assumes "\<And>S. S \<in> \<S> \<Longrightarrow> stable_subdomain S"
  shows "stable_subdomain (\<Inter> \<S>)"
proof (unfold_locales)
  fix x y assume "y \<in> \<Inter> \<S>" and "x \<sqsubseteq> y"
  with assms show "x \<in> \<Inter> \<S>"
    by (auto intro: stable_subdomain.downward)
next
  fix T t assume T: "T \<subseteq> \<Inter> \<S>" and lub: "T <<| t"
  show "t \<in> \<Inter> \<S>"
  proof (rule InterI)
    fix X assume "X \<in> \<S>"
    with assms have "stable_subdomain X" by simp
    moreover from T \<open>X \<in> \<S>\<close> have "T \<subseteq> X" by auto
    ultimately show "t \<in> X" using lub by (rule stable_subdomain.strong_closed)
  qed
qed

text \<open>A downward-closed set containing @{term \<bottom>} that is closed under pairwise joins
  and under lubs of chains is a stable subdomain. Closure under lubs of arbitrary
  bounded subsets follows because such a lub is the directed lub of the lubs of the
  finite subsets (Jung, via @{thm directed_join_of_finite_subsets}). This intro rule
  needs neither distributivity nor the full strong-closure assumption.\<close>

lemma stable_subdomainI:
  fixes S :: "'a set"
  assumes bot: "\<bottom> \<in> S"
    and down: "\<And>x y. y \<in> S \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> x \<in> S"
    and join: "\<And>a b. a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<Up> b \<Longrightarrow> a \<squnion> b \<in> S"
    and chain: "\<And>C. chain C \<Longrightarrow> (\<And>i. C i \<in> S) \<Longrightarrow> (\<Squnion>i. C i) \<in> S"
  shows "stable_subdomain S"
proof
  fix y x assume "y \<in> S" "x \<sqsubseteq> y" then show "x \<in> S" by (rule down)
next
  fix T t assume TS: "T \<subseteq> S" and lub: "T <<| t"
  have fin_in: "lub B \<in> S" if "finite B" "B \<subseteq> S" "B <| u" for B u
    using that
  proof (induction B arbitrary: u rule: finite_induct)
    case empty
    then show ?case using bot by (simp add: lub_eqI[OF lub_empty])
  next
    case (insert x F)
    from insert.prems have xS: "x \<in> S" and FS: "F \<subseteq> S" and ub: "insert x F <| u" by auto
    from ub have Fu: "F <| u" and xu: "x \<sqsubseteq> u" by (simp_all add: is_ub_insert)
    from insert.IH[OF FS Fu] have lubF_S: "lub F \<in> S" .
    from Fu have F_lub: "F <<| lub F" by (rule ex_bound_lub)
    from F_lub Fu have "lub F \<sqsubseteq> u" by (rule is_lubD2)
    with xu have jn: "x \<Up> lub F" by (rule joinableI)
    have "insert x F <<| x \<squnion> lub F"
    proof (rule is_lubI)
      show "insert x F <| x \<squnion> lub F"
      proof (subst is_ub_insert, intro conjI)
        show "x \<sqsubseteq> x \<squnion> lub F" using jn by (rule joinableD(1))
        show "F <| x \<squnion> lub F"
          using is_lubD1[OF F_lub] joinableD(2)[OF jn] by (rule is_ub_upward)
      qed
    next
      fix w assume "insert x F <| w"
      then have xw: "x \<sqsubseteq> w" and Fw: "F <| w" by (simp_all add: is_ub_insert)
      from F_lub Fw have "lub F \<sqsubseteq> w" by (rule is_lubD2)
      with xw show "x \<squnion> lub F \<sqsubseteq> w" by (rule join_belowI)
    qed
    then have "lub (insert x F) = x \<squnion> lub F" by (rule lub_eqI)
    with join[OF xS lubF_S jn] show ?case by simp
  qed
  define PT where "PT = {B. B \<subseteq> T \<and> finite B}"
  have flubs: "B <<| lub B" if "B \<in> PT" for B
  proof -
    from that have "B \<subseteq> T" by (simp add: PT_def)
    with is_lubD1[OF lub] have "B <| t" by (auto simp: is_ub_def)
    then show "B <<| lub B" by (rule ex_bound_lub)
  qed
  have dir: "directed (lub ` PT)"
    using flubs unfolding PT_def by (rule directed_join_of_finite_subsets(1))
  have Tlub: "T <<| lub (lub ` PT)"
    using flubs unfolding PT_def by (rule directed_join_of_finite_subsets(2))
  have subS: "lub ` PT \<subseteq> S"
  proof (rule subsetI)
    fix z assume "z \<in> lub ` PT"
    then obtain B where B: "B \<in> PT" and z: "z = lub B" by auto
    from B have fB: "finite B" and BT: "B \<subseteq> T" by (auto simp: PT_def)
    from BT TS have BS: "B \<subseteq> S" by auto
    from BT is_lubD1[OF lub] have "B <| t" by (auto simp: is_ub_def)
    with fB BS have "lub B \<in> S" by (rule fin_in)
    with z show "z \<in> S" by simp
  qed
  have ne: "lub ` PT \<noteq> {}" by (auto simp: PT_def)
  have "chain_complete S"
    unfolding chain_complete_def using chain by (auto simp: image_subset_iff)
  then have "dcomplete S" by (simp add: chain_complete_iff_dcomplete)
  with dir subS ne have "lub (lub ` PT) \<in> S" unfolding dcomplete_def by blast
  with Tlub lub show "t \<in> S" by (metis is_lub_unique)
qed

text \<open>The join of two stable subdomains is the \emph{pointwise join} (Jung, Lemma 4.1.9):
  the set of joins of pairs drawn from each, where those joins exist.  Distributivity of the
  underlying domain is what makes this set downward-closed.\<close>

lemma stable_subdomain_join:
  assumes A: "stable_subdomain A" and B: "stable_subdomain B"
  shows "stable_subdomain {a \<squnion> b |a b. a \<in> A \<and> b \<in> B \<and> a \<Up> b}"
proof -
  interpret A: stable_subdomain A by (rule A)
  interpret B: stable_subdomain B by (rule B)
  define J where "J = {a \<squnion> b |a b. a \<in> A \<and> b \<in> B \<and> a \<Up> b}"
  have memJ: "c \<in> J \<longleftrightarrow> (\<exists>a b. a \<in> A \<and> b \<in> B \<and> a \<Up> b \<and> c = a \<squnion> b)" for c
    unfolding J_def by blast
  have A_join: "a1 \<squnion> a2 \<in> A" if "a1 \<in> A" "a2 \<in> A" "a1 \<Up> a2" for a1 a2
    using A.strong_closed[OF _ join_is_lub[OF joinableD(1)[OF that(3)] joinableD(2)[OF that(3)]]] that
    by blast
  have B_join: "b1 \<squnion> b2 \<in> B" if "b1 \<in> B" "b2 \<in> B" "b1 \<Up> b2" for b1 b2
    using B.strong_closed[OF _ join_is_lub[OF joinableD(1)[OF that(3)] joinableD(2)[OF that(3)]]] that
    by blast
  have "stable_subdomain J"
  proof (rule stable_subdomainI)
    have "(\<bottom>::'a) = \<bottom> \<squnion> \<bottom>" by (simp add: join_absorbI[OF below_refl])
    then show "\<bottom> \<in> J" using A.bot_in_S B.bot_in_S joinable_refl memJ by blast
  next
    fix x y assume yJ: "y \<in> J" and xy: "x \<sqsubseteq> y"
    from yJ obtain a b where ab: "a \<in> A" "b \<in> B" "a \<Up> b" and yeq: "y = a \<squnion> b"
      using memJ by blast
    have a': "x \<sqinter> a \<in> A" by (rule A.downward[OF ab(1) meet_below2])
    have b': "x \<sqinter> b \<in> B" by (rule B.downward[OF ab(2) meet_below2])
    have jn: "x \<sqinter> a \<Up> x \<sqinter> b" by (rule joinableI[OF meet_below1 meet_below1])
    have "x = x \<sqinter> y" using xy by (simp add: meet_absorbI)
    also have "\<dots> = (x \<sqinter> a) \<squnion> (x \<sqinter> b)" unfolding yeq by (rule meet_join_distrib[OF ab(3)])
    finally have "x = (x \<sqinter> a) \<squnion> (x \<sqinter> b)" .
    with a' b' jn show "x \<in> J" using memJ by blast
  next
    fix c1 c2 assume c1J: "c1 \<in> J" and c2J: "c2 \<in> J" and j12: "c1 \<Up> c2"
    from c1J obtain a1 b1 where d1: "a1 \<in> A" "b1 \<in> B" "a1 \<Up> b1" and e1: "c1 = a1 \<squnion> b1"
      using memJ by blast
    from c2J obtain a2 b2 where d2: "a2 \<in> A" "b2 \<in> B" "a2 \<Up> b2" and e2: "c2 = a2 \<squnion> b2"
      using memJ by blast
    have c1w: "c1 \<sqsubseteq> c1 \<squnion> c2" by (rule joinableD(1)[OF j12])
    have c2w: "c2 \<sqsubseteq> c1 \<squnion> c2" by (rule joinableD(2)[OF j12])
    have a1w: "a1 \<sqsubseteq> c1 \<squnion> c2" using joinableD(1)[OF d1(3)] c1w e1 below_trans by metis
    have b1w: "b1 \<sqsubseteq> c1 \<squnion> c2" using joinableD(2)[OF d1(3)] c1w e1 below_trans by metis
    have a2w: "a2 \<sqsubseteq> c1 \<squnion> c2" using joinableD(1)[OF d2(3)] c2w e2 below_trans by metis
    have b2w: "b2 \<sqsubseteq> c1 \<squnion> c2" using joinableD(2)[OF d2(3)] c2w e2 below_trans by metis
    have aa: "a1 \<squnion> a2 \<in> A" by (rule A_join[OF d1(1) d2(1) joinableI[OF a1w a2w]])
    have bb: "b1 \<squnion> b2 \<in> B" by (rule B_join[OF d1(2) d2(2) joinableI[OF b1w b2w]])
    have aw: "a1 \<squnion> a2 \<sqsubseteq> c1 \<squnion> c2" by (rule join_belowI[OF a1w a2w])
    have bw: "b1 \<squnion> b2 \<sqsubseteq> c1 \<squnion> c2" by (rule join_belowI[OF b1w b2w])
    have jnab: "a1 \<squnion> a2 \<Up> b1 \<squnion> b2" by (rule joinableI[OF aw bw])
    have aaR: "a1 \<squnion> a2 \<sqsubseteq> (a1 \<squnion> a2) \<squnion> (b1 \<squnion> b2)" by (rule joinableD(1)[OF jnab])
    have bbR: "b1 \<squnion> b2 \<sqsubseteq> (a1 \<squnion> a2) \<squnion> (b1 \<squnion> b2)" by (rule joinableD(2)[OF jnab])
    have a1aa: "a1 \<sqsubseteq> a1 \<squnion> a2" by (rule joinableD(1)[OF joinableI[OF a1w a2w]])
    have a2aa: "a2 \<sqsubseteq> a1 \<squnion> a2" by (rule joinableD(2)[OF joinableI[OF a1w a2w]])
    have b1bb: "b1 \<sqsubseteq> b1 \<squnion> b2" by (rule joinableD(1)[OF joinableI[OF b1w b2w]])
    have b2bb: "b2 \<sqsubseteq> b1 \<squnion> b2" by (rule joinableD(2)[OF joinableI[OF b1w b2w]])
    have c1R: "c1 \<sqsubseteq> (a1 \<squnion> a2) \<squnion> (b1 \<squnion> b2)" unfolding e1
      by (rule join_belowI[OF below_trans[OF a1aa aaR] below_trans[OF b1bb bbR]])
    have c2R: "c2 \<sqsubseteq> (a1 \<squnion> a2) \<squnion> (b1 \<squnion> b2)" unfolding e2
      by (rule join_belowI[OF below_trans[OF a2aa aaR] below_trans[OF b2bb bbR]])
    have "c1 \<squnion> c2 = (a1 \<squnion> a2) \<squnion> (b1 \<squnion> b2)"
      by (rule below_antisym[OF join_belowI[OF c1R c2R] join_belowI[OF aw bw]])
    with aa bb jnab show "c1 \<squnion> c2 \<in> J" using memJ by blast
  next
    fix C :: "nat \<Rightarrow> 'a" assume chC: "chain C" and CJ: "\<And>i. C i \<in> J"
    define L where "L = (\<Squnion>i. C i)"
    have aL: "A.p\<cdot>L \<in> A" by (simp add: A.proj_in_S)
    have bL: "B.p\<cdot>L \<in> B" by (simp add: B.proj_in_S)
    have aLb: "A.p\<cdot>L \<sqsubseteq> L" by (rule A.below)
    have bLb: "B.p\<cdot>L \<sqsubseteq> L" by (rule B.below)
    have jn: "A.p\<cdot>L \<Up> B.p\<cdot>L" by (rule joinableI[OF aLb bLb])
    have CiBound: "C i \<sqsubseteq> A.p\<cdot>L \<squnion> B.p\<cdot>L" for i
    proof -
      from CJ[of i] obtain a b where ab: "a \<in> A" "b \<in> B" "a \<Up> b" and ci: "C i = a \<squnion> b"
        using memJ by blast
      have aL': "a \<sqsubseteq> A.p\<cdot>L"
      proof -
        have "a \<sqsubseteq> L" unfolding L_def
          using joinableD(1)[OF ab(3)] ci is_ub_thelub[OF chC, of i] below_trans by metis
        then have "A.p\<cdot>a \<sqsubseteq> A.p\<cdot>L" by (rule monofun_cfun_arg)
        with A.proj_fixed[OF ab(1)] show ?thesis by simp
      qed
      have bL': "b \<sqsubseteq> B.p\<cdot>L"
      proof -
        have "b \<sqsubseteq> L" unfolding L_def
          using joinableD(2)[OF ab(3)] ci is_ub_thelub[OF chC, of i] below_trans by metis
        then have "B.p\<cdot>b \<sqsubseteq> B.p\<cdot>L" by (rule monofun_cfun_arg)
        with B.proj_fixed[OF ab(2)] show ?thesis by simp
      qed
      from aL' joinableD(1)[OF jn] have "a \<sqsubseteq> A.p\<cdot>L \<squnion> B.p\<cdot>L" by (rule below_trans)
      moreover from bL' joinableD(2)[OF jn] have "b \<sqsubseteq> A.p\<cdot>L \<squnion> B.p\<cdot>L" by (rule below_trans)
      ultimately show "C i \<sqsubseteq> A.p\<cdot>L \<squnion> B.p\<cdot>L" unfolding ci by (rule join_belowI)
    qed
    have "L \<sqsubseteq> A.p\<cdot>L \<squnion> B.p\<cdot>L" using lub_below[OF chC CiBound, folded L_def] .
    moreover have "A.p\<cdot>L \<squnion> B.p\<cdot>L \<sqsubseteq> L" using aLb bLb by (rule join_belowI)
    ultimately have "L = A.p\<cdot>L \<squnion> B.p\<cdot>L" by (rule below_antisym)
    with aL bL jn have "L \<in> J" using memJ by blast
    then show "(\<Squnion>i. C i) \<in> J" unfolding L_def .
  qed
  then show ?thesis unfolding J_def .
qed

typedef 'a stable_subdom = "{S :: 'a set. stable_subdomain S}"
  morphisms set_of_subdom subdom_of_set
  using stable_subdomain_UNIV by blast

setup_lifting type_definition_stable_subdom

lemma stable_subdomain_Int:
  "stable_subdomain S \<Longrightarrow> stable_subdomain T \<Longrightarrow> stable_subdomain (S \<inter> T)"
  using stable_subdomain_Inter[of "{S, T}"] by auto

instantiation stable_subdom :: ("{bifinite,distributive_cpo}") bounded_lattice
begin
lift_definition less_eq_stable_subdom :: "'a stable_subdom \<Rightarrow> 'a stable_subdom \<Rightarrow> bool"
  is "(\<subseteq>)" .

lift_definition less_stable_subdom :: "'a stable_subdom \<Rightarrow> 'a stable_subdom \<Rightarrow> bool"
  is "(\<subset>)" .

lift_definition inf_stable_subdom :: "'a stable_subdom \<Rightarrow> 'a stable_subdom \<Rightarrow> 'a stable_subdom"
  is "(\<inter>)" by (auto intro: stable_subdomain_Int)

lift_definition sup_stable_subdom :: "'a stable_subdom \<Rightarrow> 'a stable_subdom \<Rightarrow> 'a stable_subdom"
  is "\<lambda>A B. \<Inter>{S. stable_subdomain S \<and> A \<subseteq> S \<and> B \<subseteq> S}"
  by (auto intro: stable_subdomain_Inter)

lift_definition top_stable_subdom :: "'a stable_subdom"
  is UNIV by (rule stable_subdomain_UNIV)

lift_definition bot_stable_subdom :: "'a stable_subdom"
  is "{\<bottom>}" by (rule stable_subdomain_bot)

instance
  by (standard; transfer) (auto intro: stable_subdomain.bot_in_S)

end

instantiation stable_subdom :: ("{bifinite,distributive_cpo}") complete_lattice
begin

lift_definition Inf_stable_subdom :: "'a stable_subdom set \<Rightarrow> 'a stable_subdom"
  is "\<Inter>" by (rule stable_subdomain_Inter)

lift_definition Sup_stable_subdom :: "'a stable_subdom set \<Rightarrow> 'a stable_subdom"
  is "\<lambda>\<A>. \<Inter>{S. stable_subdomain S \<and> (\<forall>A\<in>\<A>. A \<subseteq> S)}" by (auto intro: stable_subdomain_Inter)

instance
  by (standard; transfer) (auto intro: stable_subdomain.bot_in_S stable_subdomain_bot)

end

end