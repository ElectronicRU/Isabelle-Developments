theory Subdomain 
  imports HOLCF "HOLCF-extra.Directed" "HOLCF-extra.Distributive"
    "Order_Lattice_Props.Order_Lattice_Props"
  abbrevs ",," = "\<downharpoonright>"
begin

text \<open>\<open>Order_Lattice_Props\<close> switches on HOL's lattice syntax (bottom, meet, and so on), takes the
  up-arrow for up-sets, and has its own order-based notion of directedness; HOLCF's meanings win
  here.\<close>

unbundle no lattice_syntax
no_notation ord_class.upset_set (\<open>\<Up>\<close>)
hide_const (open) ord_class.directed

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
  ultimately show "x \<sqsubseteq> lub D" by (rule below_trans[rotated])
qed

lemma directed_approximants:
  fixes D :: "('a::bifinite) set"
  assumes "directed D" "D \<noteq> {}"
  shows "approximants (lub D) = (\<Union>x \<in> D. approximants x)"
  unfolding approximants_def
  using compact_directedD[OF assms] by auto

locale stable_subdomain =
  fixes S :: "'a set" (structure)
  assumes lub_closed:  "T \<subseteq> S \<Longrightarrow> T <<| t \<Longrightarrow> t \<in> S"
  assumes downward: "y \<in> S \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> x \<in> S"
begin
definition "proj a = lub {x \<in> S. x \<sqsubseteq> a}"

lemma proj_set_directed: "directed {x \<in> S. x \<sqsubseteq> a}"
proof (rule directedI, safe)
  fix x y assume S: "x \<in> S" "y \<in> S"
  assume a: "x \<sqsubseteq> a" "y \<sqsubseteq> a"
  then have lub: "{x, y} <<| (x \<squnion> y)" by (rule join_is_lub)
  from lub_closed[OF _ this] S have lubS: "x \<squnion> y \<in> S"
    by blast
  from lub have le: "x \<sqsubseteq> x \<squnion> y" "y \<sqsubseteq> x \<squnion> y" by (auto dest: is_lubD1 is_ubD)
  moreover from a have "x \<squnion> y \<sqsubseteq> a"
    using is_lubD2[OF lub, of a] by auto
  ultimately show "\<exists>z \<in> {x \<in> S. x \<sqsubseteq> a}. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
    using lubS by blast
qed

lemma bot_in_S: "\<bottom> \<in> S"
  using lub_closed[of "{}" "\<bottom>"] by simp

lemma proj_set_ne: "{x \<in> S. x \<sqsubseteq> a} \<noteq> {}"
proof -
  have "\<bottom> \<in> {x \<in> S. x \<sqsubseteq> a}" using bot_in_S by simp
  then show ?thesis by auto
qed

corollary proj_is_lub: "{x \<in> S. x \<sqsubseteq> a} <<| proj a"
  unfolding proj_def using proj_set_directed by (rule directed_lub)

corollary proj_in_S: "proj a \<in> S"
  using lub_closed[OF _ proj_is_lub] by blast

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

corollary below_proj_of: "a \<in> S \<Longrightarrow> a \<sqsubseteq> x \<Longrightarrow> a \<sqsubseteq> proj x"
  using proj_is_lub[THEN is_lubD1, THEN is_ubD] by blast

lemma proj_monoD: "x \<sqsubseteq> y \<Longrightarrow> proj x \<sqsubseteq> proj y"
  by (rule monofunE[OF proj_mono])

text \<open>Jung, Lemma 4.1.6(i): the projection of \<open>x\<close> below some \<open>y \<in> S\<close> is the meet \<open>x \<sqinter> y\<close>.\<close>
lemma proj_meet:
  assumes y: "y \<in> S" and le: "proj x \<sqsubseteq> y"
  shows "proj x = x \<sqinter> y"
proof (rule below_antisym)
  show "proj x \<sqsubseteq> x \<sqinter> y" using proj_below le by (rule meet_greatest)
  have "x \<sqinter> y \<in> S" using downward[OF y meet_below2] .
  moreover have "x \<sqinter> y \<sqsubseteq> x" by (rule meet_below1)
  ultimately show "x \<sqinter> y \<sqsubseteq> proj x" by (rule below_proj_of)
qed

text \<open>Jung, Lemma 4.1.6(ii) (binary form): the projection preserves existing joins.
  This is where distributivity of the domain is used.\<close>
lemma proj_join:
  assumes j: "x \<Up> y"
  shows "proj (x \<squnion> y) = proj x \<squnion> proj y"
proof -
  have px: "proj x = x \<sqinter> proj (x \<squnion> y)"
    by (rule proj_meet[OF proj_in_S proj_monoD[OF joinableD(1)[OF j]]])
  have py: "proj y = y \<sqinter> proj (x \<squnion> y)"
    by (rule proj_meet[OF proj_in_S proj_monoD[OF joinableD(2)[OF j]]])
  have "proj x \<squnion> proj y = (x \<sqinter> proj (x \<squnion> y)) \<squnion> (y \<sqinter> proj (x \<squnion> y))"
    using px py by simp
  also have "\<dots> = (x \<squnion> y) \<sqinter> proj (x \<squnion> y)"
    by (rule meet_join_distrib2[OF j, symmetric])
  also have "\<dots> = proj (x \<squnion> y)"
    by (metis meet_sym meet_absorbI proj_below)
  finally show ?thesis by (rule sym)
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

definition p where "p \<equiv> \<Lambda> a. proj a"

lemma p_beta: "p\<cdot>x = proj x"
  unfolding p_def
  by (simp add: proj_cont)

lemma deflation_p: "deflation p"
proof
  show "p\<cdot>(p\<cdot>x) = p\<cdot>x" for x
    using proj_in_S proj_fixed
    by (simp add: p_beta)
  show "p\<cdot>x \<sqsubseteq> x" for x
    using proj_below by (simp add: p_beta)
qed

sublocale deflation p by (rule deflation_p)

text \<open>\<open>p\<close>-form duplicates of the projection lemmas.  Since \<open>p_beta\<close> (\<open>p\<cdot>x = proj x\<close>) is
  deliberately not a simp rule — it rewrites \<open>p\<cdot>x\<close> against \<open>deflation.below\<close> etc. — we
  restate the projection facts directly for \<open>p\<cdot>x\<close> via \<open>proj = Rep_cfun p\<close> and use those.\<close>
lemma proj_Rep_p: "proj = Rep_cfun p"
  by (rule ext) (simp add: p_beta)

lemmas p_in_S[simp] = proj_in_S[unfolded proj_Rep_p]
lemmas p_below = proj_below[unfolded proj_Rep_p]
lemmas p_fixed = proj_fixed[unfolded proj_Rep_p]
lemmas p_fixed_iff = proj_fixed_iff[unfolded proj_Rep_p]
lemmas below_p_of = below_proj_of[unfolded proj_Rep_p]
lemmas p_meet = proj_meet[unfolded proj_Rep_p]
lemmas p_join = proj_join[unfolded proj_Rep_p]

lemma p_fixes: "{x. p\<cdot>x = x} = S"
  by (simp add: proj_fixed_iff p_beta)

lemma p_range: "range (\<lambda>x. p\<cdot>x) = S"
  by (simp only: p_fixes range_eq_fixes)

end


locale semi_factor_subdomain = stable_subdomain +
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

lemma deflation_lub_closed:
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
  with deflation_lub_closed[OF d] show "t \<in> {x. d\<cdot>x = x}" by simp
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
    from deflation_lub_closed[OF defl this rcx]
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
    and Q_lub_closed: "\<And>A a. A \<subseteq> Q \<Longrightarrow> A <<| a \<Longrightarrow> a \<in> Q"
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
  from Q_lub_closed[OF this l] have lQ: "l \<in> Q" .
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


text \<open>Continuity of binary meet (@{thm [source] cont_meet_arg}) is in \<open>Distributive\<close>.\<close>


section \<open>Stable subdomains as a lattice of sets\<close>

text \<open>Stable subdomains form a closure system: they contain @{term UNIV} and are
  closed under arbitrary intersection. Hence they form a complete lattice under
  inclusion, with meet given by intersection.\<close>

lemma stable_subdomain_UNIV: "stable_subdomain UNIV"
  by unfold_locales auto

lemma p_UNIV: "stable_subdomain.p UNIV\<cdot>x = x"
  by (simp add: stable_subdomain.p_fixed[OF stable_subdomain_UNIV])

lemma stable_subdomain_bot: "stable_subdomain {\<bottom>::'a}"
proof
  fix t :: 'a and T :: "'a set" assume "T \<subseteq> {\<bottom>}"
  then have "T = {} \<or> T = {\<bottom>}" by fast
  then have "T <<| \<bottom>" by auto
  moreover assume "T <<| t"
  ultimately have "t = \<bottom>" by (rule is_lub_unique[symmetric])
  then show "t \<in> {\<bottom>}" ..
qed auto

lemma p_bot: "stable_subdomain.p {\<bottom>}\<cdot>x = \<bottom>"
  using stable_subdomain.p_in_S[OF stable_subdomain_bot] by fast

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
    ultimately show "t \<in> X" using lub by (rule stable_subdomain.lub_closed)
  qed
qed

text \<open>Jung, Lemma 4.1.5(ii) (one direction): a finer stable subdomain has a smaller projection.\<close>
(* NOTE: this can be shown without going to definitions by lemma deflation.belowI *)
lemma proj_mono_subdomain:
  assumes A: "stable_subdomain A" and S: "stable_subdomain S" and sub: "A \<subseteq> S"
  shows "stable_subdomain.proj A x \<sqsubseteq> stable_subdomain.proj S x"
proof -
  interpret A: stable_subdomain A by (rule A)
  interpret S: stable_subdomain S by (rule S)
  have "{a \<in> A. a \<sqsubseteq> x} \<subseteq> {s \<in> S. s \<sqsubseteq> x}" using sub by blast
  with A.proj_is_lub S.proj_is_lub show "A.proj x \<sqsubseteq> S.proj x"
    by (rule lub_subset_mono)
qed

text \<open>The projection-cfun version of @{thm proj_mono_subdomain}.\<close>
lemma p_mono_subdomain:
  assumes A: "stable_subdomain A" and S: "stable_subdomain S" and sub: "A \<subseteq> S"
  shows "stable_subdomain.p A \<sqsubseteq> stable_subdomain.p S"
proof (rule cfun_belowI)
  fix x
  interpret A: stable_subdomain A by (rule A)
  interpret S: stable_subdomain S by (rule S)
  show "stable_subdomain.p A\<cdot>x \<sqsubseteq> stable_subdomain.p S\<cdot>x"
    using proj_mono_subdomain[OF A S sub] by (simp add: A.p_beta S.p_beta)
qed

text \<open>The join of two stable subdomains is the \emph{pointwise join} (Jung, Lemma 4.1.9):
  the set of joins of pairs drawn from each, where those joins exist.  Distributivity of the
  underlying domain is what makes this set downward-closed.\<close>

context
  fixes A B J
  assumes A: "stable_subdomain A" and B: "stable_subdomain B"
  defines "J \<equiv> {a \<squnion> b |a b. a \<in> A \<and> b \<in> B \<and> a \<Up> b}"
begin
interpretation A: stable_subdomain A by (rule A)
interpretation B: stable_subdomain B by (rule B)

private lemma memJ: "c \<in> J \<longleftrightarrow> (\<exists>a b. a \<in> A \<and> b \<in> B \<and> a \<Up> b \<and> c = a \<squnion> b)" for c
  unfolding J_def by blast

lemma A_sub_join: "A \<subseteq> J"
  using B.bot_in_S
  apply (intro subsetI)
  unfolding memJ
  by fastforce

lemma B_sub_join: "B \<subseteq> J"
  using A.bot_in_S
  apply (intro subsetI)
  unfolding memJ
  by fastforce

lemma J_join: fixes x assumes "x \<in> J"
  shows "A.p\<cdot>x \<squnion> B.p\<cdot>x = x"
proof (rule below_antisym)
  from assms memJ obtain a b where a: "a \<in> A" and b: "b \<in> B"
    and ab: "a \<Up> b" and x: "x = a \<squnion> b"
    by blast
  from ab x have "a \<sqsubseteq> x" using joinableD by simp
  with a have 1: "a \<sqsubseteq> A.p\<cdot>x" by (rule A.below_p_of)
  from ab x have "b \<sqsubseteq> x" using joinableD by simp
  with b have 2: "b \<sqsubseteq> B.p\<cdot>x" by (rule B.below_p_of)
  have jn: "A.p\<cdot>x \<Up> B.p\<cdot>x" by (rule joinableI[OF A.below B.below])
  from 1 2 joinableD[OF this]
  show "x \<sqsubseteq> A.p\<cdot>x \<squnion> B.p\<cdot>x" unfolding x
    using join_belowI[where x=a and y=b] below_trans
    by blast
next
  from A.below B.below
  show "A.p\<cdot>x \<squnion> B.p\<cdot>x \<sqsubseteq> x"
    by (rule join_belowI)
qed

lemma stable_subdomain_join:
  "stable_subdomain J"
proof    
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
  fix T t assume TJ: "T \<subseteq> J" and lub: "T <<| t"
  \<comment> \<open>Every existing lub of \<open>J\<close>-elements is recovered by projecting onto each side:
      \<open>t = p\<^sub>A t \<squnion> p\<^sub>B t\<close>.  No pairwise/chain case-split is needed.\<close>
  have aT: "A.p\<cdot>t \<in> A" by (simp add: A.proj_in_S A.p_beta)
  have bT: "B.p\<cdot>t \<in> B" by (simp add: B.proj_in_S B.p_beta)
  have aTb: "A.p\<cdot>t \<sqsubseteq> t" by (rule A.below)
  have bTb: "B.p\<cdot>t \<sqsubseteq> t" by (rule B.below)
  have jn: "A.p\<cdot>t \<Up> B.p\<cdot>t" by (rule joinableI[OF aTb bTb])
  have ub: "x \<sqsubseteq> A.p\<cdot>t \<squnion> B.p\<cdot>t" if xT: "x \<in> T" for x
  proof -
    from xT TJ have "x \<in> J" by blast
    then obtain a b where ab: "a \<in> A" "b \<in> B" "a \<Up> b" and xeq: "x = a \<squnion> b"
      using memJ by blast
    have xt: "x \<sqsubseteq> t" by (rule is_ubD[OF is_lubD1[OF lub] xT])
    have "a \<sqsubseteq> t" using joinableD(1)[OF ab(3)] xeq xt below_trans by metis
    with ab(1) have aPt: "a \<sqsubseteq> A.p\<cdot>t" by (rule A.below_p_of)
    have "b \<sqsubseteq> t" using joinableD(2)[OF ab(3)] xeq xt below_trans by metis
    with ab(2) have bPt: "b \<sqsubseteq> B.p\<cdot>t" by (rule B.below_p_of)
    from aPt joinableD(1)[OF jn] have "a \<sqsubseteq> A.p\<cdot>t \<squnion> B.p\<cdot>t" by (rule below_trans)
    moreover from bPt joinableD(2)[OF jn] have "b \<sqsubseteq> A.p\<cdot>t \<squnion> B.p\<cdot>t" by (rule below_trans)
    ultimately show "x \<sqsubseteq> A.p\<cdot>t \<squnion> B.p\<cdot>t" unfolding xeq by (rule join_belowI)
  qed
  have "t \<sqsubseteq> A.p\<cdot>t \<squnion> B.p\<cdot>t" by (rule is_lubD2[OF lub is_ubI[OF ub]])
  moreover have "A.p\<cdot>t \<squnion> B.p\<cdot>t \<sqsubseteq> t" using aTb bTb by (rule join_belowI)
  ultimately have "t = A.p\<cdot>t \<squnion> B.p\<cdot>t" by (rule below_antisym)
  with aT bT jn show "t \<in> J" using memJ by blast
qed

interpretation J: stable_subdomain J by (rule stable_subdomain_join)


lemma pA_below_pJ: "A.p \<sqsubseteq> J.p"
  using A stable_subdomain_join A_sub_join
  by (rule p_mono_subdomain)

lemma pB_below_pJ: "B.p \<sqsubseteq> J.p"
  using B stable_subdomain_join B_sub_join
  by (rule p_mono_subdomain)

lemma proj_joinable[simp]: "A.p\<cdot>x \<Up> B.p\<cdot>x"
  using A.below B.below by (rule joinableI)

lemma stable_subdomain_join_proj:
  "A.p\<cdot>y \<squnion> B.p\<cdot>y = J.p\<cdot>y"
proof -
  have "A.p\<cdot>(J.p\<cdot>y) \<squnion> B.p\<cdot>(J.p\<cdot>y) = J.p\<cdot>y"
    by (rule J_join) simp
  also have "A.p\<cdot>(J.p\<cdot>y) = A.p\<cdot>y"
    using deflation_below_comp1[OF A.deflation_p J.deflation_p]
      pA_below_pJ
    .
  also have "B.p\<cdot>(J.p\<cdot>y) = B.p\<cdot>y"
    using deflation_below_comp1[OF B.deflation_p J.deflation_p]
      pB_below_pJ
    .
  finally show "A.p\<cdot>y \<squnion> B.p\<cdot>y = J.p\<cdot>y" .
qed

text \<open>Jung, Lemma 4.1.9(i): the pointwise join of two semi-factors again satisfies the
  slide condition.  The projection of the join decomposes as \<open>p\<^bsub>A\<^esub> y \<squnion> p\<^bsub>B\<^esub> y\<close>, and the
  argument slides first through @{term A} and then through @{term B}.\<close>

lemma semi_factor_subdomain_join':
  assumes As: "semi_factor_subdomain A" and Bs: "semi_factor_subdomain B"
  shows "semi_factor_subdomain J"
proof
  interpret As: semi_factor_subdomain A by (rule As)
  interpret Bs: semi_factor_subdomain B by (rule Bs)
  fix x y assume yJ: "y \<in> J" and pJx_y: "J.p\<cdot>x \<sqsubseteq> y"
  define pa where "pa = A.p\<cdot>y"
  define pb where "pb = B.p\<cdot>y"
  have paA: "pa \<in> A" unfolding pa_def by simp
  have pbB: "pb \<in> B" unfolding pb_def by simp
  have pay: "pa \<sqsubseteq> y" unfolding pa_def by (rule A.p_below)
  have yab: "y = pa \<squnion> pb" unfolding pa_def pb_def using J_join[OF yJ] ..
  \<comment> \<open>\<open>p\<^bsub>A\<^esub> x \<sqsubseteq> pa\<close>, hence by @{term A}'s slide condition \<open>x \<Up> pa\<close>.\<close>
  from pA_below_pJ have pAxJ: "A.p\<cdot>x \<sqsubseteq> J.p\<cdot>x"
    by (rule monofun_cfun_fun)
  then have "A.p\<cdot>x \<sqsubseteq> y" using pJx_y by (rule below_trans)
  then have pAx_pa: "A.p\<cdot>x \<sqsubseteq> pa" unfolding pa_def
    by (auto intro: A.below_p_of)
  from As.slide_rule[OF paA this] have x_pa: "x \<Up> pa" .
  have pa_x: "pa \<Up> x" using x_pa by (simp add: joinable_sym)
  \<comment> \<open>\<open>p\<^bsub>B\<^esub> (pa \<squnion> x) \<sqsubseteq> pb\<close>, hence by @{term B}'s slide condition \<open>pa \<squnion> x \<Up> pb\<close>.\<close>
  from pay have pBpa_pb: "B.p\<cdot>pa \<sqsubseteq> pb" unfolding pb_def by (rule monofun_cfun_arg)
  from pB_below_pJ have "B.p\<cdot>x \<sqsubseteq> J.p\<cdot>x" by (rule monofun_cfun_fun)
  then have "B.p\<cdot>x \<sqsubseteq> y" using pJx_y by (rule below_trans)
  then have pBx_pb: "B.p\<cdot>x \<sqsubseteq> pb" unfolding pb_def
    by (auto intro: B.below_p_of)
  have "B.p\<cdot>(pa \<squnion> x) = B.p\<cdot>pa \<squnion> B.p\<cdot>x" by (rule B.p_join[OF pa_x])
  also have "B.p\<cdot>pa \<squnion> B.p\<cdot>x \<sqsubseteq> pb" using pBpa_pb pBx_pb by (rule join_belowI)
  finally have "B.p\<cdot>(pa \<squnion> x) \<sqsubseteq> pb" .
  from Bs.slide_rule[OF pbB this] have pax_pb: "pa \<squnion> x \<Up> pb" .
  \<comment> \<open>Both \<open>x\<close> and \<open>y\<close> lie below \<open>(pa \<squnion> x) \<squnion> pb\<close>, so \<open>x \<Up> y\<close>.\<close>
  from joinableD[OF pa_x] joinableD[OF pax_pb]
  have "x \<sqsubseteq> (pa \<squnion> x) \<squnion> pb" "y \<sqsubseteq> (pa \<squnion> x) \<squnion> pb"
    unfolding yab by (auto intro: join_belowI below_trans)
  then show "x \<Up> y" by (rule joinableI)
qed

text \<open>@{term J} is the \emph{least} stable subdomain containing both @{term A} and
  @{term B}: any stable @{term K} above both is closed under the joinable joins that
  generate @{term J}.\<close>
lemma J_below:
  assumes AK: "A \<subseteq> K" and BK: "B \<subseteq> K" and K: "stable_subdomain K"
  shows "J \<subseteq> K"
proof (rule subsetI)
  fix x assume "x \<in> J"
  then obtain a b where a: "a \<in> A" and b: "b \<in> B" and ab: "a \<Up> b" and x: "x = a \<squnion> b"
    using memJ by blast
  interpret K: stable_subdomain K by (rule K)
  have "{a, b} \<subseteq> K" using a b AK BK by blast
  moreover have "{a, b} <<| a \<squnion> b"
    by (rule join_is_lub[OF joinableD(1)[OF ab] joinableD(2)[OF ab]])
  ultimately have "a \<squnion> b \<in> K" by (rule K.lub_closed)
  with x show "x \<in> K" by simp
qed

text \<open>Hence @{term J} is the carrier of the lattice join of @{term A} and @{term B}.\<close>
lemma J_eq_Inter: "J = \<Inter>{S. stable_subdomain S \<and> A \<subseteq> S \<and> B \<subseteq> S}" (is "J = \<Inter>?\<S>")
proof
  show "J \<subseteq> \<Inter>?\<S>"
  proof (rule Inter_greatest)
    fix X assume "X \<in> ?\<S>"
    then have "A \<subseteq> X" "B \<subseteq> X" "stable_subdomain X" by auto
    then show "J \<subseteq> X" by (rule J_below)
  qed
  have "J \<in> ?\<S>" using stable_subdomain_join A_sub_join B_sub_join by blast
  then show "\<Inter>?\<S> \<subseteq> J" by (rule Inter_lower)
qed

end

lemma semi_factor_subdomain_join: "semi_factor_subdomain A \<Longrightarrow> semi_factor_subdomain B \<Longrightarrow>
  semi_factor_subdomain {a \<squnion> b |a b. a \<in> A \<and> b \<in> B \<and> a \<Up> b}"
  using semi_factor_subdomain_join'[OF semi_factor_subdomain.axioms(1) semi_factor_subdomain.axioms(1)]
  by fast

lemma lub_join:
  assumes "insert x X <<| l" and "X <<| m"
  shows "l = x \<squnion> m"
  unfolding join_def
proof (intro lub_eqI[symmetric] is_lubI, simp_all, safe)
  from lub_subset_mono[OF assms(2) assms(1)]
  show "m \<sqsubseteq> l" by auto
  from lub_subset_mono[OF is_lub_singleton assms(1)]
  show "x \<sqsubseteq> l" by auto
  fix u assume "m \<sqsubseteq> u"
  then have "X <| u"
    using assms(2) is_lubD1 is_ub_upward by blast
  moreover assume "x \<sqsubseteq> u"
  ultimately have "insert x X <| u" by simp
  with assms(1) show "l \<sqsubseteq> u" by (rule is_lubD2)
qed

text \<open>A nonempty family of stable subdomains that is up-directed by inclusion.  Its
  projections form an up-directed set of deflations bounded by @{term ID}, so their lub
  @{term dd} exists.  We show that @{term dd} is below the identity and — the key new
  content, following the user's sketch — that its set of fixed points is downward-closed.
  The latter is exactly where @{thm cont_directed_lub} (meet preserves directed lubs) enters.\<close>
locale directed_stable_family =
  fixes \<A> :: "'a set set"
  assumes stable: "A \<in> \<A> \<Longrightarrow> stable_subdomain A"
    and updir: "\<lbrakk>A \<in> \<A>; B \<in> \<A>\<rbrakk> \<Longrightarrow> \<exists>C\<in>\<A>. A \<subseteq> C \<and> B \<subseteq> C"
    and nonempty: "\<A> \<noteq> {}"
begin

definition "P = stable_subdomain.p ` \<A>"
definition "dd = lub P"

lemma P_ne: "P \<noteq> {}" using nonempty unfolding P_def by blast
lemma P_directed: "directed P"
  unfolding P_def
  by (intro directedI, simp, safe)
    (metis updir p_mono_subdomain[OF stable stable])

lemma P_dd: "P <<| dd" unfolding dd_def using P_directed by (rule directed_lub)

lemma deflation_dd: "deflation dd"
  unfolding dd_def
  using directed_admD[OF adm_deflation P_directed P_ne]
    stable[THEN stable_subdomain.deflation_p]
  by (simp add: P_def)

lemma dd_app_is_lub: "(\<lambda>A. stable_subdomain.p A\<cdot>x) ` \<A> <<| dd\<cdot>x"
  using cont_directed_is_lub[OF cont_Rep_cfun1 P_directed P_ne]
  unfolding dd_def P_def
  by (simp add: image_image)

corollary dd_app: "dd\<cdot>x = lub ((\<lambda>A. stable_subdomain.p A\<cdot>x) ` \<A>)"
  using dd_app_is_lub by (rule lub_eqI[symmetric])

lemma dd_below: "dd\<cdot>x \<sqsubseteq> x" using deflation_dd by (rule deflation.below)

text \<open>Jung, Lemma 4.1.9(iii) ingredient: the fixed-point set of @{term dd} is downward
  closed.  If @{term \<open>dd\<cdot>x = x\<close>} and @{term \<open>y \<sqsubseteq> x\<close>} then, projecting through each member,
  @{term \<open>stable_subdomain.p A\<cdot>y = y \<sqinter> stable_subdomain.p A\<cdot>x\<close>} (Lemma 4.1.6(i)); since the
  pointwise projections form a directed set and meet is continuous, the lub commutes with
  the meet, giving @{term \<open>dd\<cdot>y = y \<sqinter> x\<close>}, which is @{term y}.\<close>
lemma dd_fixed_downward:
  assumes fx: "dd\<cdot>x = x" and yx: "y \<sqsubseteq> x"
  shows "dd\<cdot>y = y"
proof -
  define Px where "Px = (\<lambda>A. stable_subdomain.p A\<cdot>x) ` \<A>"
  have ddx: "dd\<cdot>x = lub Px" unfolding Px_def by (rule dd_app)
  have Pxeq: "(\<lambda>p. p\<cdot>x) ` P = Px" unfolding P_def Px_def by (simp add: image_image)
  have dirPx: "directed Px"
    unfolding Pxeq[symmetric]
    by (fast intro: directed_mono_image[OF _ P_directed] monofun_cfun_fun)
  have nePx: "Px \<noteq> {}" unfolding Px_def using nonempty by blast
  have key: "stable_subdomain.p A\<cdot>y = y \<sqinter> stable_subdomain.p A\<cdot>x" if A: "A \<in> \<A>" for A
  proof -
    interpret A: stable_subdomain A using A by (rule stable)
    have "A.p\<cdot>x \<in> A" by (simp add: A.proj_in_S)
    moreover have le: "A.p\<cdot>y \<sqsubseteq> A.p\<cdot>x" using yx by (rule monofun_cfun_arg)
    ultimately show "A.p\<cdot>y = y \<sqinter> A.p\<cdot>x" by (rule A.p_meet)
  qed
  have "dd\<cdot>y = lub ((\<lambda>A. stable_subdomain.p A\<cdot>y) ` \<A>)" by (rule dd_app)
  also have "(\<lambda>A. stable_subdomain.p A\<cdot>y) ` \<A> = (\<lambda>A. y \<sqinter> stable_subdomain.p A\<cdot>x) ` \<A>"
    by (rule image_cong[OF refl]) (simp add: key)
  also have "(\<lambda>A. y \<sqinter> stable_subdomain.p A\<cdot>x) ` \<A> = (\<lambda>z. y \<sqinter> z) ` Px"
    unfolding Px_def by (simp add: image_image)
  also have "lub ((\<lambda>z. y \<sqinter> z) ` Px) = y \<sqinter> lub Px"
    by (rule cont_directed_lub[OF cont_meet_arg2 dirPx nePx])
  also have "y \<sqinter> lub Px = y" by (metis ddx fx yx meet_absorbI)
  finally show "dd\<cdot>y = y" .
qed

lemma proj_at_directed: "directed ((\<lambda>A. stable_subdomain.p A\<cdot>x) ` \<A>)"
proof -
  have "(\<lambda>p. p\<cdot>x) ` P = (\<lambda>A. stable_subdomain.p A\<cdot>x) ` \<A>"
    unfolding P_def by (simp add: image_image)
  moreover have "directed ((\<lambda>p. p\<cdot>x) ` P)"
    by (fast intro: directed_mono_image[OF _ P_directed] monofun_cfun_fun)
  ultimately show ?thesis by simp
qed

text \<open>The fixed points of @{term dd} form a stable subdomain (downward by
  @{thm dd_fixed_downward}, closed under existing lubs since @{term dd} is monotone and below @{term ID}).\<close>
lemma dd_fixes_stable: "stable_subdomain {x. dd\<cdot>x = x}"
proof
  fix x y assume "y \<in> {x. dd\<cdot>x = x}" and yx: "x \<sqsubseteq> y"
  then have "dd\<cdot>y = y" by simp
  from this yx have "dd\<cdot>x = x" by (rule dd_fixed_downward)
  then show "x \<in> {x. dd\<cdot>x = x}" by simp
next
  fix T t assume TF: "T \<subseteq> {x. dd\<cdot>x = x}" and lub: "T <<| t"
  have "T <| dd\<cdot>t"
  proof (rule is_ubI)
    fix z assume zT: "z \<in> T"
    then have "dd\<cdot>z = z" using TF by auto
    moreover have "z \<sqsubseteq> t" using is_ubD[OF is_lubD1[OF lub] zT] .
    ultimately show "z \<sqsubseteq> dd\<cdot>t" using monofun_cfun_arg by metis
  qed
  with lub have "t \<sqsubseteq> dd\<cdot>t" by (rule is_lubD2)
  with dd_below[of t] have "dd\<cdot>t = t" by (rule below_antisym)
  then show "t \<in> {x. dd\<cdot>x = x}" by simp
qed

text \<open>Each base subdomain consists of points fixed by @{term dd}: for \<open>a \<in> A\<close> we have
  \<open>a = p\<^bsub>A\<^esub>\<cdot>a \<sqsubseteq> dd\<cdot>a \<sqsubseteq> a\<close>.\<close>
lemma base_below_dd_fixes:
  assumes A: "A \<in> \<A>" shows "A \<subseteq> {x. dd\<cdot>x = x}"
proof (rule subsetI)
  fix a assume aA: "a \<in> A"
  interpret A: stable_subdomain A using A by (rule stable)
  have pmem: "stable_subdomain.p A \<in> P" unfolding P_def using A by blast
  have "a = A.p\<cdot>a" using aA by (simp add: A.p_fixed)
  also have "A.p\<cdot>a \<sqsubseteq> dd\<cdot>a" using is_ubD[OF is_lubD1[OF P_dd] pmem] by (rule monofun_cfun_fun)
  finally have "a \<sqsubseteq> dd\<cdot>a" .
  with dd_below[of a] have "dd\<cdot>a = a" by (rule below_antisym)
  then show "a \<in> {x. dd\<cdot>x = x}" by simp
qed

text \<open>\dots\ and the fixes are the \emph{least} such stable subdomain: any stable @{term S}
  containing every base set contains them.  Each \<open>p\<^bsub>A\<^esub>\<cdot>x \<in> A \<subseteq> S\<close>;
  their (directed) lub is @{term \<open>dd\<cdot>x = x\<close>}, which @{term S} contains, being closed under lubs.\<close>
lemma dd_fixes_least:
  assumes S: "stable_subdomain S" and sub: "\<And>A. A \<in> \<A> \<Longrightarrow> A \<subseteq> S"
  shows "{x. dd\<cdot>x = x} \<subseteq> S"
proof (rule subsetI)
  fix x assume "x \<in> {x. dd\<cdot>x = x}"
  then have fx: "dd\<cdot>x = x" by simp
  interpret S: stable_subdomain S by (rule S)
  have "(\<lambda>A. stable_subdomain.p A\<cdot>x) ` \<A> \<subseteq> S"
  proof (rule subsetI)
    fix z assume "z \<in> (\<lambda>A. stable_subdomain.p A\<cdot>x) ` \<A>"
    then obtain A where A: "A \<in> \<A>" and z: "z = stable_subdomain.p A\<cdot>x" by blast
    interpret A: stable_subdomain A using A by (rule stable)
    from A.p_in_S[of x] sub[OF A] z show "z \<in> S" by auto
  qed
  moreover have "(\<lambda>A. stable_subdomain.p A\<cdot>x) ` \<A> <<| x"
  proof -
    have "(\<lambda>A. stable_subdomain.p A\<cdot>x) ` \<A> <<| lub ((\<lambda>A. stable_subdomain.p A\<cdot>x) ` \<A>)"
      by (rule directed_lub[OF proj_at_directed])
    moreover have "lub ((\<lambda>A. stable_subdomain.p A\<cdot>x) ` \<A>) = x" using dd_app[of x] fx by simp
    ultimately show ?thesis by simp
  qed
  ultimately show "x \<in> S" by (rule S.lub_closed)
qed

text \<open>Combining the three facts: the fixes of @{term dd} are exactly the least stable
  subdomain containing every member of the family — i.e. the carrier of its supremum.\<close>
lemma dd_fixes_eq_Inter:
  "{x. dd\<cdot>x = x} = \<Inter>{S. stable_subdomain S \<and> (\<forall>A\<in>\<A>. A \<subseteq> S)}"
  (is "?Fix = \<Inter>?\<S>")
proof
  show "?Fix \<subseteq> \<Inter>?\<S>"
  proof (rule Inter_greatest)
    fix X assume "X \<in> ?\<S>"
    then have X: "stable_subdomain X" and sub: "\<forall>A\<in>\<A>. A \<subseteq> X" by auto
    show "?Fix \<subseteq> X"
    proof (rule dd_fixes_least[OF X])
      fix A assume "A \<in> \<A>" with sub show "A \<subseteq> X" by blast
    qed
  qed
  have "?Fix \<in> ?\<S>" using dd_fixes_stable base_below_dd_fixes by blast
  then show "\<Inter>?\<S> \<subseteq> ?Fix" by (rule Inter_lower)
qed


end

typedef 'a stable_subdom = "{S :: 'a set. stable_subdomain S}"
  morphisms set_of_subdom subdom_of_set
  using stable_subdomain_UNIV by blast

setup_lifting type_definition_stable_subdom

lemma stable_subdomain_Int:
  "stable_subdomain S \<Longrightarrow> stable_subdomain T \<Longrightarrow> stable_subdomain (S \<inter> T)"
  using stable_subdomain_Inter[of "{S, T}"] by auto

lift_definition stable_subdom_p :: "'a stable_subdom \<Rightarrow> 'a \<rightarrow> 'a"
   (\<open>\<p>\<index>\<close>)
is "stable_subdomain.p" .

lemma stable_subdomain_of_set_of_subdom:
  "stable_subdomain (set_of_subdom A)"
  using set_of_subdom by auto

interpretation subdom: stable_subdomain "set_of_subdom A"
  rewrites "stable_subdomain.p (set_of_subdom A) \<equiv> \<p>\<^bsub>A\<^esub>"
  by (simp_all add: stable_subdomain_of_set_of_subdom stable_subdom_p.rep_eq)

instantiation stable_subdom :: ("{bifinite,distributive_cpo}") bounded_lattice
begin
lift_definition less_eq_stable_subdom :: "'a stable_subdom \<Rightarrow> 'a stable_subdom \<Rightarrow> bool"
  is "(\<subseteq>)" .

lift_definition less_stable_subdom :: "'a stable_subdom \<Rightarrow> 'a stable_subdom \<Rightarrow> bool"
  is "(\<subset>)" .

lift_definition inf_stable_subdom :: "'a stable_subdom \<Rightarrow> 'a stable_subdom \<Rightarrow> 'a stable_subdom"
  is "(\<inter>)" by (auto intro: stable_subdomain_Int)

lift_definition sup_stable_subdom :: "'a stable_subdom \<Rightarrow> 'a stable_subdom \<Rightarrow> 'a stable_subdom"
  is "\<lambda>A B. {p \<squnion> q |p q. p \<in> A \<and> q \<in> B \<and> p \<Up> q}"
  by (auto intro: stable_subdomain_join)

lift_definition top_stable_subdom :: "'a stable_subdom"
  is UNIV by (rule stable_subdomain_UNIV)

lift_definition bot_stable_subdom :: "'a stable_subdom"
  is "{\<bottom>}" by (rule stable_subdomain_bot)

instance
  by (standard; transfer) (auto intro: stable_subdomain.bot_in_S simp add: J_eq_Inter)

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

lemma p_fixes: "\<p>\<^bsub>A\<^esub>\<cdot>x = x \<longleftrightarrow> x \<in> set_of_subdom A"
  using subdom.p_fixes
  by auto

lemma le_of_p_below: "\<p>\<^bsub>A\<^esub> \<sqsubseteq> \<p>\<^bsub>B\<^esub> \<Longrightarrow> A \<le> B"
  using subdom.deflation_p p_fixes deflation.belowD
  unfolding less_eq_stable_subdom.rep_eq
  by fast

lemma p_below_of_le: "A \<le> B \<Longrightarrow> \<p>\<^bsub>A\<^esub> \<sqsubseteq> \<p>\<^bsub>B\<^esub>"
  by transfer (intro p_mono_subdomain)

lemma p_below_iff_le: "\<p>\<^bsub>A\<^esub> \<sqsubseteq> \<p>\<^bsub>B\<^esub> \<longleftrightarrow> A \<le> B"
  using le_of_p_below p_below_of_le ..

text \<open>The bottom subdomain @{term \<open>{\<bottom>}\<close>} satisfies the slide condition trivially.\<close>
lemma semi_factor_subdomain_bot: "semi_factor_subdomain {\<bottom>}"
proof (intro semi_factor_subdomain.intro[OF stable_subdomain_bot] semi_factor_subdomain_axioms.intro)
  fix x y assume "y \<in> {\<bottom>}" and "stable_subdomain.p {\<bottom>}\<cdot>x \<sqsubseteq> y"
  then have "y = \<bottom>" by simp
  then show "x \<Up> y" by simp
qed

definition "is_semi_factor A \<equiv> semi_factor_subdomain (set_of_subdom A)"

lemma is_semi_factorI:
  assumes slide: "\<And>x y. y \<in> set_of_subdom A \<Longrightarrow> \<p>\<^bsub>A\<^esub>\<cdot>x \<sqsubseteq> y \<Longrightarrow> x \<Up> y"
  shows "is_semi_factor A"
  unfolding is_semi_factor_def using assms
  by transfer (intro semi_factor_subdomain_axioms.intro semi_factor_subdomain.intro)

lemma is_semi_factor_bot: "is_semi_factor bot"
  by (rule is_semi_factorI, transfer, simp)

lemma is_semi_factor_top: "is_semi_factor top"
  by (rule is_semi_factorI, transfer)
    (auto intro: joinableI simp add: p_UNIV)

text \<open>@{const semi_factor_subdomain} lifts through the binary join (Jung 4.1.9(i)).\<close>
lemma is_semi_factor_sup:
  assumes "is_semi_factor a" and "is_semi_factor b"
  shows "is_semi_factor (sup a b)"
  using assms
  unfolding is_semi_factor_def by (transfer, intro semi_factor_subdomain_join)

text \<open>\dots\ and hence, by induction, through finite suprema.\<close>
lemma finite_semi_factor_Sup:
  assumes "finite \<A>" and "\<And>A. A \<in> \<A> \<Longrightarrow> is_semi_factor A"
  shows "is_semi_factor (Sup \<A>)"
  using assms
proof (induction \<A> rule: finite_induct)
  case empty
  show ?case by (simp add: is_semi_factor_def semi_factor_subdomain_bot bot_stable_subdom.rep_eq)
next
  case (insert A \<A>)
  from insert.prems have "is_semi_factor A" by blast
  moreover have "is_semi_factor (Sup \<A>)"
    by (rule insert.IH) (use insert.prems in blast)
  ultimately show ?case using is_semi_factor_sup
    by simp
qed

lemma directed_stable_proj_sup:
  fixes \<A> :: "'a stable_subdom set"
  assumes directed: "\<And>X Y. X \<in> \<A> \<Longrightarrow> Y \<in> \<A> \<Longrightarrow> \<exists>Z \<in> \<A>. X \<le> Z \<and> Y \<le> Z"
    and nonempty: "\<A> \<noteq> {}"
  shows "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` \<A> <<| \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x"
proof -
  from assms interpret directed_stable_family "set_of_subdom ` \<A>"
    apply (intro directed_stable_family.intro)
    using stable_subdomain_of_set_of_subdom
    unfolding less_eq_stable_subdom.rep_eq by force+
  let ?P = "{\<p>\<^bsub>A\<^esub> | A. A \<in> \<A>}"
  have "?P = P"
    unfolding P_def stable_subdom_p.rep_eq
    by blast
  from dd_fixes_eq_Inter
  have "{x. dd\<cdot>x = x} = set_of_subdom (Sup \<A>)"
    by transfer' simp
  then have "dd = \<p>\<^bsub>Sup \<A>\<^esub>"
    unfolding stable_subdom_p.rep_eq
    using stable_subdomain_deflation
      stable_subdomain_of_set_of_subdom
      deflation_dd
    by fastforce
  with dd_app_is_lub
  show ?thesis by (simp add: image_image stable_subdom_p.rep_eq)
qed

lemma directed_semi_factor_Sup:
  fixes \<A> :: "'a stable_subdom set"
  assumes directed: "\<And>X Y. X \<in> \<A> \<Longrightarrow> Y \<in> \<A> \<Longrightarrow> \<exists>Z \<in> \<A>. X \<le> Z \<and> Y \<le> Z"
    and nonempty: "\<A> \<noteq> {}"
    and sf: "\<And>A. A \<in> \<A> \<Longrightarrow> is_semi_factor A"
  shows "is_semi_factor (Sup \<A>)"
proof (rule is_semi_factorI)
  fix x y assume y: "y \<in> set_of_subdom (Sup \<A>)"
  assume px_below: "\<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x \<sqsubseteq> y"
  from directed_stable_proj_sup[OF directed nonempty]
  have p_lub: "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` \<A> <<| \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x" for x .
  let ?P = "{\<p>\<^bsub>A\<^esub> | A. A \<in> \<A>}"
  let ?p = "\<p>\<^bsub>Sup \<A>\<^esub>"

  interpret \<A>: stable_subdomain "set_of_subdom (Sup \<A>)"
    by (rule stable_subdomain_of_set_of_subdom)

  have xpAy: "x \<Up> \<p>\<^bsub>A\<^esub>\<cdot>y" if "A \<in> \<A>" for A
  proof - 
    interpret A: semi_factor_subdomain "set_of_subdom A"
      rewrites "stable_subdomain.p (set_of_subdom A) \<equiv> \<p>\<^bsub>A\<^esub>"
      by (simp_all add: sf[OF that, unfolded is_semi_factor_def] stable_subdom_p.rep_eq)
    have "\<p>\<^bsub>A\<^esub> \<in> ?P" by (auto simp add: that)
    from that have pA_dd: "\<p>\<^bsub>A\<^esub> \<sqsubseteq> ?p" by (intro p_below_of_le Sup_upper)
    then have "\<p>\<^bsub>A\<^esub>\<cdot>x = \<p>\<^bsub>A\<^esub>\<cdot>(?p\<cdot>x)"
      (*TODO: this could be a lemma *)
      by (simp add: deflation_below_comp1[OF subdom.deflation_p subdom.deflation_p])
      
    also have "\<dots> \<sqsubseteq> \<p>\<^bsub>A\<^esub>\<cdot>y" using px_below by (rule monofun_cfun_arg)
    finally have "\<p>\<^bsub>A\<^esub>\<cdot>x \<sqsubseteq> \<p>\<^bsub>A\<^esub>\<cdot>y" .
    with subdom.p_in_S show "x \<Up> \<p>\<^bsub>A\<^esub>\<cdot>y" by (rule A.slide_rule)
  qed
  let ?W = "(\<lambda>A. x \<squnion> \<p>\<^bsub>A\<^esub>\<cdot>y) ` \<A>"
  have dirW: "directed ?W"
  proof (rule directedI)
    fix u v assume "u \<in> ?W" "v \<in> ?W"
    then obtain A B where A: "A \<in> \<A>" "u = x \<squnion> \<p>\<^bsub>A\<^esub>\<cdot>y"
      and B: "B \<in> \<A>" "v = x \<squnion> \<p>\<^bsub>B\<^esub>\<cdot>y" by blast
    from directed[OF A(1) B(1)] obtain C where C: "C \<in> \<A>" "A \<le> C" "B \<le> C" by blast
    from C(2) have AC: "\<p>\<^bsub>A\<^esub>\<cdot>y \<sqsubseteq> \<p>\<^bsub>C\<^esub>\<cdot>y"
      by (auto intro: p_below_of_le monofun_cfun_fun)
    from C(3) have BC: "\<p>\<^bsub>B\<^esub>\<cdot>y \<sqsubseteq> \<p>\<^bsub>C\<^esub>\<cdot>y"
      by (auto intro: p_below_of_le monofun_cfun_fun)
    have "u \<sqsubseteq> x \<squnion> \<p>\<^bsub>C\<^esub>\<cdot>y" unfolding A(2)
      by (rule join_mono2[OF xpAy[OF C(1)] AC])
    moreover have "v \<sqsubseteq> x \<squnion> \<p>\<^bsub>C\<^esub>\<cdot>y" unfolding B(2)
      by (rule join_mono2[OF xpAy[OF C(1)] BC])
    moreover have "x \<squnion> \<p>\<^bsub>C\<^esub>\<cdot>y \<in> ?W" using C(1) by blast
    ultimately show "\<exists>z\<in>?W. u \<sqsubseteq> z \<and> v \<sqsubseteq> z" by blast
  qed
  define w where "w = lub ?W"
  have Wlub: "?W <<| w" unfolding w_def using dirW by (rule directed_lub)
  from nonempty obtain A0 where A0: "A0 \<in> \<A>" by blast
  have memA0: "x \<squnion> \<p>\<^bsub>A0\<^esub>\<cdot>y \<in> ?W" using A0 by blast
  have "x \<sqsubseteq> x \<squnion> \<p>\<^bsub>A0\<^esub>\<cdot>y" by (rule joinableD(1)[OF xpAy[OF A0]])
  also have "\<dots> \<sqsubseteq> w" using is_ubD[OF is_lubD1[OF Wlub] memA0] .
  finally have xw: "x \<sqsubseteq> w" .
  have Py_y: "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>y) ` \<A> <<| y"
    using p_lub[of y] subdom.p_fixed[OF y] by simp
  have Py_w: "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>y) ` \<A> <| w"
  proof (rule ub_imageI)
    fix A assume A: "A \<in> \<A>"
    have memA: "x \<squnion> \<p>\<^bsub>A\<^esub>\<cdot>y \<in> ?W" using A by blast
    have "\<p>\<^bsub>A\<^esub>\<cdot>y \<sqsubseteq> x \<squnion>  \<p>\<^bsub>A\<^esub>\<cdot>y" by (rule joinableD(2)[OF xpAy[OF A]])
    also have "\<dots> \<sqsubseteq> w" using is_ubD[OF is_lubD1[OF Wlub] memA] .
    finally show "\<p>\<^bsub>A\<^esub>\<cdot>y \<sqsubseteq> w" .
  qed
  have yw: "y \<sqsubseteq> w" using Py_y Py_w by (rule is_lubD2)
  show "x \<Up> y" using xw yw by (rule joinableI)
qed

lemma Fpow_singleton: "x \<in> A \<Longrightarrow> {x} \<in> Fpow A"
  by (simp add: Fpow_def)

lemma (in complete_lattice) Sup_of_Fpow: "Sup (Sup ` Fpow(\<A>)) = Sup \<A>"
proof (rule order_antisym)
  show "Sup \<A> \<le> Sup (Sup ` Fpow \<A>)"
    by (rule Sup_least, rule Sup_upper, drule Fpow_singleton, force)
  show "Sup (Sup ` Fpow \<A>) \<le> Sup \<A>"
    by (rule Sup_least, erule imageE, auto simp add: Sup_subset_mono Fpow_def )
qed

lemma is_semi_factor_Sup:
  fixes \<A> :: "'a stable_subdom set"
  assumes sf: "\<And>A. A \<in> \<A> \<Longrightarrow> is_semi_factor A"
  shows "is_semi_factor (Sup \<A>)"
proof -
  have directed: "X \<in> Sup ` Fpow(\<A>) \<Longrightarrow> Y \<in> Sup ` Fpow(\<A>) \<Longrightarrow> \<exists>Z \<in> Sup ` Fpow(\<A>). X \<le> Z \<and> Y \<le> Z"
    for X Y
  proof (simp, safe, intro bexI)
    fix x y :: "'a stable_subdom set"
    show "Sup x \<le> Sup (x \<union> y) \<and> Sup y \<le> Sup (x \<union> y)"
      by (simp add: Sup_subset_mono)
    assume "x \<in> Fpow(\<A>)" "y \<in> Fpow(\<A>)"
    then show "x \<union> y \<in> Fpow(\<A>)" by (simp add: Fpow_def)
  qed
  moreover have "Sup ` Fpow(\<A>) \<noteq> {}" by (simp add: Fpow_not_empty)
  moreover have "B \<in> Sup ` Fpow(\<A>) \<Longrightarrow> is_semi_factor (B)" for B
    using finite_semi_factor_Sup sf unfolding Fpow_def by auto
  ultimately have "is_semi_factor (Sup (Sup ` Fpow(\<A>)))"
    by (rule directed_semi_factor_Sup)
  then show ?thesis by (simp add: Sup_of_Fpow)
qed


text \<open>Composition of projections is the projection onto the intersection (pointwise):
  \<open>p\<^bsub>B\<^esub>\<cdot>(p\<^bsub>A\<^esub>\<cdot>x) = p\<^bsub>A\<inter>B\<^esub>\<cdot>x\<close>.  Projecting \<open>x\<close> into \<open>A\<close> is the lub of the
  directed below-set \<open>{a\<in>A. a\<sqsubseteq>x}\<close>; applying \<open>p\<^bsub>B\<^esub>\<close> (continuous) sends it to the lub of
  its image, which is exactly \<open>{z\<in>A\<inter>B. z\<sqsubseteq>x}\<close>: each \<open>p\<^bsub>B\<^esub>\<cdot>a \<sqsubseteq> a \<in> A\<close> is in \<open>A\<close>
  (downward) and in \<open>B\<close>, and every \<open>z\<in>A\<inter>B\<close> below \<open>x\<close> is its own \<open>p\<^bsub>B\<^esub>\<close>-image.\<close>
lemma p_compose_Int:
  assumes A: "stable_subdomain A" and B: "stable_subdomain B"
  shows "stable_subdomain.p B\<cdot>(stable_subdomain.p A\<cdot>x) = stable_subdomain.p (A \<inter> B)\<cdot>x"
proof -
  interpret A: stable_subdomain A by (rule A)
  interpret B: stable_subdomain B by (rule B)
  interpret AB: stable_subdomain "A \<inter> B" using A B by (rule stable_subdomain_Int)
  have Apx: "A.p\<cdot>x = lub {a \<in> A. a \<sqsubseteq> x}"
    using lub_eqI[OF A.proj_is_lub] by (simp add: A.p_beta)
  have ABpx: "AB.p\<cdot>x = lub {z \<in> A \<inter> B. z \<sqsubseteq> x}"
    using lub_eqI[OF AB.proj_is_lub] by (simp add: AB.p_beta)
  have setEq: "(\<lambda>z. B.p\<cdot>z) ` {a \<in> A. a \<sqsubseteq> x} = {z \<in> A \<inter> B. z \<sqsubseteq> x}"
  proof (intro set_eqI iffI)
    fix w assume "w \<in> (\<lambda>z. B.p\<cdot>z) ` {a \<in> A. a \<sqsubseteq> x}"
    then obtain a where a: "a \<in> A" "a \<sqsubseteq> x" and w: "w = B.p\<cdot>a" by auto
    have le: "B.p\<cdot>a \<sqsubseteq> a" by (rule B.p_below)
    from a(1) le have "B.p\<cdot>a \<in> A" by (rule A.downward)
    moreover have "B.p\<cdot>a \<in> B" by simp
    moreover have "B.p\<cdot>a \<sqsubseteq> x" using le a(2) by (rule below_trans)
    ultimately show "w \<in> {z \<in> A \<inter> B. z \<sqsubseteq> x}" using w by simp
  next
    fix w assume "w \<in> {z \<in> A \<inter> B. z \<sqsubseteq> x}"
    then have w: "w \<in> A" "w \<in> B" "w \<sqsubseteq> x" by auto
    from w(2) have "B.p\<cdot>w = w" by (rule B.p_fixed)
    moreover from w(1) w(3) have "w \<in> {a \<in> A. a \<sqsubseteq> x}" by simp
    ultimately show "w \<in> (\<lambda>z. B.p\<cdot>z) ` {a \<in> A. a \<sqsubseteq> x}" by force
  qed
  have "B.p\<cdot>(A.p\<cdot>x) = lub ((\<lambda>z. B.p\<cdot>z) ` {a \<in> A. a \<sqsubseteq> x})"
    unfolding Apx
    by (rule cont_directed_lub[OF cont_Rep_cfun2 A.proj_set_directed A.proj_set_ne, symmetric])
  also have "\<dots> = lub {z \<in> A \<inter> B. z \<sqsubseteq> x}" unfolding setEq ..
  also have "\<dots> = AB.p\<cdot>x" unfolding ABpx ..
  finally show "stable_subdomain.p B\<cdot>(stable_subdomain.p A\<cdot>x) = stable_subdomain.p (A \<inter> B)\<cdot>x" .
qed

text \<open>The pairwise projection-of-sup, lifted pointwise to @{typ "'a stable_subdom"}:
  \<open>p\<^bsub>a\<squnion>b\<^esub>\<cdot>x = p\<^bsub>a\<^esub>\<cdot>x \<squnion> p\<^bsub>b\<^esub>\<cdot>x\<close>.\<close>
lemma p_sup_join: "\<p>\<^bsub>sup a b\<^esub>\<cdot>x = \<p>\<^bsub>a\<^esub>\<cdot>x \<squnion> \<p>\<^bsub>b\<^esub>\<cdot>x"
  by (transfer, rule stable_subdomain_join_proj[symmetric])

lemma p_inf_meet:
  "\<p>\<^bsub>inf A B\<^esub>\<cdot>x = \<p>\<^bsub>A\<^esub>\<cdot>x \<sqinter> \<p>\<^bsub>B\<^esub>\<cdot>x"
proof -
  let ?below = "\<lambda>X. {x' \<in> set_of_subdom X. x' \<sqsubseteq> x}"
  let ?down = "\<lambda>X. {x'. x' \<sqsubseteq> \<p>\<^bsub>X\<^esub>\<cdot>x}"
  have set_inf: "set_of_subdom (inf A B) = set_of_subdom A \<inter> set_of_subdom B"
    by (rule inf_stable_subdom.rep_eq)
  then have "?below (inf A B) = ?below A \<inter> ?below B"
    by fast
  then have "?down (inf A B) = ?down A \<inter> ?down B"
    by (simp add: subdom.below_set_is_down_set[unfolded subdom.proj_Rep_p])
  then have "y \<sqsubseteq> \<p>\<^bsub>inf A B\<^esub>\<cdot>x \<longleftrightarrow> y \<sqsubseteq> \<p>\<^bsub>A\<^esub>\<cdot>x \<and> y \<sqsubseteq> \<p>\<^bsub>B\<^esub>\<cdot>x" for y
    by fast
  then show ?thesis
    using meet_below1 meet_below2 by (blast intro: below_antisym meet_greatest)
qed

lemma p_joinable[simp]: "\<p>\<^bsub>A\<^esub>\<cdot>x \<Up> \<p>\<^bsub>B\<^esub>\<cdot>x"
  by (rule joinableI; rule subdom.below)

lemma stable_subdom_proj_eqI:
"\<p>\<^bsub>A\<^esub> = \<p>\<^bsub>B\<^esub> \<Longrightarrow> A = B"
  by (intro order.antisym le_of_p_below, simp_all)

instance stable_subdom :: ("{bifinite,distributive_cpo}") distrib_lattice
  by (intro_classes, intro stable_subdom_proj_eqI cfun_eqI)
    (simp add: p_inf_meet p_sup_join join_meet_distrib)

lemma set_of_subdom_inf: "set_of_subdom (inf a b) = set_of_subdom a \<inter> set_of_subdom b"
  by (rule inf_stable_subdom.rep_eq)

text \<open>Lifted to @{typ "'a stable_subdom"} (pointwise), and commutative.\<close>
lemma p_comp_inf: "\<p>\<^bsub>b\<^esub>\<cdot>(\<p>\<^bsub>a\<^esub>\<cdot>x) = \<p>\<^bsub>inf a b\<^esub>\<cdot>x"
  using p_compose_Int[OF stable_subdomain_of_set_of_subdom stable_subdomain_of_set_of_subdom]
  by (simp add: stable_subdom_p.rep_eq inf_stable_subdom.rep_eq)

lemma p_app_commute: "\<p>\<^bsub>a\<^esub>\<cdot>(\<p>\<^bsub>b\<^esub>\<cdot>x) = \<p>\<^bsub>b\<^esub>\<cdot>(\<p>\<^bsub>a\<^esub>\<cdot>x)"
  by (simp add: p_comp_inf inf_commute)

lemma p_comp_inf2:  "\<p>\<^bsub>a\<^esub>\<cdot>(\<p>\<^bsub>b\<^esub>\<cdot>x) = \<p>\<^bsub>inf a b\<^esub>\<cdot>x"
  by (simp add: p_comp_inf inf_commute)

lemma (in stable_subdomain) join_closed:
  "a \<Up> b \<Longrightarrow> a \<in> S \<Longrightarrow> b \<in> S \<Longrightarrow> a \<squnion> b \<in> S"
  using lub_closed[OF _ joinable_lub]
  by fast

text \<open>Jung, Lemma 4.1.9(ii): the meet of two semi-factors is a semi-factor.  Using
  \<open>p\<^bsub>a\<sqinter>b\<^esub>\<cdot>x = p\<^bsub>a\<^esub>\<cdot>(p\<^bsub>b\<^esub>\<cdot>x)\<close>, the slide condition of @{term a} gives
  \<open>p\<^bsub>b\<^esub>\<cdot>x \<Up> y\<close>; the join \<open>p\<^bsub>b\<^esub>\<cdot>x \<squnion> y\<close> lies in @{term b}, and the slide condition of
  @{term b} then bounds @{term x} and @{term y}.\<close>
lemma is_semi_factor_inf:
  assumes a: "is_semi_factor a" and b: "is_semi_factor b"
  shows "is_semi_factor (inf a b)"
proof (rule is_semi_factorI)
  fix x y assume y: "y \<in> set_of_subdom (inf a b)" and px: "\<p>\<^bsub>inf a b\<^esub>\<cdot>x \<sqsubseteq> y"
  from y have yA: "y \<in> set_of_subdom a" and yB: "y \<in> set_of_subdom b"
    by (auto simp: set_of_subdom_inf)
  interpret A: semi_factor_subdomain "set_of_subdom a"
    rewrites "stable_subdomain.p (set_of_subdom a) \<equiv> \<p>\<^bsub>a\<^esub>"
    by (simp_all add: a[unfolded is_semi_factor_def] stable_subdom_p.rep_eq)
  interpret B: semi_factor_subdomain "set_of_subdom b"
    rewrites "stable_subdomain.p (set_of_subdom b) \<equiv> \<p>\<^bsub>b\<^esub>"
    by (simp_all add: b[unfolded is_semi_factor_def] stable_subdom_p.rep_eq)
  from px have "\<p>\<^bsub>a\<^esub>\<cdot>(\<p>\<^bsub>b\<^esub>\<cdot>x) \<sqsubseteq> y" by (simp add: p_comp_inf2)
  with yA have step1: "\<p>\<^bsub>b\<^esub>\<cdot>x \<Up> y" by (rule A.slide_rule)
  with yB have memB: "(\<p>\<^bsub>b\<^esub>\<cdot>x) \<squnion> y \<in> set_of_subdom b"
    by (auto intro: subdom.join_closed)
  from step1 have "\<p>\<^bsub>b\<^esub>\<cdot>x \<sqsubseteq> (\<p>\<^bsub>b\<^esub>\<cdot>x) \<squnion> y" by auto
  with memB have step2: "x \<Up> (\<p>\<^bsub>b\<^esub>\<cdot>x) \<squnion> y" by (rule B.slide_rule)
  then have "x \<sqsubseteq> x \<squnion> ((\<p>\<^bsub>b\<^esub>\<cdot>x) \<squnion> y)" by auto
  moreover from step1 step2 have "y \<sqsubseteq> x \<squnion> ((\<p>\<^bsub>b\<^esub>\<cdot>x) \<squnion> y)"
    by (blast dest: joinableD(2) below_trans)
  ultimately show "x \<Up> y" by (rule joinableI)
qed

lemma insert_join_is_lub:
  assumes Sl: "S <<| l" and j: "z \<Up> l"
  shows "insert z S <<| z \<squnion> l"
proof (rule is_lubI)
  show "insert z S <| z \<squnion> l"
  proof (rule is_ubI)
    fix w assume w: "w \<in> insert z S"
    show "w \<sqsubseteq> z \<squnion> l"
    proof (cases "w = z")
      case True then show ?thesis by (simp add: joinableD(1)[OF j])
    next
      case False with w have "w \<in> S" by simp
      with is_lubD1[OF Sl] have "w \<sqsubseteq> l" by (rule is_ubD)
      also have "l \<sqsubseteq> z \<squnion> l" by (rule joinableD(2)[OF j])
      finally show ?thesis .
    qed
  qed
next
  fix u assume "insert z S <| u"
  then have zu: "z \<sqsubseteq> u" and Su: "S <| u" by (auto simp: is_ub_insert)
  from Sl Su have "l \<sqsubseteq> u" by (rule is_lubD2)
  with zu show "z \<squnion> l \<sqsubseteq> u" by (rule join_belowI)
qed

text \<open>The projection of a finite (nonempty) sup is the lub of the pointwise projections.\<close>
lemma finite_proj_sup:
  assumes "finite \<A>" and "\<A> \<noteq> {}"
  shows "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` \<A> <<| \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x"
  using assms
proof (induction rule: finite_ne_induct)
  case (singleton A)
  have "{\<p>\<^bsub>A\<^esub>\<cdot>x} <<| \<p>\<^bsub>A\<^esub>\<cdot>x" by (rule is_lub_singleton)
  then show ?case by simp
next
  case (insert A \<A>)
  have j: "\<p>\<^bsub>A\<^esub>\<cdot>x \<Up> \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x" by (rule joinableI[OF subdom.p_below subdom.p_below])
  have "insert (\<p>\<^bsub>A\<^esub>\<cdot>x) ((\<lambda>B. \<p>\<^bsub>B\<^esub>\<cdot>x) ` \<A>) <<| \<p>\<^bsub>A\<^esub>\<cdot>x \<squnion> \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x"
    by (rule insert_join_is_lub[OF insert.IH j])
  moreover have "(\<lambda>B. \<p>\<^bsub>B\<^esub>\<cdot>x) ` insert A \<A> = insert (\<p>\<^bsub>A\<^esub>\<cdot>x) ((\<lambda>B. \<p>\<^bsub>B\<^esub>\<cdot>x) ` \<A>)" by simp
  moreover have "\<p>\<^bsub>A\<^esub>\<cdot>x \<squnion> \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x = \<p>\<^bsub>Sup (insert A \<A>)\<^esub>\<cdot>x"
    by (simp add: p_sup_join)
  ultimately show ?case by simp
qed

text \<open>The projection of an \emph{arbitrary} sup is the lub of the pointwise projections
  (Jung's full \<open>p\<^bsub>\<Squnion>\<A>\<^esub>\<cdot>x = \<Squnion>\<^bsub>A\<in>\<A>\<^esub> p\<^bsub>A\<^esub>\<cdot>x\<close>, in @{text "<<|"} form): combine the
  directed result over @{term "Sup ` Fpow \<A>"} (whose sup is @{term "Sup \<A>"}) with the
  finite case.  An upper bound of the pointwise projections bounds every finite sub-join,
  hence the directed lub, hence @{term "\<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x"}.\<close>
lemma proj_Sup:
  fixes \<A> :: "'a stable_subdom set"
  shows "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` \<A> <<| \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x"
proof -
  have dir: "X \<in> Sup ` Fpow \<A> \<Longrightarrow> Y \<in> Sup ` Fpow \<A> \<Longrightarrow> \<exists>Z \<in> Sup ` Fpow \<A>. X \<le> Z \<and> Y \<le> Z"
    for X Y
  proof (simp, safe, intro bexI)
    fix x y :: "'a stable_subdom set"
    show "Sup x \<le> Sup (x \<union> y) \<and> Sup y \<le> Sup (x \<union> y)" by (simp add: Sup_subset_mono)
    assume "x \<in> Fpow \<A>" "y \<in> Fpow \<A>"
    then show "x \<union> y \<in> Fpow \<A>" by (simp add: Fpow_def)
  qed
  have neF: "Sup ` Fpow \<A> \<noteq> {}" by (simp add: Fpow_not_empty)
  have D: "(\<lambda>F. \<p>\<^bsub>F\<^esub>\<cdot>x) ` (Sup ` Fpow \<A>) <<| \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x"
    using directed_stable_proj_sup[OF dir neF] by (simp add: Sup_of_Fpow)
  show ?thesis
  proof (rule is_lubI)
    show "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` \<A> <| \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x"
    proof (rule ub_imageI)
      fix A assume "A \<in> \<A>"
      then have "\<p>\<^bsub>A\<^esub> \<sqsubseteq> \<p>\<^bsub>Sup \<A>\<^esub>" by (intro p_below_of_le Sup_upper)
      then show "\<p>\<^bsub>A\<^esub>\<cdot>x \<sqsubseteq> \<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x" by (rule monofun_cfun_fun)
    qed
  next
    fix u assume u: "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` \<A> <| u"
    have "(\<lambda>F. \<p>\<^bsub>F\<^esub>\<cdot>x) ` (Sup ` Fpow \<A>) <| u"
    proof (rule ub_imageI)
      fix F assume "F \<in> Sup ` Fpow \<A>"
      then obtain G where G: "G \<in> Fpow \<A>" and F: "F = Sup G" by auto
      from G have finG: "finite G" and GA: "G \<subseteq> \<A>" by (auto simp: Fpow_def)
      show "\<p>\<^bsub>F\<^esub>\<cdot>x \<sqsubseteq> u"
      proof (cases "G = {}")
        case True
        have "\<p>\<^bsub>bot\<^esub>\<cdot>x = \<bottom>" using subdom.p_in_S[of bot x] by (simp add: bot_stable_subdom.rep_eq)
        with True F show ?thesis by simp
      next
        case False
        have lub: "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` G <<| \<p>\<^bsub>Sup G\<^esub>\<cdot>x" using finG False by (rule finite_proj_sup)
        have "(\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` G <| u"
        proof (rule ub_imageI)
          fix A assume "A \<in> G"
          with GA have "\<p>\<^bsub>A\<^esub>\<cdot>x \<in> (\<lambda>A. \<p>\<^bsub>A\<^esub>\<cdot>x) ` \<A>" by auto
          with u show "\<p>\<^bsub>A\<^esub>\<cdot>x \<sqsubseteq> u" by (rule is_ubD)
        qed
        with lub have "\<p>\<^bsub>Sup G\<^esub>\<cdot>x \<sqsubseteq> u" by (rule is_lubD2)
        with F show ?thesis by simp
      qed
    qed
    with D show "\<p>\<^bsub>Sup \<A>\<^esub>\<cdot>x \<sqsubseteq> u" by (rule is_lubD2)
  qed
qed

text \<open>The frame law: binary meet distributes over arbitrary joins.  An element of
  \<open>A \<sqinter> \<Squnion>\<B>\<close> is the lub of its projections through the members of \<open>\<B>\<close> (@{thm [source] proj_Sup}),
  and each of those lies in \<open>A \<sqinter> B\<close>.\<close>

lemma inf_Sup_stable_subdom:
  fixes A :: "'a stable_subdom"
  shows "inf A (Sup \<B>) = (SUP B\<in>\<B>. inf A B)"
proof (rule order.antisym)
  show "(SUP B\<in>\<B>. inf A B) \<le> inf A (Sup \<B>)"
    by (rule SUP_least) (auto intro: inf_mono Sup_upper le_infI2)
  show "inf A (Sup \<B>) \<le> (SUP B\<in>\<B>. inf A B)"
    unfolding less_eq_stable_subdom.rep_eq
  proof
    fix y assume "y \<in> set_of_subdom (inf A (Sup \<B>))"
    then have yA: "y \<in> set_of_subdom A" and yB: "y \<in> set_of_subdom (Sup \<B>)"
      by (simp_all add: inf_stable_subdom.rep_eq)
    let ?C = "SUP B\<in>\<B>. inf A B"
    have "\<p>\<^bsub>Sup \<B>\<^esub>\<cdot>y = y" using yB by (simp add: p_fixes)
    then have lub: "(\<lambda>B. \<p>\<^bsub>B\<^esub>\<cdot>y) ` \<B> <<| y" using proj_Sup[where \<A> = \<B> and x = y] by simp
    have "(\<lambda>B. \<p>\<^bsub>B\<^esub>\<cdot>y) ` \<B> \<subseteq> set_of_subdom ?C"
    proof safe
      fix B assume B: "B \<in> \<B>"
      have "\<p>\<^bsub>B\<^esub>\<cdot>y \<in> set_of_subdom (inf A B)"
        using subdom.downward[OF yA subdom.p_below] by (simp add: inf_stable_subdom.rep_eq)
      moreover have "inf A B \<le> ?C" using B by (rule SUP_upper)
      ultimately show "\<p>\<^bsub>B\<^esub>\<cdot>y \<in> set_of_subdom ?C" by (auto simp: less_eq_stable_subdom.rep_eq)
    qed
    then show "y \<in> set_of_subdom ?C" using lub by (rule subdom.lub_closed)
  qed
qed

instance stable_subdom :: ("{bifinite,distributive_cpo}") complete_heyting_algebra
  by standard (rule inf_Sup_stable_subdom)

lemma Sup_contains_top: "top \<in> (X::'a::complete_lattice set) \<Longrightarrow> Sup X = top"
  by (rule order.antisym) (auto intro: Sup_upper)

section \<open>The type of semi-factors\<close>

text \<open>Following Jung, the semi-factors (stable subdomains satisfying the slide condition) form a
  complete lattice.  Sups, binary meets, top and bottom are inherited from the type
  \<open>'a stable_subdom\<close> (the semi-factors are closed under those operations), but an arbitrary
  intersection of semi-factors need not be one.  The meet of a family is therefore recovered
  as the sup of its semi-factor lower bounds.\<close>

typedef 'a semi_factor = "{A :: 'a stable_subdom. is_semi_factor A}"
  morphisms subdom_of_factor factor_of_subdom
  using is_semi_factor_bot by blast

setup_lifting type_definition_semi_factor

lemma is_semi_factor_subdom_of_factor: "is_semi_factor (subdom_of_factor F)"
  using subdom_of_factor by blast

instantiation semi_factor :: ("{bifinite,distributive_cpo}") complete_lattice
begin

lift_definition less_eq_semi_factor :: "'a semi_factor \<Rightarrow> 'a semi_factor \<Rightarrow> bool"
  is "(\<le>)" .

lift_definition less_semi_factor :: "'a semi_factor \<Rightarrow> 'a semi_factor \<Rightarrow> bool"
  is "(<)" .

lift_definition inf_semi_factor :: "'a semi_factor \<Rightarrow> 'a semi_factor \<Rightarrow> 'a semi_factor"
  is "inf" by (rule is_semi_factor_inf)

lift_definition sup_semi_factor :: "'a semi_factor \<Rightarrow> 'a semi_factor \<Rightarrow> 'a semi_factor"
  is "sup" by (rule is_semi_factor_sup)

lift_definition top_semi_factor :: "'a semi_factor"
  is "top" by (rule is_semi_factor_top)

lift_definition bot_semi_factor :: "'a semi_factor"
  is "bot" by (rule is_semi_factor_bot)

lift_definition Sup_semi_factor :: "'a semi_factor set \<Rightarrow> 'a semi_factor"
  is "Sup" by (rule is_semi_factor_Sup)

text \<open>Arbitrary meet = sup of the semi-factor lower bounds.\<close>
lift_definition Inf_semi_factor :: "'a semi_factor set \<Rightarrow> 'a semi_factor" 
  is "\<lambda>\<S>. Sup {b. (\<forall>a\<in>\<S>. b \<le> a) \<and> is_semi_factor b}"
  by (auto intro: is_semi_factor_Sup)

instance
  by (standard; transfer) (auto intro: Sup_least Sup_upper is_semi_factor_top Sup_contains_top)

end

instance semi_factor ::  ("{bifinite,distributive_cpo}") distrib_lattice
  by (intro_classes, transfer', rule sup_inf_distrib1)

instance semi_factor :: ("{bifinite,distributive_cpo}") complete_heyting_algebra
  by standard (transfer, rule ch_dist)

lift_definition semi_factor_p :: "'a semi_factor \<Rightarrow> 'a \<rightarrow> 'a"
is "stable_subdom_p" .

lift_definition set_of_factor :: "'a semi_factor \<Rightarrow> 'a set"
is "set_of_subdom" .

interpretation semi_factor: semi_factor_subdomain "set_of_factor A"
  rewrites semi_factor_p_eq: "stable_subdomain.p (set_of_factor A) \<equiv> semi_factor_p A"
proof -
  show "semi_factor_subdomain (set_of_factor A)" by (transfer, simp add: is_semi_factor_def)
  show "stable_subdomain.p (set_of_factor A) \<equiv> semi_factor_p A"
    unfolding set_of_factor.rep_eq semi_factor_p.rep_eq
      stable_subdom_p.rep_eq .
qed

abbreviation semi_factor_proj (infixl \<open>\<downharpoonright>\<close> 200)
  where "semi_factor_proj x a \<equiv> semi_factor_p a\<cdot>x"

lemma semi_factor_proj_comp:
  "x \<downharpoonright> a \<downharpoonright> b = x \<downharpoonright> (inf a b)"
  by (transfer', rule p_comp_inf)

lemma semi_factor_proj_comm:
  "x \<downharpoonright> a \<downharpoonright> b = x \<downharpoonright> b \<downharpoonright> a"
  by (simp add: semi_factor_proj_comp inf_commute)

corollary semi_factor_comp_simp[simp]:
  "a \<le> b \<Longrightarrow> x \<downharpoonright> a \<downharpoonright> b = x \<downharpoonright> a"
  "a \<le> b \<Longrightarrow> x \<downharpoonright> b \<downharpoonright> a = x \<downharpoonright> a"
  by (simp_all add: semi_factor_proj_comp inf_absorb1 inf_absorb2)

end