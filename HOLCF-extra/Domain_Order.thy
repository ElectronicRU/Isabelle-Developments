theory Domain_Order
  imports Filter_Sum
begin

section \<open>Order structure of domain-package types\<close>

text \<open>The domain package presents each domain as isomorphic, through \<open>abs\<close> and \<open>rep\<close> satisfying
  the laws of @{locale iso}, to a combination of its constructor arguments.  An isomorphism of
  pointed cpos is an order isomorphism, so it preserves bounds, lubs and meets.

  For recursive domains the order classes are derived from the map functional: each class
  property is stated for the image of a deflation (a locale over @{locale deflation}), pushed
  through \<open>ssum_map\<close>, \<open>sprod_map\<close>, \<open>u_map\<close> and the \<open>abs\<close>/\<open>rep\<close> isomorphism, and established for
  \<open>T_map\<cdot>v\<close> by fixed-point induction; at \<open>v = ID\<close> this gives the instance.  This is the
  \<^emph>\<open>minimal invariant\<close> technique of Pitts (\<^emph>\<open>Relational Properties of Domains\<close>, Information and
  Computation 127, 1996, Definition 3.2 and Section 6): \<open>ID\<close> is the least fixed point of
  \<open>e \<mapsto> abs oo F e oo rep\<close>, so an admissible property holding at \<open>\<bottom>\<close> and preserved by that map holds
  at \<open>ID\<close>.  Dependencies between properties are expressed as sort constraints on the component
  types rather than as hypotheses on the deflations: each class is derived for the type before
  the classes that need it.\<close>

subsection \<open>Transfer along isomorphisms\<close>

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

lemma bounded_complete_iso:
  fixes abs :: "'r::bounded_complete \<rightarrow> 't::pcpo" and rep
  assumes "iso abs rep" shows "OFCLASS('t, bounded_complete_class)"
proof intro_classes
  interpret iso abs rep by fact
  fix A :: "'t set" and b assume ne: "A \<noteq> {}" and ub: "A <| b"
  from ub have ub': "(\<lambda>x. rep\<cdot>x) ` A <| rep\<cdot>b" using iso_is_ub_iff[OF assms, of A "rep\<cdot>b"] by simp
  from ne have "(\<lambda>x. rep\<cdot>x) ` A \<noteq> {}" by simp
  then have "\<exists>l. (\<lambda>x. rep\<cdot>x) ` A <<| l" using ub' by (rule bounded_complete_class.ex_bound_ne_ex_lub)
  then obtain l :: 'r where "(\<lambda>x. rep\<cdot>x) ` A <<| l" by (elim exE)
  then have "A <<| abs\<cdot>l" by (rule iso_is_lub_iff[OF assms, THEN iffD1])
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

subsection \<open>Map functionals\<close>

text \<open>The domain package defines \<open>T_map \<equiv> \<Lambda> v. \<mu> f. abs oo F v f oo rep\<close>, with \<open>F\<close> built from
  the rep-type combinators. A predicate preserved by \<open>F\<close> and holding at \<open>\<bottom>\<close> holds for the map
  by fixed-point induction, if admissible; at \<open>v = ID\<close> (\<open>T_map\<cdot>ID = ID\<close>) this yields the
  instance. Only the preservation step needs proof search.\<close>

definition preserves :: "(('a::pcpo \<rightarrow> 'a) \<Rightarrow> bool) \<Rightarrow> (('a \<rightarrow> 'a) \<rightarrow> ('a \<rightarrow> 'a)) \<Rightarrow> bool" where
  "preserves P F \<longleftrightarrow> (\<forall>f. P f \<longrightarrow> P (F\<cdot>f))"

lemma preserves_LAM: "cont G \<Longrightarrow> (\<And>f. P f \<Longrightarrow> P (G f)) \<Longrightarrow> preserves P (\<Lambda> f. G f)"
  by (simp add: preserves_def)

lemma fix_preserves: "adm P \<Longrightarrow> P \<bottom> \<Longrightarrow> preserves P F \<Longrightarrow> P (fix\<cdot>F)"
  by (erule fix_ind) (simp_all add: preserves_def)


section \<open>Order predicates as deflation locales\<close>

text \<open>The class properties, relativised to the image of a deflation.  Bundling @{const deflation}
  into every predicate keeps the connective rules uniform: the deflation part rides along through
  the HOLCF @{text "deflation_*_map"} lemmas inside each connective rule, and admissibility gains
  @{thm [source] adm_deflation}.  The image of a chain's lub is approximated by the images of
  its members, which gives admissibility of the order predicates.\<close>

locale bounded_complete_defl = deflation d for d :: "'a::bifinite \<rightarrow> 'a" +
  assumes pair_lubs: "d\<cdot>a \<sqsubseteq> c \<Longrightarrow> d\<cdot>b \<sqsubseteq> c \<Longrightarrow> \<exists>z. {d\<cdot>a, d\<cdot>b} <<| z"

locale filter_sum_defl = deflation d for d :: "'a::bifinite \<rightarrow> 'a" +
  assumes filter_sum_image:
    "d\<cdot>x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> d\<cdot>x \<sqsubseteq> u \<Longrightarrow> y \<sqsubseteq> u \<Longrightarrow> \<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> d\<cdot>x \<and> l \<sqsubseteq> y"

lemma (in bounded_complete_defl) deflation: "deflation d" by (fact deflation_axioms)

lemma (in filter_sum_defl) deflation: "deflation d" by (fact deflation_axioms)

subsection \<open>Bounded completeness\<close>

lemma bounded_complete_deflI:
  "deflation d \<Longrightarrow> (\<And>a b c. d\<cdot>a \<sqsubseteq> c \<Longrightarrow> d\<cdot>b \<sqsubseteq> c \<Longrightarrow> \<exists>z. {d\<cdot>a, d\<cdot>b} <<| z) \<Longrightarrow> bounded_complete_defl d"
  by (simp add: bounded_complete_defl_def bounded_complete_defl_axioms_def)

lemma bounded_complete_defl_bottom: "bounded_complete_defl (\<bottom> :: 'a::bifinite \<rightarrow> 'a)"
  by (rule bounded_complete_deflI[OF deflation_bottom]) (auto intro: is_lub_singleton)

lemma bounded_complete_defl_ID: "bounded_complete_defl (ID :: 'a::{bifinite, bounded_complete} \<rightarrow> 'a)"
proof (rule bounded_complete_deflI[OF deflation_ID])
  fix a b c :: 'a assume "ID\<cdot>a \<sqsubseteq> c" "ID\<cdot>b \<sqsubseteq> c"
  then have "{ID\<cdot>a, ID\<cdot>b} <| c" by (simp add: is_ub_def)
  then show "\<exists>z. {ID\<cdot>a, ID\<cdot>b} <<| z" by (rule ex_bound_ex_lub)
qed

lemma up_is_lub_pair: "{x, y} <<| z \<Longrightarrow> {up\<cdot>x, up\<cdot>y} <<| up\<cdot>z"
proof (rule is_lubI)
  assume z: "{x, y} <<| z"
  then have "x \<sqsubseteq> z" "y \<sqsubseteq> z" by (auto dest: is_lubD1 is_ubD)
  then show "{up\<cdot>x, up\<cdot>y} <| up\<cdot>z" by (auto intro!: is_ubI)
next
  fix u assume z: "{x, y} <<| z" and u: "{up\<cdot>x, up\<cdot>y} <| u"
  then have "up\<cdot>x \<sqsubseteq> u" "up\<cdot>y \<sqsubseteq> u" by (auto dest: is_ubD)
  then obtain u' where "u = up\<cdot>u'" "x \<sqsubseteq> u'" "y \<sqsubseteq> u'" by (cases u) auto
  with z show "up\<cdot>z \<sqsubseteq> u" by (auto intro: is_lubD2 is_ubI)
qed

lemma bounded_complete_defl_u_map:
  assumes f: "bounded_complete_defl f" shows "bounded_complete_defl (u_map\<cdot>f)"
proof (rule bounded_complete_deflI[OF deflation_u_map[OF bounded_complete_defl.axioms(1)[OF f]]])
  fix a b c assume ac: "u_map\<cdot>f\<cdot>a \<sqsubseteq> c" and bc: "u_map\<cdot>f\<cdot>b \<sqsubseteq> c"
  show "\<exists>z. {u_map\<cdot>f\<cdot>a, u_map\<cdot>f\<cdot>b} <<| z"
  proof (cases "a = \<bottom> \<or> b = \<bottom>")
    case True then show ?thesis
    proof
      assume "a = \<bottom>" then show ?thesis
        by (intro exI[of _ "u_map\<cdot>f\<cdot>b"]) (simp add: is_lub_bin)
    next
      assume "b = \<bottom>" then show ?thesis
        by (intro exI[of _ "u_map\<cdot>f\<cdot>a"]) (simp add: is_lub_bin insert_commute)
    qed
  next
    case False
    then obtain x y where ab: "a = up\<cdot>x" "b = up\<cdot>y" by (cases a; cases b) auto
    with ac obtain c' where c: "c = up\<cdot>c'" "f\<cdot>x \<sqsubseteq> c'" by (cases c) auto
    with ab bc have "f\<cdot>y \<sqsubseteq> c'" by simp
    from bounded_complete_defl.pair_lubs[OF f \<open>f\<cdot>x \<sqsubseteq> c'\<close> this]
    obtain z where "{f\<cdot>x, f\<cdot>y} <<| z" by (elim exE)
    then have "{up\<cdot>(f\<cdot>x), up\<cdot>(f\<cdot>y)} <<| up\<cdot>z" by (rule up_is_lub_pair)
    then show ?thesis by (auto simp: ab)
  qed
qed

lemma sinl_is_lub_pair:
  assumes z: "{x, y} <<| z" shows "{sinl\<cdot>x, sinl\<cdot>y} <<| (sinl\<cdot>z :: 'a::pcpo \<oplus> 'b::pcpo)"
proof (rule is_lubI)
  have "x \<sqsubseteq> z" "y \<sqsubseteq> z" using z by (auto dest: is_lubD1 is_ubD)
  then show "{sinl\<cdot>x, sinl\<cdot>y} <| (sinl\<cdot>z :: 'a \<oplus> 'b)" by (auto intro!: is_ubI)
next
  fix u :: "'a \<oplus> 'b" assume "{sinl\<cdot>x, sinl\<cdot>y} <| u"
  then have u: "sinl\<cdot>x \<sqsubseteq> u" "sinl\<cdot>y \<sqsubseteq> u" by (auto dest: is_ubD)
  show "sinl\<cdot>z \<sqsubseteq> u"
  proof (cases u)
    case bottom
    with u have "{x, y} <| \<bottom>" by (auto intro!: is_ubI)
    with z have "z = \<bottom>" by (blast dest: is_lubD2 intro: bottomI)
    then show ?thesis by simp
  next
    case (sinl w)
    with u have "{x, y} <| w" by (auto intro!: is_ubI)
    with z sinl show ?thesis by (simp add: is_lubD2)
  next
    case (sinr w)
    with u have "{x, y} <| \<bottom>" by (auto intro!: is_ubI)
    with z have "z = \<bottom>" by (blast dest: is_lubD2 intro: bottomI)
    then show ?thesis by simp
  qed
qed

lemma sinr_is_lub_pair:
  assumes z: "{x, y} <<| z" shows "{sinr\<cdot>x, sinr\<cdot>y} <<| (sinr\<cdot>z :: 'a::pcpo \<oplus> 'b::pcpo)"
proof (rule is_lubI)
  have "x \<sqsubseteq> z" "y \<sqsubseteq> z" using z by (auto dest: is_lubD1 is_ubD)
  then show "{sinr\<cdot>x, sinr\<cdot>y} <| (sinr\<cdot>z :: 'a \<oplus> 'b)" by (auto intro!: is_ubI)
next
  fix u :: "'a \<oplus> 'b" assume "{sinr\<cdot>x, sinr\<cdot>y} <| u"
  then have u: "sinr\<cdot>x \<sqsubseteq> u" "sinr\<cdot>y \<sqsubseteq> u" by (auto dest: is_ubD)
  show "sinr\<cdot>z \<sqsubseteq> u"
  proof (cases u)
    case bottom
    with u have "{x, y} <| \<bottom>" by (auto intro!: is_ubI)
    with z have "z = \<bottom>" by (blast dest: is_lubD2 intro: bottomI)
    then show ?thesis by simp
  next
    case (sinl w)
    with u have "{x, y} <| \<bottom>" by (auto intro!: is_ubI)
    with z have "z = \<bottom>" by (blast dest: is_lubD2 intro: bottomI)
    then show ?thesis by simp
  next
    case (sinr w)
    with u have "{x, y} <| w" by (auto intro!: is_ubI)
    with z sinr show ?thesis by (simp add: is_lubD2)
  qed
qed

lemma ex_lub_pair_bottom: "x = \<bottom> \<or> y = \<bottom> \<Longrightarrow> \<exists>z. {x, y} <<| (z::'a::pcpo)"
proof (elim disjE)
  assume "x = \<bottom>" then show ?thesis by (intro exI[of _ y]) (simp add: is_lub_bin)
next
  assume "y = \<bottom>" then show ?thesis by (intro exI[of _ x]) (simp add: is_lub_bin insert_commute)
qed

lemma bounded_complete_defl_ssum_map:
  assumes f: "bounded_complete_defl f" and g: "bounded_complete_defl g"
  shows "bounded_complete_defl (ssum_map\<cdot>f\<cdot>g)"
proof (rule bounded_complete_deflI)
  show "deflation (ssum_map\<cdot>f\<cdot>g)"
    by (rule deflation_ssum_map[OF bounded_complete_defl.axioms(1)[OF f]
          bounded_complete_defl.axioms(1)[OF g]])
  fix a b c
  assume ac: "ssum_map\<cdot>f\<cdot>g\<cdot>a \<sqsubseteq> c" and bc: "ssum_map\<cdot>f\<cdot>g\<cdot>b \<sqsubseteq> c"
  show "\<exists>z. {ssum_map\<cdot>f\<cdot>g\<cdot>a, ssum_map\<cdot>f\<cdot>g\<cdot>b} <<| z"
  proof (cases "ssum_map\<cdot>f\<cdot>g\<cdot>a = \<bottom> \<or> ssum_map\<cdot>f\<cdot>g\<cdot>b = \<bottom>")
    case True then show ?thesis by (rule ex_lub_pair_bottom)
  next
    case False
    then have A: "ssum_map\<cdot>f\<cdot>g\<cdot>a \<noteq> \<bottom>" and B: "ssum_map\<cdot>f\<cdot>g\<cdot>b \<noteq> \<bottom>" by simp_all
    show ?thesis
    proof (cases c)
      case bottom with ac A show ?thesis by simp
    next
      case (sinl w)
      obtain x where a: "a = sinl\<cdot>x" "x \<noteq> \<bottom>" "f\<cdot>x \<sqsubseteq> w"
        using ac A sinl by (cases a) auto
      obtain y where b: "b = sinl\<cdot>y" "y \<noteq> \<bottom>" "f\<cdot>y \<sqsubseteq> w"
        using bc B sinl by (cases b) auto
      from bounded_complete_defl.pair_lubs[OF f \<open>f\<cdot>x \<sqsubseteq> w\<close> \<open>f\<cdot>y \<sqsubseteq> w\<close>]
      obtain z where "{f\<cdot>x, f\<cdot>y} <<| z" by (elim exE)
      then have "{sinl\<cdot>(f\<cdot>x), sinl\<cdot>(f\<cdot>y)} <<| (sinl\<cdot>z :: _ \<oplus> _)" by (rule sinl_is_lub_pair)
      with a b show ?thesis by auto
    next
      case (sinr w)
      obtain x where a: "a = sinr\<cdot>x" "x \<noteq> \<bottom>" "g\<cdot>x \<sqsubseteq> w"
        using ac A sinr by (cases a) auto
      obtain y where b: "b = sinr\<cdot>y" "y \<noteq> \<bottom>" "g\<cdot>y \<sqsubseteq> w"
        using bc B sinr by (cases b) auto
      from bounded_complete_defl.pair_lubs[OF g \<open>g\<cdot>x \<sqsubseteq> w\<close> \<open>g\<cdot>y \<sqsubseteq> w\<close>]
      obtain z where "{g\<cdot>x, g\<cdot>y} <<| z" by (elim exE)
      then have "{sinr\<cdot>(g\<cdot>x), sinr\<cdot>(g\<cdot>y)} <<| (sinr\<cdot>z :: _ \<oplus> _)" by (rule sinr_is_lub_pair)
      with a b show ?thesis by auto
    qed
  qed
qed

lemma spair_is_lub_pair:
  assumes z1: "{x1, y1} <<| z1" and z2: "{x2, y2} <<| z2"
    and nb: "x1 \<noteq> \<bottom>" "x2 \<noteq> \<bottom>" "y1 \<noteq> \<bottom>" "y2 \<noteq> \<bottom>"
  shows "{(:x1, x2:), (:y1, y2:)} <<| (:z1, z2:)"
proof -
  have ub: "x1 \<sqsubseteq> z1" "y1 \<sqsubseteq> z1" "x2 \<sqsubseteq> z2" "y2 \<sqsubseteq> z2"
    using z1 z2 by (auto dest: is_lubD1 is_ubD)
  with nb have nbz: "z1 \<noteq> \<bottom>" "z2 \<noteq> \<bottom>" by auto
  show ?thesis
  proof (rule is_lubI)
  from ub nb nbz show "{(:x1, x2:), (:y1, y2:)} <| (:z1, z2:)"
    by (auto intro!: is_ubI simp: below_sprod)
next
  fix u assume "{(:x1, x2:), (:y1, y2:)} <| u"
  then have "(:x1, x2:) \<sqsubseteq> u" "(:y1, y2:) \<sqsubseteq> u" by (auto dest: is_ubD)
  with nb have "{x1, y1} <| sfst\<cdot>u" "{x2, y2} <| ssnd\<cdot>u"
    by (auto intro!: is_ubI simp: below_sprod)
  with z1 z2 have "z1 \<sqsubseteq> sfst\<cdot>u" "z2 \<sqsubseteq> ssnd\<cdot>u" by (auto dest: is_lubD2)
  with nbz show "(:z1, z2:) \<sqsubseteq> u" by (simp add: below_sprod)
  qed
qed

lemma bounded_complete_defl_sprod_map:
  assumes f: "bounded_complete_defl f" and g: "bounded_complete_defl g"
  shows "bounded_complete_defl (sprod_map\<cdot>f\<cdot>g)"
proof (rule bounded_complete_deflI)
  show "deflation (sprod_map\<cdot>f\<cdot>g)"
    by (rule deflation_sprod_map[OF bounded_complete_defl.axioms(1)[OF f]
          bounded_complete_defl.axioms(1)[OF g]])
  fix a b c
  assume ac: "sprod_map\<cdot>f\<cdot>g\<cdot>a \<sqsubseteq> c" and bc: "sprod_map\<cdot>f\<cdot>g\<cdot>b \<sqsubseteq> c"
  show "\<exists>z. {sprod_map\<cdot>f\<cdot>g\<cdot>a, sprod_map\<cdot>f\<cdot>g\<cdot>b} <<| z"
  proof (cases "sprod_map\<cdot>f\<cdot>g\<cdot>a = \<bottom> \<or> sprod_map\<cdot>f\<cdot>g\<cdot>b = \<bottom>")
    case True then show ?thesis by (rule ex_lub_pair_bottom)
  next
    case False
    then have A: "sprod_map\<cdot>f\<cdot>g\<cdot>a \<noteq> \<bottom>" and B: "sprod_map\<cdot>f\<cdot>g\<cdot>b \<noteq> \<bottom>" by simp_all
    obtain a1 a2 where a: "a = (:a1, a2:)" "a1 \<noteq> \<bottom>" "a2 \<noteq> \<bottom>" using A by (cases a) auto
    obtain b1 b2 where b: "b = (:b1, b2:)" "b1 \<noteq> \<bottom>" "b2 \<noteq> \<bottom>" using B by (cases b) auto
    from A a have fa: "f\<cdot>a1 \<noteq> \<bottom>" "g\<cdot>a2 \<noteq> \<bottom>" by simp_all
    from B b have fb: "f\<cdot>b1 \<noteq> \<bottom>" "g\<cdot>b2 \<noteq> \<bottom>" by simp_all
    from ac a fa have "f\<cdot>a1 \<sqsubseteq> sfst\<cdot>c" "g\<cdot>a2 \<sqsubseteq> ssnd\<cdot>c" by (simp_all add: below_sprod)
    moreover from bc b fb have "f\<cdot>b1 \<sqsubseteq> sfst\<cdot>c" "g\<cdot>b2 \<sqsubseteq> ssnd\<cdot>c" by (simp_all add: below_sprod)
    ultimately obtain z1 z2 where "{f\<cdot>a1, f\<cdot>b1} <<| z1" "{g\<cdot>a2, g\<cdot>b2} <<| z2"
      using bounded_complete_defl.pair_lubs[OF f] bounded_complete_defl.pair_lubs[OF g] by meson
    then have "{(:f\<cdot>a1, g\<cdot>a2:), (:f\<cdot>b1, g\<cdot>b2:)} <<| (:z1, z2:)"
      using fa fb by (rule spair_is_lub_pair)
    with a b show ?thesis by auto
  qed
qed

lemma bounded_complete_defl_iso:
  fixes abs :: "'r::bifinite \<rightarrow> 't::bifinite" and rep
  assumes iso_abs: "\<And>x. rep\<cdot>(abs\<cdot>x) = x" and iso_rep: "\<And>y. abs\<cdot>(rep\<cdot>y) = y"
    and f: "bounded_complete_defl f"
  shows "bounded_complete_defl (abs oo f oo rep)"
proof (rule bounded_complete_deflI)
  have iso: "iso abs rep" by (rule iso.intro[OF iso_abs iso_rep])
  interpret iso abs rep by (fact iso)
  show "deflation (abs oo f oo rep)"
    by (rule deflation_abs_rep[OF abs_iso rep_iso bounded_complete_defl.axioms(1)[OF f]])
  fix a b c assume "(abs oo f oo rep)\<cdot>a \<sqsubseteq> c" "(abs oo f oo rep)\<cdot>b \<sqsubseteq> c"
  then have "f\<cdot>(rep\<cdot>a) \<sqsubseteq> rep\<cdot>c" "f\<cdot>(rep\<cdot>b) \<sqsubseteq> rep\<cdot>c" by (simp_all add: abs_below[symmetric])
  from bounded_complete_defl.pair_lubs[OF f this]
  obtain z :: 'r where z: "{f\<cdot>(rep\<cdot>a), f\<cdot>(rep\<cdot>b)} <<| z" by (elim exE)
  have "(\<lambda>x. rep\<cdot>x) ` {abs\<cdot>(f\<cdot>(rep\<cdot>a)), abs\<cdot>(f\<cdot>(rep\<cdot>b))} = {f\<cdot>(rep\<cdot>a), f\<cdot>(rep\<cdot>b)}" by simp
  with z have "{abs\<cdot>(f\<cdot>(rep\<cdot>a)), abs\<cdot>(f\<cdot>(rep\<cdot>b))} <<| abs\<cdot>z"
    by (simp only: iso_is_lub_iff[OF iso, symmetric])
  then show "\<exists>z. {(abs oo f oo rep)\<cdot>a, (abs oo f oo rep)\<cdot>b} <<| z" by auto
qed

lemma adm_bounded_complete_defl: "adm (bounded_complete_defl :: ('a::bifinite \<rightarrow> 'a) \<Rightarrow> bool)"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'a" assume Y: "chain Y" and P: "\<forall>i. bounded_complete_defl (Y i)"
  have chx: "chain (\<lambda>n. Y n\<cdot>x)" for x by (rule ch2ch_Rep_cfunL[OF Y])
  have reach: "(\<Squnion>n. Y n\<cdot>x) = (\<Squnion>i. Y i)\<cdot>x" for x by (rule contlub_cfun_fun[OF Y, symmetric])
  have below: "Y n\<cdot>x \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x" for n x
    using is_ub_thelub[OF chx, of n x] by (simp only: reach)
  show "bounded_complete_defl (\<Squnion>i. Y i)"
  proof (rule bounded_complete_deflI)
    show "deflation (\<Squnion>i. Y i)"
      by (rule admD[OF adm_deflation Y]) (rule bounded_complete_defl.axioms(1)[OF P[rule_format]])
    fix a b c assume ac: "(\<Squnion>i. Y i)\<cdot>a \<sqsubseteq> c" and bc: "(\<Squnion>i. Y i)\<cdot>b \<sqsubseteq> c"
    define L where "L n = lub {Y n\<cdot>a, Y n\<cdot>b}" for n
    have L: "{Y n\<cdot>a, Y n\<cdot>b} <<| L n" for n
    proof -
      have "Y n\<cdot>a \<sqsubseteq> c" "Y n\<cdot>b \<sqsubseteq> c"
        using below_trans[OF below[of n a] ac] below_trans[OF below[of n b] bc] .
      from bounded_complete_defl.pair_lubs[OF P[rule_format] this]
      obtain z where "{Y n\<cdot>a, Y n\<cdot>b} <<| z" by (elim exE)
      then show ?thesis unfolding L_def by (rule is_lub_lub)
    qed
    have chL: "chain L"
    proof (rule chainI)
      fix n
      have "Y n\<cdot>a \<sqsubseteq> L (Suc n)" "Y n\<cdot>b \<sqsubseteq> L (Suc n)"
        using chainE[OF chx] is_lubD1[OF L, THEN is_ubD] by (blast intro: below_trans)+
      then show "L n \<sqsubseteq> L (Suc n)" by (blast intro: is_lubD2[OF L] is_ubI)
    qed
    have "{(\<Squnion>i. Y i)\<cdot>a, (\<Squnion>i. Y i)\<cdot>b} <<| (\<Squnion>n. L n)"
    proof (rule is_lubI)
      have "(\<Squnion>n. Y n\<cdot>a) \<sqsubseteq> (\<Squnion>n. L n)" "(\<Squnion>n. Y n\<cdot>b) \<sqsubseteq> (\<Squnion>n. L n)"
        using is_lubD1[OF L, THEN is_ubD] by (blast intro: lub_mono chx chL)+
      then show "{(\<Squnion>i. Y i)\<cdot>a, (\<Squnion>i. Y i)\<cdot>b} <| (\<Squnion>n. L n)" by (simp add: reach is_ub_def)
    next
      fix u assume "{(\<Squnion>i. Y i)\<cdot>a, (\<Squnion>i. Y i)\<cdot>b} <| u"
      then have "(\<Squnion>i. Y i)\<cdot>a \<sqsubseteq> u" "(\<Squnion>i. Y i)\<cdot>b \<sqsubseteq> u" by (auto dest: is_ubD)
      then have "L n \<sqsubseteq> u" for n
        using below[of n a] below[of n b] by (blast intro: is_lubD2[OF L] is_ubI below_trans)
      then show "(\<Squnion>n. L n) \<sqsubseteq> u" by (rule lub_below[OF chL])
    qed
    then show "\<exists>z. {(\<Squnion>i. Y i)\<cdot>a, (\<Squnion>i. Y i)\<cdot>b} <<| z" ..
  qed
qed

text \<open>Antitone among deflations: a smaller deflation has a smaller image.\<close>

lemma bounded_complete_defl_below:
  assumes le: "d \<sqsubseteq> e" and e: "bounded_complete_defl e" and d: "deflation d"
  shows "bounded_complete_defl d"
proof (rule bounded_complete_deflI[OF d])
  have de: "deflation e" by (rule bounded_complete_defl.axioms(1)[OF e])
  fix a b c assume "d\<cdot>a \<sqsubseteq> c" "d\<cdot>b \<sqsubseteq> c"
  moreover have "e\<cdot>(d\<cdot>a) = d\<cdot>a" "e\<cdot>(d\<cdot>b) = d\<cdot>b" by (rule deflation_below_comp2[OF d de le])+
  ultimately show "\<exists>z. {d\<cdot>a, d\<cdot>b} <<| z"
    using bounded_complete_defl.pair_lubs[OF e, of "d\<cdot>a" c "d\<cdot>b"] by simp
qed

lemma bounded_complete_class_deflI:
  assumes d: "bounded_complete_defl (ID :: 'a::bifinite \<rightarrow> 'a)"
  shows "OFCLASS('a, bounded_complete_class)"
proof (rule bounded_complete_chainI[of "\<lambda>n. ID"])
  show "chain (\<lambda>n. ID :: 'a \<rightarrow> 'a)" by simp
  show "(\<Squnion>n. ID :: 'a \<rightarrow> 'a) = ID" by simp
  fix n and a b c :: 'a
  assume "ID\<cdot>a \<sqsubseteq> c" "ID\<cdot>b \<sqsubseteq> c"
  then show "\<exists>z. {ID\<cdot>a, ID\<cdot>b} <<| z" by (rule bounded_complete_defl.pair_lubs[OF d])
qed

subsection \<open>Separation\<close>

text \<open>Separation is stated one-sidedly: a nonbottom image element shares a nonbottom lower bound
  with every nonbottom element it is joinable with, the second element being arbitrary.  At
  @{term ID} this is @{class filter_sum}.  The one-sided form is admissible without conditions
  on the images (a witness found at a finite stage stays a witness in the limit), and it is the
  shape that carries over to separated sums, where the witness is a global atom.\<close>

lemma filter_sum_deflI:
  assumes "deflation d"
    and "\<And>x y u. d\<cdot>x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> d\<cdot>x \<sqsubseteq> u \<Longrightarrow> y \<sqsubseteq> u \<Longrightarrow> \<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> d\<cdot>x \<and> l \<sqsubseteq> y"
  shows "filter_sum_defl d"
  using assms by (simp add: filter_sum_defl_def filter_sum_defl_axioms_def)

lemma filter_sum_defl_bottom: "filter_sum_defl (\<bottom> :: 'a::bifinite \<rightarrow> 'a)"
  by (rule filter_sum_deflI[OF deflation_bottom]) simp

lemma filter_sum_defl_ID: "filter_sum_defl (ID :: 'a::{bifinite, filter_sum} \<rightarrow> 'a)"
  by (rule filter_sum_deflI[OF deflation_ID]) (simp add: filter_sum)

lemma filter_sum_class_deflI:
  assumes d: "filter_sum_defl (ID :: 'a::bifinite \<rightarrow> 'a)"
  shows "OFCLASS('a, filter_sum_class)"
proof
  fix x y u :: 'a assume "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" "x \<sqsubseteq> u" "y \<sqsubseteq> u"
  then show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
    using filter_sum_defl.filter_sum_image[OF d, of x y u] by simp
qed

text \<open>Lifting separates unconditionally: only the deflation property of @{term f} is needed.\<close>

lemma filter_sum_defl_u_map:
  assumes f: "deflation (f :: 'a::bifinite \<rightarrow> 'a)" shows "filter_sum_defl (u_map\<cdot>f)"
proof (rule filter_sum_deflI[OF deflation_u_map[OF f]])
  fix x y u :: "'a\<^sub>\<bottom>" assume x: "u_map\<cdot>f\<cdot>x \<noteq> \<bottom>" and y: "y \<noteq> \<bottom>"
  from x obtain x' where "x = up\<cdot>x'" by (cases x) auto
  moreover from y obtain y' where "y = up\<cdot>y'" by (cases y) auto
  ultimately show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> u_map\<cdot>f\<cdot>x \<and> l \<sqsubseteq> y" by (intro exI[of _ "up\<cdot>\<bottom>"]) simp
qed

lemma filter_sum_defl_ssum_map:
  assumes f: "filter_sum_defl f" and g: "filter_sum_defl g"
  shows "filter_sum_defl (ssum_map\<cdot>f\<cdot>g)"
proof (rule filter_sum_deflI)
  show "deflation (ssum_map\<cdot>f\<cdot>g)"
    using f g by (intro deflation_ssum_map) (simp_all add: filter_sum_defl_def)
  fix x y u assume x: "ssum_map\<cdot>f\<cdot>g\<cdot>x \<noteq> \<bottom>" and y: "y \<noteq> \<bottom>"
    and xu: "ssum_map\<cdot>f\<cdot>g\<cdot>x \<sqsubseteq> u" and yu: "y \<sqsubseteq> u"
  show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> ssum_map\<cdot>f\<cdot>g\<cdot>x \<and> l \<sqsubseteq> y"
  proof (cases x)
    case bottom with x show ?thesis by simp
  next
    case (sinl x')
    with x have fx: "f\<cdot>x' \<noteq> \<bottom>" and img: "ssum_map\<cdot>f\<cdot>g\<cdot>x = sinl\<cdot>(f\<cdot>x')" by simp_all
    obtain u' where u: "u = sinl\<cdot>u'" "f\<cdot>x' \<sqsubseteq> u'"
      using xu fx img by (cases u) auto
    obtain y' where yy: "y = sinl\<cdot>y'" "y' \<noteq> \<bottom>" "y' \<sqsubseteq> u'"
      using yu y u by (cases y) auto
    obtain l' where l': "l' \<noteq> \<bottom>" "l' \<sqsubseteq> f\<cdot>x'" "l' \<sqsubseteq> y'"
      using filter_sum_defl.filter_sum_image[OF f fx yy(2) u(2) yy(3)] by auto
    show ?thesis using l' img yy(1) by (intro exI[of _ "sinl\<cdot>l'"]) simp
  next
    case (sinr x')
    with x have gx: "g\<cdot>x' \<noteq> \<bottom>" and img: "ssum_map\<cdot>f\<cdot>g\<cdot>x = sinr\<cdot>(g\<cdot>x')" by simp_all
    obtain u' where u: "u = sinr\<cdot>u'" "g\<cdot>x' \<sqsubseteq> u'"
      using xu gx img by (cases u) auto
    obtain y' where yy: "y = sinr\<cdot>y'" "y' \<noteq> \<bottom>" "y' \<sqsubseteq> u'"
      using yu y u by (cases y) auto
    obtain l' where l': "l' \<noteq> \<bottom>" "l' \<sqsubseteq> g\<cdot>x'" "l' \<sqsubseteq> y'"
      using filter_sum_defl.filter_sum_image[OF g gx yy(2) u(2) yy(3)] by auto
    show ?thesis using l' img yy(1) by (intro exI[of _ "sinr\<cdot>l'"]) simp
  qed
qed

lemma filter_sum_defl_sprod_map:
  assumes f: "filter_sum_defl f" and g: "filter_sum_defl g"
  shows "filter_sum_defl (sprod_map\<cdot>f\<cdot>g)"
proof (rule filter_sum_deflI)
  show "deflation (sprod_map\<cdot>f\<cdot>g)"
    using f g by (intro deflation_sprod_map) (simp_all add: filter_sum_defl_def)
  fix x y u assume x: "sprod_map\<cdot>f\<cdot>g\<cdot>x \<noteq> \<bottom>" and y: "y \<noteq> \<bottom>"
    and xu: "sprod_map\<cdot>f\<cdot>g\<cdot>x \<sqsubseteq> u" and yu: "y \<sqsubseteq> u"
  obtain x1 x2 where xx: "x = (:x1, x2:)" "x1 \<noteq> \<bottom>" "x2 \<noteq> \<bottom>" using x by (cases x) auto
  with x have fx: "f\<cdot>x1 \<noteq> \<bottom>" "g\<cdot>x2 \<noteq> \<bottom>" and img: "sprod_map\<cdot>f\<cdot>g\<cdot>x = (:f\<cdot>x1, g\<cdot>x2:)"
    by simp_all
  obtain u1 u2 where u: "u = (:u1, u2:)" "f\<cdot>x1 \<sqsubseteq> u1" "g\<cdot>x2 \<sqsubseteq> u2"
    using xu fx img by (cases u) (auto simp: spair_below)
  obtain y1 y2 where yy: "y = (:y1, y2:)" "y1 \<noteq> \<bottom>" "y2 \<noteq> \<bottom>" "y1 \<sqsubseteq> u1" "y2 \<sqsubseteq> u2"
    using yu y u by (cases y) (auto simp: spair_below)
  obtain l1 where l1: "l1 \<noteq> \<bottom>" "l1 \<sqsubseteq> f\<cdot>x1" "l1 \<sqsubseteq> y1"
    using filter_sum_defl.filter_sum_image[OF f fx(1) yy(2) u(2) yy(4)] by auto
  obtain l2 where l2: "l2 \<noteq> \<bottom>" "l2 \<sqsubseteq> g\<cdot>x2" "l2 \<sqsubseteq> y2"
    using filter_sum_defl.filter_sum_image[OF g fx(2) yy(3) u(3) yy(5)] by auto
  show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> sprod_map\<cdot>f\<cdot>g\<cdot>x \<and> l \<sqsubseteq> y"
    using l1 l2 img yy(1) by (intro exI[of _ "(:l1, l2:)"]) (simp add: spair_below)
qed

lemma filter_sum_defl_iso:
  fixes abs :: "'r::bifinite \<rightarrow> 't::bifinite" and rep
  assumes iso_abs: "\<And>x. rep\<cdot>(abs\<cdot>x) = x" and iso_rep: "\<And>y. abs\<cdot>(rep\<cdot>y) = y"
    and f: "filter_sum_defl f"
  shows "filter_sum_defl (abs oo f oo rep)"
proof (rule filter_sum_deflI)
  interpret iso abs rep by (rule iso.intro[OF iso_abs iso_rep])
  show "deflation (abs oo f oo rep)"
    using f by (intro deflation_abs_rep[OF abs_iso rep_iso]) (simp add: filter_sum_defl_def)
  fix x y u assume x: "(abs oo f oo rep)\<cdot>x \<noteq> \<bottom>" and y: "y \<noteq> \<bottom>"
    and xu: "(abs oo f oo rep)\<cdot>x \<sqsubseteq> u" and yu: "y \<sqsubseteq> u"
  have fx: "f\<cdot>(rep\<cdot>x) \<noteq> \<bottom>" using x by (simp add: abs_bottom_iff)
  have ry: "rep\<cdot>y \<noteq> \<bottom>" using y by (simp add: rep_bottom_iff)
  have "rep\<cdot>(abs\<cdot>(f\<cdot>(rep\<cdot>x))) \<sqsubseteq> rep\<cdot>u" using monofun_cfun_arg[OF xu, of rep] by simp
  then have fxu: "f\<cdot>(rep\<cdot>x) \<sqsubseteq> rep\<cdot>u" by (simp del: rep_iso)
  have ryu: "rep\<cdot>y \<sqsubseteq> rep\<cdot>u" using yu by (rule monofun_cfun_arg)
  obtain l where l: "l \<noteq> \<bottom>" "l \<sqsubseteq> f\<cdot>(rep\<cdot>x)" "l \<sqsubseteq> rep\<cdot>y"
    using filter_sum_defl.filter_sum_image[OF f fx ry fxu ryu] by auto
  have "abs\<cdot>l \<sqsubseteq> abs\<cdot>(f\<cdot>(rep\<cdot>x))" using l(2) by (rule monofun_cfun_arg)
  moreover have "abs\<cdot>l \<sqsubseteq> abs\<cdot>(rep\<cdot>y)" using l(3) by (rule monofun_cfun_arg)
  ultimately show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> (abs oo f oo rep)\<cdot>x \<and> l \<sqsubseteq> y"
    using l(1) by (intro exI[of _ "abs\<cdot>l"]) (simp add: abs_bottom_iff)
qed

lemma adm_filter_sum_defl: "adm (filter_sum_defl :: ('a::bifinite \<rightarrow> 'a) \<Rightarrow> bool)"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'a" assume Y: "chain Y" and s: "\<forall>i. filter_sum_defl (Y i)"
  show "filter_sum_defl (\<Squnion>i. Y i)"
  proof (rule filter_sum_deflI)
    show "deflation (\<Squnion>i. Y i)"
      by (rule admD[OF adm_deflation Y]) (use s in \<open>simp add: filter_sum_defl_def\<close>)
    fix x y u assume x: "(\<Squnion>i. Y i)\<cdot>x \<noteq> \<bottom>" and y: "y \<noteq> \<bottom>"
      and xu: "(\<Squnion>i. Y i)\<cdot>x \<sqsubseteq> u" and yu: "y \<sqsubseteq> u"
    have chx: "chain (\<lambda>i. Y i\<cdot>x)" by (rule ch2ch_Rep_cfunL[OF Y])
    have lub: "(\<Squnion>i. Y i)\<cdot>x = (\<Squnion>i. Y i\<cdot>x)" by (rule contlub_cfun_fun[OF Y])
    obtain n where n: "Y n\<cdot>x \<noteq> \<bottom>" using x lub_eq_bottom_iff[OF chx] lub by auto
    have below: "Y n\<cdot>x \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x" by (rule monofun_cfun_fun[OF is_ub_thelub[OF Y]])
    obtain l where l: "l \<noteq> \<bottom>" "l \<sqsubseteq> Y n\<cdot>x" "l \<sqsubseteq> y"
      using filter_sum_defl.filter_sum_image[OF s[rule_format, of n] n y below_trans[OF below xu] yu]
      by auto
    show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x \<and> l \<sqsubseteq> y"
      using l below_trans[OF l(2) below] by auto
  qed
qed

text \<open>Antitone among deflations.\<close>

lemma filter_sum_defl_below:
  assumes le: "d \<sqsubseteq> e" and e: "filter_sum_defl e" and d: "deflation d"
  shows "filter_sum_defl d"
proof (rule filter_sum_deflI[OF d])
  fix x y u assume x: "d\<cdot>x \<noteq> \<bottom>" "y \<noteq> \<bottom>" "d\<cdot>x \<sqsubseteq> u" "y \<sqsubseteq> u"
  have "e\<cdot>(d\<cdot>x) = d\<cdot>x"
    by (rule deflation_below_comp2[OF d filter_sum_defl.axioms(1)[OF e] le])
  then show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> d\<cdot>x \<and> l \<sqsubseteq> y"
    using filter_sum_defl.filter_sum_image[OF e, of "d\<cdot>x" y u] x by simp
qed


subsection \<open>Separated sums\<close>

text \<open>The one-sided separation of the previous subsection with an \<^emph>\<open>atom\<close> of the whole type as
  witness.  Since the atom is global and the second element arbitrary, a witness found at a
  finite stage of a chain stays a witness in the limit: the predicate is admissible with no
  condition on the images.  (Minimality taken within the image instead would not be: a type
  whose nonbottom elements form a descending chain without least element has no atoms, yet is
  the limit of finite deflations whose images do have least nonbottom elements.)\<close>

locale separated_sum_defl = deflation d for d :: "'a::bifinite \<rightarrow> 'a" +
  assumes separated_sum_image:
    "d\<cdot>x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> d\<cdot>x \<sqsubseteq> u \<Longrightarrow> y \<sqsubseteq> u \<Longrightarrow> \<exists>l. atom l \<and> l \<sqsubseteq> d\<cdot>x \<and> l \<sqsubseteq> y"

lemma (in separated_sum_defl) deflation: "deflation d" by (fact deflation_axioms)

lemma separated_sum_deflI:
  assumes "deflation d"
    and "\<And>x y u. d\<cdot>x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> d\<cdot>x \<sqsubseteq> u \<Longrightarrow> y \<sqsubseteq> u \<Longrightarrow> \<exists>l. atom l \<and> l \<sqsubseteq> d\<cdot>x \<and> l \<sqsubseteq> y"
  shows "separated_sum_defl d"
  using assms by (simp add: separated_sum_defl_def separated_sum_defl_axioms_def)

lemma separated_sum_defl_bottom: "separated_sum_defl (\<bottom> :: 'a::bifinite \<rightarrow> 'a)"
  by (rule separated_sum_deflI[OF deflation_bottom]) simp

lemma separated_sum_defl_ID: "separated_sum_defl (ID :: 'a::{bifinite, separated_sum} \<rightarrow> 'a)"
  by (rule separated_sum_deflI[OF deflation_ID]) (simp add: separated_sum)

lemma separated_sum_class_deflI:
  assumes d: "separated_sum_defl (ID :: 'a::bifinite \<rightarrow> 'a)"
  shows "OFCLASS('a, separated_sum_class)"
proof
  fix x y u :: 'a assume "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" "x \<sqsubseteq> u" "y \<sqsubseteq> u"
  then show "\<exists>l. atom l \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y"
    using separated_sum_defl.separated_sum_image[OF d, of x y u] by simp
qed

lemma separated_sum_defl_u_map:
  assumes f: "deflation (f :: 'a::bifinite \<rightarrow> 'a)" shows "separated_sum_defl (u_map\<cdot>f)"
proof (rule separated_sum_deflI[OF deflation_u_map[OF f]])
  fix x y u :: "'a\<^sub>\<bottom>" assume x: "u_map\<cdot>f\<cdot>x \<noteq> \<bottom>" and y: "y \<noteq> \<bottom>"
  from x obtain x' where "x = up\<cdot>x'" by (cases x) auto
  moreover from y obtain y' where "y = up\<cdot>y'" by (cases y) auto
  ultimately show "\<exists>l. atom l \<and> l \<sqsubseteq> u_map\<cdot>f\<cdot>x \<and> l \<sqsubseteq> y"
    by (intro exI[of _ "up\<cdot>\<bottom>"]) (simp add: atom_up_bottom)
qed

lemma separated_sum_defl_ssum_map:
  assumes f: "separated_sum_defl f" and g: "separated_sum_defl g"
  shows "separated_sum_defl (ssum_map\<cdot>f\<cdot>g)"
proof (rule separated_sum_deflI)
  show "deflation (ssum_map\<cdot>f\<cdot>g)"
    using f g by (intro deflation_ssum_map) (simp_all add: separated_sum_defl_def)
  fix x y u assume x: "ssum_map\<cdot>f\<cdot>g\<cdot>x \<noteq> \<bottom>" and y: "y \<noteq> \<bottom>"
    and xu: "ssum_map\<cdot>f\<cdot>g\<cdot>x \<sqsubseteq> u" and yu: "y \<sqsubseteq> u"
  show "\<exists>l. atom l \<and> l \<sqsubseteq> ssum_map\<cdot>f\<cdot>g\<cdot>x \<and> l \<sqsubseteq> y"
  proof (cases x)
    case bottom with x show ?thesis by simp
  next
    case (sinl x')
    with x have fx: "f\<cdot>x' \<noteq> \<bottom>" and img: "ssum_map\<cdot>f\<cdot>g\<cdot>x = sinl\<cdot>(f\<cdot>x')" by simp_all
    obtain u' where u: "u = sinl\<cdot>u'" "f\<cdot>x' \<sqsubseteq> u'"
      using xu fx img by (cases u) auto
    obtain y' where yy: "y = sinl\<cdot>y'" "y' \<noteq> \<bottom>" "y' \<sqsubseteq> u'"
      using yu y u by (cases y) auto
    obtain l' where l': "atom l'" "l' \<sqsubseteq> f\<cdot>x'" "l' \<sqsubseteq> y'"
      using separated_sum_defl.separated_sum_image[OF f fx yy(2) u(2) yy(3)] by auto
    show ?thesis using l' img yy(1) by (intro exI[of _ "sinl\<cdot>l'"]) (simp add: atom_sinl_iff)
  next
    case (sinr x')
    with x have gx: "g\<cdot>x' \<noteq> \<bottom>" and img: "ssum_map\<cdot>f\<cdot>g\<cdot>x = sinr\<cdot>(g\<cdot>x')" by simp_all
    obtain u' where u: "u = sinr\<cdot>u'" "g\<cdot>x' \<sqsubseteq> u'"
      using xu gx img by (cases u) auto
    obtain y' where yy: "y = sinr\<cdot>y'" "y' \<noteq> \<bottom>" "y' \<sqsubseteq> u'"
      using yu y u by (cases y) auto
    obtain l' where l': "atom l'" "l' \<sqsubseteq> g\<cdot>x'" "l' \<sqsubseteq> y'"
      using separated_sum_defl.separated_sum_image[OF g gx yy(2) u(2) yy(3)] by auto
    show ?thesis using l' img yy(1) by (intro exI[of _ "sinr\<cdot>l'"]) (simp add: atom_sinr_iff)
  qed
qed

lemma separated_sum_defl_sprod_map:
  assumes f: "separated_sum_defl f" and g: "separated_sum_defl g"
  shows "separated_sum_defl (sprod_map\<cdot>f\<cdot>g)"
proof (rule separated_sum_deflI)
  show "deflation (sprod_map\<cdot>f\<cdot>g)"
    using f g by (intro deflation_sprod_map) (simp_all add: separated_sum_defl_def)
  fix x y u assume x: "sprod_map\<cdot>f\<cdot>g\<cdot>x \<noteq> \<bottom>" and y: "y \<noteq> \<bottom>"
    and xu: "sprod_map\<cdot>f\<cdot>g\<cdot>x \<sqsubseteq> u" and yu: "y \<sqsubseteq> u"
  obtain x1 x2 where xx: "x = (:x1, x2:)" "x1 \<noteq> \<bottom>" "x2 \<noteq> \<bottom>" using x by (cases x) auto
  with x have fx: "f\<cdot>x1 \<noteq> \<bottom>" "g\<cdot>x2 \<noteq> \<bottom>" and img: "sprod_map\<cdot>f\<cdot>g\<cdot>x = (:f\<cdot>x1, g\<cdot>x2:)"
    by simp_all
  obtain u1 u2 where u: "u = (:u1, u2:)" "f\<cdot>x1 \<sqsubseteq> u1" "g\<cdot>x2 \<sqsubseteq> u2"
    using xu fx img by (cases u) (auto simp: spair_below)
  obtain y1 y2 where yy: "y = (:y1, y2:)" "y1 \<noteq> \<bottom>" "y2 \<noteq> \<bottom>" "y1 \<sqsubseteq> u1" "y2 \<sqsubseteq> u2"
    using yu y u by (cases y) (auto simp: spair_below)
  obtain l1 where l1: "atom l1" "l1 \<sqsubseteq> f\<cdot>x1" "l1 \<sqsubseteq> y1"
    using separated_sum_defl.separated_sum_image[OF f fx(1) yy(2) u(2) yy(4)] by auto
  obtain l2 where l2: "atom l2" "l2 \<sqsubseteq> g\<cdot>x2" "l2 \<sqsubseteq> y2"
    using separated_sum_defl.separated_sum_image[OF g fx(2) yy(3) u(3) yy(5)] by auto
  show "\<exists>l. atom l \<and> l \<sqsubseteq> sprod_map\<cdot>f\<cdot>g\<cdot>x \<and> l \<sqsubseteq> y"
    using l1 l2 img yy(1) atom_nonbottom[OF l1(1)] atom_nonbottom[OF l2(1)]
    by (intro exI[of _ "(:l1, l2:)"]) (simp add: atom_spair spair_below)
qed

text \<open>An isomorphism maps atoms to atoms.\<close>

lemma iso_atom:
  fixes abs :: "'r::pcpo \<rightarrow> 't::pcpo" and rep
  assumes iso: "iso abs rep" and l: "atom l" shows "atom (abs\<cdot>l)"
proof (rule atomI)
  interpret iso abs rep by (fact iso)
  show "abs\<cdot>l \<noteq> \<bottom>" using atom_nonbottom[OF l] by (simp add: abs_bottom_iff)
  fix z assume "z \<sqsubseteq> abs\<cdot>l"
  then have "rep\<cdot>z \<sqsubseteq> l" by (simp add: abs_below[symmetric])
  from atomD[OF l this] show "z = \<bottom> \<or> z = abs\<cdot>l" by (auto simp: rep_bottom_iff)
qed

lemma separated_sum_defl_iso:
  fixes abs :: "'r::bifinite \<rightarrow> 't::bifinite" and rep
  assumes iso_abs: "\<And>x. rep\<cdot>(abs\<cdot>x) = x" and iso_rep: "\<And>y. abs\<cdot>(rep\<cdot>y) = y"
    and f: "separated_sum_defl f"
  shows "separated_sum_defl (abs oo f oo rep)"
proof (rule separated_sum_deflI)
  have iso: "iso abs rep" by (rule iso.intro[OF iso_abs iso_rep])
  interpret iso abs rep by (fact iso)
  show "deflation (abs oo f oo rep)"
    using f by (intro deflation_abs_rep[OF abs_iso rep_iso]) (simp add: separated_sum_defl_def)
  fix x y u assume x: "(abs oo f oo rep)\<cdot>x \<noteq> \<bottom>" and y: "y \<noteq> \<bottom>"
    and xu: "(abs oo f oo rep)\<cdot>x \<sqsubseteq> u" and yu: "y \<sqsubseteq> u"
  have fx: "f\<cdot>(rep\<cdot>x) \<noteq> \<bottom>" using x by (simp add: abs_bottom_iff)
  have ry: "rep\<cdot>y \<noteq> \<bottom>" using y by (simp add: rep_bottom_iff)
  have "rep\<cdot>(abs\<cdot>(f\<cdot>(rep\<cdot>x))) \<sqsubseteq> rep\<cdot>u" using monofun_cfun_arg[OF xu, of rep] by simp
  then have fxu: "f\<cdot>(rep\<cdot>x) \<sqsubseteq> rep\<cdot>u" by (simp del: rep_iso)
  have ryu: "rep\<cdot>y \<sqsubseteq> rep\<cdot>u" using yu by (rule monofun_cfun_arg)
  obtain l where l: "atom l" "l \<sqsubseteq> f\<cdot>(rep\<cdot>x)" "l \<sqsubseteq> rep\<cdot>y"
    using separated_sum_defl.separated_sum_image[OF f fx ry fxu ryu] by auto
  have "abs\<cdot>l \<sqsubseteq> abs\<cdot>(f\<cdot>(rep\<cdot>x))" using l(2) by (rule monofun_cfun_arg)
  moreover have "abs\<cdot>l \<sqsubseteq> abs\<cdot>(rep\<cdot>y)" using l(3) by (rule monofun_cfun_arg)
  ultimately show "\<exists>l. atom l \<and> l \<sqsubseteq> (abs oo f oo rep)\<cdot>x \<and> l \<sqsubseteq> y"
    using iso_atom[OF iso l(1)] by (intro exI[of _ "abs\<cdot>l"]) simp
qed

lemma adm_separated_sum_defl: "adm (separated_sum_defl :: ('a::bifinite \<rightarrow> 'a) \<Rightarrow> bool)"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'a" assume Y: "chain Y" and s: "\<forall>i. separated_sum_defl (Y i)"
  show "separated_sum_defl (\<Squnion>i. Y i)"
  proof (rule separated_sum_deflI)
    show "deflation (\<Squnion>i. Y i)"
      by (rule admD[OF adm_deflation Y]) (use s in \<open>simp add: separated_sum_defl_def\<close>)
    fix x y u assume x: "(\<Squnion>i. Y i)\<cdot>x \<noteq> \<bottom>" and y: "y \<noteq> \<bottom>"
      and xu: "(\<Squnion>i. Y i)\<cdot>x \<sqsubseteq> u" and yu: "y \<sqsubseteq> u"
    have chx: "chain (\<lambda>i. Y i\<cdot>x)" by (rule ch2ch_Rep_cfunL[OF Y])
    have lub: "(\<Squnion>i. Y i)\<cdot>x = (\<Squnion>i. Y i\<cdot>x)" by (rule contlub_cfun_fun[OF Y])
    obtain n where n: "Y n\<cdot>x \<noteq> \<bottom>" using x lub_eq_bottom_iff[OF chx] lub by auto
    have below: "Y n\<cdot>x \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x" by (rule monofun_cfun_fun[OF is_ub_thelub[OF Y]])
    obtain l where l: "atom l" "l \<sqsubseteq> Y n\<cdot>x" "l \<sqsubseteq> y"
      using separated_sum_defl.separated_sum_image[OF s[rule_format, of n] n y
          below_trans[OF below xu] yu]
      by auto
    show "\<exists>l. atom l \<and> l \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x \<and> l \<sqsubseteq> y"
      using l below_trans[OF l(2) below] by auto
  qed
qed

subsection \<open>Distributivity\<close>

text \<open>The distributive law with only the meeting element @{term c} restricted to the image.  The
  type itself is required to be bounded complete (that class is derived first), so meets and
  joins are the class operations; other order properties of the components enter the same way,
  as sort constraints (@{class filter_sum} for the smash product).  Admissibility needs no
  downward closure, only continuity of meet (@{thm [source] cont_meet_arg}).\<close>

locale distributive_defl = deflation d for d :: "'a::{bifinite, bounded_complete} \<rightarrow> 'a" +
  assumes distrib_image: "a \<Up> b \<Longrightarrow> d\<cdot>c \<sqinter> (a \<squnion> b) = d\<cdot>c \<sqinter> a \<squnion> d\<cdot>c \<sqinter> b"

lemma (in distributive_defl) deflation: "deflation d" by (fact deflation_axioms)

lemma distributive_deflI:
  "deflation d \<Longrightarrow> (\<And>a b c. a \<Up> b \<Longrightarrow> d\<cdot>c \<sqinter> (a \<squnion> b) = d\<cdot>c \<sqinter> a \<squnion> d\<cdot>c \<sqinter> b) \<Longrightarrow> distributive_defl d"
  by (simp add: distributive_defl_def distributive_defl_axioms_def)

lemma distributive_defl_bottom: "distributive_defl (\<bottom> :: 'a::{bifinite, bounded_complete} \<rightarrow> 'a)"
  by (rule distributive_deflI[OF deflation_bottom]) simp

lemma distributive_defl_ID: "distributive_defl (ID :: 'a::{bifinite, distributive_cpo} \<rightarrow> 'a)"
  by (rule distributive_deflI[OF deflation_ID]) (simp add: meet_join_distrib)

lemma distributive_cpo_class_deflI:
  assumes "distributive_defl (ID :: 'a::{bifinite, bounded_complete} \<rightarrow> 'a)"
  shows "OFCLASS('a, distributive_cpo_class)"
  by intro_classes (simp add: distributive_defl.distrib_image[OF assms, simplified])

lemma adm_distributive_defl:
  "adm (distributive_defl :: ('a::{bifinite, bounded_complete} \<rightarrow> 'a) \<Rightarrow> bool)"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'a"
  assume chain: "chain Y" and H: "\<forall>i. distributive_defl (Y i)"
  show "distributive_defl (\<Squnion>i. Y i)"
  proof (rule distributive_deflI)
    show "deflation (\<Squnion>i. Y i)"
      by (rule admD[OF adm_deflation chain]) (simp add: distributive_defl.deflation H)
    fix a b c :: 'a assume ab: "a \<Up> b"
    have ch: "chain (\<lambda>n. Y n\<cdot>c)" by (rule ch2ch_Rep_cfunL[OF chain])
    have reach: "(\<Squnion>i. Y i)\<cdot>c = (\<Squnion>n. Y n\<cdot>c)" by (rule contlub_cfun_fun[OF chain])
    have lim: "(\<Squnion>n. Y n\<cdot>c) \<sqinter> y = (\<Squnion>n. Y n\<cdot>c \<sqinter> y)" and chy: "chain (\<lambda>n. Y n\<cdot>c \<sqinter> y)" for y
      using cont2contlubE[OF cont_meet_arg ch, of y] ch2ch_cont[OF cont_meet_arg ch, of y]
      by simp_all
    have j: "Y n\<cdot>c \<sqinter> a \<Up> Y n\<cdot>c \<sqinter> b" for n by (rule joinableI[OF meet_below1 meet_below1])
    have "(\<Squnion>n. Y n\<cdot>c) \<sqinter> (a \<squnion> b) = (\<Squnion>n. Y n\<cdot>c \<sqinter> (a \<squnion> b))" by (rule lim)
    also have "\<dots> = (\<Squnion>n. Y n\<cdot>c \<sqinter> a \<squnion> Y n\<cdot>c \<sqinter> b)"
      by (simp only: distributive_defl.distrib_image[OF H[rule_format] ab])
    also have "\<dots> = (\<Squnion>n. Y n\<cdot>c \<sqinter> a) \<squnion> (\<Squnion>n. Y n\<cdot>c \<sqinter> b)" by (rule lub_join_chains(3)[OF chy chy j])
    also have "\<dots> = (\<Squnion>n. Y n\<cdot>c) \<sqinter> a \<squnion> (\<Squnion>n. Y n\<cdot>c) \<sqinter> b" by (simp only: lim[symmetric])
    finally show "(\<Squnion>i. Y i)\<cdot>c \<sqinter> (a \<squnion> b) = (\<Squnion>i. Y i)\<cdot>c \<sqinter> a \<squnion> (\<Squnion>i. Y i)\<cdot>c \<sqinter> b"
      by (simp only: reach)
  qed
qed

lemma distributive_defl_iso:
  fixes abs :: "'r::{bifinite, bounded_complete} \<rightarrow> 't::{bifinite, bounded_complete}" and rep
  assumes iso_abs: "\<And>x. rep\<cdot>(abs\<cdot>x) = x" and iso_rep: "\<And>y. abs\<cdot>(rep\<cdot>y) = y"
    and f: "distributive_defl f"
  shows "distributive_defl (abs oo f oo rep)"
proof (rule distributive_deflI)
  have iso: "iso abs rep" by (rule iso.intro[OF iso_abs iso_rep])
  interpret iso abs rep by (fact iso)
  show "deflation (abs oo f oo rep)"
    by (rule deflation_abs_rep[OF abs_iso rep_iso distributive_defl.deflation[OF f]])
  fix a b c :: 't assume ab: "a \<Up> b"
  let ?c = "(abs oo f oo rep)\<cdot>c"
  have rc: "rep\<cdot>?c = f\<cdot>(rep\<cdot>c)" by simp
  have cab: "?c \<sqinter> a \<Up> ?c \<sqinter> b" by (rule joinableI[OF meet_below1 meet_below1])
  have "rep\<cdot>(?c \<sqinter> (a \<squnion> b)) = f\<cdot>(rep\<cdot>c) \<sqinter> (rep\<cdot>a \<squnion> rep\<cdot>b)"
    by (simp only: iso_rep_meet[OF iso] iso_rep_join[OF iso ab] rc)
  also have "\<dots> = f\<cdot>(rep\<cdot>c) \<sqinter> rep\<cdot>a \<squnion> f\<cdot>(rep\<cdot>c) \<sqinter> rep\<cdot>b"
    using ab by (simp add: distributive_defl.distrib_image[OF f] iso_rep_joinable_iff[OF iso])
  also have "\<dots> = rep\<cdot>(?c \<sqinter> a \<squnion> ?c \<sqinter> b)"
    by (simp only: iso_rep_meet[OF iso] iso_rep_join[OF iso cab] rc)
  finally show "?c \<sqinter> (a \<squnion> b) = ?c \<sqinter> a \<squnion> ?c \<sqinter> b" by (simp only: rep_eq)
qed

lemma distributive_defl_u_map:
  assumes f: "distributive_defl (f :: 'a::{bifinite, bounded_complete} \<rightarrow> 'a)"
  shows "distributive_defl (u_map\<cdot>f)"
proof (rule distributive_deflI)
  show "deflation (u_map\<cdot>f)" by (rule deflation_u_map[OF distributive_defl.deflation[OF f]])
  fix a b c :: "'a u" assume ab: "a \<Up> b"
  show "u_map\<cdot>f\<cdot>c \<sqinter> (a \<squnion> b) = u_map\<cdot>f\<cdot>c \<sqinter> a \<squnion> u_map\<cdot>f\<cdot>c \<sqinter> b"
  proof (cases a; cases b; cases c)
    fix a' b' c' assume *: "a = up\<cdot>a'" "b = up\<cdot>b'" "c = up\<cdot>c'"
    with ab have a'b': "a' \<Up> b'" by simp
    have "f\<cdot>c' \<sqinter> a' \<Up> f\<cdot>c' \<sqinter> b'" by (rule joinableI[OF meet_below1 meet_below1])
    with * a'b' show ?thesis by (simp add: up_join distributive_defl.distrib_image[OF f])
  qed simp_all
qed

lemma distributive_defl_ssum_map:
  assumes f: "distributive_defl (f :: 'a::{bifinite, bounded_complete} \<rightarrow> 'a)"
    and g: "distributive_defl (g :: 'b::{bifinite, bounded_complete} \<rightarrow> 'b)"
  shows "distributive_defl (ssum_map\<cdot>f\<cdot>g)"
proof (rule distributive_deflI)
  show "deflation (ssum_map\<cdot>f\<cdot>g)"
    by (rule deflation_ssum_map[OF distributive_defl.deflation[OF f] distributive_defl.deflation[OF g]])
  fix a b c :: "'a \<oplus> 'b" assume ab: "a \<Up> b"
  have ml: "x \<sqinter> x' \<Up> x \<sqinter> x''" for x x' x'' :: 'a by (rule joinableI[OF meet_below1 meet_below1])
  have mr: "y \<sqinter> y' \<Up> y \<sqinter> y''" for y y' y'' :: 'b by (rule joinableI[OF meet_below1 meet_below1])
  show "ssum_map\<cdot>f\<cdot>g\<cdot>c \<sqinter> (a \<squnion> b) = ssum_map\<cdot>f\<cdot>g\<cdot>c \<sqinter> a \<squnion> ssum_map\<cdot>f\<cdot>g\<cdot>c \<sqinter> b"
    using ab by (cases a; cases b; cases c)
      (simp_all add: sinl_join sinr_join distributive_defl.distrib_image[OF f]
        distributive_defl.distrib_image[OF g] ml mr)
qed

text \<open>Separation of both components keeps the smash product distributive, as for the class
  instance: joinable nonbottom pairs meet a third pair to \<open>\<bottom>\<close> together.\<close>

lemma distributive_defl_sprod_map:
  assumes f: "distributive_defl (f :: 'a::{bifinite, bounded_complete, filter_sum} \<rightarrow> 'a)"
    and g: "distributive_defl (g :: 'b::{bifinite, bounded_complete, filter_sum} \<rightarrow> 'b)"
  shows "distributive_defl (sprod_map\<cdot>f\<cdot>g)"
proof (rule distributive_deflI)
  show "deflation (sprod_map\<cdot>f\<cdot>g)"
    by (rule deflation_sprod_map[OF distributive_defl.deflation[OF f] distributive_defl.deflation[OF g]])
  fix a b c :: "'a \<otimes> 'b" assume "a \<Up> b"
  let ?x = "sprod_map\<cdot>f\<cdot>g\<cdot>c"
  show "?x \<sqinter> (a \<squnion> b) = ?x \<sqinter> a \<squnion> ?x \<sqinter> b"
  proof (cases "a = \<bottom> \<or> b = \<bottom> \<or> ?x = \<bottom>")
    case True then show ?thesis by (elim disjE) simp_all
  next
    case False
    then obtain a1 a2 b1 b2 c1 c2 where
      ab: "a = (:a1, a2:)" "b = (:b1, b2:)" and x: "?x = (:f\<cdot>c1, g\<cdot>c2:)" and
      nb: "a1 \<noteq> \<bottom>" "a2 \<noteq> \<bottom>" "b1 \<noteq> \<bottom>" "b2 \<noteq> \<bottom>" "f\<cdot>c1 \<noteq> \<bottom>" "g\<cdot>c2 \<noteq> \<bottom>"
      by (cases a; cases b; cases c) auto
    from \<open>a \<Up> b\<close> have j: "a1 \<Up> b1" "a2 \<Up> b2" by (simp_all add: ab nb spair_joinable_iff)
    have cong: "f\<cdot>c1 \<sqinter> a1 = \<bottom> \<longleftrightarrow> f\<cdot>c1 \<sqinter> b1 = \<bottom>" "g\<cdot>c2 \<sqinter> a2 = \<bottom> \<longleftrightarrow> g\<cdot>c2 \<sqinter> b2 = \<bottom>"
      using filter_sum_meet_bottom_cong[OF j(1) nb(1,3)] filter_sum_meet_bottom_cong[OF j(2) nb(2,4)]
        filter_sum_meet_bottom_cong[OF joinable_sym[THEN iffD1, OF j(1)] nb(3,1)]
        filter_sum_meet_bottom_cong[OF joinable_sym[THEN iffD1, OF j(2)] nb(4,2)]
      by blast+
    have mj: "x \<sqinter> y \<Up> x \<sqinter> z" for x y z :: "'c::bounded_complete"
      by (rule joinableI[OF meet_below1 meet_below1])
    have lhs: "?x \<sqinter> (a \<squnion> b) = (:f\<cdot>c1 \<sqinter> a1 \<squnion> f\<cdot>c1 \<sqinter> b1, g\<cdot>c2 \<sqinter> a2 \<squnion> g\<cdot>c2 \<sqinter> b2:)"
      by (simp only: x ab spair_join[OF nb(1,2,3,4) j] spair_meet
        distributive_defl.distrib_image[OF f j(1)] distributive_defl.distrib_image[OF g j(2)])
    have rhs: "?x \<sqinter> a \<squnion> ?x \<sqinter> b = (:f\<cdot>c1 \<sqinter> a1, g\<cdot>c2 \<sqinter> a2:) \<squnion> (:f\<cdot>c1 \<sqinter> b1, g\<cdot>c2 \<sqinter> b2:)"
      by (simp only: x ab spair_meet)
    show ?thesis
    proof (cases "f\<cdot>c1 \<sqinter> a1 = \<bottom> \<or> g\<cdot>c2 \<sqinter> a2 = \<bottom>")
      case True
      with cong show ?thesis unfolding lhs rhs by auto
    next
      case False
      with cong have "f\<cdot>c1 \<sqinter> a1 \<noteq> \<bottom>" "g\<cdot>c2 \<sqinter> a2 \<noteq> \<bottom>" "f\<cdot>c1 \<sqinter> b1 \<noteq> \<bottom>" "g\<cdot>c2 \<sqinter> b2 \<noteq> \<bottom>" by simp_all
      then show ?thesis unfolding lhs rhs by (simp add: spair_join mj)
    qed
  qed
qed

end