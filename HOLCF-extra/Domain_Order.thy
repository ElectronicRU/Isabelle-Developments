theory Domain_Order
  imports Separated
begin

section \<open>Order structure of domain-package types\<close>

text \<open>The domain package presents each domain as isomorphic, through \<open>abs\<close> and \<open>rep\<close> satisfying
  the laws of @{locale iso}, to a combination of its constructor arguments.  An isomorphism of
  pointed cpos is an order isomorphism, so it preserves bounds, lubs and meets.

  For recursive domains the order classes are derived from the map functional: each class
  property is stated for the image of a deflation (a locale over @{locale deflation}), pushed
  through \<open>ssum_map\<close>, \<open>sprod_map\<close>, \<open>u_map\<close> and the \<open>abs\<close>/\<open>rep\<close> isomorphism, and established for
  \<open>T_map\<cdot>v\<close> by fixed-point induction; at \<open>v = ID\<close> this gives the instance.\<close>

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

text \<open>Fixed-point induction where the step may also use that the iterate lies below the fixed
  point.  With an antitone predicate @{term Q} this transfers @{term "Q (fix\<cdot>F)"}, proved
  beforehand, to every iterate, so @{term Q} need not be carried through the induction.\<close>

lemma fix_preserves_below:
  fixes G :: "('a::pcpo \<rightarrow> 'a) \<Rightarrow> 'a \<rightarrow> 'a"
  assumes cont: "cont G" and adm: "adm P" and bot: "P \<bottom>"
    and step: "\<And>f. f \<sqsubseteq> fix\<cdot>(\<Lambda> f. G f) \<Longrightarrow> P f \<Longrightarrow> P (G f)"
  shows "P (fix\<cdot>(\<Lambda> f. G f))"
proof -
  let ?F = "\<Lambda> f. G f"
  have fx: "fix\<cdot>?F = G (fix\<cdot>?F)" by (subst fix_eq) (simp add: cont)
  have "P (fix\<cdot>?F) \<and> fix\<cdot>?F \<sqsubseteq> fix\<cdot>?F"
  proof (rule fix_preserves[where P="\<lambda>f. P f \<and> f \<sqsubseteq> fix\<cdot>?F"])
    show "adm (\<lambda>f. P f \<and> f \<sqsubseteq> fix\<cdot>?F)" by (rule adm_conj[OF adm], simp)
    show "P \<bottom> \<and> \<bottom> \<sqsubseteq> fix\<cdot>?F" using bot by simp
    show "preserves (\<lambda>f. P f \<and> f \<sqsubseteq> fix\<cdot>?F) ?F"
    proof (rule preserves_LAM[OF cont])
      fix f assume f: "P f \<and> f \<sqsubseteq> fix\<cdot>?F"
      have "G f \<sqsubseteq> G (fix\<cdot>?F)" using f by (intro monofunE[OF cont2mono[OF cont]]) simp
      then have "G f \<sqsubseteq> fix\<cdot>?F" by (simp only: fx[symmetric])
      with f step show "P (G f) \<and> G f \<sqsubseteq> fix\<cdot>?F" by simp
    qed
  qed
  then show ?thesis ..
qed

section \<open>Order predicates as deflation locales\<close>

text \<open>The class properties, relativised to the image of a deflation.  Bundling @{const deflation}
  into every predicate keeps the connective rules uniform: the deflation part rides along through
  the HOLCF @{text "deflation_*_map"} lemmas inside each connective rule, and admissibility gains
  @{thm [source] adm_deflation}.  The image of a chain's lub is approximated by the images of
  its members, which gives admissibility of the order predicates.\<close>

locale bounded_complete_defl = deflation d for d :: "'a::bifinite \<rightarrow> 'a" +
  assumes pair_lubs: "d\<cdot>a \<sqsubseteq> c \<Longrightarrow> d\<cdot>b \<sqsubseteq> c \<Longrightarrow> \<exists>z. {d\<cdot>a, d\<cdot>b} <<| z"

locale separated_defl = deflation d for d :: "'a::bifinite \<rightarrow> 'a" +
  assumes separated_image:
    "d\<cdot>x \<noteq> \<bottom> \<Longrightarrow> d\<cdot>y \<noteq> \<bottom> \<Longrightarrow> d\<cdot>x \<sqsubseteq> u \<Longrightarrow> d\<cdot>y \<sqsubseteq> u \<Longrightarrow> \<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> d\<cdot>x \<and> l \<sqsubseteq> d\<cdot>y"

lemma (in bounded_complete_defl) deflation: "deflation d" by (fact deflation_axioms)

lemma (in separated_defl) deflation: "deflation d" by (fact deflation_axioms)

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

lemma separated_deflI:
  "deflation d \<Longrightarrow> (\<And>x y u. d\<cdot>x \<noteq> \<bottom> \<Longrightarrow> d\<cdot>y \<noteq> \<bottom> \<Longrightarrow> d\<cdot>x \<sqsubseteq> u \<Longrightarrow> d\<cdot>y \<sqsubseteq> u \<Longrightarrow>
    \<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> d\<cdot>x \<and> l \<sqsubseteq> d\<cdot>y) \<Longrightarrow> separated_defl d"
  by (simp add: separated_defl_def separated_defl_axioms_def)

lemma separated_deflE:
  assumes "separated_defl f" "f\<cdot>x \<noteq> \<bottom>" "f\<cdot>y \<noteq> \<bottom>" "f\<cdot>x \<sqsubseteq> u" "f\<cdot>y \<sqsubseteq> u"
  obtains l where "l \<noteq> \<bottom>" "l \<sqsubseteq> f\<cdot>x" "l \<sqsubseteq> f\<cdot>y"
  using separated_defl.separated_image[OF assms] by blast

lemma separated_defl_bottom: "separated_defl (\<bottom> :: 'a::bifinite \<rightarrow> 'a)"
  by (rule separated_deflI[OF deflation_bottom]) simp

lemma separated_defl_ID: "separated_defl (ID :: 'a::{bifinite, separated_po} \<rightarrow> 'a)"
  by (rule separated_deflI[OF deflation_ID]) (simp add: separated_pcpo)

text \<open>Lifting separates unconditionally: only the deflation property of @{term f} is needed.\<close>

lemma separated_defl_u_map:
  assumes f: "deflation (f :: 'a::bifinite \<rightarrow> 'a)" shows "separated_defl (u_map\<cdot>f)"
proof (rule separated_deflI[OF deflation_u_map[OF f]])
  fix x y u :: "'a\<^sub>\<bottom>" assume "u_map\<cdot>f\<cdot>x \<noteq> \<bottom>" "u_map\<cdot>f\<cdot>y \<noteq> \<bottom>"
  then obtain x' y' where "x = up\<cdot>x'" "y = up\<cdot>y'" by (cases x; cases y) auto
  then have "up\<cdot>\<bottom> \<noteq> \<bottom> \<and> up\<cdot>\<bottom> \<sqsubseteq> u_map\<cdot>f\<cdot>x \<and> up\<cdot>\<bottom> \<sqsubseteq> u_map\<cdot>f\<cdot>y" by simp
  then show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> u_map\<cdot>f\<cdot>x \<and> l \<sqsubseteq> u_map\<cdot>f\<cdot>y" ..
qed

lemma separated_defl_ssum_map:
  assumes f: "separated_defl f" and g: "separated_defl g"
  shows "separated_defl (ssum_map\<cdot>f\<cdot>g)"
proof (rule separated_deflI)
  show "deflation (ssum_map\<cdot>f\<cdot>g)"
    by (rule deflation_ssum_map[OF separated_defl.axioms(1)[OF f] separated_defl.axioms(1)[OF g]])
  fix x y u
  assume A: "ssum_map\<cdot>f\<cdot>g\<cdot>x \<noteq> \<bottom>" and B: "ssum_map\<cdot>f\<cdot>g\<cdot>y \<noteq> \<bottom>"
    and xu: "ssum_map\<cdot>f\<cdot>g\<cdot>x \<sqsubseteq> u" and yu: "ssum_map\<cdot>f\<cdot>g\<cdot>y \<sqsubseteq> u"
  show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> ssum_map\<cdot>f\<cdot>g\<cdot>x \<and> l \<sqsubseteq> ssum_map\<cdot>f\<cdot>g\<cdot>y"
  proof (cases x)
    case bottom with A show ?thesis by simp
  next
    case (sinl x')
    with A have fx: "f\<cdot>x' \<noteq> \<bottom>" by simp
    with sinl xu obtain u' where u: "u = sinl\<cdot>u'" "f\<cdot>x' \<sqsubseteq> u'" by (cases u) auto
    with B yu obtain y' where y': "y = sinl\<cdot>y'" "y' \<noteq> \<bottom>" "f\<cdot>y' \<noteq> \<bottom>" "f\<cdot>y' \<sqsubseteq> u'"
      by (cases y) auto
    from f fx \<open>f\<cdot>y' \<noteq> \<bottom>\<close> \<open>f\<cdot>x' \<sqsubseteq> u'\<close> \<open>f\<cdot>y' \<sqsubseteq> u'\<close> obtain l where "l \<noteq> \<bottom>" "l \<sqsubseteq> f\<cdot>x'" "l \<sqsubseteq> f\<cdot>y'"
      by (rule separated_deflE)
    with sinl y' show ?thesis by (intro exI[of _ "sinl\<cdot>l"]) simp
  next
    case (sinr x')
    with A have gx: "g\<cdot>x' \<noteq> \<bottom>" by simp
    with sinr xu obtain u' where u: "u = sinr\<cdot>u'" "g\<cdot>x' \<sqsubseteq> u'" by (cases u) auto
    with B yu obtain y' where y': "y = sinr\<cdot>y'" "y' \<noteq> \<bottom>" "g\<cdot>y' \<noteq> \<bottom>" "g\<cdot>y' \<sqsubseteq> u'"
      by (cases y) auto
    from g gx \<open>g\<cdot>y' \<noteq> \<bottom>\<close> \<open>g\<cdot>x' \<sqsubseteq> u'\<close> \<open>g\<cdot>y' \<sqsubseteq> u'\<close> obtain l where "l \<noteq> \<bottom>" "l \<sqsubseteq> g\<cdot>x'" "l \<sqsubseteq> g\<cdot>y'"
      by (rule separated_deflE)
    with sinr y' show ?thesis by (intro exI[of _ "sinr\<cdot>l"]) simp
  qed
qed

lemma separated_defl_sprod_map:
  assumes f: "separated_defl f" and g: "separated_defl g"
  shows "separated_defl (sprod_map\<cdot>f\<cdot>g)"
proof (rule separated_deflI)
  show "deflation (sprod_map\<cdot>f\<cdot>g)"
    by (rule deflation_sprod_map[OF separated_defl.axioms(1)[OF f] separated_defl.axioms(1)[OF g]])
  fix x y u
  assume A: "sprod_map\<cdot>f\<cdot>g\<cdot>x \<noteq> \<bottom>" and B: "sprod_map\<cdot>f\<cdot>g\<cdot>y \<noteq> \<bottom>"
    and xu: "sprod_map\<cdot>f\<cdot>g\<cdot>x \<sqsubseteq> u" and yu: "sprod_map\<cdot>f\<cdot>g\<cdot>y \<sqsubseteq> u"
  obtain x1 x2 where x: "x = (:x1, x2:)" "x1 \<noteq> \<bottom>" "x2 \<noteq> \<bottom>" using A by (cases x) auto
  obtain y1 y2 where y: "y = (:y1, y2:)" "y1 \<noteq> \<bottom>" "y2 \<noteq> \<bottom>" using B by (cases y) auto
  from A x have fx: "f\<cdot>x1 \<noteq> \<bottom>" "g\<cdot>x2 \<noteq> \<bottom>" by simp_all
  from B y have fy: "f\<cdot>y1 \<noteq> \<bottom>" "g\<cdot>y2 \<noteq> \<bottom>" by simp_all
  from xu x fx have xu': "f\<cdot>x1 \<sqsubseteq> sfst\<cdot>u" "g\<cdot>x2 \<sqsubseteq> ssnd\<cdot>u" by (simp_all add: below_sprod)
  from yu y fy have yu': "f\<cdot>y1 \<sqsubseteq> sfst\<cdot>u" "g\<cdot>y2 \<sqsubseteq> ssnd\<cdot>u" by (simp_all add: below_sprod)
  from f fx(1) fy(1) xu'(1) yu'(1) obtain l1 where "l1 \<noteq> \<bottom>" "l1 \<sqsubseteq> f\<cdot>x1" "l1 \<sqsubseteq> f\<cdot>y1"
    by (rule separated_deflE)
  moreover from g fx(2) fy(2) xu'(2) yu'(2) obtain l2 where "l2 \<noteq> \<bottom>" "l2 \<sqsubseteq> g\<cdot>x2" "l2 \<sqsubseteq> g\<cdot>y2"
    by (rule separated_deflE)
  ultimately show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> sprod_map\<cdot>f\<cdot>g\<cdot>x \<and> l \<sqsubseteq> sprod_map\<cdot>f\<cdot>g\<cdot>y"
    using x y fx fy by (intro exI[of _ "(:l1, l2:)"]) (simp add: below_sprod)
qed

lemma separated_defl_iso:
  fixes abs :: "'r::bifinite \<rightarrow> 't::bifinite" and rep
  assumes iso_abs: "\<And>x. rep\<cdot>(abs\<cdot>x) = x" and iso_rep: "\<And>y. abs\<cdot>(rep\<cdot>y) = y"
    and f: "separated_defl f"
  shows "separated_defl (abs oo f oo rep)"
proof (rule separated_deflI)
  interpret iso abs rep by (rule iso.intro[OF iso_abs iso_rep])
  show "deflation (abs oo f oo rep)"
    by (rule deflation_abs_rep[OF abs_iso rep_iso separated_defl.axioms(1)[OF f]])
  fix x y u
  assume "(abs oo f oo rep)\<cdot>x \<noteq> \<bottom>" "(abs oo f oo rep)\<cdot>y \<noteq> \<bottom>"
    "(abs oo f oo rep)\<cdot>x \<sqsubseteq> u" "(abs oo f oo rep)\<cdot>y \<sqsubseteq> u"
  then have "f\<cdot>(rep\<cdot>x) \<noteq> \<bottom>" "f\<cdot>(rep\<cdot>y) \<noteq> \<bottom>" "f\<cdot>(rep\<cdot>x) \<sqsubseteq> rep\<cdot>u" "f\<cdot>(rep\<cdot>y) \<sqsubseteq> rep\<cdot>u"
    by (simp_all add: abs_below[symmetric] abs_bottom_iff)
  with f obtain l where "l \<noteq> \<bottom>" "l \<sqsubseteq> f\<cdot>(rep\<cdot>x)" "l \<sqsubseteq> f\<cdot>(rep\<cdot>y)" by (elim separated_deflE)
  then show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> (abs oo f oo rep)\<cdot>x \<and> l \<sqsubseteq> (abs oo f oo rep)\<cdot>y"
    by (intro exI[of _ "abs\<cdot>l"]) (simp add: abs_below[symmetric] abs_bottom_iff)
qed

lemma adm_separated_defl: "adm (separated_defl :: ('a::bifinite \<rightarrow> 'a) \<Rightarrow> bool)"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'a" assume Y: "chain Y" and P: "\<forall>i. separated_defl (Y i)"
  have chx: "chain (\<lambda>n. Y n\<cdot>x)" for x by (rule ch2ch_Rep_cfunL[OF Y])
  have reach: "(\<Squnion>n. Y n\<cdot>x) = (\<Squnion>i. Y i)\<cdot>x" for x by (rule contlub_cfun_fun[OF Y, symmetric])
  have below: "Y n\<cdot>x \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x" for n x
    using is_ub_thelub[OF chx, of n x] by (simp only: reach)
  show "separated_defl (\<Squnion>i. Y i)"
  proof (rule separated_deflI)
    show "deflation (\<Squnion>i. Y i)"
      by (rule admD[OF adm_deflation Y]) (rule separated_defl.axioms(1)[OF P[rule_format]])
    fix x y u assume nx: "(\<Squnion>i. Y i)\<cdot>x \<noteq> \<bottom>" and ny: "(\<Squnion>i. Y i)\<cdot>y \<noteq> \<bottom>"
      and xu: "(\<Squnion>i. Y i)\<cdot>x \<sqsubseteq> u" and yu: "(\<Squnion>i. Y i)\<cdot>y \<sqsubseteq> u"
    from nx obtain n where n: "Y n\<cdot>x \<noteq> \<bottom>"
      by (auto simp: reach[symmetric] lub_eq_bottom_iff[OF chx])
    from ny obtain m where m: "Y m\<cdot>y \<noteq> \<bottom>"
      by (auto simp: reach[symmetric] lub_eq_bottom_iff[OF chx])
    define k where "k = max n m"
    have "Y n\<cdot>x \<sqsubseteq> Y k\<cdot>x" "Y m\<cdot>y \<sqsubseteq> Y k\<cdot>y"
      unfolding k_def by (simp_all add: chain_mono[OF chx])
    with n m have kx: "Y k\<cdot>x \<noteq> \<bottom>" and ky: "Y k\<cdot>y \<noteq> \<bottom>" by auto
    have "Y k\<cdot>x \<sqsubseteq> u" "Y k\<cdot>y \<sqsubseteq> u"
      using below_trans[OF below xu] below_trans[OF below yu] .
    with P[rule_format, of k] kx ky obtain l where "l \<noteq> \<bottom>" "l \<sqsubseteq> Y k\<cdot>x" "l \<sqsubseteq> Y k\<cdot>y"
      by (elim separated_deflE)
    then show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x \<and> l \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>y"
      using below_trans[OF _ below[of k x]] below_trans[OF _ below[of k y]] by blast
  qed
qed

lemma separated_defl_below:
  assumes le: "d \<sqsubseteq> e" and e: "separated_defl e" and d: "deflation d"
  shows "separated_defl d"
proof (rule separated_deflI[OF d])
  have de: "deflation e" by (rule separated_defl.axioms(1)[OF e])
  fix x y u assume "d\<cdot>x \<noteq> \<bottom>" "d\<cdot>y \<noteq> \<bottom>" "d\<cdot>x \<sqsubseteq> u" "d\<cdot>y \<sqsubseteq> u"
  moreover have "e\<cdot>(d\<cdot>x) = d\<cdot>x" "e\<cdot>(d\<cdot>y) = d\<cdot>y" by (rule deflation_below_comp2[OF d de le])+
  ultimately show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> d\<cdot>x \<and> l \<sqsubseteq> d\<cdot>y"
    using separated_defl.separated_image[OF e, of "d\<cdot>x" "d\<cdot>y" u] by simp
qed

lemma separated_po_class_deflI:
  assumes d: "separated_defl (ID :: 'a::bifinite \<rightarrow> 'a)"
  shows "OFCLASS('a, separated_po_class)"
proof (rule separated_poI)
  fix x y u :: 'a
  assume "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" "x \<sqsubseteq> u" "y \<sqsubseteq> u"
  then have "ID\<cdot>x \<noteq> \<bottom>" "ID\<cdot>y \<noteq> \<bottom>" "ID\<cdot>x \<sqsubseteq> u" "ID\<cdot>y \<sqsubseteq> u" by simp_all
  with d obtain l where "l \<noteq> \<bottom>" "l \<sqsubseteq> ID\<cdot>x" "l \<sqsubseteq> ID\<cdot>y" by (elim separated_deflE)
  then show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y" by auto
qed


subsection \<open>Downward-closed images\<close>

text \<open>A deflation with downward-closed image (its fixed points form a stable subdomain).  For
  deflations this is the stability needed for distributivity: it implies preservation of
  existing binary meets.  Unlike the predicates above it is not antitone among deflations, but
  it is admissible on algebraic types (port of \<open>Subdomain.adm_dc_defl\<close>).\<close>

locale downclosed_defl = deflation d for d :: "'a::bifinite \<rightarrow> 'a" +
  assumes downclosed: "d\<cdot>y = y \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> d\<cdot>x = x"

lemma (in downclosed_defl) deflation: "deflation d" by (fact deflation_axioms)

lemma downclosed_deflI:
  "deflation d \<Longrightarrow> (\<And>x y. d\<cdot>y = y \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> d\<cdot>x = x) \<Longrightarrow> downclosed_defl d"
  by (simp add: downclosed_defl_def downclosed_defl_axioms_def)

lemma deflation_lub_fixed:
  assumes d: "deflation d" and T: "T \<subseteq> {x. d\<cdot>x = x}" and lub: "T <<| t"
  shows "d\<cdot>t = t"
proof -
  interpret deflation d by (rule d)
  have "T <| d\<cdot>t"
  proof (rule is_ubI)
    fix x assume x: "x \<in> T"
    with T have "d\<cdot>x = x" by auto
    moreover from is_lubD1[OF lub] x have "x \<sqsubseteq> t" by (rule is_ubD)
    then have "d\<cdot>x \<sqsubseteq> d\<cdot>t" by (rule monofun_cfun_arg)
    ultimately show "x \<sqsubseteq> d\<cdot>t" by simp
  qed
  from is_lubD2[OF lub this] have "t \<sqsubseteq> d\<cdot>t" .
  with below show "d\<cdot>t = t" by (rule below_antisym)
qed

lemma downclosed_defl_bottom: "downclosed_defl (\<bottom> :: 'a::bifinite \<rightarrow> 'a)"
  by (rule downclosed_deflI[OF deflation_bottom]) simp

lemma downclosed_defl_ID: "downclosed_defl (ID :: 'a::bifinite \<rightarrow> 'a)"
  by (rule downclosed_deflI[OF deflation_ID]) simp

lemma adm_downclosed_defl: "adm (downclosed_defl :: ('a::bifinite \<rightarrow> 'a) \<Rightarrow> bool)"
proof (rule admI)
  fix D :: "nat \<Rightarrow> 'a \<rightarrow> 'a"
  assume chain: "chain D" and H: "\<forall>i. downclosed_defl (D i)"
  have Hd: "deflation (D i)" for i by (rule downclosed_defl.axioms(1)[OF H[rule_format]])
  have defl: "deflation (\<Squnion>i. D i)" by (rule admD[OF adm_deflation chain Hd])
  show "downclosed_defl (\<Squnion>i. D i)"
  proof (rule downclosed_deflI[OF defl])
    fix x y assume fy: "(\<Squnion>i. D i)\<cdot>y = y" and xy: "x \<sqsubseteq> y"
    obtain C where C: "chain C" "\<forall>i. compact (C i)" "x = (\<Squnion>i. C i)"
      by (rule obtain_compact_chain)
    have fixed: "(\<Squnion>i. D i)\<cdot>(C i) = C i" for i
    proof -
      have "C i \<sqsubseteq> x" using is_ub_thelub[OF C(1)] C(3) by simp
      then have "C i \<sqsubseteq> y" using xy by (rule below_trans)
      then have "C i \<sqsubseteq> (\<Squnion>i. D i)\<cdot>y" using fy by simp
      also have "\<dots> = (\<Squnion>j. D j\<cdot>y)" by (rule contlub_cfun_fun[OF chain])
      finally have Cilub: "C i \<sqsubseteq> (\<Squnion>j. D j\<cdot>y)" .
      have chy: "chain (\<lambda>j. D j\<cdot>y)" by (rule ch2ch_Rep_cfunL[OF chain])
      from compactD2[OF C(2)[rule_format] chy Cilub] obtain j where j: "C i \<sqsubseteq> D j\<cdot>y" by blast
      have idem: "D j\<cdot>(D j\<cdot>y) = D j\<cdot>y" by (rule deflation.idem[OF Hd])
      have CiFix: "D j\<cdot>(C i) = C i"
        by (rule downclosed_defl.downclosed[OF H[rule_format] idem j])
      have "D j \<sqsubseteq> (\<Squnion>i. D i)" by (rule is_ub_thelub[OF chain])
      then have "D j\<cdot>(C i) \<sqsubseteq> (\<Squnion>i. D i)\<cdot>(C i)" by (rule monofun_cfun_fun)
      with CiFix have "C i \<sqsubseteq> (\<Squnion>i. D i)\<cdot>(C i)" by simp
      then show ?thesis by (rule below_antisym[OF deflation.below[OF defl]])
    qed
    have rcx: "range C <<| x" using cpo_lubI[OF C(1)] C(3) by simp
    have "range C \<subseteq> {z. (\<Squnion>i. D i)\<cdot>z = z}" using fixed by auto
    from deflation_lub_fixed[OF defl this rcx] show "(\<Squnion>i. D i)\<cdot>x = x" .
  qed
qed

lemma downclosed_defl_u_map:
  assumes f: "downclosed_defl (f :: 'a::bifinite \<rightarrow> 'a)"
  shows "downclosed_defl (u_map\<cdot>f)"
proof (rule downclosed_deflI)
  have fd: "deflation f" by (rule downclosed_defl.axioms(1)[OF f])
  then show "deflation (u_map\<cdot>f)" by (rule deflation_u_map)
  fix x y assume fy: "u_map\<cdot>f\<cdot>y = y" and xy: "x \<sqsubseteq> y"
  show "u_map\<cdot>f\<cdot>x = x"
  proof (cases x)
    case bottom then show ?thesis by simp
  next
    case (up x')
    with xy obtain y' where y: "y = up\<cdot>y'" "x' \<sqsubseteq> y'" by (cases y) auto
    with fy have "f\<cdot>y' = y'" by simp
    from downclosed_defl.downclosed[OF f this \<open>x' \<sqsubseteq> y'\<close>] up show ?thesis by simp
  qed
qed

lemma downclosed_defl_ssum_map:
  assumes f: "downclosed_defl f" and g: "downclosed_defl g"
  shows "downclosed_defl (ssum_map\<cdot>f\<cdot>g)"
proof (rule downclosed_deflI)
  show "deflation (ssum_map\<cdot>f\<cdot>g)"
    by (rule deflation_ssum_map[OF downclosed_defl.axioms(1)[OF f] downclosed_defl.axioms(1)[OF g]])
  fix x y assume fy: "ssum_map\<cdot>f\<cdot>g\<cdot>y = y" and xy: "x \<sqsubseteq> y"
  show "ssum_map\<cdot>f\<cdot>g\<cdot>x = x"
  proof (cases x)
    case bottom then show ?thesis by simp
  next
    case (sinl x')
    with xy obtain y' where y: "y = sinl\<cdot>y'" "y' \<noteq> \<bottom>" "x' \<sqsubseteq> y'" by (cases y) auto
    with fy have "f\<cdot>y' = y'" by simp
    from downclosed_defl.downclosed[OF f this \<open>x' \<sqsubseteq> y'\<close>] sinl show ?thesis by simp
  next
    case (sinr x')
    with xy obtain y' where y: "y = sinr\<cdot>y'" "y' \<noteq> \<bottom>" "x' \<sqsubseteq> y'" by (cases y) auto
    with fy have "g\<cdot>y' = y'" by simp
    from downclosed_defl.downclosed[OF g this \<open>x' \<sqsubseteq> y'\<close>] sinr show ?thesis by simp
  qed
qed

lemma downclosed_defl_sprod_map:
  assumes f: "downclosed_defl f" and g: "downclosed_defl g"
  shows "downclosed_defl (sprod_map\<cdot>f\<cdot>g)"
proof (rule downclosed_deflI)
  show "deflation (sprod_map\<cdot>f\<cdot>g)"
    by (rule deflation_sprod_map[OF downclosed_defl.axioms(1)[OF f] downclosed_defl.axioms(1)[OF g]])
  fix x y assume fy: "sprod_map\<cdot>f\<cdot>g\<cdot>y = y" and xy: "x \<sqsubseteq> y"
  show "sprod_map\<cdot>f\<cdot>g\<cdot>x = x"
  proof (cases x)
    case bottom then show ?thesis by simp
  next
    case (spair a b)
    with xy obtain c e where y: "y = (:c, e:)" "c \<noteq> \<bottom>" "e \<noteq> \<bottom>" "a \<sqsubseteq> c" "b \<sqsubseteq> e"
      by (cases y) (auto simp: spair_below_iff)
    with fy have "f\<cdot>c = c" "g\<cdot>e = e" by (auto simp: spair_eq_iff)
    with downclosed_defl.downclosed[OF f] downclosed_defl.downclosed[OF g] y spair
    have "f\<cdot>a = a" "g\<cdot>b = b" by blast+
    with spair show ?thesis by simp
  qed
qed

lemma downclosed_defl_iso:
  fixes abs :: "'r::bifinite \<rightarrow> 't::bifinite" and rep
  assumes iso_abs: "\<And>x. rep\<cdot>(abs\<cdot>x) = x" and iso_rep: "\<And>y. abs\<cdot>(rep\<cdot>y) = y"
    and f: "downclosed_defl f"
  shows "downclosed_defl (abs oo f oo rep)"
proof (rule downclosed_deflI)
  interpret iso abs rep by (rule iso.intro[OF iso_abs iso_rep])
  show "deflation (abs oo f oo rep)"
    by (rule deflation_abs_rep[OF abs_iso rep_iso downclosed_defl.axioms(1)[OF f]])
  fix x y assume fy: "(abs oo f oo rep)\<cdot>y = y" and xy: "x \<sqsubseteq> y"
  from fy have "rep\<cdot>(abs\<cdot>(f\<cdot>(rep\<cdot>y))) = rep\<cdot>y" by simp
  then have "f\<cdot>(rep\<cdot>y) = rep\<cdot>y" by simp
  moreover from xy have "rep\<cdot>x \<sqsubseteq> rep\<cdot>y" by (rule monofun_cfun_arg)
  ultimately have "f\<cdot>(rep\<cdot>x) = rep\<cdot>x" by (rule downclosed_defl.downclosed[OF f])
  then show "(abs oo f oo rep)\<cdot>x = x" by simp
qed

text \<open>Every lower bound of an image element lies in the image; hence the deflation commutes with
  existing binary meets.\<close>

lemma (in downclosed_defl) lower_fixed: "l \<sqsubseteq> d\<cdot>x \<Longrightarrow> d\<cdot>l = l"
  by (rule downclosed[OF idem])

lemma (in downclosed_defl) glb_fixed:
  assumes m: "is_glb {x, y} m"
  shows "is_glb {d\<cdot>x, d\<cdot>y} (d\<cdot>m)"
proof (rule is_glbI)
  fix z assume "z \<in> {d\<cdot>x, d\<cdot>y}"
  moreover have "m \<sqsubseteq> x" "m \<sqsubseteq> y" using m by (auto intro: is_glb_below)
  ultimately show "d\<cdot>m \<sqsubseteq> z" by (auto intro: monofun_cfun_arg)
next
  fix l assume "\<forall>z\<in>{d\<cdot>x, d\<cdot>y}. l \<sqsubseteq> z"
  then have lx: "l \<sqsubseteq> d\<cdot>x" and ly: "l \<sqsubseteq> d\<cdot>y" by simp_all
  have fix_l: "d\<cdot>l = l" using lx by (rule lower_fixed)
  have "l \<sqsubseteq> x" using lx below by (rule below_trans)
  moreover have "l \<sqsubseteq> y" using ly below by (rule below_trans)
  ultimately have "l \<sqsubseteq> m" using m by (auto intro: is_glb_greatest)
  then have "d\<cdot>l \<sqsubseteq> d\<cdot>m" by (rule monofun_cfun_arg)
  with fix_l show "l \<sqsubseteq> d\<cdot>m" by simp
qed

text \<open>Below an image element, meeting with @{term z} or with its image is the same.\<close>

lemma (in downclosed_defl) glb_relative:
  assumes m: "is_glb {d\<cdot>c, d\<cdot>z} m"
  shows "is_glb {d\<cdot>c, z} m"
proof (rule is_glbI)
  fix w assume "w \<in> {d\<cdot>c, z}"
  moreover have "m \<sqsubseteq> d\<cdot>c" "m \<sqsubseteq> d\<cdot>z" using m by (auto intro: is_glb_below)
  ultimately show "m \<sqsubseteq> w" using below[of z] by (auto intro: below_trans)
next
  fix l assume "\<forall>w\<in>{d\<cdot>c, z}. l \<sqsubseteq> w"
  then have lc: "l \<sqsubseteq> d\<cdot>c" and lz: "l \<sqsubseteq> z" by simp_all
  have "d\<cdot>l = l" using lc by (rule lower_fixed)
  moreover from lz have "d\<cdot>l \<sqsubseteq> d\<cdot>z" by (rule monofun_cfun_arg)
  ultimately have "l \<sqsubseteq> d\<cdot>z" by simp
  with lc show "l \<sqsubseteq> m" using m by (auto intro: is_glb_greatest)
qed


subsection \<open>Meets in the image\<close>

text \<open>Pair lubs in the image extend to finite, and then (via the directed set of finite joins)
  to arbitrary bounded subsets of the image.  An existing lub of fixed points is itself fixed
  (@{thm [source] deflation_lub_fixed}), so the induction need not track the image.\<close>

lemma (in bounded_complete_defl) finite_lubs:
  assumes "finite B" "B \<subseteq> {x. d\<cdot>x = x}" "B <| c"
  shows "B <<| lub B"
  using assms
proof (induct B rule: finite_induct)
  case empty
  have bot: "{} <<| (\<bottom> :: 'a)" by (rule is_lubI) (auto intro: is_ubI)
  then have "lub {} = (\<bottom> :: 'a)" by (rule lub_eqI)
  with bot show ?case by simp
next
  case (insert x B)
  from insert.prems have xF: "d\<cdot>x = x" and BF: "B \<subseteq> {x. d\<cdot>x = x}" by auto
  from insert.prems have xc: "x \<sqsubseteq> c" and Bc: "B <| c" by (auto intro: is_ubI dest: is_ubD)
  from insert.hyps(3)[OF BF Bc] have IH: "B <<| lub B" .
  have zF: "d\<cdot>(lub B) = lub B" by (rule deflation_lub_fixed[OF deflation_axioms BF IH])
  have zc: "lub B \<sqsubseteq> c" using Bc by (rule is_lubD2[OF IH])
  from pair_lubs[of x c "lub B"] xF zF xc zc obtain w where w: "{x, lub B} <<| w" by auto
  have "insert x B <<| w"
  proof (rule is_lubI)
    have "x \<sqsubseteq> w" "lub B \<sqsubseteq> w" using w by (auto dest: is_lubD1 is_ubD)
    moreover have "y \<sqsubseteq> lub B" if "y \<in> B" for y using IH that by (auto dest: is_lubD1 is_ubD)
    ultimately show "insert x B <| w" by (auto intro!: is_ubI intro: below_trans)
  next
    fix u assume "insert x B <| u"
    then have "x \<sqsubseteq> u" "B <| u" by (auto intro: is_ubI dest: is_ubD)
    then have "{x, lub B} <| u" using is_lubD2[OF IH] by (auto intro!: is_ubI)
    then show "w \<sqsubseteq> u" by (rule is_lubD2[OF w])
  qed
  then show ?case by (simp add: lub_eqI)
qed

lemma (in bounded_complete_defl) bounded_lub:
  assumes A: "A \<subseteq> {x. d\<cdot>x = x}" and c: "A <| c"
  shows "\<exists>z. A <<| z"
proof -
  have "B <<| lub B" if "B \<in> Fpow A" for B
  proof -
    from that have "finite B" "B \<subseteq> A" by (simp_all add: Fpow_def)
    moreover from \<open>B \<subseteq> A\<close> c have "B <| c" by (auto intro: is_ubI dest: is_ubD)
    ultimately show ?thesis using A by (blast intro: finite_lubs)
  qed
  then have "A <<| lub (lub ` Fpow A)" by (rule lub_lub)
  then show ?thesis ..
qed

text \<open>With downward closure every lower bound of an image element lies in the image, so the lub
  of all common lower bounds of an image element and an arbitrary element exists and is their
  meet, in the whole type.\<close>

lemma image_meet_exists:
  assumes bc: "bounded_complete_defl d" and dc: "downclosed_defl d"
  shows "\<exists>m. is_glb {d\<cdot>a, z} m \<and> d\<cdot>m = m"
proof -
  interpret bounded_complete_defl d by (fact bc)
  interpret dc: downclosed_defl d by (fact dc)
  define L where "L = {l. l \<sqsubseteq> d\<cdot>a \<and> l \<sqsubseteq> z}"
  have LF: "L \<subseteq> {x. d\<cdot>x = x}" unfolding L_def by (auto intro: dc.lower_fixed)
  have La: "L <| d\<cdot>a" and Lz: "L <| z" unfolding L_def by (auto intro: is_ubI)
  from bounded_lub[OF LF La] obtain m where m: "L <<| m" by blast
  have "is_glb {d\<cdot>a, z} m"
  proof (rule is_glbI)
    fix w assume "w \<in> {d\<cdot>a, z}"
    with La Lz show "m \<sqsubseteq> w" by (auto intro: is_lubD2[OF m])
  next
    fix l assume "\<forall>w\<in>{d\<cdot>a, z}. l \<sqsubseteq> w"
    then have "l \<in> L" unfolding L_def by simp
    with m show "l \<sqsubseteq> m" by (auto dest: is_lubD1 is_ubD)
  qed
  moreover have "d\<cdot>m = m" by (rule deflation_lub_fixed[OF deflation_axioms LF m])
  ultimately show ?thesis by blast
qed

subsection \<open>Distributivity\<close>

text \<open>The distributive law, relationally, with only the meeting element @{term c} restricted to
  the image (@{term a}, @{term b} are arbitrary: the limit argument approximates @{term c} alone,
  as downward-closed deflations need not preserve joins).  By @{thm [source] image_meet_exists}
  the meets involved always exist.\<close>

locale distributive_defl = bounded_complete_defl d + downclosed_defl d
  for d :: "'a::bifinite \<rightarrow> 'a" +
  assumes distrib_image:
    "{a, b} <<| j \<Longrightarrow> is_glb {d\<cdot>c, j} m \<Longrightarrow> is_glb {d\<cdot>c, a} ma \<Longrightarrow> is_glb {d\<cdot>c, b} mb \<Longrightarrow> {ma, mb} <<| m"

lemma (in distributive_defl) deflation: "deflation d" by (fact deflation_axioms)

lemma distributive_deflI:
  assumes "bounded_complete_defl d" "downclosed_defl d"
    and "\<And>a b j c m ma mb. {a, b} <<| j \<Longrightarrow> is_glb {d\<cdot>c, j} m \<Longrightarrow> is_glb {d\<cdot>c, a} ma \<Longrightarrow>
      is_glb {d\<cdot>c, b} mb \<Longrightarrow> {ma, mb} <<| m"
  shows "distributive_defl d"
  using assms by (simp add: distributive_defl_def distributive_defl_axioms_def)

lemma lub_pair_chains:
  fixes X Z W :: "nat \<Rightarrow> 'a::cpo"
  assumes X: "chain X" and Z: "chain Z" and W: "chain W" and lv: "\<And>n. {X n, Z n} <<| W n"
  shows "{\<Squnion>n. X n, \<Squnion>n. Z n} <<| (\<Squnion>n. W n)"
proof (rule is_lubI)
  have "X n \<sqsubseteq> W n" "Z n \<sqsubseteq> W n" for n using lv[of n] by (auto dest: is_lubD1 is_ubD)
  then have "(\<Squnion>n. X n) \<sqsubseteq> (\<Squnion>n. W n)" "(\<Squnion>n. Z n) \<sqsubseteq> (\<Squnion>n. W n)"
    by (simp_all add: lub_mono X Z W)
  then show "{\<Squnion>n. X n, \<Squnion>n. Z n} <| (\<Squnion>n. W n)" by (auto intro: is_ubI)
next
  fix u assume "{\<Squnion>n. X n, \<Squnion>n. Z n} <| u"
  then have "(\<Squnion>n. X n) \<sqsubseteq> u" "(\<Squnion>n. Z n) \<sqsubseteq> u" by (auto dest: is_ubD)
  then have "X n \<sqsubseteq> u" "Z n \<sqsubseteq> u" for n
    using is_ub_thelub[OF X, of n] is_ub_thelub[OF Z, of n] by (auto intro: below_trans)
  then have "W n \<sqsubseteq> u" for n by (auto intro: is_lubD2[OF lv] is_ubI)
  then show "(\<Squnion>n. W n) \<sqsubseteq> u" by (rule lub_below[OF W])
qed

text \<open>Admissibility, without continuity of meets: at each level the deflation commutes with the
  meets in question (@{thm [source] downclosed_defl.glb_fixed}), and the limit is again
  bounded-complete and downward closed, so the limit's meets are fixed and are the lubs of the
  levels' meets.\<close>

lemma adm_distributive_defl: "adm (distributive_defl :: ('a::bifinite \<rightarrow> 'a) \<Rightarrow> bool)"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'a"
  assume chain: "chain Y" and H: "\<forall>i. distributive_defl (Y i)"
  have Hbc: "bounded_complete_defl (Y i)" for i using H by (simp add: distributive_defl_def)
  have Hdc: "downclosed_defl (Y i)" for i using H by (simp add: distributive_defl_def)
  have Hd: "deflation (Y i)" for i by (rule downclosed_defl.axioms(1)[OF Hdc])
  define D where "D = (\<Squnion>i. Y i)"
  have bc: "bounded_complete_defl D"
    unfolding D_def by (rule admD[OF adm_bounded_complete_defl chain Hbc])
  have dc: "downclosed_defl D"
    unfolding D_def by (rule admD[OF adm_downclosed_defl chain Hdc])
  have defl: "deflation D" by (rule downclosed_defl.axioms(1)[OF dc])
  have below: "Y n \<sqsubseteq> D" for n unfolding D_def by (rule is_ub_thelub[OF chain])
  have comp: "Y n\<cdot>(D\<cdot>x) = Y n\<cdot>x" for n x by (rule deflation_below_comp1[OF Hd defl below])
  have reach: "D\<cdot>x = (\<Squnion>n. Y n\<cdot>x)" for x unfolding D_def by (rule contlub_cfun_fun[OF chain])
  have chx: "chain (\<lambda>n. Y n\<cdot>x)" for x by (rule ch2ch_Rep_cfunL[OF chain])
  have level: "is_glb {Y n\<cdot>c, z} (Y n\<cdot>m)" if "is_glb {D\<cdot>c, z} m" for n c z m
  proof -
    from downclosed_defl.glb_fixed[OF Hdc that]
    have "is_glb {Y n\<cdot>(D\<cdot>c), Y n\<cdot>z} (Y n\<cdot>m)" .
    then have "is_glb {Y n\<cdot>c, Y n\<cdot>z} (Y n\<cdot>m)" by (simp only: comp)
    then show ?thesis by (rule downclosed_defl.glb_relative[OF Hdc])
  qed
  have fixD: "D\<cdot>m = m" if "is_glb {D\<cdot>c, z} m" for c z m
  proof -
    have "m \<sqsubseteq> D\<cdot>c" using that by (auto intro: is_glb_below)
    then show ?thesis by (rule downclosed_defl.lower_fixed[OF dc])
  qed
  have "distributive_defl D"
  proof (rule distributive_deflI[OF bc dc])
    fix a b j c m ma mb
    assume j: "{a, b} <<| j" and m: "is_glb {D\<cdot>c, j} m"
      and ma: "is_glb {D\<cdot>c, a} ma" and mb: "is_glb {D\<cdot>c, b} mb"
    have lv: "{Y n\<cdot>ma, Y n\<cdot>mb} <<| Y n\<cdot>m" for n
      by (rule distributive_defl.distrib_image[OF H[rule_format, of n] j
            level[OF m] level[OF ma] level[OF mb]])
    have "{\<Squnion>n. Y n\<cdot>ma, \<Squnion>n. Y n\<cdot>mb} <<| (\<Squnion>n. Y n\<cdot>m)"
      by (rule lub_pair_chains[OF chx chx chx lv])
    moreover have "(\<Squnion>n. Y n\<cdot>ma) = ma" "(\<Squnion>n. Y n\<cdot>mb) = mb" "(\<Squnion>n. Y n\<cdot>m) = m"
      using fixD[OF ma] fixD[OF mb] fixD[OF m] by (simp_all add: reach)
    ultimately show "{ma, mb} <<| m" by simp
  qed
  then show "distributive_defl (\<Squnion>i. Y i)" by (simp add: D_def)
qed

text \<open>Relational and class-level meets and joins.\<close>

lemma meet_is_glb: "is_glb {x, y} (x \<sqinter> (y :: 'a::bounded_complete))"
  by (rule is_glbI) (auto intro: meet_below1 meet_below2 meet_greatest)

lemma distrib_relational:
  fixes a b c :: "'a::distributive_cpo"
  assumes j: "{a, b} <<| j" and m: "is_glb {c, j} m"
    and ma: "is_glb {c, a} ma" and mb: "is_glb {c, b} mb"
  shows "{ma, mb} <<| m"
proof -
  have ab: "a \<Up> b" using j by (auto intro: joinableI dest: is_lubD1 is_ubD)
  have "j = a \<squnion> b" using j joinable_lub[OF ab] by (rule is_lub_unique)
  then have "m = c \<sqinter> (a \<squnion> b)" using m meet_is_glb by (auto intro: is_glb_unique)
  moreover have "ma = c \<sqinter> a" "mb = c \<sqinter> b" using ma mb meet_is_glb by (auto intro: is_glb_unique)
  moreover have "c \<sqinter> a \<Up> c \<sqinter> b" by (rule joinableI[OF meet_below1 meet_below1])
  ultimately show ?thesis by (simp add: meet_join_distrib[OF ab] joinable_lub)
qed

lemma distributive_defl_bottom: "distributive_defl (\<bottom> :: 'a::bifinite \<rightarrow> 'a)"
proof (rule distributive_deflI[OF bounded_complete_defl_bottom downclosed_defl_bottom])
  fix a b j c m ma mb :: 'a
  assume m: "is_glb {\<bottom>\<cdot>c, j} m" and ma: "is_glb {\<bottom>\<cdot>c, a} ma" and mb: "is_glb {\<bottom>\<cdot>c, b} mb"
  have "m \<sqsubseteq> \<bottom>\<cdot>c" by (rule is_glb_below[OF m]) simp
  moreover have "ma \<sqsubseteq> \<bottom>\<cdot>c" by (rule is_glb_below[OF ma]) simp
  moreover have "mb \<sqsubseteq> \<bottom>\<cdot>c" by (rule is_glb_below[OF mb]) simp
  ultimately show "{ma, mb} <<| m" by simp
qed

lemma distributive_defl_ID: "distributive_defl (ID :: 'a::{bifinite, distributive_cpo} \<rightarrow> 'a)"
proof (rule distributive_deflI[OF bounded_complete_defl_ID downclosed_defl_ID])
  fix a b j c m ma mb :: 'a
  assume "{a, b} <<| j" "is_glb {ID\<cdot>c, j} m" "is_glb {ID\<cdot>c, a} ma" "is_glb {ID\<cdot>c, b} mb"
  then show "{ma, mb} <<| m" by (simp add: distrib_relational)
qed

lemma distributive_cpo_class_deflI:
  assumes d: "distributive_defl (ID :: 'a::{bifinite, bounded_complete} \<rightarrow> 'a)"
  shows "OFCLASS('a, distributive_cpo_class)"
proof intro_classes
  fix a b c :: 'a assume ab: "a \<Up> b"
  have "{c \<sqinter> a, c \<sqinter> b} <<| c \<sqinter> (a \<squnion> b)"
    using distributive_defl.distrib_image[OF d joinable_lub[OF ab],
        of c "c \<sqinter> (a \<squnion> b)" "c \<sqinter> a" "c \<sqinter> b"]
    by (simp add: meet_is_glb)
  moreover have "{c \<sqinter> a, c \<sqinter> b} <<| c \<sqinter> a \<squnion> c \<sqinter> b"
    by (rule joinable_lub[OF joinableI[OF meet_below1 meet_below1]])
  ultimately show "c \<sqinter> (a \<squnion> b) = c \<sqinter> a \<squnion> c \<sqinter> b" by (rule is_lub_unique)
qed

lemma iso_is_glb_pair:
  fixes abs :: "'r::pcpo \<rightarrow> 't::pcpo" and rep
  assumes iso: "iso abs rep" and m: "is_glb {x, y} m"
  shows "is_glb {rep\<cdot>x, rep\<cdot>y} (rep\<cdot>m)"
proof (rule is_glbI)
  interpret iso abs rep by (fact iso)
  fix z assume "z \<in> {rep\<cdot>x, rep\<cdot>y}"
  moreover have "m \<sqsubseteq> x" "m \<sqsubseteq> y" using m by (auto intro: is_glb_below)
  ultimately show "rep\<cdot>m \<sqsubseteq> z" by (auto intro: monofun_cfun_arg)
next
  interpret iso abs rep by (fact iso)
  fix l assume "\<forall>z\<in>{rep\<cdot>x, rep\<cdot>y}. l \<sqsubseteq> z"
  then have lx: "l \<sqsubseteq> rep\<cdot>x" and ly: "l \<sqsubseteq> rep\<cdot>y" by simp_all
  have "abs\<cdot>l \<sqsubseteq> x" using monofun_cfun_arg[OF lx, of abs] by simp
  moreover have "abs\<cdot>l \<sqsubseteq> y" using monofun_cfun_arg[OF ly, of abs] by simp
  ultimately have "abs\<cdot>l \<sqsubseteq> m" by (intro is_glb_greatest[OF m]) simp
  then have "rep\<cdot>(abs\<cdot>l) \<sqsubseteq> rep\<cdot>m" by (rule monofun_cfun_arg)
  then show "l \<sqsubseteq> rep\<cdot>m" by simp
qed

lemma iso_is_lub_pair:
  fixes abs :: "'r::pcpo \<rightarrow> 't::pcpo" and rep
  assumes iso: "iso abs rep" and j: "{a, b} <<| j"
  shows "{rep\<cdot>a, rep\<cdot>b} <<| rep\<cdot>j"
proof -
  interpret iso abs rep by (fact iso)
  have "(\<lambda>x. rep\<cdot>x) ` {a, b} <<| rep\<cdot>j" using iso_is_lub_iff[OF iso, of "{a, b}" "rep\<cdot>j"] j by simp
  then show ?thesis by simp
qed

lemma distributive_defl_iso:
  fixes abs :: "'r::bifinite \<rightarrow> 't::bifinite" and rep
  assumes iso_abs: "\<And>x. rep\<cdot>(abs\<cdot>x) = x" and iso_rep: "\<And>y. abs\<cdot>(rep\<cdot>y) = y"
    and f: "distributive_defl f"
  shows "distributive_defl (abs oo f oo rep)"
proof (rule distributive_deflI)
  have iso: "iso abs rep" by (rule iso.intro[OF iso_abs iso_rep])
  interpret iso abs rep by (fact iso)
  have fbc: "bounded_complete_defl f" and fdc: "downclosed_defl f"
    using f by (simp_all add: distributive_defl_def)
  show "bounded_complete_defl (abs oo f oo rep)"
    by (rule bounded_complete_defl_iso[OF iso_abs iso_rep fbc])
  show "downclosed_defl (abs oo f oo rep)" by (rule downclosed_defl_iso[OF iso_abs iso_rep fdc])
  fix a b j c m ma mb
  assume j: "{a, b} <<| j" and m: "is_glb {(abs oo f oo rep)\<cdot>c, j} m"
    and ma: "is_glb {(abs oo f oo rep)\<cdot>c, a} ma" and mb: "is_glb {(abs oo f oo rep)\<cdot>c, b} mb"
  from iso_is_glb_pair[OF iso m] iso_is_glb_pair[OF iso ma] iso_is_glb_pair[OF iso mb]
  have "is_glb {f\<cdot>(rep\<cdot>c), rep\<cdot>j} (rep\<cdot>m)" "is_glb {f\<cdot>(rep\<cdot>c), rep\<cdot>a} (rep\<cdot>ma)"
    "is_glb {f\<cdot>(rep\<cdot>c), rep\<cdot>b} (rep\<cdot>mb)" by simp_all
  from distributive_defl.distrib_image[OF f iso_is_lub_pair[OF iso j] this]
  have "{rep\<cdot>ma, rep\<cdot>mb} <<| rep\<cdot>m" .
  then show "{ma, mb} <<| m" using iso_is_lub_iff[OF iso, of "{ma, mb}" "rep\<cdot>m"] by simp
qed

text \<open>The distributive law degenerates when one of the three elements is @{term \<bottom>}.\<close>

lemma glb_bottom: "is_glb {\<bottom>, z} m \<Longrightarrow> m = \<bottom>"
proof -
  assume m: "is_glb {\<bottom>, z} m"
  have "m \<sqsubseteq> \<bottom>" by (rule is_glb_below[OF m]) simp
  then show "m = \<bottom>" by simp
qed

lemma distrib_case_c_bottom:
  "is_glb {\<bottom>, j} m \<Longrightarrow> is_glb {\<bottom>, a} ma \<Longrightarrow> is_glb {\<bottom>, b} mb \<Longrightarrow> {ma, mb} <<| m"
  by (auto dest!: glb_bottom)

lemma distrib_case_a_bottom:
  assumes j: "{\<bottom>, b} <<| j" and m: "is_glb {x, j} m" and ma: "is_glb {x, \<bottom>} ma"
    and mb: "is_glb {x, b} mb"
  shows "{ma, mb} <<| m"
proof -
  have "j = b" using j is_lub_bin[OF minimal[of b]] by (rule is_lub_unique)
  with m mb have "m = mb" by (auto intro: is_glb_unique)
  moreover have "ma = \<bottom>" using ma by (auto intro: glb_bottom simp: insert_commute)
  ultimately show ?thesis by (simp add: is_lub_bin)
qed

lemma distrib_case_b_bottom:
  assumes j: "{a, \<bottom>} <<| j" and m: "is_glb {x, j} m" and ma: "is_glb {x, a} ma"
    and mb: "is_glb {x, \<bottom>} mb"
  shows "{ma, mb} <<| m"
proof -
  have "{\<bottom>, a} <<| j" using j by (simp add: insert_commute)
  from distrib_case_a_bottom[OF this m mb ma] show ?thesis by (simp add: insert_commute)
qed

text \<open>Pair lubs and glbs of lifted elements come from the level below.\<close>

lemma up_lub_pair_dec:
  assumes j: "{up\<cdot>x, up\<cdot>y} <<| j"
  obtains j' where "j = up\<cdot>j'" "{x, y} <<| j'"
proof -
  have "up\<cdot>x \<sqsubseteq> j" using j by (auto dest: is_lubD1 is_ubD)
  then obtain j' where jj: "j = up\<cdot>j'" by (cases j) auto
  have "{x, y} <<| j'"
  proof (rule is_lubI)
    have "up\<cdot>x \<sqsubseteq> up\<cdot>j'" "up\<cdot>y \<sqsubseteq> up\<cdot>j'" using j jj by (auto dest: is_lubD1 is_ubD)
    then show "{x, y} <| j'" by (auto intro: is_ubI)
  next
    fix u assume u: "{x, y} <| u"
    have "x \<sqsubseteq> u" "y \<sqsubseteq> u" using u by (auto dest: is_ubD)
    then have "{up\<cdot>x, up\<cdot>y} <| up\<cdot>u" by (auto intro!: is_ubI)
    then have "j \<sqsubseteq> up\<cdot>u" by (rule is_lubD2[OF j])
    with jj show "j' \<sqsubseteq> u" by simp
  qed
  with jj show thesis by (rule that)
qed

lemma up_glb_pair_dec:
  fixes x y :: "'a::pcpo"
  assumes m: "is_glb {up\<cdot>x, up\<cdot>y} m"
  obtains m' where "m = up\<cdot>m'" "is_glb {x, y} m'"
proof -
  have "up\<cdot>\<bottom> \<sqsubseteq> m" by (rule is_glb_greatest[OF m]) simp
  then obtain m' where mm: "m = up\<cdot>m'" by (cases m) auto
  have "is_glb {x, y} m'"
  proof (rule is_glbI)
    fix z assume z: "z \<in> {x, y}"
    have "m \<sqsubseteq> up\<cdot>z" by (rule is_glb_below[OF m]) (use z in auto)
    with mm show "m' \<sqsubseteq> z" by simp
  next
    fix l assume "\<forall>z\<in>{x, y}. l \<sqsubseteq> z"
    then have "up\<cdot>l \<sqsubseteq> m" by (intro is_glb_greatest[OF m]) auto
    with mm show "l \<sqsubseteq> m'" by simp
  qed
  with mm show thesis by (rule that)
qed

lemma distributive_defl_u_map:
  assumes f: "distributive_defl (f :: 'a::bifinite \<rightarrow> 'a)"
  shows "distributive_defl (u_map\<cdot>f)"
proof (rule distributive_deflI)
  have fbc: "bounded_complete_defl f" and fdc: "downclosed_defl f"
    using f by (simp_all add: distributive_defl_def)
  show "bounded_complete_defl (u_map\<cdot>f)" by (rule bounded_complete_defl_u_map[OF fbc])
  show "downclosed_defl (u_map\<cdot>f)" by (rule downclosed_defl_u_map[OF fdc])
  fix a b j c m ma mb
  assume j: "{a, b} <<| j" and m: "is_glb {u_map\<cdot>f\<cdot>c, j} m"
    and ma: "is_glb {u_map\<cdot>f\<cdot>c, a} ma" and mb: "is_glb {u_map\<cdot>f\<cdot>c, b} mb"
  show "{ma, mb} <<| m"
  proof (cases "u_map\<cdot>f\<cdot>c = \<bottom>")
    case True with m ma mb show ?thesis by (simp add: distrib_case_c_bottom)
  next
    case False
    then obtain c' where c: "c = up\<cdot>c'" by (cases c) auto
    show ?thesis
    proof (cases "a = \<bottom>")
      case True with j m ma mb show ?thesis by (simp add: distrib_case_a_bottom)
    next
      case False
      show ?thesis
      proof (cases "b = \<bottom>")
        case True with j m ma mb show ?thesis by (simp add: distrib_case_b_bottom)
      next
        case False
        with \<open>a \<noteq> \<bottom>\<close> obtain a' b' where ab: "a = up\<cdot>a'" "b = up\<cdot>b'" by (cases a; cases b) auto
        from j ab obtain j' where jj: "j = up\<cdot>j'" and j': "{a', b'} <<| j'"
          by (auto elim: up_lub_pair_dec)
        from m c jj obtain m' where mm: "m = up\<cdot>m'" and m': "is_glb {f\<cdot>c', j'} m'"
          by (auto elim: up_glb_pair_dec)
        from ma c ab obtain ma' where mma: "ma = up\<cdot>ma'" and ma': "is_glb {f\<cdot>c', a'} ma'"
          by (auto elim: up_glb_pair_dec)
        from mb c ab obtain mb' where mmb: "mb = up\<cdot>mb'" and mb': "is_glb {f\<cdot>c', b'} mb'"
          by (auto elim: up_glb_pair_dec)
        from distributive_defl.distrib_image[OF f j' m' ma' mb']
        have "{ma', mb'} <<| m'" .
        then have "{up\<cdot>ma', up\<cdot>mb'} <<| up\<cdot>m'" by (rule up_is_lub_pair)
        with mm mma mmb show ?thesis by simp
      qed
    qed
  qed
qed

text \<open>Pair lubs and glbs in a strict sum, on one side.\<close>

lemma sinl_lub_pair_dec:
  assumes j: "{sinl\<cdot>x, sinl\<cdot>y} <<| (j :: 'a::pcpo \<oplus> 'b::pcpo)" and x: "x \<noteq> \<bottom>"
  obtains j' where "j = sinl\<cdot>j'" "{x, y} <<| j'"
proof -
  have xj: "sinl\<cdot>x \<sqsubseteq> j" using j by (auto dest: is_lubD1 is_ubD)
  with x obtain j' where jj: "j = sinl\<cdot>j'" by (cases j) auto
  have "{x, y} <<| j'"
  proof (rule is_lubI)
    have "sinl\<cdot>x \<sqsubseteq> sinl\<cdot>j'" "sinl\<cdot>y \<sqsubseteq> sinl\<cdot>j'" using j jj by (auto dest: is_lubD1 is_ubD)
    then show "{x, y} <| j'" by (auto intro: is_ubI)
  next
    fix u assume u: "{x, y} <| u"
    have "x \<sqsubseteq> u" "y \<sqsubseteq> u" using u by (auto dest: is_ubD)
    then have "{sinl\<cdot>x, sinl\<cdot>y} <| (sinl\<cdot>u :: 'a \<oplus> 'b)" by (auto intro!: is_ubI)
    then have "j \<sqsubseteq> sinl\<cdot>u" by (rule is_lubD2[OF j])
    with jj show "j' \<sqsubseteq> u" by simp
  qed
  with jj show thesis by (rule that)
qed

lemma sinr_lub_pair_dec:
  assumes j: "{sinr\<cdot>x, sinr\<cdot>y} <<| (j :: 'a::pcpo \<oplus> 'b::pcpo)" and x: "x \<noteq> \<bottom>"
  obtains j' where "j = sinr\<cdot>j'" "{x, y} <<| j'"
proof -
  have xj: "sinr\<cdot>x \<sqsubseteq> j" using j by (auto dest: is_lubD1 is_ubD)
  with x obtain j' where jj: "j = sinr\<cdot>j'" by (cases j) auto
  have "{x, y} <<| j'"
  proof (rule is_lubI)
    have "sinr\<cdot>x \<sqsubseteq> sinr\<cdot>j'" "sinr\<cdot>y \<sqsubseteq> sinr\<cdot>j'" using j jj by (auto dest: is_lubD1 is_ubD)
    then show "{x, y} <| j'" by (auto intro: is_ubI)
  next
    fix u assume u: "{x, y} <| u"
    have "x \<sqsubseteq> u" "y \<sqsubseteq> u" using u by (auto dest: is_ubD)
    then have "{sinr\<cdot>x, sinr\<cdot>y} <| (sinr\<cdot>u :: 'a \<oplus> 'b)" by (auto intro!: is_ubI)
    then have "j \<sqsubseteq> sinr\<cdot>u" by (rule is_lubD2[OF j])
    with jj show "j' \<sqsubseteq> u" by simp
  qed
  with jj show thesis by (rule that)
qed

lemma sinl_glb_pair_dec:
  assumes m: "is_glb {sinl\<cdot>x, sinl\<cdot>y} (m :: 'a::pcpo \<oplus> 'b::pcpo)"
  obtains m' where "m = sinl\<cdot>m'" "is_glb {x, y} m'"
proof -
  have mx: "m \<sqsubseteq> sinl\<cdot>x" by (rule is_glb_below[OF m]) simp
  obtain m' where mm: "m = sinl\<cdot>m'" using mx by (cases m) (auto intro: sinl_strict[symmetric])
  have "is_glb {x, y} m'"
  proof (rule is_glbI)
    fix z assume z: "z \<in> {x, y}"
    have "m \<sqsubseteq> sinl\<cdot>z" by (rule is_glb_below[OF m]) (use z in auto)
    with mm show "m' \<sqsubseteq> z" by simp
  next
    fix l assume "\<forall>z\<in>{x, y}. l \<sqsubseteq> z"
    then have "sinl\<cdot>l \<sqsubseteq> m" by (intro is_glb_greatest[OF m]) auto
    with mm show "l \<sqsubseteq> m'" by simp
  qed
  with mm show thesis by (rule that)
qed

lemma sinr_glb_pair_dec:
  assumes m: "is_glb {sinr\<cdot>x, sinr\<cdot>y} (m :: 'a::pcpo \<oplus> 'b::pcpo)"
  obtains m' where "m = sinr\<cdot>m'" "is_glb {x, y} m'"
proof -
  have mx: "m \<sqsubseteq> sinr\<cdot>x" by (rule is_glb_below[OF m]) simp
  obtain m' where mm: "m = sinr\<cdot>m'" using mx by (cases m) (auto intro: sinr_strict[symmetric])
  have "is_glb {x, y} m'"
  proof (rule is_glbI)
    fix z assume z: "z \<in> {x, y}"
    have "m \<sqsubseteq> sinr\<cdot>z" by (rule is_glb_below[OF m]) (use z in auto)
    with mm show "m' \<sqsubseteq> z" by simp
  next
    fix l assume "\<forall>z\<in>{x, y}. l \<sqsubseteq> z"
    then have "sinr\<cdot>l \<sqsubseteq> m" by (intro is_glb_greatest[OF m]) auto
    with mm show "l \<sqsubseteq> m'" by simp
  qed
  with mm show thesis by (rule that)
qed

lemma sinl_sinr_glb: "is_glb {sinl\<cdot>x, sinr\<cdot>y} (m :: 'a::pcpo \<oplus> 'b::pcpo) \<Longrightarrow> m = \<bottom>"
proof -
  assume m: "is_glb {sinl\<cdot>x, sinr\<cdot>y} m"
  have "m \<sqsubseteq> sinl\<cdot>x" "m \<sqsubseteq> sinr\<cdot>y" by (rule is_glb_below[OF m], simp)+
  then show "m = \<bottom>" by (cases m) auto
qed

lemma sinl_sinr_not_joinable:
  "x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> sinl\<cdot>x \<sqsubseteq> (u :: 'a::pcpo \<oplus> 'b::pcpo) \<Longrightarrow> sinr\<cdot>y \<sqsubseteq> u \<Longrightarrow> False"
  by (cases u) auto

lemma distributive_defl_ssum_map:
  assumes f: "distributive_defl (f :: 'a::bifinite \<rightarrow> 'a)"
    and g: "distributive_defl (g :: 'b::bifinite \<rightarrow> 'b)"
  shows "distributive_defl (ssum_map\<cdot>f\<cdot>g)"
proof (rule distributive_deflI)
  have fbc: "bounded_complete_defl f" and fdc: "downclosed_defl f"
    using f by (simp_all add: distributive_defl_def)
  have gbc: "bounded_complete_defl g" and gdc: "downclosed_defl g"
    using g by (simp_all add: distributive_defl_def)
  show "bounded_complete_defl (ssum_map\<cdot>f\<cdot>g)" by (rule bounded_complete_defl_ssum_map[OF fbc gbc])
  show "downclosed_defl (ssum_map\<cdot>f\<cdot>g)" by (rule downclosed_defl_ssum_map[OF fdc gdc])
  fix a b j c m ma mb
  assume j: "{a, b} <<| j" and m: "is_glb {ssum_map\<cdot>f\<cdot>g\<cdot>c, j} m"
    and ma: "is_glb {ssum_map\<cdot>f\<cdot>g\<cdot>c, a} ma" and mb: "is_glb {ssum_map\<cdot>f\<cdot>g\<cdot>c, b} mb"
  have ab: "a \<sqsubseteq> j" "b \<sqsubseteq> j" using j by (auto dest: is_lubD1 is_ubD)
  show "{ma, mb} <<| m"
  proof (cases "ssum_map\<cdot>f\<cdot>g\<cdot>c = \<bottom>")
    case True with m ma mb show ?thesis by (simp add: distrib_case_c_bottom)
  next
    case cnz: False
    show ?thesis
    proof (cases "a = \<bottom>")
      case True with j m ma mb show ?thesis by (simp add: distrib_case_a_bottom)
    next
      case anz: False
      show ?thesis
      proof (cases "b = \<bottom>")
        case True with j m ma mb show ?thesis by (simp add: distrib_case_b_bottom)
      next
        case bnz: False
        show ?thesis
        proof (cases a)
          case bottom with anz show ?thesis by simp
        next
          case (sinl a')
          obtain b' where b: "b = sinl\<cdot>b'" "b' \<noteq> \<bottom>"
          proof (cases b)
            case bottom with bnz show ?thesis by simp
          next
            case (sinl b'') then show ?thesis by (rule that)
          next
            case (sinr b'')
            have False by (rule sinl_sinr_not_joinable[of a' b'' j]) (use sinl sinr ab in simp_all)
            then show ?thesis ..
          qed
          have jab: "{sinl\<cdot>a', sinl\<cdot>b'} <<| j" using j sinl b by simp
          obtain j' where jj: "j = sinl\<cdot>j'" and j': "{a', b'} <<| j'"
            by (rule sinl_lub_pair_dec[OF jab \<open>a' \<noteq> \<bottom>\<close>])
          show ?thesis
          proof (cases c)
            case bottom with cnz show ?thesis by simp
          next
            case (sinl c')
            then have fc: "ssum_map\<cdot>f\<cdot>g\<cdot>c = sinl\<cdot>(f\<cdot>c')" by simp
            obtain m' where mm: "m = sinl\<cdot>m'" and m': "is_glb {f\<cdot>c', j'} m'"
              by (rule sinl_glb_pair_dec) (use m fc jj in simp)
            obtain ma' where mma: "ma = sinl\<cdot>ma'" and ma': "is_glb {f\<cdot>c', a'} ma'"
              by (rule sinl_glb_pair_dec) (use ma fc \<open>a = sinl\<cdot>a'\<close> in simp)
            obtain mb' where mmb: "mb = sinl\<cdot>mb'" and mb': "is_glb {f\<cdot>c', b'} mb'"
              by (rule sinl_glb_pair_dec) (use mb fc b in simp)
            from distributive_defl.distrib_image[OF f j' m' ma' mb']
            have "{ma', mb'} <<| m'" .
            then have "{sinl\<cdot>ma', sinl\<cdot>mb'} <<| (sinl\<cdot>m' :: 'a \<oplus> 'b)" by (rule sinl_is_lub_pair)
            with mm mma mmb show ?thesis by simp
          next
            case (sinr c')
            then have gc: "ssum_map\<cdot>f\<cdot>g\<cdot>c = sinr\<cdot>(g\<cdot>c')" by simp
            have "m = \<bottom>" by (rule sinl_sinr_glb) (use m gc jj in \<open>simp add: insert_commute\<close>)
            moreover have "ma = \<bottom>"
              by (rule sinl_sinr_glb) (use ma gc \<open>a = sinl\<cdot>a'\<close> in \<open>simp add: insert_commute\<close>)
            moreover have "mb = \<bottom>"
              by (rule sinl_sinr_glb) (use mb gc b in \<open>simp add: insert_commute\<close>)
            ultimately show ?thesis by simp
          qed
        next
          case (sinr a')
          obtain b' where b: "b = sinr\<cdot>b'" "b' \<noteq> \<bottom>"
          proof (cases b)
            case bottom with bnz show ?thesis by simp
          next
            case (sinl b'')
            have False by (rule sinl_sinr_not_joinable[of b'' a' j]) (use sinl sinr ab in simp_all)
            then show ?thesis ..
          next
            case (sinr b'') then show ?thesis by (rule that)
          qed
          have jab: "{sinr\<cdot>a', sinr\<cdot>b'} <<| j" using j sinr b by simp
          obtain j' where jj: "j = sinr\<cdot>j'" and j': "{a', b'} <<| j'"
            by (rule sinr_lub_pair_dec[OF jab \<open>a' \<noteq> \<bottom>\<close>])
          show ?thesis
          proof (cases c)
            case bottom with cnz show ?thesis by simp
          next
            case (sinl c')
            then have fc: "ssum_map\<cdot>f\<cdot>g\<cdot>c = sinl\<cdot>(f\<cdot>c')" by simp
            have "m = \<bottom>" by (rule sinl_sinr_glb) (use m fc jj in simp)
            moreover have "ma = \<bottom>" by (rule sinl_sinr_glb) (use ma fc \<open>a = sinr\<cdot>a'\<close> in simp)
            moreover have "mb = \<bottom>" by (rule sinl_sinr_glb) (use mb fc b in simp)
            ultimately show ?thesis by simp
          next
            case (sinr c')
            then have gc: "ssum_map\<cdot>f\<cdot>g\<cdot>c = sinr\<cdot>(g\<cdot>c')" by simp
            obtain m' where mm: "m = sinr\<cdot>m'" and m': "is_glb {g\<cdot>c', j'} m'"
              by (rule sinr_glb_pair_dec) (use m gc jj in simp)
            obtain ma' where mma: "ma = sinr\<cdot>ma'" and ma': "is_glb {g\<cdot>c', a'} ma'"
              by (rule sinr_glb_pair_dec) (use ma gc \<open>a = sinr\<cdot>a'\<close> in simp)
            obtain mb' where mmb: "mb = sinr\<cdot>mb'" and mb': "is_glb {g\<cdot>c', b'} mb'"
              by (rule sinr_glb_pair_dec) (use mb gc b in simp)
            from distributive_defl.distrib_image[OF g j' m' ma' mb']
            have "{ma', mb'} <<| m'" .
            then have "{sinr\<cdot>ma', sinr\<cdot>mb'} <<| (sinr\<cdot>m' :: 'a \<oplus> 'b)" by (rule sinr_is_lub_pair)
            with mm mma mmb show ?thesis by simp
          qed
        qed
      qed
    qed
  qed
qed

subsubsection \<open>One-sided separation\<close>

text \<open>The smash product collapses \<open>(:a, \<bottom>:) = \<bottom>\<close>, so distributivity of @{term "sprod_map\<cdot>f\<cdot>g"}
  needs: whenever an image element meets \<open>j\<close> nontrivially, it meets every nonbottom \<open>a \<sqsubseteq> j\<close>
  nontrivially.  This follows from one-sided separation: a nonbottom image element shares a
  nonbottom lower bound with every nonbottom element it is joinable with.  Unlike
  @{const separated_defl} the second element is arbitrary, so this constrains the kernel
  (killing \<open>a\<close> but not a joinable \<open>b\<close> is excluded).  At @{term ID} it is @{class separated_po};
  every deflation on a flat type has it.  It is needed only as a premise of the smash product
  rule, and carried through the induction only when recursion passes through \<open>\<otimes>\<close>.\<close>

locale separating_defl = deflation d for d :: "'a::bifinite \<rightarrow> 'a" +
  assumes separating:
    "d\<cdot>x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> d\<cdot>x \<sqsubseteq> u \<Longrightarrow> y \<sqsubseteq> u \<Longrightarrow> \<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> d\<cdot>x \<and> l \<sqsubseteq> y"

lemma (in separating_defl) deflation: "deflation d" by (fact deflation_axioms)

lemma separating_deflI:
  assumes "deflation d"
    and "\<And>x y u. d\<cdot>x \<noteq> \<bottom> \<Longrightarrow> y \<noteq> \<bottom> \<Longrightarrow> d\<cdot>x \<sqsubseteq> u \<Longrightarrow> y \<sqsubseteq> u \<Longrightarrow> \<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> d\<cdot>x \<and> l \<sqsubseteq> y"
  shows "separating_defl d"
  using assms by (simp add: separating_defl_def separating_defl_axioms_def)

lemma separating_defl_bottom: "separating_defl (\<bottom> :: 'a::bifinite \<rightarrow> 'a)"
  by (rule separating_deflI[OF deflation_bottom]) simp

lemma separating_defl_ID: "separating_defl (ID :: 'a::{bifinite, separated_po} \<rightarrow> 'a)"
  by (rule separating_deflI[OF deflation_ID]) (simp add: separated_pcpo)

lemma separating_defl_flat:
  assumes f: "deflation (f :: 'a::{bifinite, flat} \<rightarrow> 'a)" shows "separating_defl f"
proof (rule separating_deflI[OF f])
  fix x y u assume x: "f\<cdot>x \<noteq> \<bottom>" and y: "y \<noteq> \<bottom>" and xu: "f\<cdot>x \<sqsubseteq> u" and yu: "y \<sqsubseteq> u"
  have "f\<cdot>x = u" using flat_eq[OF x] xu by simp
  moreover have "y = u" using flat_eq[OF y] yu by simp
  ultimately show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> f\<cdot>x \<and> l \<sqsubseteq> y" using x by auto
qed

lemma separating_defl_u_map:
  assumes f: "deflation (f :: 'a::bifinite \<rightarrow> 'a)" shows "separating_defl (u_map\<cdot>f)"
proof (rule separating_deflI[OF deflation_u_map[OF f]])
  fix x y u :: "'a\<^sub>\<bottom>" assume x: "u_map\<cdot>f\<cdot>x \<noteq> \<bottom>" and y: "y \<noteq> \<bottom>"
  from x obtain x' where "x = up\<cdot>x'" by (cases x) auto
  moreover from y obtain y' where "y = up\<cdot>y'" by (cases y) auto
  ultimately show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> u_map\<cdot>f\<cdot>x \<and> l \<sqsubseteq> y" by (intro exI[of _ "up\<cdot>\<bottom>"]) simp
qed

lemma separating_defl_ssum_map:
  assumes f: "separating_defl f" and g: "separating_defl g"
  shows "separating_defl (ssum_map\<cdot>f\<cdot>g)"
proof (rule separating_deflI)
  show "deflation (ssum_map\<cdot>f\<cdot>g)"
    using f g by (intro deflation_ssum_map) (simp_all add: separating_defl_def)
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
      using separating_defl.separating[OF f fx yy(2) u(2) yy(3)] by auto
    show ?thesis using l' img yy(1) by (intro exI[of _ "sinl\<cdot>l'"]) simp
  next
    case (sinr x')
    with x have gx: "g\<cdot>x' \<noteq> \<bottom>" and img: "ssum_map\<cdot>f\<cdot>g\<cdot>x = sinr\<cdot>(g\<cdot>x')" by simp_all
    obtain u' where u: "u = sinr\<cdot>u'" "g\<cdot>x' \<sqsubseteq> u'"
      using xu gx img by (cases u) auto
    obtain y' where yy: "y = sinr\<cdot>y'" "y' \<noteq> \<bottom>" "y' \<sqsubseteq> u'"
      using yu y u by (cases y) auto
    obtain l' where l': "l' \<noteq> \<bottom>" "l' \<sqsubseteq> g\<cdot>x'" "l' \<sqsubseteq> y'"
      using separating_defl.separating[OF g gx yy(2) u(2) yy(3)] by auto
    show ?thesis using l' img yy(1) by (intro exI[of _ "sinr\<cdot>l'"]) simp
  qed
qed

lemma separating_defl_sprod_map:
  assumes f: "separating_defl f" and g: "separating_defl g"
  shows "separating_defl (sprod_map\<cdot>f\<cdot>g)"
proof (rule separating_deflI)
  show "deflation (sprod_map\<cdot>f\<cdot>g)"
    using f g by (intro deflation_sprod_map) (simp_all add: separating_defl_def)
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
    using separating_defl.separating[OF f fx(1) yy(2) u(2) yy(4)] by auto
  obtain l2 where l2: "l2 \<noteq> \<bottom>" "l2 \<sqsubseteq> g\<cdot>x2" "l2 \<sqsubseteq> y2"
    using separating_defl.separating[OF g fx(2) yy(3) u(3) yy(5)] by auto
  show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> sprod_map\<cdot>f\<cdot>g\<cdot>x \<and> l \<sqsubseteq> y"
    using l1 l2 img yy(1) by (intro exI[of _ "(:l1, l2:)"]) (simp add: spair_below)
qed

lemma separating_defl_iso:
  fixes abs :: "'r::bifinite \<rightarrow> 't::bifinite" and rep
  assumes iso_abs: "\<And>x. rep\<cdot>(abs\<cdot>x) = x" and iso_rep: "\<And>y. abs\<cdot>(rep\<cdot>y) = y"
    and f: "separating_defl f"
  shows "separating_defl (abs oo f oo rep)"
proof (rule separating_deflI)
  interpret iso abs rep by (rule iso.intro[OF iso_abs iso_rep])
  show "deflation (abs oo f oo rep)"
    using f by (intro deflation_abs_rep[OF abs_iso rep_iso]) (simp add: separating_defl_def)
  fix x y u assume x: "(abs oo f oo rep)\<cdot>x \<noteq> \<bottom>" and y: "y \<noteq> \<bottom>"
    and xu: "(abs oo f oo rep)\<cdot>x \<sqsubseteq> u" and yu: "y \<sqsubseteq> u"
  have fx: "f\<cdot>(rep\<cdot>x) \<noteq> \<bottom>" using x by (simp add: abs_bottom_iff)
  have ry: "rep\<cdot>y \<noteq> \<bottom>" using y by (simp add: rep_bottom_iff)
  have "rep\<cdot>(abs\<cdot>(f\<cdot>(rep\<cdot>x))) \<sqsubseteq> rep\<cdot>u" using monofun_cfun_arg[OF xu, of rep] by simp
  then have fxu: "f\<cdot>(rep\<cdot>x) \<sqsubseteq> rep\<cdot>u" by (simp del: rep_iso)
  have ryu: "rep\<cdot>y \<sqsubseteq> rep\<cdot>u" using yu by (rule monofun_cfun_arg)
  obtain l where l: "l \<noteq> \<bottom>" "l \<sqsubseteq> f\<cdot>(rep\<cdot>x)" "l \<sqsubseteq> rep\<cdot>y"
    using separating_defl.separating[OF f fx ry fxu ryu] by auto
  have "abs\<cdot>l \<sqsubseteq> abs\<cdot>(f\<cdot>(rep\<cdot>x))" using l(2) by (rule monofun_cfun_arg)
  moreover have "abs\<cdot>l \<sqsubseteq> abs\<cdot>(rep\<cdot>y)" using l(3) by (rule monofun_cfun_arg)
  ultimately show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> (abs oo f oo rep)\<cdot>x \<and> l \<sqsubseteq> y"
    using l(1) by (intro exI[of _ "abs\<cdot>l"]) (simp add: abs_bottom_iff)
qed

lemma adm_separating_defl: "adm (separating_defl :: ('a::bifinite \<rightarrow> 'a) \<Rightarrow> bool)"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'a" assume Y: "chain Y" and s: "\<forall>i. separating_defl (Y i)"
  show "separating_defl (\<Squnion>i. Y i)"
  proof (rule separating_deflI)
    show "deflation (\<Squnion>i. Y i)"
      by (rule admD[OF adm_deflation Y]) (use s in \<open>simp add: separating_defl_def\<close>)
    fix x y u assume x: "(\<Squnion>i. Y i)\<cdot>x \<noteq> \<bottom>" and y: "y \<noteq> \<bottom>"
      and xu: "(\<Squnion>i. Y i)\<cdot>x \<sqsubseteq> u" and yu: "y \<sqsubseteq> u"
    have chx: "chain (\<lambda>i. Y i\<cdot>x)" by (rule ch2ch_Rep_cfunL[OF Y])
    have lub: "(\<Squnion>i. Y i)\<cdot>x = (\<Squnion>i. Y i\<cdot>x)" by (rule contlub_cfun_fun[OF Y])
    obtain n where n: "Y n\<cdot>x \<noteq> \<bottom>" using x lub_eq_bottom_iff[OF chx] lub by auto
    have below: "Y n\<cdot>x \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x" by (rule monofun_cfun_fun[OF is_ub_thelub[OF Y]])
    obtain l where l: "l \<noteq> \<bottom>" "l \<sqsubseteq> Y n\<cdot>x" "l \<sqsubseteq> y"
      using separating_defl.separating[OF s[rule_format, of n] n y below_trans[OF below xu] yu]
      by auto
    show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x \<and> l \<sqsubseteq> y"
      using l below_trans[OF l(2) below] by auto
  qed
qed

lemma separating_defl_below:
  assumes le: "d \<sqsubseteq> e" and e: "separating_defl e" and d: "deflation d"
  shows "separating_defl d"
proof (rule separating_deflI[OF d])
  fix x y u assume x: "d\<cdot>x \<noteq> \<bottom>" "y \<noteq> \<bottom>" "d\<cdot>x \<sqsubseteq> u" "y \<sqsubseteq> u"
  have "e\<cdot>(d\<cdot>x) = d\<cdot>x"
    by (rule deflation_below_comp2[OF d separating_defl.axioms(1)[OF e] le])
  then show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> d\<cdot>x \<and> l \<sqsubseteq> y"
    using separating_defl.separating[OF e, of "d\<cdot>x" y u] x by simp
qed

text \<open>The consequence used by the smash product rule.\<close>

lemma separating_glb_nonbottom:
  assumes s: "separating_defl d" and dc: "downclosed_defl d"
    and m: "is_glb {d\<cdot>c, j} m" and m0: "m \<noteq> \<bottom>" and a: "a \<sqsubseteq> j" "a \<noteq> \<bottom>"
    and ma: "is_glb {d\<cdot>c, a} ma"
  shows "ma \<noteq> \<bottom>"
proof
  assume ma0: "ma = \<bottom>"
  have mc: "m \<sqsubseteq> d\<cdot>c" "m \<sqsubseteq> j" by (rule is_glb_below[OF m], simp)+
  have dm: "d\<cdot>m = m" by (rule downclosed_defl.lower_fixed[OF dc mc(1)])
  obtain l where l: "l \<noteq> \<bottom>" "l \<sqsubseteq> m" "l \<sqsubseteq> a"
    using separating_defl.separating[OF s, of m a j] dm m0 a mc(2) by auto
  have "l \<sqsubseteq> d\<cdot>c" using l(2) mc(1) by (rule below_trans)
  then have "l \<sqsubseteq> ma" using l(3) by (intro is_glb_greatest[OF ma]) auto
  with ma0 l(1) show False by simp
qed

subsubsection \<open>Smash products\<close>

lemma spair_lub_pair_dec:
  assumes j: "{(:a1, a2:), (:b1, b2:)} <<| j"
    and nb: "a1 \<noteq> \<bottom>" "a2 \<noteq> \<bottom>" "b1 \<noteq> \<bottom>" "b2 \<noteq> \<bottom>"
  obtains j1 j2 where "j = (:j1, j2:)" "{a1, b1} <<| j1" "{a2, b2} <<| j2"
proof -
  have aj: "(:a1, a2:) \<sqsubseteq> j" and bj: "(:b1, b2:) \<sqsubseteq> j" using j by (auto dest: is_lubD1 is_ubD)
  obtain j1 j2 where jj: "j = (:j1, j2:)" and jnb: "j1 \<noteq> \<bottom>" "j2 \<noteq> \<bottom>"
    using aj nb by (cases j) auto
  have le: "a1 \<sqsubseteq> j1" "a2 \<sqsubseteq> j2" "b1 \<sqsubseteq> j1" "b2 \<sqsubseteq> j2"
    using aj[unfolded jj] bj[unfolded jj] by (simp_all add: spair_below nb)
  have "{a1, b1} <<| j1"
  proof (rule is_lubI)
    show "{a1, b1} <| j1" using le by (auto intro: is_ubI)
  next
    fix u assume u: "{a1, b1} <| u"
    then have "a1 \<sqsubseteq> u" "b1 \<sqsubseteq> u" by (auto dest: is_ubD)
    then have "{(:a1, a2:), (:b1, b2:)} <| (:u, j2:)"
      using le by (auto intro!: is_ubI simp: spair_below nb)
    then have "j \<sqsubseteq> (:u, j2:)" by (rule is_lubD2[OF j])
    then show "j1 \<sqsubseteq> u" using jj jnb by (simp add: spair_below)
  qed
  moreover have "{a2, b2} <<| j2"
  proof (rule is_lubI)
    show "{a2, b2} <| j2" using le by (auto intro: is_ubI)
  next
    fix u assume u: "{a2, b2} <| u"
    then have "a2 \<sqsubseteq> u" "b2 \<sqsubseteq> u" by (auto dest: is_ubD)
    then have "{(:a1, a2:), (:b1, b2:)} <| (:j1, u:)"
      using le by (auto intro!: is_ubI simp: spair_below nb)
    then have "j \<sqsubseteq> (:j1, u:)" by (rule is_lubD2[OF j])
    then show "j2 \<sqsubseteq> u" using jj jnb by (simp add: spair_below)
  qed
  ultimately show thesis using jj by (intro that)
qed

lemma spair_glb_pair:
  assumes m1: "is_glb {x1, y1} m1" and m2: "is_glb {x2, y2} m2"
  shows "is_glb {(:x1, x2:), (:y1, y2:)} (:m1, m2:)"
proof (rule is_glbI)
  have "m1 \<sqsubseteq> x1" "m1 \<sqsubseteq> y1" by (rule is_glb_below[OF m1], simp)+
  moreover have "m2 \<sqsubseteq> x2" "m2 \<sqsubseteq> y2" by (rule is_glb_below[OF m2], simp)+
  moreover fix z assume "z \<in> {(:x1, x2:), (:y1, y2:)}"
  ultimately show "(:m1, m2:) \<sqsubseteq> z" by (auto simp: spair_below_iff)
next
  fix l assume l: "\<forall>z\<in>{(:x1, x2:), (:y1, y2:)}. l \<sqsubseteq> z"
  show "l \<sqsubseteq> (:m1, m2:)"
  proof (cases l)
    case bottom then show ?thesis by simp
  next
    case (spair l1 l2)
    with l have "l1 \<sqsubseteq> x1" "l1 \<sqsubseteq> y1" "l2 \<sqsubseteq> x2" "l2 \<sqsubseteq> y2" by (simp_all add: spair_below)
    then have "l1 \<sqsubseteq> m1" "l2 \<sqsubseteq> m2"
      by (intro is_glb_greatest[OF m1] is_glb_greatest[OF m2]; simp)+
    with spair show ?thesis by (simp add: spair_below)
  qed
qed

lemma distributive_defl_sprod_map:
  assumes f: "distributive_defl (f :: 'a::bifinite \<rightarrow> 'a)" and fs: "separating_defl f"
    and g: "distributive_defl (g :: 'b::bifinite \<rightarrow> 'b)" and gs: "separating_defl g"
  shows "distributive_defl (sprod_map\<cdot>f\<cdot>g)"
proof (rule distributive_deflI)
  have fbc: "bounded_complete_defl f" and fdc: "downclosed_defl f"
    using f by (simp_all add: distributive_defl_def)
  have gbc: "bounded_complete_defl g" and gdc: "downclosed_defl g"
    using g by (simp_all add: distributive_defl_def)
  show "bounded_complete_defl (sprod_map\<cdot>f\<cdot>g)" by (rule bounded_complete_defl_sprod_map[OF fbc gbc])
  show "downclosed_defl (sprod_map\<cdot>f\<cdot>g)" by (rule downclosed_defl_sprod_map[OF fdc gdc])
  fix a b j c m ma mb
  assume j: "{a, b} <<| j" and m: "is_glb {sprod_map\<cdot>f\<cdot>g\<cdot>c, j} m"
    and ma: "is_glb {sprod_map\<cdot>f\<cdot>g\<cdot>c, a} ma" and mb: "is_glb {sprod_map\<cdot>f\<cdot>g\<cdot>c, b} mb"
  show "{ma, mb} <<| m"
  proof (cases "sprod_map\<cdot>f\<cdot>g\<cdot>c = \<bottom>")
    case True with m ma mb show ?thesis by (simp add: distrib_case_c_bottom)
  next
    case cnz: False
    show ?thesis
    proof (cases "a = \<bottom>")
      case True with j m ma mb show ?thesis by (simp add: distrib_case_a_bottom)
    next
      case anz: False
      show ?thesis
      proof (cases "b = \<bottom>")
        case True with j m ma mb show ?thesis by (simp add: distrib_case_b_bottom)
      next
        case bnz: False
        obtain c1 c2 where c: "c = (:c1, c2:)" "c1 \<noteq> \<bottom>" "c2 \<noteq> \<bottom>" using cnz by (cases c) auto
        have fc: "sprod_map\<cdot>f\<cdot>g\<cdot>c = (:f\<cdot>c1, g\<cdot>c2:)" using c by simp
        obtain a1 a2 where a: "a = (:a1, a2:)" "a1 \<noteq> \<bottom>" "a2 \<noteq> \<bottom>" using anz by (cases a) auto
        obtain b1 b2 where b: "b = (:b1, b2:)" "b1 \<noteq> \<bottom>" "b2 \<noteq> \<bottom>" using bnz by (cases b) auto
        have jab: "{(:a1, a2:), (:b1, b2:)} <<| j" using j a b by simp
        obtain j1 j2 where jj: "j = (:j1, j2:)" and j1: "{a1, b1} <<| j1" and j2: "{a2, b2} <<| j2"
          by (rule spair_lub_pair_dec[OF jab a(2) a(3) b(2) b(3)])
        obtain m1 where m1: "is_glb {f\<cdot>c1, j1} m1"
          using image_meet_exists[OF fbc fdc] by auto
        obtain ma1 where ma1: "is_glb {f\<cdot>c1, a1} ma1"
          using image_meet_exists[OF fbc fdc] by auto
        obtain mb1 where mb1: "is_glb {f\<cdot>c1, b1} mb1"
          using image_meet_exists[OF fbc fdc] by auto
        obtain m2 where m2: "is_glb {g\<cdot>c2, j2} m2"
          using image_meet_exists[OF gbc gdc] by auto
        obtain ma2 where ma2: "is_glb {g\<cdot>c2, a2} ma2"
          using image_meet_exists[OF gbc gdc] by auto
        obtain mb2 where mb2: "is_glb {g\<cdot>c2, b2} mb2"
          using image_meet_exists[OF gbc gdc] by auto
        have mm: "m = (:m1, m2:)"
          using m fc jj by (auto intro: is_glb_unique[OF _ spair_glb_pair[OF m1 m2]])
        have mma: "ma = (:ma1, ma2:)"
          using ma fc a(1) by (auto intro: is_glb_unique[OF _ spair_glb_pair[OF ma1 ma2]])
        have mmb: "mb = (:mb1, mb2:)"
          using mb fc b(1) by (auto intro: is_glb_unique[OF _ spair_glb_pair[OF mb1 mb2]])
        have l1: "{ma1, mb1} <<| m1" by (rule distributive_defl.distrib_image[OF f j1 m1 ma1 mb1])
        have l2: "{ma2, mb2} <<| m2" by (rule distributive_defl.distrib_image[OF g j2 m2 ma2 mb2])
        have le: "ma1 \<sqsubseteq> m1" "mb1 \<sqsubseteq> m1" "ma2 \<sqsubseteq> m2" "mb2 \<sqsubseteq> m2"
          using l1 l2 by (auto dest: is_lubD1 is_ubD)
        have ab_j: "a1 \<sqsubseteq> j1" "b1 \<sqsubseteq> j1" "a2 \<sqsubseteq> j2" "b2 \<sqsubseteq> j2"
          using j1 j2 by (auto dest: is_lubD1 is_ubD)
        show ?thesis
        proof (cases "m1 = \<bottom> \<or> m2 = \<bottom>")
          case True
          then show ?thesis
          proof
            assume m10: "m1 = \<bottom>"
            with le have "ma1 = \<bottom>" "mb1 = \<bottom>" by simp_all
            with m10 show ?thesis by (simp add: mm mma mmb)
          next
            assume m20: "m2 = \<bottom>"
            with le have "ma2 = \<bottom>" "mb2 = \<bottom>" by simp_all
            with m20 show ?thesis by (simp add: mm mma mmb)
          qed
        next
          case False
          then have m1nb: "m1 \<noteq> \<bottom>" and m2nb: "m2 \<noteq> \<bottom>" by simp_all
          have "ma1 \<noteq> \<bottom>" by (rule separating_glb_nonbottom[OF fs fdc m1 m1nb ab_j(1) a(2) ma1])
          moreover have "mb1 \<noteq> \<bottom>" by (rule separating_glb_nonbottom[OF fs fdc m1 m1nb ab_j(2) b(2) mb1])
          moreover have "ma2 \<noteq> \<bottom>" by (rule separating_glb_nonbottom[OF gs gdc m2 m2nb ab_j(3) a(3) ma2])
          moreover have "mb2 \<noteq> \<bottom>" by (rule separating_glb_nonbottom[OF gs gdc m2 m2nb ab_j(4) b(3) mb2])
          ultimately have "{(:ma1, ma2:), (:mb1, mb2:)} <<| (:m1, m2:)"
            using l1 l2 by (intro spair_is_lub_pair)
          with mm mma mmb show ?thesis by simp
        qed
      qed
    qed
  qed
qed

end