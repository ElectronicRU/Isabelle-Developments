theory Domain_Order
  imports Separated
begin

section \<open>Order structure of domain-package types\<close>

text \<open>The domain package presents each domain as isomorphic, through \<open>abs\<close> and \<open>rep\<close> satisfying
  the laws of @{locale iso}, to a combination of its constructor arguments.  An isomorphism of
  pointed cpos is an order isomorphism, so it preserves bounds, lubs and meets.

  For recursive domains the order classes are derived along the \<open>take\<close> chain: its \<open>Suc\<close> step is
  \<open>abs oo F(take n) oo rep\<close> with \<open>F\<close> built from \<open>ssum_map\<close>, \<open>sprod_map\<close>, \<open>u_map\<close> and \<open>ID\<close>, so
  each class property is stated for the image of a map (@{text lubs_on}, @{text sep_on},
  @{text distrib_on}) and pushed through these combinators.\<close>

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

subsection \<open>Class properties on the image of a map\<close>

text \<open>Each states the class property with one argument ranging over the image of \<open>f\<close> and the
  others arbitrary — exactly what the chain rules consume, and what passes through the
  combinators of a \<open>take\<close> step.\<close>

definition lubs_on :: "('a::pcpo \<rightarrow> 'a) \<Rightarrow> bool" where
  "lubs_on f \<longleftrightarrow> (\<forall>a b c. f\<cdot>a \<sqsubseteq> c \<longrightarrow> f\<cdot>b \<sqsubseteq> c \<longrightarrow> (\<exists>z. {f\<cdot>a, f\<cdot>b} <<| z))"

definition sep_on :: "('a::pcpo \<rightarrow> 'a) \<Rightarrow> bool" where
  "sep_on f \<longleftrightarrow> (\<forall>x y u. f\<cdot>x \<noteq> \<bottom> \<longrightarrow> f\<cdot>y \<noteq> \<bottom> \<longrightarrow> f\<cdot>x \<sqsubseteq> u \<longrightarrow> f\<cdot>y \<sqsubseteq> u \<longrightarrow>
    (\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> f\<cdot>x \<and> l \<sqsubseteq> f\<cdot>y))"

definition distrib_on :: "('a::bounded_complete \<rightarrow> 'a) \<Rightarrow> bool" where
  "distrib_on f \<longleftrightarrow> (\<forall>c a b. a \<Up> b \<longrightarrow> f\<cdot>c \<sqinter> (a \<squnion> b) = f\<cdot>c \<sqinter> a \<squnion> f\<cdot>c \<sqinter> b)"

lemma bounded_complete_takeI:
  fixes t :: "nat \<Rightarrow> 'a::dcpo \<rightarrow> 'a"
  assumes "chain t" "(\<Squnion>i. t i) = ID" "\<And>n. lubs_on (t n)"
  shows "OFCLASS('a, bounded_complete_class)"
  using assms(3) unfolding lubs_on_def by (intro bounded_complete_chainI[OF assms(1,2)]) blast

lemma distributive_cpo_takeI:
  fixes t :: "nat \<Rightarrow> 'a::{bifinite, bounded_complete} \<rightarrow> 'a"
  assumes "chain t" "(\<Squnion>i. t i) = ID" "\<And>n. distrib_on (t n)"
  shows "OFCLASS('a, distributive_cpo_class)"
  using assms(3) unfolding distrib_on_def by (intro distributive_cpo_chainI[OF assms(1,2)]) blast


subsection \<open>Map functionals\<close>

text \<open>The domain package defines \<open>T_map \<equiv> \<Lambda> v. \<mu> f. abs oo F v f oo rep\<close>, with \<open>F\<close> built from
  the rep-type combinators. A predicate preserved by \<open>F\<close> and holding at \<open>\<bottom>\<close> holds for the map
  by fixed-point induction, if admissible; at \<open>v = ID\<close> (\<open>T_map\<cdot>ID = ID\<close>) this yields the
  instance. Only the preservation step needs proof search.\<close>

definition preserves :: "(('a::pcpo \<rightarrow> 'a) \<Rightarrow> bool) \<Rightarrow> (('a \<rightarrow> 'a) \<rightarrow> ('a \<rightarrow> 'a)) \<Rightarrow> bool" where
  "preserves P F \<longleftrightarrow> (\<forall>f. P f \<longrightarrow> P (F\<cdot>f))"

lemma preservesI: "(\<And>f. P f \<Longrightarrow> P (F\<cdot>f)) \<Longrightarrow> preserves P F"
  by (simp add: preserves_def)

lemma preserves_LAM: "cont G \<Longrightarrow> (\<And>f. P f \<Longrightarrow> P (G f)) \<Longrightarrow> preserves P (\<Lambda> f. G f)"
  by (simp add: preserves_def)

lemma fix_preserves: "adm P \<Longrightarrow> P \<bottom> \<Longrightarrow> preserves P F \<Longrightarrow> P (fix\<cdot>F)"
  by (erule fix_ind) (simp_all add: preserves_def)

subsection \<open>Lubs of pairs through the combinators\<close>

lemma lubs_onI:
  "(\<And>a b c. f\<cdot>a \<sqsubseteq> c \<Longrightarrow> f\<cdot>b \<sqsubseteq> c \<Longrightarrow> \<exists>z. {f\<cdot>a, f\<cdot>b} <<| z) \<Longrightarrow> lubs_on f"
  by (simp add: lubs_on_def)

lemma lubs_onD:
  "lubs_on f \<Longrightarrow> f\<cdot>a \<sqsubseteq> c \<Longrightarrow> f\<cdot>b \<sqsubseteq> c \<Longrightarrow> \<exists>z. {f\<cdot>a, f\<cdot>b} <<| z"
  by (simp add: lubs_on_def)

lemma lubs_on_bottom: "lubs_on (\<bottom> :: 'a::pcpo \<rightarrow> 'a)"
  by (rule lubs_onI) (auto intro: is_lub_singleton)

lemma lubs_on_ID: "lubs_on (ID :: 'a::bounded_complete \<rightarrow> 'a)"
proof (rule lubs_onI)
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

lemma lubs_on_u_map: assumes f: "lubs_on f" shows "lubs_on (u_map\<cdot>f)"
proof (rule lubs_onI)
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
    from lubs_onD[OF f \<open>f\<cdot>x \<sqsubseteq> c'\<close> this] obtain z where "{f\<cdot>x, f\<cdot>y} <<| z" by (elim exE)
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

lemma lubs_on_ssum_map:
  assumes f: "lubs_on f" and g: "lubs_on g"
  shows "lubs_on (ssum_map\<cdot>f\<cdot>g)"
proof (rule lubs_onI)
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
      from lubs_onD[OF f \<open>f\<cdot>x \<sqsubseteq> w\<close> \<open>f\<cdot>y \<sqsubseteq> w\<close>] obtain z where "{f\<cdot>x, f\<cdot>y} <<| z" by (elim exE)
      then have "{sinl\<cdot>(f\<cdot>x), sinl\<cdot>(f\<cdot>y)} <<| (sinl\<cdot>z :: _ \<oplus> _)" by (rule sinl_is_lub_pair)
      with a b show ?thesis by auto
    next
      case (sinr w)
      obtain x where a: "a = sinr\<cdot>x" "x \<noteq> \<bottom>" "g\<cdot>x \<sqsubseteq> w"
        using ac A sinr by (cases a) auto
      obtain y where b: "b = sinr\<cdot>y" "y \<noteq> \<bottom>" "g\<cdot>y \<sqsubseteq> w"
        using bc B sinr by (cases b) auto
      from lubs_onD[OF g \<open>g\<cdot>x \<sqsubseteq> w\<close> \<open>g\<cdot>y \<sqsubseteq> w\<close>] obtain z where "{g\<cdot>x, g\<cdot>y} <<| z" by (elim exE)
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

lemma lubs_on_sprod_map:
  assumes f: "lubs_on f" and g: "lubs_on g"
  shows "lubs_on (sprod_map\<cdot>f\<cdot>g)"
proof (rule lubs_onI)
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
      using lubs_onD[OF f] lubs_onD[OF g] by meson
    then have "{(:f\<cdot>a1, g\<cdot>a2:), (:f\<cdot>b1, g\<cdot>b2:)} <<| (:z1, z2:)"
      using fa fb by (rule spair_is_lub_pair)
    with a b show ?thesis by auto
  qed
qed

lemma lubs_on_iso:
  fixes abs :: "'r::pcpo \<rightarrow> 't::pcpo" and rep
  assumes iso: "iso abs rep" and f: "lubs_on f"
  shows "lubs_on (abs oo f oo rep)"
proof (rule lubs_onI)
  interpret iso abs rep by (fact iso)
  fix a b c assume "(abs oo f oo rep)\<cdot>a \<sqsubseteq> c" "(abs oo f oo rep)\<cdot>b \<sqsubseteq> c"
  then have "f\<cdot>(rep\<cdot>a) \<sqsubseteq> rep\<cdot>c" "f\<cdot>(rep\<cdot>b) \<sqsubseteq> rep\<cdot>c" by (simp_all add: abs_below[symmetric])
  from lubs_onD[OF f this] obtain z :: 'r where z: "{f\<cdot>(rep\<cdot>a), f\<cdot>(rep\<cdot>b)} <<| z" by (elim exE)
  have "(\<lambda>x. rep\<cdot>x) ` {abs\<cdot>(f\<cdot>(rep\<cdot>a)), abs\<cdot>(f\<cdot>(rep\<cdot>b))} = {f\<cdot>(rep\<cdot>a), f\<cdot>(rep\<cdot>b)}" by simp
  with z have "{abs\<cdot>(f\<cdot>(rep\<cdot>a)), abs\<cdot>(f\<cdot>(rep\<cdot>b))} <<| abs\<cdot>z"
    by (simp only: iso_is_lub_iff[OF iso, symmetric])
  then show "\<exists>z. {(abs oo f oo rep)\<cdot>a, (abs oo f oo rep)\<cdot>b} <<| z" by auto
qed

lemma bounded_complete_lubs_onI:
  "lubs_on (ID :: 'a::dcpo \<rightarrow> 'a) \<Longrightarrow> OFCLASS('a, bounded_complete_class)"
  by (rule bounded_complete_takeI[of "\<lambda>n. ID"]) simp_all

subsection \<open>Separation through the combinators\<close>

lemma sep_onI:
  "(\<And>x y u. f\<cdot>x \<noteq> \<bottom> \<Longrightarrow> f\<cdot>y \<noteq> \<bottom> \<Longrightarrow> f\<cdot>x \<sqsubseteq> u \<Longrightarrow> f\<cdot>y \<sqsubseteq> u \<Longrightarrow> \<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> f\<cdot>x \<and> l \<sqsubseteq> f\<cdot>y)
    \<Longrightarrow> sep_on f"
  by (simp add: sep_on_def)

lemma sep_onE:
  assumes "sep_on f" "f\<cdot>x \<noteq> \<bottom>" "f\<cdot>y \<noteq> \<bottom>" "f\<cdot>x \<sqsubseteq> u" "f\<cdot>y \<sqsubseteq> u"
  obtains l where "l \<noteq> \<bottom>" "l \<sqsubseteq> f\<cdot>x" "l \<sqsubseteq> f\<cdot>y"
  using assms unfolding sep_on_def by blast

lemma sep_on_class: "sep_on (f :: 'a::{pcpo, separated_po} \<rightarrow> 'a)"
  by (rule sep_onI) (rule separated_pcpo)

lemma sep_on_ID: "sep_on (ID :: 'a::{pcpo, separated_po} \<rightarrow> 'a)"
  by (rule sep_on_class)

lemma sep_on_bottom: "sep_on \<bottom>"
  by (rule sep_onI) simp

lemma sep_on_u_map: "sep_on (u_map\<cdot>(f :: 'a::pcpo \<rightarrow> 'a))"
proof (rule sep_onI)
  fix x y u assume "u_map\<cdot>f\<cdot>x \<noteq> \<bottom>" "u_map\<cdot>f\<cdot>y \<noteq> \<bottom>" "u_map\<cdot>f\<cdot>x \<sqsubseteq> u" "u_map\<cdot>f\<cdot>y \<sqsubseteq> u"
  then obtain x' y' where "x = up\<cdot>x'" "y = up\<cdot>y'" by (cases x; cases y) auto
  then have "up\<cdot>\<bottom> \<noteq> \<bottom> \<and> up\<cdot>\<bottom> \<sqsubseteq> u_map\<cdot>f\<cdot>x \<and> up\<cdot>\<bottom> \<sqsubseteq> u_map\<cdot>f\<cdot>y" by simp
  then show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> u_map\<cdot>f\<cdot>x \<and> l \<sqsubseteq> u_map\<cdot>f\<cdot>y" ..
qed

lemma sep_on_ssum_map:
  assumes f: "sep_on f" and g: "sep_on g"
  shows "sep_on (ssum_map\<cdot>f\<cdot>g)"
proof (rule sep_onI)
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
      by (rule sep_onE)
    with sinl y' show ?thesis by (intro exI[of _ "sinl\<cdot>l"]) simp
  next
    case (sinr x')
    with A have gx: "g\<cdot>x' \<noteq> \<bottom>" by simp
    with sinr xu obtain u' where u: "u = sinr\<cdot>u'" "g\<cdot>x' \<sqsubseteq> u'" by (cases u) auto
    with B yu obtain y' where y': "y = sinr\<cdot>y'" "y' \<noteq> \<bottom>" "g\<cdot>y' \<noteq> \<bottom>" "g\<cdot>y' \<sqsubseteq> u'"
      by (cases y) auto
    from g gx \<open>g\<cdot>y' \<noteq> \<bottom>\<close> \<open>g\<cdot>x' \<sqsubseteq> u'\<close> \<open>g\<cdot>y' \<sqsubseteq> u'\<close> obtain l where "l \<noteq> \<bottom>" "l \<sqsubseteq> g\<cdot>x'" "l \<sqsubseteq> g\<cdot>y'"
      by (rule sep_onE)
    with sinr y' show ?thesis by (intro exI[of _ "sinr\<cdot>l"]) simp
  qed
qed

lemma sep_on_sprod_map:
  assumes f: "sep_on f" and g: "sep_on g"
  shows "sep_on (sprod_map\<cdot>f\<cdot>g)"
proof (rule sep_onI)
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
    by (rule sep_onE)
  moreover from g fx(2) fy(2) xu'(2) yu'(2) obtain l2 where "l2 \<noteq> \<bottom>" "l2 \<sqsubseteq> g\<cdot>x2" "l2 \<sqsubseteq> g\<cdot>y2"
    by (rule sep_onE)
  ultimately show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> sprod_map\<cdot>f\<cdot>g\<cdot>x \<and> l \<sqsubseteq> sprod_map\<cdot>f\<cdot>g\<cdot>y"
    using x y fx fy by (intro exI[of _ "(:l1, l2:)"]) (simp add: below_sprod)
qed

lemma sep_on_iso:
  fixes abs :: "'r::pcpo \<rightarrow> 't::pcpo" and rep
  assumes iso: "iso abs rep" and f: "sep_on f"
  shows "sep_on (abs oo f oo rep)"
proof (rule sep_onI)
  interpret iso abs rep by (fact iso)
  fix x y u
  assume "(abs oo f oo rep)\<cdot>x \<noteq> \<bottom>" "(abs oo f oo rep)\<cdot>y \<noteq> \<bottom>"
    "(abs oo f oo rep)\<cdot>x \<sqsubseteq> u" "(abs oo f oo rep)\<cdot>y \<sqsubseteq> u"
  then have "f\<cdot>(rep\<cdot>x) \<noteq> \<bottom>" "f\<cdot>(rep\<cdot>y) \<noteq> \<bottom>" "f\<cdot>(rep\<cdot>x) \<sqsubseteq> rep\<cdot>u" "f\<cdot>(rep\<cdot>y) \<sqsubseteq> rep\<cdot>u"
    by (simp_all add: abs_below[symmetric] abs_bottom_iff)
  with f obtain l where "l \<noteq> \<bottom>" "l \<sqsubseteq> f\<cdot>(rep\<cdot>x)" "l \<sqsubseteq> f\<cdot>(rep\<cdot>y)" by (elim sep_onE)
  then show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> (abs oo f oo rep)\<cdot>x \<and> l \<sqsubseteq> (abs oo f oo rep)\<cdot>y"
    by (intro exI[of _ "abs\<cdot>l"]) (simp add: abs_below[symmetric] abs_bottom_iff)
qed

subsection \<open>Image-determined predicates\<close>

text \<open>The predicates only look at the image of a map, and only get weaker on smaller images.\<close>

definition image_antitone :: "(('a \<rightarrow> 'a) \<Rightarrow> bool) \<Rightarrow> bool" where
  "image_antitone P \<longleftrightarrow> (\<forall>f g. range (Rep_cfun g) \<subseteq> range (Rep_cfun f) \<longrightarrow> P f \<longrightarrow> P g)"

lemma image_antitoneI:
  "(\<And>f g. range (Rep_cfun g) \<subseteq> range (Rep_cfun f) \<Longrightarrow> P f \<Longrightarrow> P g) \<Longrightarrow> image_antitone P"
  by (simp add: image_antitone_def)

lemma image_antitoneD:
  "image_antitone P \<Longrightarrow> range (Rep_cfun g) \<subseteq> range (Rep_cfun f) \<Longrightarrow> P f \<Longrightarrow> P g"
  by (simp add: image_antitone_def)

lemma image_antitone_oo: "image_antitone P \<Longrightarrow> P f \<Longrightarrow> P (f oo g)"
  by (erule image_antitoneD) auto

lemma image_antitone_ID: "image_antitone P \<Longrightarrow> P ID \<Longrightarrow> P g"
  by (erule image_antitoneD) auto

lemma image_antitone_lubs_on: "image_antitone lubs_on"
proof (rule image_antitoneI)
  fix f g :: "'a \<rightarrow> 'a"
  assume sub: "range (Rep_cfun g) \<subseteq> range (Rep_cfun f)" and f: "lubs_on f"
  show "lubs_on g"
  proof (rule lubs_onI)
    fix a b c assume "g\<cdot>a \<sqsubseteq> c" "g\<cdot>b \<sqsubseteq> c"
    moreover from sub obtain a' b' where "g\<cdot>a = f\<cdot>a'" "g\<cdot>b = f\<cdot>b'" by blast
    ultimately show "\<exists>z. {g\<cdot>a, g\<cdot>b} <<| z" using lubs_onD[OF f] by simp
  qed
qed

lemma image_antitone_sep_on: "image_antitone sep_on"
proof (rule image_antitoneI)
  fix f g :: "'a \<rightarrow> 'a"
  assume sub: "range (Rep_cfun g) \<subseteq> range (Rep_cfun f)" and f: "sep_on f"
  show "sep_on g"
  proof (rule sep_onI)
    fix x y u assume "g\<cdot>x \<noteq> \<bottom>" "g\<cdot>y \<noteq> \<bottom>" "g\<cdot>x \<sqsubseteq> u" "g\<cdot>y \<sqsubseteq> u"
    moreover from sub obtain x' y' where xy: "g\<cdot>x = f\<cdot>x'" "g\<cdot>y = f\<cdot>y'" by blast
    ultimately have "f\<cdot>x' \<noteq> \<bottom>" "f\<cdot>y' \<noteq> \<bottom>" "f\<cdot>x' \<sqsubseteq> u" "f\<cdot>y' \<sqsubseteq> u" by simp_all
    with f obtain l where "l \<noteq> \<bottom>" "l \<sqsubseteq> f\<cdot>x'" "l \<sqsubseteq> f\<cdot>y'" by (elim sep_onE)
    with xy show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> g\<cdot>x \<and> l \<sqsubseteq> g\<cdot>y" by auto
  qed
qed

lemmas lubs_on_oo = image_antitone_oo[OF image_antitone_lubs_on]
lemmas sep_on_oo = image_antitone_oo[OF image_antitone_sep_on]
lemmas lubs_on_from_ID = image_antitone_ID[OF image_antitone_lubs_on]
lemmas sep_on_from_ID = image_antitone_ID[OF image_antitone_sep_on]

subsection \<open>Admissibility\<close>

text \<open>The predicates only constrain the image of a map, and the image of a chain's lub is
  approximated by the images of its members; so they are admissible.\<close>

lemma adm_lubs_on: "adm (lubs_on :: ('a::pcpo \<rightarrow> 'a) \<Rightarrow> bool)"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'a" assume Y: "chain Y" and P: "\<forall>i. lubs_on (Y i)"
  have chx: "chain (\<lambda>n. Y n\<cdot>x)" for x by (rule ch2ch_Rep_cfunL[OF Y])
  have reach: "(\<Squnion>n. Y n\<cdot>x) = (\<Squnion>i. Y i)\<cdot>x" for x by (rule contlub_cfun_fun[OF Y, symmetric])
  have below: "Y n\<cdot>x \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x" for n x
    using is_ub_thelub[OF chx, of n x] by (simp only: reach)
  show "lubs_on (\<Squnion>i. Y i)"
  proof (rule lubs_onI)
    fix a b c assume ac: "(\<Squnion>i. Y i)\<cdot>a \<sqsubseteq> c" and bc: "(\<Squnion>i. Y i)\<cdot>b \<sqsubseteq> c"
    define L where "L n = lub {Y n\<cdot>a, Y n\<cdot>b}" for n
    have L: "{Y n\<cdot>a, Y n\<cdot>b} <<| L n" for n
    proof -
      have "Y n\<cdot>a \<sqsubseteq> c" "Y n\<cdot>b \<sqsubseteq> c"
        using below_trans[OF below[of n a] ac] below_trans[OF below[of n b] bc] .
      from lubs_onD[OF P[rule_format] this] obtain z where "{Y n\<cdot>a, Y n\<cdot>b} <<| z" by (elim exE)
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

lemma adm_sep_on: "adm (sep_on :: ('a::pcpo \<rightarrow> 'a) \<Rightarrow> bool)"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'a" assume Y: "chain Y" and P: "\<forall>i. sep_on (Y i)"
  have chx: "chain (\<lambda>n. Y n\<cdot>x)" for x by (rule ch2ch_Rep_cfunL[OF Y])
  have reach: "(\<Squnion>n. Y n\<cdot>x) = (\<Squnion>i. Y i)\<cdot>x" for x by (rule contlub_cfun_fun[OF Y, symmetric])
  have below: "Y n\<cdot>x \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x" for n x
    using is_ub_thelub[OF chx, of n x] by (simp only: reach)
  show "sep_on (\<Squnion>i. Y i)"
  proof (rule sep_onI)
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
      by (elim sep_onE)
    then show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>x \<and> l \<sqsubseteq> (\<Squnion>i. Y i)\<cdot>y"
      using below_trans[OF _ below[of k x]] below_trans[OF _ below[of k y]] by blast
  qed
qed

lemma separated_po_sep_onI:
  assumes "sep_on (ID :: 'a::pcpo \<rightarrow> 'a)"
  shows "OFCLASS('a, separated_po_class)"
proof (rule separated_poI)
  fix x y u :: 'a
  assume "x \<noteq> \<bottom>" "y \<noteq> \<bottom>" "x \<sqsubseteq> u" "y \<sqsubseteq> u"
  then have "ID\<cdot>x \<noteq> \<bottom>" "ID\<cdot>y \<noteq> \<bottom>" "ID\<cdot>x \<sqsubseteq> u" "ID\<cdot>y \<sqsubseteq> u" by simp_all
  with assms obtain l where "l \<noteq> \<bottom>" "l \<sqsubseteq> ID\<cdot>x" "l \<sqsubseteq> ID\<cdot>y" by (elim sep_onE)
  then show "\<exists>l. l \<noteq> \<bottom> \<and> l \<sqsubseteq> x \<and> l \<sqsubseteq> y" by auto
qed

lemma separated_po_takeI:
  fixes t :: "nat \<Rightarrow> 'a::pcpo \<rightarrow> 'a"
  assumes t: "chain t" "(\<Squnion>i. t i) = ID" and P: "\<And>n. sep_on (t n)"
  shows "OFCLASS('a, separated_po_class)"
proof (rule separated_po_sep_onI)
  have "sep_on (\<Squnion>i. t i)" by (rule admD[OF adm_sep_on t(1) P])
  then show "sep_on (ID :: 'a \<rightarrow> 'a)" by (simp only: t(2))
qed


lemma adm_distrib_on: "adm (distrib_on :: ('a::{bifinite, bounded_complete} \<rightarrow> 'a) \<Rightarrow> bool)"
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a \<rightarrow> 'a" assume Y: "chain Y" and P: "\<forall>i. distrib_on (Y i)"
  show "distrib_on (\<Squnion>i. Y i)"
    unfolding distrib_on_def
  proof (intro allI impI)
    fix c a b :: 'a assume "a \<Up> b"
    have ch: "chain (\<lambda>n. Y n\<cdot>c)" by (rule ch2ch_Rep_cfunL[OF Y])
    have reach: "(\<Squnion>n. Y n\<cdot>c) = (\<Squnion>i. Y i)\<cdot>c" by (rule contlub_cfun_fun[OF Y, symmetric])
    have lim: "(\<Squnion>i. Y i)\<cdot>c \<sqinter> y = (\<Squnion>n. Y n\<cdot>c \<sqinter> y)" and chy: "chain (\<lambda>n. Y n\<cdot>c \<sqinter> y)" for y
      using cont2contlubE[OF cont_meet_arg ch, of y] ch2ch_cont[OF cont_meet_arg ch, of y]
      by (simp_all add: reach)
    have law: "Y n\<cdot>c \<sqinter> (a \<squnion> b) = Y n\<cdot>c \<sqinter> a \<squnion> Y n\<cdot>c \<sqinter> b" for n
      using P \<open>a \<Up> b\<close> unfolding distrib_on_def by blast
    have j: "Y n\<cdot>c \<sqinter> a \<Up> Y n\<cdot>c \<sqinter> b" for n by (rule joinableI[OF meet_below1 meet_below1])
    have "(\<Squnion>i. Y i)\<cdot>c \<sqinter> (a \<squnion> b) = (\<Squnion>n. Y n\<cdot>c \<sqinter> (a \<squnion> b))" by (rule lim)
    also have "\<dots> = (\<Squnion>n. Y n\<cdot>c \<sqinter> a \<squnion> Y n\<cdot>c \<sqinter> b)" by (simp only: law)
    also have "\<dots> = (\<Squnion>n. Y n\<cdot>c \<sqinter> a) \<squnion> (\<Squnion>n. Y n\<cdot>c \<sqinter> b)" by (rule lub_join_chains(3)[OF chy chy j])
    also have "\<dots> = (\<Squnion>i. Y i)\<cdot>c \<sqinter> a \<squnion> (\<Squnion>i. Y i)\<cdot>c \<sqinter> b" by (simp only: lim[symmetric])
    finally show "(\<Squnion>i. Y i)\<cdot>c \<sqinter> (a \<squnion> b) = (\<Squnion>i. Y i)\<cdot>c \<sqinter> a \<squnion> (\<Squnion>i. Y i)\<cdot>c \<sqinter> b" .
  qed
qed

end
