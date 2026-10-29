theory Pointed_Profinite
  imports HOLCF
begin

section \<open>Pointed profinite domains are bifinite\<close>

text \<open>A profinite cpo has an approximation chain on its lifting.  If it is pointed, lowering back
  through \<open>fup\<cdot>ID\<close> gives one on the cpo itself: \<open>up\<close> followed by \<open>fup\<cdot>ID\<close> is the identity, and \<open>fup\<cdot>ID\<close>
  followed by \<open>up\<close> is above it, so the lowered finite deflations stay idempotent.\<close>

lemma up_fup_ID_above: "y \<sqsubseteq> up\<cdot>(fup\<cdot>ID\<cdot>y)"
  by (cases y) simp_all

lemma approx_chain_lower:
  assumes d: "approx_chain (d :: nat \<Rightarrow> 'a::pcpo u \<rightarrow> 'a u)"
  shows "approx_chain (\<lambda>i. fup\<cdot>ID oo d i oo up)"
proof (rule approx_chain.intro)
  interpret approx_chain d by (fact d)
  show "chain (\<lambda>i. fup\<cdot>ID oo d i oo up)"
    by (rule chainI, rule cfun_belowI) (simp add: monofun_cfun_arg monofun_cfun_fun[OF chainE[OF chain_approx]])
  then show "(\<Squnion>i. fup\<cdot>ID oo d i oo up) = ID"
  proof (intro cfun_eqI)
    fix x assume c: "chain (\<lambda>i. fup\<cdot>ID oo d i oo up)"
    have "(\<Squnion>i. fup\<cdot>ID\<cdot>(d i\<cdot>(up\<cdot>x))) = fup\<cdot>ID\<cdot>(\<Squnion>i. d i\<cdot>(up\<cdot>x))"
      by (rule cont2contlubE[OF cont_Rep_cfun2 ch2ch_Rep_cfunL[OF chain_approx], symmetric])
    then show "(\<Squnion>i. fup\<cdot>ID oo d i oo up)\<cdot>x = ID\<cdot>x"
      by (simp add: contlub_cfun_fun[OF c] contlub_cfun_fun[OF chain_approx, symmetric])
  qed
  show "finite_deflation (fup\<cdot>ID oo d i oo up)" for i
  proof -
    interpret d: finite_deflation "d i" by simp
    let ?c = "fup\<cdot>ID oo d i oo up"
    have below: "?c\<cdot>x \<sqsubseteq> x" for x
    proof -
      have "fup\<cdot>ID\<cdot>(d i\<cdot>(up\<cdot>x)) \<sqsubseteq> fup\<cdot>ID\<cdot>(up\<cdot>x)" by (rule monofun_cfun_arg[OF d.below])
      then show ?thesis by simp
    qed
    have idem: "?c\<cdot>(?c\<cdot>x) = ?c\<cdot>x" for x
    proof (rule below_antisym[OF below])
      have "d i\<cdot>(up\<cdot>x) \<sqsubseteq> up\<cdot>(fup\<cdot>ID\<cdot>(d i\<cdot>(up\<cdot>x)))" by (rule up_fup_ID_above)
      then have "d i\<cdot>(d i\<cdot>(up\<cdot>x)) \<sqsubseteq> d i\<cdot>(up\<cdot>(fup\<cdot>ID\<cdot>(d i\<cdot>(up\<cdot>x))))" by (rule monofun_cfun_arg)
      then show "?c\<cdot>x \<sqsubseteq> ?c\<cdot>(?c\<cdot>x)" by (simp add: d.idem monofun_cfun_arg)
    qed
    have fin: "finite {x. ?c\<cdot>x = x}"
    proof (rule finite_subset)
      show "{x. ?c\<cdot>x = x} \<subseteq> (\<lambda>y. fup\<cdot>ID\<cdot>y) ` {y. d i\<cdot>y = y}"
      proof
        fix x assume "x \<in> {x. ?c\<cdot>x = x}"
        then have "x = fup\<cdot>ID\<cdot>(d i\<cdot>(up\<cdot>x))" by simp
        moreover have "d i\<cdot>(d i\<cdot>(up\<cdot>x)) = d i\<cdot>(up\<cdot>x)" by (rule d.idem)
        ultimately show "x \<in> (\<lambda>y. fup\<cdot>ID\<cdot>y) ` {y. d i\<cdot>y = y}" by blast
      qed
      show "finite ((\<lambda>y. fup\<cdot>ID\<cdot>y) ` {y. d i\<cdot>y = y})" using d.finite_fixes by simp
    qed
    show ?thesis unfolding finite_deflation_def finite_deflation_axioms_def deflation_def
      using below idem fin by blast
  qed
qed

lemma bifinite_profinite_pointed: "OFCLASS('a::{profinite, pcpo}, bifinite_class)"
proof
  obtain d :: "nat \<Rightarrow> 'a u \<rightarrow> 'a u" where "approx_chain d" using profinite by blast
  then show "\<exists>a :: nat \<Rightarrow> 'a \<rightarrow> 'a. approx_chain a" by (blast intro: approx_chain_lower)
qed

section \<open>Pointed types with a domain as lifting are domains\<close>

text \<open>\<open>fup\<cdot>(strictify\<cdot>up)\<close> drops the lifted bottom: it fixes everything but \<open>up\<cdot>\<bottom>\<close>.\<close>

lemma fup_strictify_up_simps [simp]:
  "fup\<cdot>(strictify\<cdot>up)\<cdot>(up\<cdot>x) = (if x = \<bottom> then \<bottom> else up\<cdot>x)"
  by (simp add: strictify_conv_if)

lemma fup_strictify_up_idem [simp]: "fup\<cdot>(strictify\<cdot>up)\<cdot>(fup\<cdot>(strictify\<cdot>up)\<cdot>x) = fup\<cdot>(strictify\<cdot>up)\<cdot>x"
  by (cases x) (simp_all add: strictify_conv_if)

lemma strictify_up_fup_ID: "strictify\<cdot>up oo fup\<cdot>ID = fup\<cdot>(strictify\<cdot>up)"
  by (rule cfun_eqI, case_tac x) (simp_all add: strictify_conv_if)

lemma ep_pair_strictify_up: "ep_pair (strictify\<cdot>up) (fup\<cdot>(ID :: 'a::pcpo \<rightarrow> 'a))"
proof
  show "fup\<cdot>ID\<cdot>(strictify\<cdot>up\<cdot>x) = x" for x :: 'a by (simp add: strictify_conv_if)
  show "strictify\<cdot>up\<cdot>(fup\<cdot>ID\<cdot>y) \<sqsubseteq> y" for y :: "'a u" by (cases y) (simp_all add: strictify_conv_if)
qed

text \<open>A deflation that sends each point to itself or to bottom stays a finite deflation after
  any finite deflation: its fixes are the other one's, less those it kills.\<close>

lemma finite_deflation_cut_comp:
  assumes c: "deflation c" and cut: "\<And>y. c\<cdot>y = y \<or> c\<cdot>y = \<bottom>" and d: "finite_deflation d"
  shows "finite_deflation (c oo d)"
proof -
  interpret c: deflation c by (fact c)
  interpret d: finite_deflation d by (fact d)
  have db: "d\<cdot>\<bottom> = \<bottom>" by (rule bottomI[OF d.below])
  have cb: "c\<cdot>\<bottom> = \<bottom>" by (rule bottomI[OF c.below])
  have idem: "c\<cdot>(d\<cdot>(c\<cdot>(d\<cdot>x))) = c\<cdot>(d\<cdot>x)" for x
    using cut[of "d\<cdot>x"] by (auto simp: d.idem db cb)
  have below: "c\<cdot>(d\<cdot>x) \<sqsubseteq> x" for x by (rule below_trans[OF c.below d.below])
  have fin: "finite {x. c\<cdot>(d\<cdot>x) = x}"
  proof (rule finite_subset[OF _ d.finite_fixes])
    show "{x. c\<cdot>(d\<cdot>x) = x} \<subseteq> {x. d\<cdot>x = x}"
    proof
      fix x assume x: "x \<in> {x. c\<cdot>(d\<cdot>x) = x}"
      then show "x \<in> {x. d\<cdot>x = x}" using cut[of "d\<cdot>x"] by (auto simp: d.idem db)
    qed
  qed
  show ?thesis unfolding finite_deflation_def finite_deflation_axioms_def deflation_def
    using idem below fin by simp
qed

text \<open>The top algebraic deflation of a bifinite type: the one cast to the identity.\<close>

definition defl_top :: "'a::bifinite defl" where
  "defl_top = (THE t. cast\<cdot>t = ID)"

lemma cast_defl_top: "cast\<cdot>(defl_top :: 'a::bifinite defl) = ID"
proof -
  obtain a :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where a: "approx_chain a" using bifinite by blast
  interpret a: approx_chain a by (fact a)
  let ?d = "\<lambda>i. Abs_fin_defl (a i)"
  have R: "Rep_fin_defl (?d i) = a i" for i by (simp add: Abs_fin_defl_inverse)
  have ch: "chain (\<lambda>i. defl_principal (?d i))"
    by (rule chainI, rule defl.principal_mono) (simp add: below_fin_defl_def R chainE[OF a.chain_approx])
  have "cast\<cdot>(\<Squnion>i. defl_principal (?d i)) = ID"
    by (simp add: contlub_cfun_arg[OF ch] cast_defl_principal R)
  then have ex: "\<exists>t :: 'a defl. cast\<cdot>t = ID" by blast
  have un: "s = t" if "cast\<cdot>s = ID" "cast\<cdot>t = (ID :: 'a \<rightarrow> 'a)" for s t :: "'a defl"
    using that by (simp add: below_antisym cast_below_cast[symmetric])
  show ?thesis unfolding defl_top_def by (rule theI'[of "\<lambda>t. cast\<cdot>t = ID"]) (use ex un in blast)
qed

text \<open>Temporarily relax the type constraints of the domain operations, as HOLCF does for
  \<open>typedef_domain_class\<close>.\<close>

setup \<open>
  fold Sign.add_const_constraint
  [ (\<^const_name>\<open>defl\<close>, SOME \<^typ>\<open>'a::pcpo itself \<Rightarrow> udom defl\<close>)
  , (\<^const_name>\<open>emb\<close>, SOME \<^typ>\<open>'a::pcpo \<rightarrow> udom\<close>)
  , (\<^const_name>\<open>prj\<close>, SOME \<^typ>\<open>udom \<rightarrow> 'a::pcpo\<close>)
  , (\<^const_name>\<open>liftdefl\<close>, SOME \<^typ>\<open>'a::pcpo itself \<Rightarrow> udom u defl\<close>)
  , (\<^const_name>\<open>liftemb\<close>, SOME \<^typ>\<open>'a::pcpo u \<rightarrow> udom u\<close>)
  , (\<^const_name>\<open>liftprj\<close>, SOME \<^typ>\<open>udom u \<rightarrow> 'a::pcpo u\<close>) ]
\<close>

text \<open>The deflation of a pointed type whose lifting is isomorphic to a domain: the domain's top
  one with the lifted bottom dropped.\<close>

definition unlift_defl :: "('a::pcpo u \<rightarrow> 'b::domain) \<Rightarrow> ('b \<rightarrow> 'a u) \<Rightarrow> udom defl" where
  "unlift_defl f g = defl_fun1 emb prj (\<Lambda> d. (f oo fup\<cdot>(strictify\<cdot>up) oo g) oo d)\<cdot>(defl_top :: 'b defl)"

text \<open>A pointed type whose lifting is isomorphic to a domain is a domain: embed by strict lifting,
  the isomorphism and the domain's embedding; the deflation is the domain's top one with the
  lifted bottom dropped.\<close>

lemma domain_class_lift_iso:
  fixes f :: "'a::pcpo u \<rightarrow> 'b::domain" and g :: "'b \<rightarrow> 'a u"
  assumes gf: "\<And>x. g\<cdot>(f\<cdot>x) = x" and fg: "\<And>y. f\<cdot>(g\<cdot>y) = y"
    and emb: "(emb :: 'a \<rightarrow> udom) = emb oo f oo strictify\<cdot>up"
    and prj: "(prj :: udom \<rightarrow> 'a) = fup\<cdot>ID oo g oo prj"
    and defl: "(defl :: 'a itself \<Rightarrow> udom defl) = (\<lambda>_. unlift_defl f g)"
    and liftemb: "(liftemb :: 'a u \<rightarrow> udom u) = u_map\<cdot>emb"
    and liftprj: "(liftprj :: udom u \<rightarrow> 'a u) = u_map\<cdot>prj"
    and liftdefl: "(liftdefl :: 'a itself \<Rightarrow> udom u defl) = (\<lambda>t. liftdefl_of\<cdot>DEFL('a))"
  shows "OFCLASS('a, domain_class)"
proof
  have efg: "ep_pair f g" by (simp add: ep_pair_def gf fg)
  interpret fg: pcpo_ep_pair f g unfolding pcpo_ep_pair_def by (fact efg)
  have "ep_pair (f oo strictify\<cdot>up) (fup\<cdot>ID oo g)" by (rule ep_pair_comp[OF ep_pair_strictify_up efg])
  then have "ep_pair ((emb :: 'b \<rightarrow> udom) oo (f oo strictify\<cdot>up)) ((fup\<cdot>ID oo g) oo prj)"
    by (rule ep_pair_comp[OF _ ep_pair_emb_prj])
  then show "ep_pair (emb :: 'a \<rightarrow> udom) prj" unfolding emb prj by (simp only: assoc_oo)
  let ?c = "f oo fup\<cdot>(strictify\<cdot>up) oo g"
  have cut: "?c\<cdot>y = y \<or> ?c\<cdot>y = \<bottom>" for y
  proof (cases "g\<cdot>y")
    case bottom
    then have "f\<cdot>\<bottom> = y" using fg[of y] by simp
    then show ?thesis using bottom by simp
  next
    case (up x)
    then show ?thesis using fg[of y] by (auto simp: fg.e_strict strictify_conv_if)
  qed
  have dc: "deflation ?c"
  proof
    show "?c\<cdot>(?c\<cdot>y) = ?c\<cdot>y" for y
      using cut[of y] by (auto simp: fg.e_strict fg.p_strict)
    show "?c\<cdot>y \<sqsubseteq> y" for y using cut[of y] by auto
  qed
  have F: "finite_deflation ((\<Lambda> d. ?c oo d)\<cdot>d)" if "finite_deflation d" for d
    using finite_deflation_cut_comp[OF dc cut that] by simp
  have "cast\<cdot>(defl_fun1 emb prj (\<Lambda> d. ?c oo d)\<cdot>(defl_top :: 'b defl))
      = (emb :: 'b \<rightarrow> udom) oo (\<Lambda> d. ?c oo d)\<cdot>(cast\<cdot>defl_top) oo prj"
    by (rule cast_defl_fun1[OF ep_pair_emb_prj F])
  then have "cast\<cdot>DEFL('a) = (emb :: 'b \<rightarrow> udom) oo ?c oo cast\<cdot>(defl_top :: 'b defl) oo prj"
    unfolding defl unlift_defl_def by (simp add: assoc_oo)
  also have "\<dots> = emb oo (prj :: udom \<rightarrow> 'a)"
    unfolding emb prj cast_defl_top by (simp add: assoc_oo strictify_up_fup_ID[symmetric] cfcomp1)
  finally show "cast\<cdot>DEFL('a) = emb oo (prj :: udom \<rightarrow> 'a)" .
qed (simp_all only: liftemb liftprj liftdefl)

setup \<open>
  fold Sign.add_const_constraint
   [(\<^const_name>\<open>defl\<close>, SOME \<^typ>\<open>'a::domain itself \<Rightarrow> udom defl\<close>),
    (\<^const_name>\<open>emb\<close>, SOME \<^typ>\<open>'a::domain \<rightarrow> udom\<close>),
    (\<^const_name>\<open>prj\<close>, SOME \<^typ>\<open>udom \<rightarrow> 'a::domain\<close>),
    (\<^const_name>\<open>liftdefl\<close>, SOME \<^typ>\<open>'a::predomain itself \<Rightarrow> udom u defl\<close>),
    (\<^const_name>\<open>liftemb\<close>, SOME \<^typ>\<open>'a::predomain u \<rightarrow> udom u\<close>),
    (\<^const_name>\<open>liftprj\<close>, SOME \<^typ>\<open>udom u \<rightarrow> 'a::predomain u\<close>)]
\<close>

end
