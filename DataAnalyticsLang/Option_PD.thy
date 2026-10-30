theory Option_PD
  imports HOLCF "HOLCF-Library.Option_Cpo" "HOLCF-Library.List_Predomain" "HOLCF-extra.Pointed_Profinite"
begin

section \<open>Results with possible absence\<close>

text \<open>A result is a set of possible outcomes, each either absent (\<open>None\<close>) or a value: an element
  of the upper powerdomain over the lifted outcomes, without its bottom.  The one element of the
  powerdomain that contains the lifted bottom is its bottom, so the rest is a cpo; it is pointed
  again, by \<open>{None, Some \<bottom>}\<close>: possibly absent, otherwise an unknown value.  A definite absence is
  \<open>{None}\<close>, a definite value \<open>v\<close> is \<open>{Some v}\<close>, and \<open>{None, Some v}\<close> is the value \<open>v\<close>, if present.\<close>

subsection \<open>Options of profinite cpos are profinite\<close>

text \<open>An approximation chain of the lifting \<open>'a\<^sub>\<bottom>\<close> extends to \<open>('a option)\<^sub>\<bottom>\<close>, fixing \<open>None\<close>.\<close>

definition option_approx :: "(nat \<Rightarrow> 'a::cpo u \<rightarrow> 'a u) \<Rightarrow> nat \<Rightarrow> 'a option u \<rightarrow> 'a option u" where
  "option_approx d i = fup\<cdot>(\<Lambda> z. case z of None \<Rightarrow> up\<cdot>None | Some x \<Rightarrow> fup\<cdot>(\<Lambda> y. up\<cdot>(Some y))\<cdot>(d i\<cdot>(up\<cdot>x)))"

lemma option_approx_simps [simp]:
  "option_approx d i\<cdot>\<bottom> = \<bottom>" "option_approx d i\<cdot>(up\<cdot>None) = up\<cdot>None"
  "option_approx d i\<cdot>(up\<cdot>(Some x)) = fup\<cdot>(\<Lambda> y. up\<cdot>(Some y))\<cdot>(d i\<cdot>(up\<cdot>x))"
  by (simp_all add: option_approx_def)

lemma approx_chain_option_approx:
  assumes a: "approx_chain d"
  shows "approx_chain (option_approx d)"
proof (rule approx_chain.intro)
  interpret approx_chain d by (fact a)
  let ?s = "fup\<cdot>(\<Lambda> y. up\<cdot>(Some y)) :: 'a u \<rightarrow> 'a option u"
  have s_up [simp]: "?s\<cdot>(up\<cdot>x) = up\<cdot>(Some x)" for x by simp
  have cases3: "P z" if "P \<bottom>" "P (up\<cdot>None)" "\<And>x. P (up\<cdot>(Some x))" for P and z :: "'a option u"
  proof (cases z)
    case (up w) with that show ?thesis by (cases w) simp_all
  qed (simp add: that)
  show c: "chain (\<lambda>i. option_approx d i)"
  proof (rule chainI, rule cfun_belowI)
    fix i and z :: "'a option u"
    show "option_approx d i\<cdot>z \<sqsubseteq> option_approx d (Suc i)\<cdot>z"
      by (rule cases3[of _ z]) (simp_all add: monofun_cfun_arg monofun_cfun_fun[OF chainE[OF chain_approx]])
  qed
  show "(\<Squnion>i. option_approx d i) = ID"
  proof (rule cfun_eqI)
    fix z :: "'a option u"
    show "(\<Squnion>i. option_approx d i)\<cdot>z = ID\<cdot>z"
    proof (rule cases3[of _ z])
      fix x
      have "(\<Squnion>i. ?s\<cdot>(d i\<cdot>(up\<cdot>x))) = ?s\<cdot>(\<Squnion>i. d i\<cdot>(up\<cdot>x))"
        by (rule contlub_cfun_arg[OF ch2ch_Rep_cfunL[OF chain_approx], symmetric])
      then show "(\<Squnion>i. option_approx d i)\<cdot>(up\<cdot>(Some x)) = ID\<cdot>(up\<cdot>(Some x))"
        by (simp add: contlub_cfun_fun[OF c] contlub_cfun_fun[OF chain_approx, symmetric])
    qed (simp_all add: contlub_cfun_fun[OF c])
  qed
  show "finite_deflation (option_approx d i)" for i
  proof -
    interpret d: finite_deflation "d i" by simp
    have idem: "option_approx d i\<cdot>(option_approx d i\<cdot>z) = option_approx d i\<cdot>z" for z
    proof (rule cases3[of _ z])
      fix x show "option_approx d i\<cdot>(option_approx d i\<cdot>(up\<cdot>(Some x))) = option_approx d i\<cdot>(up\<cdot>(Some x))"
        using d.idem[of "up\<cdot>x"] by (cases "d i\<cdot>(up\<cdot>x)" rule: upE) simp_all
    qed simp_all
    have below: "option_approx d i\<cdot>z \<sqsubseteq> z" for z
    proof (rule cases3[of _ z])
      fix x show "option_approx d i\<cdot>(up\<cdot>(Some x)) \<sqsubseteq> up\<cdot>(Some x)"
        using monofun_cfun_arg[OF d.below[of "up\<cdot>x"], of ?s] by simp
    qed simp_all
    have fin: "finite {z. option_approx d i\<cdot>z = z}"
    proof (rule finite_subset)
      show "{z. option_approx d i\<cdot>z = z} \<subseteq> insert \<bottom> (insert (up\<cdot>None) (Rep_cfun ?s ` {w. d i\<cdot>w = w}))"
      proof
        fix z assume z: "z \<in> {z. option_approx d i\<cdot>z = z}"
        show "z \<in> insert \<bottom> (insert (up\<cdot>None) (Rep_cfun ?s ` {w. d i\<cdot>w = w}))"
        proof (rule cases3[of "\<lambda>z. option_approx d i\<cdot>z = z \<longrightarrow> z \<in> insert \<bottom> (insert (up\<cdot>None) (Rep_cfun ?s ` {w. d i\<cdot>w = w}))" z, rule_format, OF _ _ _ z[simplified]])
          fix x assume e: "option_approx d i\<cdot>(up\<cdot>(Some x)) = up\<cdot>(Some x)"
          have "d i\<cdot>(d i\<cdot>(up\<cdot>x)) = d i\<cdot>(up\<cdot>x)" by (rule d.idem)
          then show "up\<cdot>(Some x) \<in> insert \<bottom> (insert (up\<cdot>None) (Rep_cfun ?s ` {w. d i\<cdot>w = w}))"
            using e by (auto intro!: image_eqI[of _ _ "d i\<cdot>(up\<cdot>x)"])
        qed simp_all
      qed
      show "finite (insert \<bottom> (insert (up\<cdot>None) (Rep_cfun ?s ` {w. d i\<cdot>w = w})))" using d.finite_fixes by simp
    qed
    show ?thesis unfolding finite_deflation_def finite_deflation_axioms_def deflation_def
      using idem below fin by blast
  qed
qed

instance option :: (profinite) profinite
proof
  obtain d :: "nat \<Rightarrow> 'a u \<rightarrow> 'a u" where "approx_chain d" using profinite by blast
  then show "\<exists>a :: nat \<Rightarrow> 'a option u \<rightarrow> 'a option u. approx_chain a" by (blast intro: approx_chain_option_approx)
qed

subsection \<open>The type\<close>

default_sort bifinite

cpodef ('v::bifinite) option_pd = "{S :: ('v option u) upper_pd. S \<noteq> \<bottom>}"
proof
  show "{up\<cdot>None}\<sharp> \<in> {S :: ('v option u) upper_pd. S \<noteq> \<bottom>}" by simp
  show "adm (\<lambda>S. S \<in> {S :: ('v option u) upper_pd. S \<noteq> \<bottom>})" by simp
qed

lemma option_pd_Rep_nonbot [simp]: "Rep_option_pd x \<noteq> \<bottom>"
  using Rep_option_pd[of x] by simp

text \<open>The least result.\<close>

definition upper_least :: "('v option u) upper_pd" where
  "upper_least = {up\<cdot>None}\<sharp> \<union>\<sharp> {up\<cdot>(Some \<bottom>)}\<sharp>"

lemma upper_least_below:
  assumes "S \<noteq> \<bottom>"
  shows "upper_least \<sqsubseteq> S"
proof -
  have "S = \<bottom> \<or> upper_least \<sqsubseteq> S"
  proof (induct S rule: upper_pd_induct)
    case (upper_unit x)
    show ?case
    proof (cases x)
      case (up y)
      then show ?thesis by (cases y) (simp_all add: upper_least_def)
    qed simp
  next
    case (upper_plus S T)
    then show ?case by auto
  qed simp
  then show ?thesis using assms by simp
qed

lemma Rep_Abs_option_pd: "S \<noteq> \<bottom> \<Longrightarrow> Rep_option_pd (Abs_option_pd S) = S"
  by (rule Abs_option_pd_inverse) simp

lemma upper_least_nonbot: "upper_least \<noteq> \<bottom>"
  by (simp add: upper_least_def)

lemma least_option_pd: "Abs_option_pd upper_least \<sqsubseteq> y"
  unfolding below_option_pd_def Rep_Abs_option_pd[OF upper_least_nonbot] by (rule upper_least_below) simp

instance option_pd :: (bifinite) pcpo
  by standard (rule exI, rule allI, rule least_option_pd)

lemma option_pd_bottom: "(\<bottom> :: 'v option_pd) = Abs_option_pd upper_least"
  by (rule below_antisym[OF minimal least_option_pd])

subsection \<open>Bifiniteness\<close>

text \<open>Lifting the results gives back the powerdomain: the new bottom is the one cut off.  So the
  results are profinite, and, being pointed, bifinite.\<close>

lemma cont_raise_bottom: "cont (\<lambda>S :: ('v option u) upper_pd. if S = \<bottom> then upper_least else S)"
proof (rule contI2)
  show "monofun (\<lambda>S :: ('v option u) upper_pd. if S = \<bottom> then upper_least else S)"
    by (rule monofunI) (auto simp: upper_least_below)
  fix Y :: "nat \<Rightarrow> ('v option u) upper_pd" assume Y: "chain Y"
    and Z: "chain (\<lambda>i. if Y i = \<bottom> then upper_least else Y i)"
  show "(if (\<Squnion>i. Y i) = \<bottom> then upper_least else (\<Squnion>i. Y i)) \<sqsubseteq> (\<Squnion>i. if Y i = \<bottom> then upper_least else Y i)"
  proof (cases "(\<Squnion>i. Y i) = \<bottom>")
    case True
    then have "Y 0 = \<bottom>" using is_ub_thelub[OF Y, of 0] by simp
    then show ?thesis using True is_ub_thelub[OF Z, of 0] by simp
  next
    case False
    have "(\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. if Y i = \<bottom> then upper_least else Y i)"
      by (rule lub_mono[OF Y Z]) simp
    then show ?thesis using False by simp
  qed
qed

definition lift_option_pd :: "('v option u) upper_pd \<rightarrow> 'v option_pd u" where
  "lift_option_pd = (\<Lambda> S. if S = \<bottom> then \<bottom> else up\<cdot>(Abs_option_pd (if S = \<bottom> then upper_least else S)))"

lemma cont_lift_option_pd:
  "cont (\<lambda>S :: ('v option u) upper_pd. if S = \<bottom> then \<bottom> else up\<cdot>(Abs_option_pd (if S = \<bottom> then upper_least else S)))"
proof -
  have "cont (\<lambda>S :: ('v option u) upper_pd. Abs_option_pd (if S = \<bottom> then upper_least else S))"
    by (rule cont_Abs_option_pd[OF _ cont_raise_bottom]) (simp add: upper_least_nonbot)
  then show ?thesis by simp
qed

lemma lift_option_pd_apply:
  "lift_option_pd\<cdot>S = (if S = \<bottom> then \<bottom> else up\<cdot>(Abs_option_pd S))"
  by (simp add: lift_option_pd_def cont_lift_option_pd)

definition lower_option_pd :: "'v option_pd u \<rightarrow> ('v option u) upper_pd" where
  "lower_option_pd = fup\<cdot>(\<Lambda> x. Rep_option_pd x)"

lemma lower_lift_option_pd: "lower_option_pd\<cdot>(lift_option_pd\<cdot>S) = S"
  by (simp add: lower_option_pd_def lift_option_pd_apply cont_Rep_option_pd Rep_Abs_option_pd)

lemma lift_lower_option_pd: "lift_option_pd\<cdot>(lower_option_pd\<cdot>z) = z"
  by (cases z) (simp_all add: lower_option_pd_def lift_option_pd_apply cont_Rep_option_pd Rep_option_pd_inverse)

instance option_pd :: (bifinite) profinite
proof
  obtain a :: "nat \<Rightarrow> ('a option u) upper_pd \<rightarrow> ('a option u) upper_pd" where "approx_chain a"
    using bifinite by blast
  then show "\<exists>a :: nat \<Rightarrow> 'a option_pd u \<rightarrow> 'a option_pd u. approx_chain a"
    by (blast intro: approx_chain_iso lift_lower_option_pd lower_lift_option_pd)
qed

instance option_pd :: (bifinite) bifinite
  by (rule bifinite_profinite_pointed)

text \<open>The results are a domain: lifted, they are the powerdomain, a domain.\<close>

instantiation option_pd :: ("domain") "domain"
begin

definition "emb = emb oo lower_option_pd oo strictify\<cdot>up"

definition "prj = fup\<cdot>ID oo lift_option_pd oo prj"

definition "defl (t :: 'a option_pd itself) =
  unlift_defl (lower_option_pd :: 'a option_pd u \<rightarrow> ('a option u) upper_pd) lift_option_pd"

definition "(liftemb :: 'a option_pd u \<rightarrow> udom u) = u_map\<cdot>emb"

definition "(liftprj :: udom u \<rightarrow> 'a option_pd u) = u_map\<cdot>prj"

definition "liftdefl (t :: 'a option_pd itself) = liftdefl_of\<cdot>DEFL('a option_pd)"

instance
  by (rule domain_class_lift_iso[OF lift_lower_option_pd lower_lift_option_pd emb_option_pd_def prj_option_pd_def
        defl_option_pd_def[abs_def, THEN meta_eq_to_obj_eq] liftemb_option_pd_def liftprj_option_pd_def
        liftdefl_option_pd_def[abs_def, THEN meta_eq_to_obj_eq]])

end

subsection \<open>Absent, present, and their sums\<close>

definition Absent :: "'v option_pd" where
  "Absent = Abs_option_pd {up\<cdot>None}\<sharp>"

definition Present :: "'v \<rightarrow> 'v option_pd" where
  "Present = (\<Lambda> v. Abs_option_pd {up\<cdot>(Some v)}\<sharp>)"

text \<open>The sum of two results has the outcomes of both; \<open>Present\<cdot>v + Absent\<close> is the value \<open>v\<close>, if
  present.\<close>

instantiation option_pd :: (bifinite) plus
begin

definition plus_option_pd :: "'a option_pd \<Rightarrow> 'a option_pd \<Rightarrow> 'a option_pd" where
  "x + y = Abs_option_pd (Rep_option_pd x \<union>\<sharp> Rep_option_pd y)"

instance ..

end

lemma cont_Present: "cont (\<lambda>v. Abs_option_pd {up\<cdot>(Some v)}\<sharp>)"
  by (rule cont_Abs_option_pd) simp_all

lemma Rep_Absent [simp]: "Rep_option_pd Absent = {up\<cdot>None}\<sharp>"
  by (simp add: Absent_def Rep_Abs_option_pd)

lemma Rep_Present [simp]: "Rep_option_pd (Present\<cdot>v) = {up\<cdot>(Some v)}\<sharp>"
  by (simp add: Present_def cont_Present Rep_Abs_option_pd)

lemma Rep_plus [simp]: "Rep_option_pd (x + y) = Rep_option_pd x \<union>\<sharp> Rep_option_pd y"
  by (simp add: plus_option_pd_def Rep_Abs_option_pd)

lemma cont_plus_option_pd [simp, cont2cont]:
  "cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda>x. f x + g x :: 'v option_pd)"
  unfolding plus_option_pd_def by (rule cont_Abs_option_pd) (simp_all add: cont_Rep_option_pd)

lemma plus_option_pd_commute: "x + y = y + (x :: 'v option_pd)"
  by (simp add: Rep_option_pd_inject[symmetric] upper_plus_commute)

lemma plus_option_pd_assoc: "x + y + z = x + (y + z :: 'v option_pd)"
  by (simp add: Rep_option_pd_inject[symmetric] upper_plus_assoc)

lemma plus_option_pd_absorb [simp]: "x + x = (x :: 'v option_pd)"
  by (simp add: Rep_option_pd_inject[symmetric])

lemma Present_below_iff [simp]: "Present\<cdot>v \<sqsubseteq> Present\<cdot>w \<longleftrightarrow> v \<sqsubseteq> w"
  by (simp add: below_option_pd_def)

lemma Absent_not_below_Present [simp]: "\<not> Absent \<sqsubseteq> Present\<cdot>v"
  by (simp add: below_option_pd_def)

lemma Present_not_below_Absent [simp]: "\<not> Present\<cdot>v \<sqsubseteq> Absent"
  by (simp add: below_option_pd_def)

text \<open>A sum is below both summands: it is their greatest lower bound.\<close>

lemma plus_option_pd_below1: "x + y \<sqsubseteq> (x :: 'v option_pd)"
  by (simp add: below_option_pd_def upper_plus_below1)

lemma plus_option_pd_below2: "x + y \<sqsubseteq> (y :: 'v option_pd)"
  by (simp add: below_option_pd_def upper_plus_below2)

lemma plus_option_pd_greatest: "z \<sqsubseteq> x \<Longrightarrow> z \<sqsubseteq> y \<Longrightarrow> z \<sqsubseteq> x + (y :: 'v option_pd)"
  by (simp add: below_option_pd_def)

text \<open>A definite absence is maximal.\<close>

lemma upper_unit_None_maximal:
  assumes "{up\<cdot>None}\<sharp> \<sqsubseteq> S" shows "S = {up\<cdot>None}\<sharp>"
proof -
  have "\<not> {up\<cdot>None}\<sharp> \<sqsubseteq> S \<or> S = {up\<cdot>None}\<sharp>"
  proof (induct S rule: upper_pd_induct)
    case (upper_unit x)
    show ?case
    proof (cases x)
      case (up y)
      then show ?thesis by (cases y) simp_all
    qed simp
  next
    case (upper_plus S T)
    then show ?case by auto
  qed simp
  then show ?thesis using assms by simp
qed

lemma Absent_maximal: "Absent \<sqsubseteq> y \<Longrightarrow> y = Absent"
  unfolding below_option_pd_def Rep_Absent
  by (drule upper_unit_None_maximal) (simp add: Rep_option_pd_inject[symmetric])

text \<open>The least result is a value of which nothing is known, possibly absent.\<close>

lemma Present_bottom_plus_Absent: "Present\<cdot>\<bottom> + Absent = \<bottom>"
  unfolding option_pd_bottom plus_option_pd_def
  by (simp add: upper_least_def upper_plus_commute)

subsection \<open>Two-valued results and multiplying by truth values\<close>

text \<open>A plain option is a two-valued result.\<close>

definition of_option :: "'v option \<rightarrow> 'v option_pd" where
  "of_option = (\<Lambda> z. case z of None \<Rightarrow> Absent | Some v \<Rightarrow> Present\<cdot>v)"

lemma of_option_simps [simp]: "of_option\<cdot>None = Absent" "of_option\<cdot>(Some v) = Present\<cdot>v"
  by (simp_all add: of_option_def)

lemma of_option_below_iff [simp]: "of_option\<cdot>a \<sqsubseteq> of_option\<cdot>b \<longleftrightarrow> a \<sqsubseteq> b"
  by (cases a; cases b) simp_all

lemma of_option_eq_iff [simp]: "of_option\<cdot>a = of_option\<cdot>b \<longleftrightarrow> a = b"
  by (simp add: po_eq_conv)

text \<open>Multiplying a result by a truth value: false makes it absent, true leaves it, and an unknown
  truth value leaves it possibly absent.  It is monotone in the truth value since the sum is below
  both summands, and continuous since the truth values are flat.\<close>

definition tr_mult :: "tr \<rightarrow> 'v option_pd \<rightarrow> 'v option_pd" where
  "tr_mult = (\<Lambda> t x. if t = TT then x else if t = FF then Absent else x + Absent)"

abbreviation tr_mult_syn :: "tr \<Rightarrow> 'v option_pd \<Rightarrow> 'v option_pd" (infixr \<open>\<odot>\<close> 70) where
  "t \<odot> x \<equiv> tr_mult\<cdot>t\<cdot>x"

lemma cont_tr_mult1: "cont (\<lambda>t. if t = TT then x else if t = FF then Absent else x + (Absent :: 'v option_pd))"
proof (rule chfindom_monofun2cont, rule monofunI)
  fix t u :: tr assume "t \<sqsubseteq> u"
  then show "(if t = TT then x else if t = FF then Absent else x + Absent) \<sqsubseteq>
      (if u = TT then x else if u = FF then Absent else x + (Absent :: 'v option_pd))"
    by (cases t rule: trE; cases u rule: trE)
      (simp_all add: plus_option_pd_below1 plus_option_pd_below2)
qed

lemma tr_mult_simps [simp]: "TT \<odot> x = x" "FF \<odot> x = Absent" "\<bottom> \<odot> x = x + Absent"
  by (simp_all add: tr_mult_def cont2cont_LAM cont_tr_mult1)

lemma tr_mult_Absent [simp]: "t \<odot> Absent = Absent"
  by (cases t rule: trE) simp_all

lemma tr_mult_not_Absent: "t \<odot> x \<noteq> Absent \<Longrightarrow> t \<noteq> FF \<and> x \<noteq> Absent"
  by auto

subsection \<open>Lifting binary operations\<close>

text \<open>A binary function extends to the upper powerdomain by binding both arguments: on units it is
  the function, and it distributes over sums in each argument.\<close>

definition upper_bin :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<rightarrow> 'a upper_pd \<rightarrow> 'b upper_pd \<rightarrow> 'c upper_pd" where
  "upper_bin = (\<Lambda> h S T. upper_bind\<cdot>S\<cdot>(\<Lambda> s. upper_bind\<cdot>T\<cdot>(\<Lambda> t. {h\<cdot>s\<cdot>t}\<sharp>)))"

lemma upper_bin_apply: "upper_bin\<cdot>h\<cdot>S\<cdot>T = upper_bind\<cdot>S\<cdot>(\<Lambda> s. upper_bind\<cdot>T\<cdot>(\<Lambda> t. {h\<cdot>s\<cdot>t}\<sharp>))"
  by (simp add: upper_bin_def)

lemma upper_bin_unit [simp]: "upper_bin\<cdot>h\<cdot>{s}\<sharp>\<cdot>{t}\<sharp> = {h\<cdot>s\<cdot>t}\<sharp>"
  by (simp add: upper_bin_apply)

lemma upper_bin_plus1 [simp]: "upper_bin\<cdot>h\<cdot>(S \<union>\<sharp> S')\<cdot>T = upper_bin\<cdot>h\<cdot>S\<cdot>T \<union>\<sharp> upper_bin\<cdot>h\<cdot>S'\<cdot>T"
  by (simp add: upper_bin_apply)

lemma upper_bin_plus2 [simp]: "upper_bin\<cdot>h\<cdot>S\<cdot>(T \<union>\<sharp> T') = upper_bin\<cdot>h\<cdot>S\<cdot>T \<union>\<sharp> upper_bin\<cdot>h\<cdot>S\<cdot>T'"
  by (induct S rule: upper_pd_induct) (simp_all add: upper_bin_apply upper_plus_ac)

lemma upper_bin_unit1: "upper_bin\<cdot>h\<cdot>{s}\<sharp>\<cdot>T = upper_map\<cdot>(h\<cdot>s)\<cdot>T"
  by (induct T rule: upper_pd_induct) simp_all

lemma upper_bin_commute:
  assumes "\<And>s t. h\<cdot>s\<cdot>t = h\<cdot>t\<cdot>s"
  shows "upper_bin\<cdot>h\<cdot>S\<cdot>T = upper_bin\<cdot>h\<cdot>T\<cdot>S"
proof (induct S arbitrary: T rule: upper_pd_induct)
  case (upper_unit s)
  show ?case by (induct T rule: upper_pd_induct) (simp_all add: assms)
qed simp_all

lemma upper_bin_assoc:
  assumes "\<And>a b c. h\<cdot>(h\<cdot>a\<cdot>b)\<cdot>c = h\<cdot>a\<cdot>(h\<cdot>b\<cdot>c)"
  shows "upper_bin\<cdot>h\<cdot>(upper_bin\<cdot>h\<cdot>S\<cdot>T)\<cdot>U = upper_bin\<cdot>h\<cdot>S\<cdot>(upper_bin\<cdot>h\<cdot>T\<cdot>U)"
proof (induct S arbitrary: T U rule: upper_pd_induct)
  case (upper_unit s)
  show ?case
  proof (induct T arbitrary: U rule: upper_pd_induct)
    case (upper_unit t)
    show ?case by (induct U rule: upper_pd_induct) (simp_all add: assms)
  qed simp_all
qed simp_all

lemma upper_bin_nonbot:
  assumes h: "\<And>s t. s \<noteq> \<bottom> \<Longrightarrow> t \<noteq> \<bottom> \<Longrightarrow> h\<cdot>s\<cdot>t \<noteq> \<bottom>" and S: "S \<noteq> \<bottom>" and T: "T \<noteq> \<bottom>"
  shows "upper_bin\<cdot>h\<cdot>S\<cdot>T \<noteq> \<bottom>"
proof -
  have "S = \<bottom> \<or> upper_bin\<cdot>h\<cdot>S\<cdot>T \<noteq> \<bottom>"
  proof (induct S rule: upper_pd_induct)
    case (upper_unit s)
    have "T = \<bottom> \<or> s = \<bottom> \<or> upper_bin\<cdot>h\<cdot>{s}\<sharp>\<cdot>T \<noteq> \<bottom>"
    proof (induct T rule: upper_pd_induct)
      case (upper_unit t)
      then show ?case using h by auto
    next
      case (upper_plus T T')
      then show ?case by auto
    qed simp
    then show ?case using T by auto
  next
    case (upper_plus S S')
    then show ?case by auto
  qed simp
  then show ?thesis using S by simp
qed

text \<open>A binary operation on options, lifted through the lifting: defined on lifted options only.\<close>

definition lift_up2 :: "('a::cpo \<rightarrow> 'b::cpo \<rightarrow> 'c::cpo) \<Rightarrow> 'a u \<rightarrow> 'b u \<rightarrow> 'c u" where
  "lift_up2 G = (\<Lambda> s t. fup\<cdot>(\<Lambda> a. fup\<cdot>(\<Lambda> b. up\<cdot>(G\<cdot>a\<cdot>b))\<cdot>t)\<cdot>s)"

lemma lift_up2_simps [simp]:
  "lift_up2 G\<cdot>(up\<cdot>a)\<cdot>(up\<cdot>b) = up\<cdot>(G\<cdot>a\<cdot>b)" "lift_up2 G\<cdot>\<bottom>\<cdot>t = \<bottom>" "lift_up2 G\<cdot>s\<cdot>\<bottom> = \<bottom>"
  by (simp_all add: lift_up2_def) (cases s; simp)

lemma lift_up2_nonbot: "s \<noteq> \<bottom> \<Longrightarrow> t \<noteq> \<bottom> \<Longrightarrow> lift_up2 G\<cdot>s\<cdot>t \<noteq> \<bottom>"
  by (cases s; cases t) simp_all

text \<open>The lifted operation on results: every combination of the outcomes.\<close>

definition option_pd_op :: "('a option \<rightarrow> 'b option \<rightarrow> 'c option) \<Rightarrow> 'a option_pd \<Rightarrow> 'b option_pd \<Rightarrow> 'c option_pd" where
  "option_pd_op G x y = Abs_option_pd (upper_bin\<cdot>(lift_up2 G)\<cdot>(Rep_option_pd x)\<cdot>(Rep_option_pd y))"

lemma Rep_option_pd_op [simp]:
  "Rep_option_pd (option_pd_op G x y) = upper_bin\<cdot>(lift_up2 G)\<cdot>(Rep_option_pd x)\<cdot>(Rep_option_pd y)"
  unfolding option_pd_op_def by (rule Rep_Abs_option_pd, rule upper_bin_nonbot[OF lift_up2_nonbot]) simp_all

lemma cont_option_pd_op [simp, cont2cont]:
  "cont f \<Longrightarrow> cont g \<Longrightarrow> cont (\<lambda>x. option_pd_op G (f x) (g x))"
  unfolding option_pd_op_def
  by (rule cont_Abs_option_pd) (simp_all add: cont_Rep_option_pd upper_bin_nonbot lift_up2_nonbot)

lemma Rep_of_option [simp]: "Rep_option_pd (of_option\<cdot>c) = {up\<cdot>c}\<sharp>"
  by (cases c) simp_all

lemma option_pd_op_of_option [simp]:
  "option_pd_op G (of_option\<cdot>a) (of_option\<cdot>b) = of_option\<cdot>(G\<cdot>a\<cdot>b)"
  by (simp add: Rep_option_pd_inject[symmetric])

lemma option_pd_op_plus1: "option_pd_op G (x + y) z = option_pd_op G x z + option_pd_op G y z"
  by (simp add: Rep_option_pd_inject[symmetric])

lemma option_pd_op_plus2: "option_pd_op G z (x + y) = option_pd_op G z x + option_pd_op G z y"
  by (simp add: Rep_option_pd_inject[symmetric])

text \<open>A commutative monoid on options with unit \<open>None\<close> lifts to one on results with unit
  \<open>Absent\<close>.\<close>

lemma comm_monoid_option_pd_op:
  assumes G: "comm_monoid (\<lambda>a b. G\<cdot>a\<cdot>b) None"
  shows "comm_monoid (option_pd_op G) Absent"
proof -
  interpret G: comm_monoid "\<lambda>a b. G\<cdot>a\<cdot>b" None by (fact G)
  have h_comm: "lift_up2 G\<cdot>s\<cdot>t = lift_up2 G\<cdot>t\<cdot>s" for s t
    by (cases s; cases t) (simp_all add: G.commute)
  have h_assoc: "lift_up2 G\<cdot>(lift_up2 G\<cdot>a\<cdot>b)\<cdot>c = lift_up2 G\<cdot>a\<cdot>(lift_up2 G\<cdot>b\<cdot>c)" for a b c
    by (cases a; cases b; cases c) (simp_all add: G.assoc)
  have h_unit: "lift_up2 G\<cdot>(up\<cdot>None) = ID"
    by (rule cfun_eqI, case_tac x) simp_all
  show ?thesis
  proof
    show "option_pd_op G (option_pd_op G x y) z = option_pd_op G x (option_pd_op G y z)" for x y z
      by (simp add: Rep_option_pd_inject[symmetric] upper_bin_assoc[OF h_assoc])
    show "option_pd_op G x y = option_pd_op G y x" for x y
      by (simp add: Rep_option_pd_inject[symmetric] upper_bin_commute[OF h_comm])
    show "option_pd_op G x Absent = x" for x
      by (simp add: Rep_option_pd_inject[symmetric] upper_bin_commute[OF h_comm, of _ "{up\<cdot>None}\<sharp>"]
          upper_bin_unit1 h_unit upper_map_ID)
  qed
qed

subsection \<open>Lifting a commutative semigroup\<close>

text \<open>Adjoining a unit for absence: an option operation, then lifted to results.\<close>

abbreviation opt_op :: "('v::pcpo \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> 'v option \<Rightarrow> 'v option \<Rightarrow> 'v option" where
  "opt_op f \<equiv> combine_options (\<lambda>a b. f\<cdot>a\<cdot>b)"

lemma comm_monoid_opt_op:
  assumes "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
  shows "comm_monoid (opt_op f) None"
proof -
  interpret abel_semigroup "\<lambda>a b. f\<cdot>a\<cdot>b" by (fact assms)
  show ?thesis by standard (auto simp: combine_options_def assoc commute left_commute split: option.splits)
qed

lemma cont_opt_op:
  assumes u: "cont u" and w: "cont w"
  shows "cont (\<lambda>x. opt_op f (u x) (w x))"
  unfolding combine_options_def
proof (rule cont2cont_case_option[OF u w])
  fix a show "cont (\<lambda>x. case w x of None \<Rightarrow> Some a | Some y \<Rightarrow> Some (f\<cdot>a\<cdot>y))"
    by (rule cont2cont_case_option[OF w]) simp_all
next
  fix x show "cont (\<lambda>a. case w x of None \<Rightarrow> Some a | Some y \<Rightarrow> Some (f\<cdot>a\<cdot>y))" by simp
qed

definition combine_option_pd :: "('v \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> 'v option_pd \<rightarrow> 'v option_pd \<rightarrow> 'v option_pd" where
  "combine_option_pd f = (\<Lambda> x y. option_pd_op (\<Lambda> a b. opt_op f a b) x y)"

lemma opt_op_cfun_apply [simp]: "(\<Lambda> a b. opt_op f a b)\<cdot>a\<cdot>b = opt_op f a b"
proof -
  have "cont (\<lambda>a. opt_op f a b)" for b by (rule cont_opt_op) simp_all
  moreover have "cont (\<lambda>b. opt_op f a b)" for a by (rule cont_opt_op) simp_all
  ultimately show ?thesis by (simp add: cont2cont_LAM)
qed

lemma combine_option_pd_apply: "combine_option_pd f\<cdot>x\<cdot>y = option_pd_op (\<Lambda> a b. opt_op f a b) x y"
  by (simp add: combine_option_pd_def cont2cont_LAM)

lemma combine_option_pd_of_option [simp]:
  "combine_option_pd f\<cdot>(of_option\<cdot>a)\<cdot>(of_option\<cdot>b) = of_option\<cdot>(opt_op f a b)"
  by (simp add: combine_option_pd_apply)

lemma combine_option_pd_Present [simp]: "combine_option_pd f\<cdot>(Present\<cdot>a)\<cdot>(Present\<cdot>b) = Present\<cdot>(f\<cdot>a\<cdot>b)"
  using combine_option_pd_of_option[of f "Some a" "Some b"] by simp

lemma combine_option_pd_plus1: "combine_option_pd f\<cdot>(x + y)\<cdot>z = combine_option_pd f\<cdot>x\<cdot>z + combine_option_pd f\<cdot>y\<cdot>z"
  by (simp add: combine_option_pd_apply option_pd_op_plus1)

lemma combine_option_pd_plus2: "combine_option_pd f\<cdot>z\<cdot>(x + y) = combine_option_pd f\<cdot>z\<cdot>x + combine_option_pd f\<cdot>z\<cdot>y"
  by (simp add: combine_option_pd_apply option_pd_op_plus2)

lemma comm_monoid_combine_option_pd:
  assumes "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
  shows "comm_monoid (\<lambda>x y. combine_option_pd f\<cdot>x\<cdot>y) Absent"
  unfolding combine_option_pd_apply
  by (rule comm_monoid_option_pd_op) (simp add: comm_monoid_opt_op[OF assms])

subsection \<open>Absorbing absence\<close>

lemma upper_bin_unit2: "upper_bin\<cdot>h\<cdot>S\<cdot>{t}\<sharp> = upper_map\<cdot>(\<Lambda> s. h\<cdot>s\<cdot>t)\<cdot>S"
  by (induct S rule: upper_pd_induct) simp_all

lemma upper_map_const_nonbot:
  assumes f: "\<And>t. t \<noteq> \<bottom> \<Longrightarrow> f\<cdot>t = c" and T: "T \<noteq> \<bottom>"
  shows "upper_map\<cdot>f\<cdot>T = {c}\<sharp>"
proof -
  have "T = \<bottom> \<or> upper_map\<cdot>f\<cdot>T = {c}\<sharp>"
  proof (induct T rule: upper_pd_induct)
    case (upper_unit t) then show ?case using f by auto
  next
    case (upper_plus T T') then show ?case by auto
  qed simp
  then show ?thesis using T by simp
qed

text \<open>An operation absent as soon as one argument is absent lifts to one absorbing \<open>Absent\<close>.\<close>

lemma option_pd_op_Absent1:
  assumes "\<And>b. G\<cdot>None\<cdot>b = None"
  shows "option_pd_op G Absent y = Absent"
proof -
  have "upper_map\<cdot>(lift_up2 G\<cdot>(up\<cdot>None))\<cdot>(Rep_option_pd y) = {up\<cdot>None}\<sharp>"
  proof (rule upper_map_const_nonbot)
    show "lift_up2 G\<cdot>(up\<cdot>None)\<cdot>t = up\<cdot>None" if "t \<noteq> \<bottom>" for t using that assms by (cases t) simp_all
  qed simp
  then show ?thesis by (simp add: Rep_option_pd_inject[symmetric] upper_bin_unit1)
qed

lemma option_pd_op_Absent2:
  assumes "\<And>a. G\<cdot>a\<cdot>None = None"
  shows "option_pd_op G x Absent = Absent"
proof -
  have "upper_map\<cdot>(\<Lambda> s. lift_up2 G\<cdot>s\<cdot>(up\<cdot>None))\<cdot>(Rep_option_pd x) = {up\<cdot>None}\<sharp>"
  proof (rule upper_map_const_nonbot)
    show "(\<Lambda> s. lift_up2 G\<cdot>s\<cdot>(up\<cdot>None))\<cdot>t = up\<cdot>None" if "t \<noteq> \<bottom>" for t using that assms by (cases t) simp_all
  qed simp
  then show ?thesis by (simp add: Rep_option_pd_inject[symmetric] upper_bin_unit2)
qed

subsection \<open>Mapping results\<close>

lemma upper_map_u_map_nonbot: "S \<noteq> \<bottom> \<Longrightarrow> upper_map\<cdot>(u_map\<cdot>d)\<cdot>S \<noteq> \<bottom>"
proof -
  assume S: "S \<noteq> \<bottom>"
  have "S = \<bottom> \<or> upper_map\<cdot>(u_map\<cdot>d)\<cdot>S \<noteq> \<bottom>"
  proof (induct S rule: upper_pd_induct)
    case (upper_unit t) then show ?case by (cases t) simp_all
  next
    case (upper_plus T T') then show ?case by auto
  qed simp
  then show ?thesis using S by simp
qed

lemma cont_map_Abs: "cont (\<lambda>x. Abs_option_pd (upper_map\<cdot>(u_map\<cdot>(option_map g))\<cdot>(Rep_option_pd x)))"
  by (rule cont_Abs_option_pd) (simp_all add: cont_Rep_option_pd upper_map_u_map_nonbot)

definition map_option_pd :: "('a \<rightarrow> 'b) \<Rightarrow> 'a option_pd \<rightarrow> 'b option_pd" where
  "map_option_pd g = (\<Lambda> x. Abs_option_pd (upper_map\<cdot>(u_map\<cdot>(option_map g))\<cdot>(Rep_option_pd x)))"

lemma Rep_map_option_pd [simp]:
  "Rep_option_pd (map_option_pd g\<cdot>x) = upper_map\<cdot>(u_map\<cdot>(option_map g))\<cdot>(Rep_option_pd x)"
  unfolding map_option_pd_def beta_cfun[OF cont_map_Abs]
  by (rule Rep_Abs_option_pd, rule upper_map_u_map_nonbot) simp

lemma map_option_pd_simps [simp]:
  "map_option_pd g\<cdot>Absent = Absent" "map_option_pd g\<cdot>(Present\<cdot>v) = Present\<cdot>(g\<cdot>v)"
  "map_option_pd g\<cdot>(of_option\<cdot>a) = of_option\<cdot>(map_option (Rep_cfun g) a)"
  "map_option_pd g\<cdot>(x + y) = map_option_pd g\<cdot>x + map_option_pd g\<cdot>y"
  by (simp_all add: Rep_option_pd_inject[symmetric])

subsection \<open>Binary operations strict in absence\<close>

text \<open>A binary function on values lifted to results: present where both arguments are.\<close>

definition strict_opt2 :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<Rightarrow> 'a option \<rightarrow> 'b option \<rightarrow> 'c option" where
  "strict_opt2 f = (\<Lambda> a b. case a of None \<Rightarrow> None | Some v \<Rightarrow> (case b of None \<Rightarrow> None | Some w \<Rightarrow> Some (f\<cdot>v\<cdot>w)))"

lemma strict_opt2_simps [simp]:
  "strict_opt2 f\<cdot>None\<cdot>b = None" "strict_opt2 f\<cdot>a\<cdot>None = None" "strict_opt2 f\<cdot>(Some v)\<cdot>(Some w) = Some (f\<cdot>v\<cdot>w)"
  by (simp_all add: strict_opt2_def) (cases a; simp)

definition lift2_option_pd :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<Rightarrow> 'a option_pd \<rightarrow> 'b option_pd \<rightarrow> 'c option_pd" where
  "lift2_option_pd f = (\<Lambda> x y. option_pd_op (strict_opt2 f) x y)"

lemma lift2_option_pd_apply: "lift2_option_pd f\<cdot>x\<cdot>y = option_pd_op (strict_opt2 f) x y"
  by (simp add: lift2_option_pd_def cont2cont_LAM)

lemma lift2_option_pd_simps [simp]:
  "lift2_option_pd f\<cdot>(Present\<cdot>v)\<cdot>(Present\<cdot>w) = Present\<cdot>(f\<cdot>v\<cdot>w)"
  "lift2_option_pd f\<cdot>Absent\<cdot>y = Absent" "lift2_option_pd f\<cdot>x\<cdot>Absent = Absent"
proof -
  show "lift2_option_pd f\<cdot>(Present\<cdot>v)\<cdot>(Present\<cdot>w) = Present\<cdot>(f\<cdot>v\<cdot>w)"
    using option_pd_op_of_option[of "strict_opt2 f" "Some v" "Some w"] by (simp add: lift2_option_pd_apply)
qed (simp_all add: lift2_option_pd_apply option_pd_op_Absent1 option_pd_op_Absent2)


subsection \<open>Absence is decided by absence\<close>

text \<open>A result is absent only when the operations' arguments force it: mapping keeps absence, a
  strict operation is absent exactly where one argument is, the unit-lax one where both are.  The
  proofs go through the outcomes: the absent unit is below a powerdomain element exactly when all
  of its outcomes are absent.\<close>

lemma option_u_cases3:
  assumes "P \<bottom>" and "P (up\<cdot>None)" and "\<And>x. P (up\<cdot>(Some x))"
  shows "P z"
proof (cases z)
  case (up w)
  then show ?thesis using assms by (cases w) simp_all
qed (simp add: assms)

lemma upper_map_None_below:
  assumes h: "\<And>x. up\<cdot>None \<sqsubseteq> h\<cdot>x \<Longrightarrow> up\<cdot>None \<sqsubseteq> x" and U: "{up\<cdot>None}\<sharp> \<sqsubseteq> upper_map\<cdot>h\<cdot>S"
  shows "{up\<cdot>None}\<sharp> \<sqsubseteq> S"
proof -
  have "\<not> {up\<cdot>None}\<sharp> \<sqsubseteq> upper_map\<cdot>h\<cdot>S \<or> {up\<cdot>None}\<sharp> \<sqsubseteq> S"
  proof (induct S rule: upper_pd_induct)
    case (upper_unit x)
    show ?case using h[of x] by auto
  next
    case (upper_plus S T)
    then show ?case by (auto intro: upper_plus_greatest)
  qed simp
  then show ?thesis using U by blast
qed

lemma Absent_below_iff: "Absent \<sqsubseteq> x \<longleftrightarrow> x = Absent"
  using Absent_maximal by auto

lemma Present_neq_Absent [simp]: "Present\<cdot>v \<noteq> Absent" "Absent \<noteq> Present\<cdot>v"
  using Present_not_below_Absent[of v] by (metis below_refl)+

lemma bottom_neq_Absent [simp]: "(\<bottom> :: 'v option_pd) \<noteq> Absent" "Absent \<noteq> (\<bottom> :: 'v option_pd)"
proof -
  have "\<bottom> \<sqsubseteq> Present\<cdot>(\<bottom> :: 'v)" by (rule minimal)
  then have "(\<bottom> :: 'v option_pd) = Absent \<Longrightarrow> False" by (metis Absent_maximal Present_neq_Absent(1))
  then show "(\<bottom> :: 'v option_pd) \<noteq> Absent" "Absent \<noteq> (\<bottom> :: 'v option_pd)" by auto
qed

lemma compact_Present_bottom: "compact (Present\<cdot>\<bottom>)"
  by (rule typedef_compact[OF type_definition_option_pd below_option_pd_def]) simp_all

lemma Absent_below_Rep: "{up\<cdot>None}\<sharp> \<sqsubseteq> Rep_option_pd x \<longleftrightarrow> x = Absent"
  using Absent_below_iff[of x] by (simp add: below_option_pd_def)

lemma map_option_pd_Absent_iff [simp]: "map_option_pd g\<cdot>x = Absent \<longleftrightarrow> x = Absent"
proof
  assume "map_option_pd g\<cdot>x = Absent"
  then have m: "{up\<cdot>None}\<sharp> \<sqsubseteq> upper_map\<cdot>(u_map\<cdot>(option_map g))\<cdot>(Rep_option_pd x)"
    by (simp add: Rep_option_pd_inject[symmetric])
  have "{up\<cdot>None}\<sharp> \<sqsubseteq> Rep_option_pd x"
  proof (rule upper_map_None_below[OF _ m])
    fix z assume "up\<cdot>None \<sqsubseteq> u_map\<cdot>(option_map g)\<cdot>z"
    then show "up\<cdot>None \<sqsubseteq> z" by (cases z; simp)
  qed
  then show "x = Absent" by (simp only: Absent_below_Rep)
qed simp

lemma tr_mult_Absent_iff: "t \<odot> x = Absent \<longleftrightarrow> t = FF \<or> x = Absent"
proof (cases t rule: trE)
  case bottom
  have "x + Absent = Absent \<Longrightarrow> x = Absent"
    using plus_option_pd_below1[of x Absent] by (metis Absent_maximal)
  then show ?thesis using bottom by auto
qed simp_all

lemma upper_bin_strict_None:
  assumes U: "{up\<cdot>None}\<sharp> \<sqsubseteq> upper_bin\<cdot>(lift_up2 (strict_opt2 f))\<cdot>S\<cdot>T"
  shows "{up\<cdot>None}\<sharp> \<sqsubseteq> S \<or> {up\<cdot>None}\<sharp> \<sqsubseteq> T"
proof -
  let ?U = "{up\<cdot>None}\<sharp>"
  have "\<forall>T. \<not> ?U \<sqsubseteq> upper_bin\<cdot>(lift_up2 (strict_opt2 f))\<cdot>S\<cdot>T \<or> ?U \<sqsubseteq> S \<or> ?U \<sqsubseteq> T"
  proof (induct S rule: upper_pd_induct)
    case (upper_unit s)
    show ?case
    proof (intro allI)
      fix T
      have "?U \<sqsubseteq> T" if m0: "?U \<sqsubseteq> upper_bin\<cdot>(lift_up2 (strict_opt2 f))\<cdot>{s}\<sharp>\<cdot>T" and s: "\<not> up\<cdot>None \<sqsubseteq> s"
      proof (rule upper_map_None_below)
        show "?U \<sqsubseteq> upper_map\<cdot>(lift_up2 (strict_opt2 f)\<cdot>s)\<cdot>T" using m0 by (simp add: upper_bin_unit1)
        fix z assume z: "up\<cdot>None \<sqsubseteq> lift_up2 (strict_opt2 f)\<cdot>s\<cdot>z"
        show "up\<cdot>None \<sqsubseteq> z"
        proof (cases s)
          case (up a)
          then show ?thesis using z s by (cases a; cases z; simp) (rename_tac w, case_tac w, simp_all)
        qed (use z in simp)
      qed
      then show "\<not> ?U \<sqsubseteq> upper_bin\<cdot>(lift_up2 (strict_opt2 f))\<cdot>{s}\<sharp>\<cdot>T \<or> ?U \<sqsubseteq> {s}\<sharp> \<or> ?U \<sqsubseteq> T"
        by auto
    qed
  next
    case (upper_plus S1 S2)
    then show ?case by (auto intro: upper_plus_greatest)
  qed simp
  then show ?thesis using U by blast
qed

lemma lift2_option_pd_Absent_iff: "lift2_option_pd f\<cdot>x\<cdot>y = Absent \<longleftrightarrow> x = Absent \<or> y = Absent"
proof
  assume "lift2_option_pd f\<cdot>x\<cdot>y = Absent"
  then have "{up\<cdot>None}\<sharp> \<sqsubseteq> upper_bin\<cdot>(lift_up2 (strict_opt2 f))\<cdot>(Rep_option_pd x)\<cdot>(Rep_option_pd y)"
    by (simp add: lift2_option_pd_apply Rep_option_pd_inject[symmetric])
  then have "{up\<cdot>None}\<sharp> \<sqsubseteq> Rep_option_pd x \<or> {up\<cdot>None}\<sharp> \<sqsubseteq> Rep_option_pd y" by (rule upper_bin_strict_None)
  then show "x = Absent \<or> y = Absent" by (simp only: Absent_below_Rep)
qed auto

lemma upper_bin_lax_None:
  assumes U: "{up\<cdot>None}\<sharp> \<sqsubseteq> upper_bin\<cdot>(lift_up2 (\<Lambda> a b. opt_op f a b))\<cdot>S\<cdot>T"
  shows "{up\<cdot>None}\<sharp> \<sqsubseteq> S \<and> {up\<cdot>None}\<sharp> \<sqsubseteq> T"
proof -
  let ?U = "{up\<cdot>None}\<sharp>" and ?h = "lift_up2 (\<Lambda> a b. opt_op f a b)"
  have "\<forall>T. \<not> ?U \<sqsubseteq> upper_bin\<cdot>?h\<cdot>S\<cdot>T \<or> (?U \<sqsubseteq> S \<and> ?U \<sqsubseteq> T)"
  proof (induct S rule: upper_pd_induct)
    case (upper_unit s)
    show ?case
    proof (intro allI)
      fix T
      have "?U \<sqsubseteq> {s}\<sharp> \<and> ?U \<sqsubseteq> T" if m0: "?U \<sqsubseteq> upper_bin\<cdot>?h\<cdot>{s}\<sharp>\<cdot>T"
      proof -
      have m: "?U \<sqsubseteq> upper_map\<cdot>(?h\<cdot>s)\<cdot>T" using m0 by (simp add: upper_bin_unit1)
      have T: "?U \<sqsubseteq> T" if "\<And>z. up\<cdot>None \<sqsubseteq> ?h\<cdot>s\<cdot>z \<Longrightarrow> up\<cdot>None \<sqsubseteq> z"
        by (rule upper_map_None_below[OF that m])
      show "?U \<sqsubseteq> {s}\<sharp> \<and> ?U \<sqsubseteq> T"
      proof (cases s)
        case bottom
        have "?U \<sqsubseteq> T" proof (rule T)
          fix z assume a: "up\<cdot>None \<sqsubseteq> ?h\<cdot>s\<cdot>z"
          have "up\<cdot>None \<sqsubseteq> ?h\<cdot>s\<cdot>z \<longrightarrow> up\<cdot>None \<sqsubseteq> z" by (rule option_u_cases3[of _ z]) (simp_all add: bottom)
          with a show "up\<cdot>None \<sqsubseteq> z" by blast
        qed
        then have "T = ?U" by (rule upper_unit_None_maximal)
        then show ?thesis using m bottom by simp
      next
        case (up a)
        show ?thesis
        proof (cases a)
          case None
          have "?U \<sqsubseteq> T" proof (rule T)
          fix z assume a: "up\<cdot>None \<sqsubseteq> ?h\<cdot>s\<cdot>z"
          have "up\<cdot>None \<sqsubseteq> ?h\<cdot>s\<cdot>z \<longrightarrow> up\<cdot>None \<sqsubseteq> z" by (rule option_u_cases3[of _ z]) (simp_all add: up None)
          with a show "up\<cdot>None \<sqsubseteq> z" by blast
        qed
          then show ?thesis using up None by simp
        next
          case (Some v)
          have "?U \<sqsubseteq> T" proof (rule T)
          fix z assume a: "up\<cdot>None \<sqsubseteq> ?h\<cdot>s\<cdot>z"
          have "up\<cdot>None \<sqsubseteq> ?h\<cdot>s\<cdot>z \<longrightarrow> up\<cdot>None \<sqsubseteq> z" by (rule option_u_cases3[of _ z]) (simp_all add: up Some)
          with a show "up\<cdot>None \<sqsubseteq> z" by blast
        qed
          then have "T = ?U" by (rule upper_unit_None_maximal)
          then show ?thesis using m up Some by simp
        qed
      qed
      qed
      then show "\<not> ?U \<sqsubseteq> upper_bin\<cdot>?h\<cdot>{s}\<sharp>\<cdot>T \<or> (?U \<sqsubseteq> {s}\<sharp> \<and> ?U \<sqsubseteq> T)" by blast
    qed
  next
    case (upper_plus S1 S2)
    show ?case
    proof (intro allI)
      fix T
      show "\<not> ?U \<sqsubseteq> upper_bin\<cdot>?h\<cdot>(S1 \<union>\<sharp> S2)\<cdot>T \<or> (?U \<sqsubseteq> S1 \<union>\<sharp> S2 \<and> ?U \<sqsubseteq> T)"
      proof (cases "?U \<sqsubseteq> upper_bin\<cdot>?h\<cdot>(S1 \<union>\<sharp> S2)\<cdot>T")
        case True
        then have b1: "?U \<sqsubseteq> upper_bin\<cdot>?h\<cdot>S1\<cdot>T" and b2: "?U \<sqsubseteq> upper_bin\<cdot>?h\<cdot>S2\<cdot>T" by simp_all
        have "?U \<sqsubseteq> S1" "?U \<sqsubseteq> T" using spec[OF upper_plus(1), of T] b1 by blast+
        moreover have "?U \<sqsubseteq> S2" using spec[OF upper_plus(2), of T] b2 by blast
        ultimately show ?thesis by (simp add: upper_plus_greatest)
      qed simp
    qed
  qed simp
  then show ?thesis using U by blast
qed

lemma combine_option_pd_Absent_iff: "combine_option_pd f\<cdot>x\<cdot>y = Absent \<longleftrightarrow> x = Absent \<and> y = Absent"
proof
  assume "combine_option_pd f\<cdot>x\<cdot>y = Absent"
  then have "{up\<cdot>None}\<sharp> \<sqsubseteq> upper_bin\<cdot>(lift_up2 (\<Lambda> a b. opt_op f a b))\<cdot>(Rep_option_pd x)\<cdot>(Rep_option_pd y)"
    by (simp add: combine_option_pd_apply Rep_option_pd_inject[symmetric])
  then have "{up\<cdot>None}\<sharp> \<sqsubseteq> Rep_option_pd x \<and> {up\<cdot>None}\<sharp> \<sqsubseteq> Rep_option_pd y" by (rule upper_bin_lax_None)
  then show "x = Absent \<and> y = Absent" by (simp only: Absent_below_Rep)
next
  assume "x = Absent \<and> y = Absent"
  then show "combine_option_pd f\<cdot>x\<cdot>y = Absent"
    using combine_option_pd_of_option[of f None None] by simp
qed

end
