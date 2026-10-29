theory Option_PD
  imports HOLCF "HOLCF-Library.Option_Cpo" "HOLCF-extra.Pointed_Profinite"
begin

section \<open>Results with possible absence\<close>

text \<open>A result is a set of possible outcomes, each either absent (\<open>None\<close>) or a value: an element
  of the upper powerdomain over the lifted outcomes, without its bottom.  The one element of the
  powerdomain that contains the lifted bottom is its bottom, so the rest is a cpo; it is pointed
  again, by \<open>{None, Some \<bottom>}\<close>: possibly absent, otherwise an unknown value.  A definite absence is
  \<open>{None}\<close>, a definite value \<open>v\<close> is \<open>{Some v}\<close>, and \<open>{None, Some v}\<close> is the value \<open>v\<close>, if present.\<close>

cpodef 'v option_pd = "{S :: ('v option u) upper_pd. S \<noteq> \<bottom>}"
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

instance option_pd :: ("domain") pcpo
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

instance option_pd :: ("domain") profinite
proof
  obtain a :: "nat \<Rightarrow> ('a option u) upper_pd \<rightarrow> ('a option u) upper_pd" where "approx_chain a"
    using bifinite by blast
  then show "\<exists>a :: nat \<Rightarrow> 'a option_pd u \<rightarrow> 'a option_pd u. approx_chain a"
    by (blast intro: approx_chain_iso lift_lower_option_pd lower_lift_option_pd)
qed

instance option_pd :: ("domain") bifinite
  by (rule bifinite_profinite_pointed)

subsection \<open>Absent, present, and their sums\<close>

definition Absent :: "'v option_pd" where
  "Absent = Abs_option_pd {up\<cdot>None}\<sharp>"

definition Present :: "'v \<rightarrow> 'v option_pd" where
  "Present = (\<Lambda> v. Abs_option_pd {up\<cdot>(Some v)}\<sharp>)"

text \<open>The sum of two results has the outcomes of both; \<open>Present\<cdot>v + Absent\<close> is the value \<open>v\<close>, if
  present.\<close>

instantiation option_pd :: ("domain") plus
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

end
