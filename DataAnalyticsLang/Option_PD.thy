theory Option_PD
  imports HOLCF "HOLCF-Library.Option_Cpo"
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

definition pd_least :: "('v option u) upper_pd" where
  "pd_least = {up\<cdot>None}\<sharp> \<union>\<sharp> {up\<cdot>(Some \<bottom>)}\<sharp>"

lemma pd_least_below:
  assumes "S \<noteq> \<bottom>"
  shows "pd_least \<sqsubseteq> S"
proof -
  have "S = \<bottom> \<or> pd_least \<sqsubseteq> S"
  proof (induct S rule: upper_pd_induct)
    case (upper_unit x)
    show ?case
    proof (cases x)
      case (up y)
      then show ?thesis by (cases y) (simp_all add: pd_least_def)
    qed simp
  next
    case (upper_plus S T)
    then show ?case by auto
  qed simp
  then show ?thesis using assms by simp
qed

lemma Rep_Abs_option_pd: "S \<noteq> \<bottom> \<Longrightarrow> Rep_option_pd (Abs_option_pd S) = S"
  by (rule Abs_option_pd_inverse) simp

lemma pd_least_nonbot: "pd_least \<noteq> \<bottom>"
  by (simp add: pd_least_def)

lemma least_option_pd: "Abs_option_pd pd_least \<sqsubseteq> y"
  unfolding below_option_pd_def Rep_Abs_option_pd[OF pd_least_nonbot] by (rule pd_least_below) simp

instance option_pd :: ("domain") pcpo
  by standard (rule exI, rule allI, rule least_option_pd)

lemma option_pd_bottom: "(\<bottom> :: 'v option_pd) = Abs_option_pd pd_least"
  by (rule below_antisym[OF minimal least_option_pd])

subsection \<open>Absent, present, maybe\<close>

definition pd_absent :: "'v option_pd" where
  "pd_absent = Abs_option_pd {up\<cdot>None}\<sharp>"

definition pd_present :: "'v \<rightarrow> 'v option_pd" where
  "pd_present = (\<Lambda> v. Abs_option_pd {up\<cdot>(Some v)}\<sharp>)"

definition pd_maybe :: "'v option_pd \<rightarrow> 'v option_pd" where
  "pd_maybe = (\<Lambda> x. Abs_option_pd (Rep_option_pd x \<union>\<sharp> {up\<cdot>None}\<sharp>))"

lemma cont_pd_present: "cont (\<lambda>v. Abs_option_pd {up\<cdot>(Some v)}\<sharp>)"
  by (rule cont_Abs_option_pd) simp_all

lemma cont_pd_maybe: "cont (\<lambda>x. Abs_option_pd (Rep_option_pd x \<union>\<sharp> {up\<cdot>None}\<sharp>))"
  by (rule cont_Abs_option_pd) (simp_all add: cont_Rep_option_pd)

lemma Rep_pd_absent [simp]: "Rep_option_pd pd_absent = {up\<cdot>None}\<sharp>"
  by (simp add: pd_absent_def Rep_Abs_option_pd)

lemma Rep_pd_present [simp]: "Rep_option_pd (pd_present\<cdot>v) = {up\<cdot>(Some v)}\<sharp>"
  by (simp add: pd_present_def cont_pd_present Rep_Abs_option_pd)

lemma Rep_pd_maybe [simp]: "Rep_option_pd (pd_maybe\<cdot>x) = Rep_option_pd x \<union>\<sharp> {up\<cdot>None}\<sharp>"
  by (simp add: pd_maybe_def cont_pd_maybe Rep_Abs_option_pd)

lemma pd_present_below_iff [simp]: "pd_present\<cdot>v \<sqsubseteq> pd_present\<cdot>w \<longleftrightarrow> v \<sqsubseteq> w"
  by (simp add: below_option_pd_def)

lemma pd_absent_not_below_present [simp]: "\<not> pd_absent \<sqsubseteq> pd_present\<cdot>v"
  by (simp add: below_option_pd_def)

lemma pd_present_not_below_absent [simp]: "\<not> pd_present\<cdot>v \<sqsubseteq> pd_absent"
  by (simp add: below_option_pd_def)

lemma pd_maybe_below: "pd_maybe\<cdot>x \<sqsubseteq> x"
  by (simp add: below_option_pd_def upper_plus_below1)

lemma pd_maybe_below_absent: "pd_maybe\<cdot>x \<sqsubseteq> pd_absent"
  by (simp add: below_option_pd_def upper_plus_below2)

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

lemma pd_absent_maximal: "pd_absent \<sqsubseteq> y \<Longrightarrow> y = pd_absent"
  unfolding below_option_pd_def Rep_pd_absent
  by (drule upper_unit_None_maximal) (simp add: Rep_option_pd_inject[symmetric])

text \<open>The least result is a value of which nothing is known, possibly absent.\<close>

lemma pd_maybe_present_bottom: "pd_maybe\<cdot>(pd_present\<cdot>\<bottom>) = \<bottom>"
  unfolding option_pd_bottom pd_maybe_def
  by (simp add: cont_pd_maybe pd_least_def upper_plus_commute)

end
