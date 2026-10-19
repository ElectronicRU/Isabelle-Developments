theory Cpo_Topology imports HOLCF HOL.Topological_Spaces begin

definition "cpopen (A :: 'a::cpo set) \<equiv> (\<forall>x \<in> A. \<forall>y. x \<sqsubseteq> y \<longrightarrow> y \<in> A) \<and> (adm (\<lambda>x. x \<notin> A))"

lemma cpopen_upper: "cpopen A \<Longrightarrow> x \<in> A \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> y \<in> A"
  by (simp add: cpopen_def)

lemma cpopen_nadm: "cpopen A \<Longrightarrow> adm (\<lambda>x. x \<notin> A)"
  by (simp add: cpopen_def)

lemma cpopen_adm: "cpopen A \<Longrightarrow> adm (\<lambda>x. x \<in> A)"
  by (fast dest!: cpopen_upper intro!: adm_upward)

lemma adm_Inf: assumes "\<forall>P \<in> U. adm P" shows "adm (Inf U)"
proof (rule admI)
  show "\<forall>i. Inf U (Y i) \<Longrightarrow> Inf U (\<Squnion>i. Y i)" if "chain Y" for Y
  proof
    fix P assume P: "P \<in> U"
    with assms have "adm P" by simp
    assume "\<forall>i. Inf U (Y i)"
    with P have "\<forall>i. P (Y i)" by auto
    with admD[OF \<open>adm P\<close> that] show "P (\<Squnion>i. Y i)" by simp
  qed
qed

theorem cpopen_Int: "cpopen A \<Longrightarrow> cpopen B \<Longrightarrow> cpopen (A \<inter> B)"
  unfolding cpopen_def
  by auto

theorem cpopen_Union: "\<forall>P \<in> U. cpopen P \<Longrightarrow> cpopen (\<Union>U)"
  unfolding cpopen_def by fastforce


interpretation cpo_topology: topological_space cpopen
proof
  show "cpopen UNIV" by (simp add: cpopen_def)
qed (fact cpopen_Int cpopen_Union)+

hide_const Topological_Spaces.compact

lemma cpopen_chain_cases[consumes 2]:
  assumes cpopen: "cpopen P" and Y: "chain Y"
  obtains "(\<Squnion>i. Y i) \<notin> P" "\<forall>i. Y i \<notin> P" |
    j where "(\<Squnion>i. Y i) \<in> P" "\<forall>i. Y (i + j) \<in> P"
proof (cases "(\<Squnion>i. Y i) \<in> P")
  case 1: False
  then have 2: "\<forall>i. Y i \<notin> P"
    by (auto intro: is_ub_thelub[OF Y] cpopen_upper[OF cpopen])
  from 1 2 show ?thesis by (rule that(1))
next
  case 1: True
  have "\<not>\<not>(\<exists>j. Y j \<in> P)"
  proof
    assume "\<nexists>j. Y j \<in> P"
    then have "\<forall>j. Y j \<notin> P"
      by simp
    with cpopen_nadm[OF cpopen, THEN admD, OF Y]
    have "(\<Squnion>i. Y i) \<notin> P" by simp
    with 1 show False by contradiction
  qed
  then have 2: "\<exists>j. Y j \<in> P" by simp
  then obtain j where "Y j \<in> P" ..
  with cpopen_upper[OF cpopen] chain_mono[OF Y]
  have 2: "Y (i + j) \<in> P" for i
    by auto
  from 1 2 show ?thesis by (fast intro: that(2))
qed

end