theory FiniteCF imports HOLCF begin

default_sort type

lemma (in po) finite_has_maximal:
  fixes A :: "'a set"
  shows "\<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>x\<in>A. \<forall>y\<in>A. x \<sqsubseteq> y \<longrightarrow> x = y"
proof (induct rule: finite_ne_induct)
  case (singleton x)
    show ?case by simp
next
  case (insert a A)
  from \<open>\<exists>x\<in>A. \<forall>y\<in>A. x \<sqsubseteq> y \<longrightarrow> x = y\<close>
  obtain x where x: "x \<in> A"
           and x_eq: "\<And>y. \<lbrakk>y \<in> A; x \<sqsubseteq> y\<rbrakk> \<Longrightarrow> x = y" by fast
  show ?case
  proof (intro bexI ballI impI)
    fix y
    assume "y \<in> insert a A" and "(if x \<sqsubseteq> a then a else x) \<sqsubseteq> y"
    thus "(if x \<sqsubseteq> a then a else x) = y"
      by (auto split: if_splits intro: below_antisym dest: below_trans x_eq)
  next
    show "(if x \<sqsubseteq> a then a else x) \<in> insert a A"
      by (simp add: x)
  qed
qed

lemma (in po) smyth_ub_mono:
  assumes "\<forall>x \<in> A. \<exists>y \<in> B. x \<sqsubseteq> y"
  "B <| b"
shows "A <| b"
  using assms by (blast intro: is_ubI below_trans dest: is_ubD)

lemma (in po) lub_mono_general:
  assumes "A <<| a" "B <<| b" and smyth_ord: "\<forall>x \<in> A. \<exists>y \<in> B. x \<sqsubseteq> y"
  shows "a \<sqsubseteq> b"
proof -
  from \<open>B <<| b\<close> have "B <| b" by (rule is_lubD1)
  with smyth_ord have "A <| b" by (rule smyth_ub_mono)
  with \<open>A <<| a\<close> show "a \<sqsubseteq> b" by (rule is_lubD2)
qed

lemma (in po) ch2ch_lub_gen:
  assumes lub: "\<And>i. J i <<| Y i"
    and smyth_ord: "\<And>i. \<forall>x \<in> J i. \<exists>y \<in> J (Suc i). x \<sqsubseteq> y"
  shows "chain Y"
  by (rule chainI) (rule lub_mono_general[OF lub lub smyth_ord])


theorem ch2ch_lub:
  assumes chain: "\<And>j. j \<in> J \<Longrightarrow> chain (\<lambda>i. Y i j)"
    and lub: "\<And>i. Y i ` J <<| lub (Y i ` J)"
  shows "chain (\<lambda>i. lub (Y i ` J))"
proof -
  have "Y (Suc i) ` J <| x \<Longrightarrow> Y i ` J <| x" for i x
  proof (rule ub_imageI, drule ub_imageD)
    fix j assume "j \<in> J"
    then have "chain (\<lambda>i. Y i j)" by (rule chain)
    then have "Y i j \<sqsubseteq> Y (Suc i) j" by (rule chainE)
    also assume "Y (Suc i) j \<sqsubseteq> x"
    finally show "Y i j \<sqsubseteq> x" .
  qed
  from lub[THEN is_lubD2, OF this, OF lub[THEN is_lubD1]] show ?thesis
    by (rule chainI)
qed

theorem chain_lub_family:
  fixes Y :: "nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo"
  assumes chain: "\<And>j. j \<in> J \<Longrightarrow> chain (\<lambda>i. Y i j)"
    and lub: "\<And>i. Y i ` J <<| lub (Y i ` J)"
  defines "L \<equiv> (\<Squnion>i. lub (Y i ` J))"
  shows "(\<lambda>j. \<Squnion>i. Y i j) ` J <<| L"
proof (rule is_lubI)
  have "chain (\<lambda>i. lub (Y i ` J))" using chain lub by (rule ch2ch_lub)
  then have lub_L: "range (\<lambda>i. lub (Y i ` J)) <<| L"
    unfolding L_def by (rule cpo_lubI)
  show "(\<lambda>j. \<Squnion>i. Y i j) ` J <| L"
  proof (rule ub_imageI)
    fix j assume j: "j \<in> J"
    {
      fix i
      have "Y i j \<sqsubseteq> lub (Y i ` J)"
        using lub[of i, THEN is_lubD1, THEN ub_imageD, OF j] .
      also have "... \<sqsubseteq> L"
        using lub_L[THEN is_lubD1, THEN ub_imageD] by blast
      finally have "Y i j \<sqsubseteq> L" .
    }
    from chain[OF j] this show "(\<Squnion>i. Y i j) \<sqsubseteq> L"
      by (rule lub_below)
  qed
  show "(\<lambda>j. \<Squnion>i. Y i j) ` J <| u \<Longrightarrow> L \<sqsubseteq> u" for u
  proof -
    assume ub: "(\<lambda>j. \<Squnion>i. Y i j) ` J <| u"
    {
      fix j assume j: "j \<in> J"
      from chain[OF j] have "Y i j \<sqsubseteq> (\<Squnion>i. Y i j)" for i by (rule is_ub_thelub)
      also assume "(\<Squnion>i. Y i j) \<sqsubseteq> u"
      finally have "Y i j \<sqsubseteq> u" for i .
    }
    from this ub[THEN ub_imageD] have "Y i j \<sqsubseteq> u" if "j \<in> J" for i j using that by blast
    from lub[THEN is_lubD2, OF ub_imageI, OF this] have "lub (Y i ` J) \<sqsubseteq> u" for i by simp
    from lub_L[THEN is_lubD2, OF ub_imageI, OF this] show "L \<sqsubseteq> u".
  qed
qed

corollary chain_lub_family_converse:
  fixes Y :: "nat \<Rightarrow> 'a::type \<Rightarrow> 'b::cpo"
  assumes chain: "\<And>j. j \<in> J \<Longrightarrow> chain (\<lambda>i. Y i j)"
    and lub: "\<And>i. Y i ` J <<| lub (Y i ` J)"
  shows "range (\<lambda>i. lub (Y i ` J)) <<| (\<Squnion>j\<in>J. (\<Squnion>i. Y i j))"
proof -
  have "chain (\<lambda>i. lub (Y i ` J))" using chain lub by (rule ch2ch_lub)
  then have *: "range (\<lambda>i. lub (Y i ` J)) <<| (\<Squnion>i. lub (Y i ` J))"
    by (rule cpo_lubI)
  from chain lub have "((\<lambda>j. \<Squnion>i. Y i j) ` J) <<| (\<Squnion>i. lub (Y i ` J))"
    by (rule chain_lub_family)
  then have "lub ((\<lambda>j. \<Squnion>i. Y i j) ` J) = (\<Squnion>i. lub (Y i ` J))"
    by (rule lub_eqI)
  with * show ?thesis by simp
qed

lemma (in approx_chain) approx_ch2ch_lub:
  assumes "\<And>i. (\<lambda>x. approx i\<cdot>x) ` S <<| (\<Squnion>x \<in> S. approx i\<cdot>x)"
  shows "chain (\<lambda>i. (\<Squnion> x \<in> S. approx i\<cdot>x))"
  by (rule ch2ch_lub) (simp_all add: assms)



lemma (in approx_chain) approx_lub_family:
  assumes "\<And>i. (\<lambda>x. approx i\<cdot>x) ` S <<| (\<Squnion>x \<in> S. approx i\<cdot>x)"
  shows "S <<| (\<Squnion>i. \<Squnion>x \<in> S. approx i\<cdot>x)"
proof -
  have "S = (\<lambda>j. \<Squnion>i. approx i\<cdot>j) ` S"
  proof -
    have "(\<Squnion>i. approx i\<cdot>j) = j" for j
      using lub_approx chain_approx[THEN contlub_cfun_fun] by simp
    then show ?thesis by simp
  qed
  also have "... <<| (\<Squnion>i. \<Squnion>x \<in> S. approx i\<cdot>x)"
    by (intro chain_lub_family assms) simp
  finally show ?thesis .
qed

end