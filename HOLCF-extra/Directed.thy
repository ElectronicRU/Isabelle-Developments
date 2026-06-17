theory Directed imports HOLCF FiniteCF HOL.Zorn begin

default_sort type

context po begin
definition directed :: "'a set \<Rightarrow> bool" where "directed S \<equiv> \<forall>x \<in> S. \<forall>y \<in> S. \<exists>z \<in> S. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"

lemma directedI[intro]:
  assumes "\<And>x y. x \<in> S \<Longrightarrow> y \<in> S \<Longrightarrow> \<exists>z \<in> S. x \<sqsubseteq> z \<and> y \<sqsubseteq> z"
  shows "directed S"
  using assms by (simp add: directed_def)

lemma directedE[elim]:
  assumes "directed S" "x \<in> S" "y \<in> S"
  obtains z where "z \<in> S" "x \<sqsubseteq> z" "y \<sqsubseteq> z"
  using assms by (auto simp add: directed_def)

lemma directed_finite_has_lub:
  assumes directed: "directed S"
    and finite_ne: "finite S" "S \<noteq> {}"
  shows "\<exists>x \<in> S. S <<| x"
proof -
  from finite_ne
  obtain w where w: "w \<in> S"
    and w_max: "\<And>x. x \<in> S \<Longrightarrow> w \<sqsubseteq> x \<Longrightarrow> w = x"
    by (blast dest: finite_has_maximal)
  {
    fix x assume x: "x \<in> S"
    define T where "T \<equiv> {y \<in> S. x \<sqsubseteq> y}"
    from finite_ne x
    have "finite T" "T \<noteq> {}" unfolding T_def
      by auto
    then obtain wx where "wx \<in> T"
      and wx_max': "\<And>y. y \<in> T \<Longrightarrow> wx \<sqsubseteq> y \<Longrightarrow> wx = y"
      by (blast dest: finite_has_maximal)
    from \<open>wx \<in> T\<close> T_def have "x \<sqsubseteq> wx" "wx \<in> S" by auto
    have wx_max: "wx = y" if "y \<in> S" "wx \<sqsubseteq> y" for y
    proof -
      from that below_trans[OF \<open>x \<sqsubseteq> wx\<close>]
      have "y \<in> T" by (simp add: T_def)
      with that show ?thesis by (simp add: wx_max')
    qed
    have "wx = w" proof -
      from directed \<open>wx \<in> S\<close> \<open>w \<in> S\<close> obtain w'
        where "w' \<in> S" "wx \<sqsubseteq> w'" "w \<sqsubseteq> w'"
        by auto
      with w_max wx_max show ?thesis by blast
    qed
    with \<open>x \<sqsubseteq> wx\<close> have "x \<sqsubseteq> w" by simp
  }
  then have "S <| w" by (rule is_ubI)
  from this \<open>w \<in> S\<close> have "S <<| w" by (rule is_lub_maximal)
  with \<open>w \<in> S\<close> show ?thesis by rule
qed

corollary directed_finite_lub:
  "directed S \<Longrightarrow> finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> S <<| lub S"
  by (blast dest: directed_finite_has_lub intro: is_lub_lub)


corollary (in pcpo) directed_finite_lub_pcpo:
  fixes S :: "'a set"
  assumes "directed S" "finite S"
  shows "S <<| lub S"
proof (cases "S = {}")
  case True
  then have "S <<| \<bottom>" by (simp add: is_lub_def is_ub_def)
  then show ?thesis by (rule is_lub_lub)
next
  case False
  with assms show ?thesis by (rule directed_finite_lub)
qed

corollary finite_directed_lub_mem:
"lub S \<in> S" if "directed S" "finite S" "S \<noteq> {}"
proof -
  from that obtain w where "w \<in> S" "S <<| w"
    using directed_finite_has_lub by blast
  then show ?thesis by (subst lub_eqI)
qed

lemma directed_mono_image:
  fixes f :: "'a \<Rightarrow> 'b::po"
  assumes "\<And>x y. x \<sqsubseteq> y \<Longrightarrow> f x \<sqsubseteq> f y"
  "directed S"
shows "directed (f ` S)" 
  using assms(2) 
  unfolding directed_def po_class.directed_def
  by (blast intro: assms(1))

lemma chain_directed: "directed (range C)" if "chain C"
proof (rule, clarsimp)
  fix i j
  from chain_mono[OF that]
  show "\<exists>k. C i \<sqsubseteq> C k \<and> C j \<sqsubseteq> C k"
    by (cases rule: le_cases[of i j]) blast+
qed

end

class dcpo = po +
  assumes dcpo: "\<And>S. directed S \<Longrightarrow> \<exists>x. S <<| x"
begin
theorem directed_lub: "directed S \<Longrightarrow> S <<| lub S"
  using dcpo is_lub_lub by auto
end

subclass (in dcpo) cpo
proof
  fix S :: "nat \<Rightarrow> 'a"
  assume "chain S"
  from chain_directed[OF this] show "\<exists>x. range S <<| x"
    using directed_lub by blast
qed

subclass (in dcpo) pcpo
proof
  have "directed {}" by auto
  then obtain x where "{} <<| x" using dcpo by blast
  then have "x \<sqsubseteq> y" for y using is_lubD2 is_ubI by simp
  then show "\<exists>x. \<forall>y. x \<sqsubseteq> y" by auto
qed

instance bifinite \<subseteq> dcpo
proof
  fix S :: "'a set"
  assume "directed S"
  obtain a :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where "approx_chain a"
    using bifinite ..
  then interpret approx_chain a .
  define T where "T i = (\<lambda>x. a i\<cdot>x) ` S" for i
  {
    fix i
    have "directed (T i)"
      using monofun_cfun_arg \<open>directed S\<close> 
      unfolding T_def
      by (rule directed_mono_image)
    moreover have "finite (T i)"
      by (simp add: T_def finite_deflation.finite_image)
    ultimately have "T i <<| lub (T i)"
      by (rule directed_finite_lub_pcpo)
  }
  from approx_lub_family[OF this[unfolded T_def]]
  show "\<exists>x. S <<| x" ..
qed

primrec chainify :: "'a::po set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)"
  where "chainify A f 0 = f 0"
  | "chainify A f (Suc n) = (SOME x. x \<in> A \<and> chainify A f n \<sqsubseteq> x \<and> f (Suc n) \<sqsubseteq> x)"

lemma chainifyPropI:
  assumes "directed S"
    "f (Suc i) \<in> S" "chainify S f i \<in> S"
  shows "chainify S f (Suc i) \<in> S
    \<and> chainify S f i \<sqsubseteq> chainify S f (Suc i)
    \<and> f (Suc i) \<sqsubseteq> chainify S f (Suc i)"
proof -
  from assms obtain x where "x \<in> S \<and> chainify S f i \<sqsubseteq> x \<and> f (Suc i) \<sqsubseteq> x"
    by auto
  from someI[of "\<lambda>x. x \<in> S \<and> chainify S f i \<sqsubseteq> x \<and> f (Suc i) \<sqsubseteq> x", OF this]
  show ?thesis by simp
qed

lemma chainify_directed_mem:
  assumes "directed S" "\<And>i. f i \<in> S"
  shows "chainify S f i \<in> S"
proof (induct i)
  case 0
  then show ?case by (simp add: assms(2))
next
  case (Suc i)
  from chainifyPropI[OF assms this] show ?case by blast
qed

lemma chainify_directed_chain:
  assumes "directed S" "\<And>i. f i \<in> S"
  shows "chain (chainify S f)"
proof (rule chainI)
  fix i
  have "chainify S f i \<in> S"
    using assms by (rule chainify_directed_mem)
  from chainifyPropI[OF assms this]
  show "chainify S f i \<sqsubseteq> chainify S f (Suc i)" by simp
qed

lemma chainify_directed_below:
  assumes "directed S" "\<And>i. f i \<in> S"
  shows "f i \<sqsubseteq> chainify S f i"
proof (cases i)
  case 0
  then show ?thesis by simp
next
  case (Suc i)
  have "chainify S f i \<in> S"
    using assms by (rule chainify_directed_mem)
  from chainifyPropI[OF assms this]
  show ?thesis unfolding Suc by simp
qed

lemma lub_subset_mono:
  assumes "A <<| a" "B <<| b" "A \<subseteq> B"
  shows "a \<sqsubseteq> b"
proof -
  from \<open>B <<| b\<close> have "B <| b" by (rule is_lubD1)
  with \<open>A \<subseteq> B\<close> have "A <| b" unfolding is_ub_def by blast
  with \<open>A <<| a\<close> show ?thesis by (rule is_lubD2)
qed

lemma obtain_directed_chain:
  fixes S :: "'a::bifinite set"
  assumes "directed S" "S \<noteq> {}"
  obtains C where "chain C" "\<forall>i. C i \<in> S" "(\<Squnion>i. C i) = lub S"
proof -
  obtain a :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where "approx_chain a"
    using bifinite ..
  then interpret approx_chain a . 
  define T where "T i = (\<lambda>x. a i\<cdot>x) ` S" for i
  have "directed (T i)" for i
    using monofun_cfun_arg \<open>directed S\<close> 
    unfolding T_def
    by (rule directed_mono_image)
  moreover have "finite (T i)" for i
    by (simp add: T_def finite_deflation.finite_image)
  ultimately have T_lub: "T i <<| lub (T i)" for i
    by (rule directed_finite_lub_pcpo)
  then have SleT: "S <<| (\<Squnion>i. lub (T i))"
    unfolding T_def
    by (rule approx_lub_family)
  from T_lub have chainT: "chain (\<lambda>i. lub (T i))"
    unfolding T_def
    by (rule approx_ch2ch_lub)
  have "T i \<noteq> {}" for i by (simp add: \<open>S \<noteq> {}\<close> T_def)
  with \<open>\<And>i. directed (T i)\<close> \<open>\<And>i. finite (T i)\<close>
  have "lub (T i) \<in> T i" for i
    by (rule finite_directed_lub_mem)
  then have "\<exists>x \<in> S. a i\<cdot>x = lub (T i)" for i
    unfolding T_def using imageE by metis
  with approx_below have "\<exists>x \<in> S. lub (T i) \<sqsubseteq> x" for i
    by metis
  then obtain f where f: "f i \<in> S" and f_above: "lub (T i) \<sqsubseteq> f i" for i
    by metis
  define C where "C i \<equiv> chainify S f i" for i
  from \<open>directed S\<close> f have
    Cmem: "\<And>i. C i \<in> S"
    and chainC: "chain C"
    and aboveC: "\<And>i. f i \<sqsubseteq> C i"
    unfolding C_def
    by (auto intro:
        chainify_directed_mem chainify_directed_chain
        chainify_directed_below)
  from f_above aboveC have "lub (T i) \<sqsubseteq> C i" for i
    by (rule below_trans)
  with chainT chainC have TleC: "(\<Squnion>i. lub (T i)) \<sqsubseteq> (\<Squnion>i. C i)"
    by (rule lub_mono)
  from SleT have "S <<| lub S" by (rule is_lub_lub)
  with cpo_lubI[OF chainC] have CleS: "(\<Squnion>i. C i) \<sqsubseteq> lub S"
    by (blast intro: Cmem lub_subset_mono)
  from SleT have "lub S = (\<Squnion>i. lub (T i))" by (rule lub_eqI)
  with CleS TleC below_antisym have "(\<Squnion>i. C i) = lub S" by auto
  from chainC Cmem this show thesis using that by presburger
qed

text \<open>In a bifinite (hence directed-complete) domain a continuous function preserves
  \emph{directed} lubs, not just lubs of chains: the image of a nonempty directed set has
  the image of the lub as its least upper bound.  The directed set is replaced by a cofinal
  chain via @{thm obtain_directed_chain}, on which ordinary continuity applies.

  Combined with distributivity this shows that binary meet preserves \emph{all} existing
  lubs — finite ones by the distributive law \<open>meet_join_distrib\<close>, directed ones by this lemma.\<close>
lemma cont_directed_is_lub:
  fixes S :: "'a::bifinite set"
  assumes cont: "cont f" and dir: "directed S" and ne: "S \<noteq> {}"
  shows "f ` S <<| f (lub S)"
proof -
  have mono: "monofun f" using cont by (rule cont2mono)
  from dir ne obtain C where chainC: "chain C" and Cmem: "\<forall>i. C i \<in> S"
    and Club: "(\<Squnion>i. C i) = lub S"
    by (rule obtain_directed_chain)
  have fC: "f (lub S) = (\<Squnion>i. f (C i))"
    using Club cont2contlubE[OF cont chainC] by simp
  show "f ` S <<| f (lub S)"
  proof (rule is_lubI)
    show "f ` S <| f (lub S)"
    proof (rule is_ubI)
      fix z assume "z \<in> f ` S"
      then obtain s where s: "s \<in> S" and z: "z = f s" by blast
      from dir have "S <<| lub S" by (rule directed_lub)
      with s have "s \<sqsubseteq> lub S" by (auto dest: is_lubD1 is_ubD)
      then have "f s \<sqsubseteq> f (lub S)" by (rule monofunE[OF mono])
      with z show "z \<sqsubseteq> f (lub S)" by simp
    qed
  next
    fix u assume ub: "f ` S <| u"
    have chfC: "chain (\<lambda>i. f (C i))" using mono chainC by (rule ch2ch_monofun)
    have "(\<Squnion>i. f (C i)) \<sqsubseteq> u"
    proof (rule lub_below[OF chfC])
      fix i
      from Cmem have "f (C i) \<in> f ` S" by blast
      with ub show "f (C i) \<sqsubseteq> u" by (rule is_ubD)
    qed
    with fC show "f (lub S) \<sqsubseteq> u" by simp
  qed
qed

corollary cont_directed_lub:
  fixes S :: "'a::bifinite set"
  assumes "cont f" and "directed S" and "S \<noteq> {}"
  shows "lub (f ` S) = f (lub S)"
  using cont_directed_is_lub[OF assms] by (rule lub_eqI)

lemma directed_admD:
  fixes D :: "'a::bifinite set"
  assumes "adm P" and D: "directed D" "D \<noteq> {}"
    and forall: "\<forall>x \<in> D. P x"
  shows "P (lub D)"
proof -
  from obtain_directed_chain[OF D]
  obtain C where "chain C" and mem: "\<forall>i. C i \<in> D" and lub: "(\<Squnion>i. C i) = lub D" .
  from forall mem have "\<forall>i. P (C i)" by fast
  with admD[OF \<open>adm P\<close> \<open>chain C\<close>] lub
  show "P (lub D)" by simp
qed

definition "Chain C \<equiv> \<forall>a \<in> C. \<forall>b \<in> C. a \<sqsubseteq> b \<or> b \<sqsubseteq> a"

lemma ChainE: assumes "Chain C" "a \<in> C" "b \<in> C"
  obtains "a \<sqsubseteq> b" | "b \<sqsubseteq> a"
  using assms unfolding Chain_def by auto

lemma Chain_directedI: "Chain C \<Longrightarrow> directed C"
  unfolding Chain_def directed_def by metis

lemma Chain_mono_image: "monofun f \<Longrightarrow> Chain C \<Longrightarrow> Chain (f ` C)"
  unfolding Chain_def
  by (auto dest: monofunE)

lemma chain_ChainI: "Chain (range C)" if "chain C"
  unfolding Chain_def
proof (intro strip)
  fix a b assume "a \<in> range C" "b \<in> range C"
  then obtain i j where ab: "a = C i" "b = C j" by blast
  from chain_mono[OF that] have "C i \<sqsubseteq> C j \<or> C j \<sqsubseteq> C i"
    by (cases rule: le_cases[of i j]) auto
  with ab show "a \<sqsubseteq> b \<or> b \<sqsubseteq> a" by simp
qed

lemma po_Zorn_lemma:
  fixes A :: "'a::po set"
  assumes "\<And>C. Chain C \<Longrightarrow> C \<subseteq> A \<Longrightarrow> \<exists> u \<in> A. C <| u"
  shows "\<exists> m \<in> A. \<forall> a \<in> A. m \<sqsubseteq> a \<longrightarrow> a = m"
proof (rule predicate_Zorn)
  show "partial_order_on A (relation_of below A)"
    by (rule partial_order_on_relation_ofI)
      (auto intro: below_trans below_antisym)
next
  fix C assume "C \<in> Zorn.Chains (relation_of below A)"
  then have "Chain C" "C \<subseteq> A"
    by (auto simp add: Zorn.Chains_def Chain_def relation_of_def)
  then have "\<exists>u \<in> A. C <| u" by (rule assms)
  then show "\<exists>u \<in> A. \<forall>a \<in> C. a \<sqsubseteq> u" by (simp add: is_ub_def)
qed

theorem obtain_total_above:
  fixes S :: "'a::po set" and x :: 'a
  assumes x: "x \<in> S" and directed: "\<And>T. T \<subseteq> S \<Longrightarrow> directed T \<Longrightarrow> \<exists>a \<in> S. T <| a"
  obtains y where "y \<in> S" "x \<sqsubseteq> y" "\<forall>z \<in> S. y \<sqsubseteq> z \<longrightarrow> y = z"
proof -
  define S_above where "S_above = {y \<in> S. x \<sqsubseteq> y}"
  have S_above_iff: "y \<in> S_above \<longleftrightarrow> x \<sqsubseteq> y \<and> y \<in> S" for y
    by (auto simp add: S_above_def)
  have "\<exists>m \<in> S_above. \<forall>y \<in> S_above. m \<sqsubseteq> y \<longrightarrow> y = m"
  proof (rule po_Zorn_lemma)
    fix C assume "Chain C" "C \<subseteq> S_above"
    then have "C \<subseteq> S" "directed C"
      by (auto intro: Chain_directedI simp: S_above_def)
    then obtain a where "a \<in> S" "C <| a" 
      by (blast dest: directed)
    show "\<exists>u \<in> S_above. C <| u"
    proof (cases "C = {}")
      case True
      then show ?thesis
        by (intro bexI[where x=x]) (auto simp add: x S_above_def)
    next
      case False
      then obtain y where "y \<in> C" by blast
      with \<open>C <| a\<close> have "y \<sqsubseteq> a" by (rule is_ubD)
      from \<open>y \<in> C\<close> \<open>C \<subseteq> S_above\<close> S_above_def
      have "x \<sqsubseteq> y" by auto
      from below_trans[OF this \<open>y \<sqsubseteq> a\<close>] \<open>a \<in> S\<close>
      have "a \<in> S_above" by (simp add: S_above_def)
      from this \<open>C <| a\<close> show ?thesis by blast
    qed
  qed
  then obtain m where "m \<in> S_above" and m_max: "\<forall>y. y \<in> S_above \<longrightarrow> m \<sqsubseteq> y \<longrightarrow> m = y"
    by blast
  from \<open>m \<in> S_above\<close> have "m \<in> S" "x \<sqsubseteq> m" by (simp_all add: S_above_iff)
  have "m = y" if "y \<in> S" "m \<sqsubseteq> y" for y
  proof -
    from \<open>x \<sqsubseteq> m\<close> \<open>m \<sqsubseteq> y\<close> have "x \<sqsubseteq> y" by (rule below_trans)
    with \<open>y \<in> S\<close> have "y \<in> S_above" by (simp add: S_above_iff)
    with m_max \<open>m \<sqsubseteq> y\<close> show "m = y" by blast
  qed
  from \<open>m \<in> S\<close> \<open>x \<sqsubseteq> m\<close> this
  show thesis
    using that[of m]
    by blast
qed

lemma directed_join_of_finite_subsets:
  fixes A :: "'a::dcpo set"
  assumes lubs: "\<And>B. B \<in> Fpow(A) \<Longrightarrow> B <<| lub B"
  shows directed_lubs: "directed (lub ` Fpow(A))"
    and lub_lub: "A <<| lub (lub ` Fpow(A))"
proof -
  show "directed (lub ` Fpow(A))"
  proof (intro directedI, safe)
    fix x y assume xy: "x \<in> Fpow(A)" "y \<in> Fpow(A)"
    then have un: "x \<union> y \<in> Fpow(A)" by (auto simp add: Fpow_def)
    with xy lubs have "lub x \<sqsubseteq> lub (x \<union> y) \<and> lub y \<sqsubseteq> lub (x \<union> y)"
      using lub_subset_mono by fast
    with un show "\<exists>z \<in> lub ` Fpow(A). lub x \<sqsubseteq> z \<and> lub y \<sqsubseteq> z" by fast
  qed
  then have pa_lub: "lub ` Fpow(A) <<| lub (lub ` Fpow(A))" by (rule directed_lub)
  show "A <<| lub (lub ` Fpow(A))"
  proof (intro is_lubI is_ubI)
    fix x assume "x \<in> A"
    then have "{x} \<in> Fpow(A)" by (simp add: Fpow_def)
    then have "x \<in> lub ` Fpow(A)" by force
    with pa_lub[THEN is_lubD1, THEN is_ubD] show "x \<sqsubseteq> lub (lub ` Fpow(A))" .
  next
    fix u assume "A <| u"
    then have "B \<in> Fpow(A) \<Longrightarrow> B <| u" for B by (auto simp add: Fpow_def is_ub_def)
    with lubs[THEN is_lubD2] have "B \<in> Fpow(A) \<Longrightarrow> lub B \<sqsubseteq> u" for B by simp
    then have "lub ` Fpow(A) <| u" by (rule ub_imageI)
    with pa_lub[THEN is_lubD2] show "lub (lub ` Fpow(A)) \<sqsubseteq> u" .
  qed
qed

section \<open>Lemmas concerning completion, complete sets and closed sets\<close>

context fixes A :: "'a::bifinite set"
begin

definition "chain_complete \<equiv> \<forall>C. chain C \<and> range C \<subseteq> A \<longrightarrow> Lub C \<in> A"

definition "dcomplete \<equiv> \<forall>B. B \<subseteq> A \<and> directed B \<and> B \<noteq> {} \<longrightarrow> lub B \<in> A"

lemma chain_complete_iff_dcomplete:
  "chain_complete \<longleftrightarrow> dcomplete"
  unfolding chain_complete_def dcomplete_def
  apply (rule iffI)
  using obtain_directed_chain
   apply (metis image_subsetI subsetD)
  using chain_directed by blast

end



end