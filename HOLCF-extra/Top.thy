theory Top imports HOLCF begin

datatype 'a::type top = Of (top_down: 'a) | Top

instantiation top :: (below) below
begin
definition below_top_def:
"(\<sqsubseteq>) a b \<equiv> case b of Top \<Rightarrow> True |
  Of b \<Rightarrow> (case a of Top \<Rightarrow> False | Of a \<Rightarrow> a \<sqsubseteq> b)"

instance ..

theorem below_Top[simp]: "x \<sqsubseteq> Top" by (simp add: below_top_def)

theorem Top_below[simp]: "Top \<sqsubseteq> x \<longleftrightarrow> x = Top" by (cases x) (simp_all add: below_top_def)

theorem below_Of: "Of x \<sqsubseteq> Of y \<longleftrightarrow> x \<sqsubseteq> y" by (simp add: below_top_def)

end

instance top :: (po) po
  by (intro_classes)
   (auto simp add: below_top_def 
     intro: below_trans below_antisym
     split: top.splits)

lemma not_Top: assumes "x \<noteq> Top" obtains y where "x = Of y"
using assms by (cases x) simp_all

lemma ch2ch_top:
  assumes "chain S" 
    "Top \<notin> range S"
  obtains T where "chain T" "S = (\<lambda>i. Of (T i))"
proof -
  from \<open>Top \<notin> range S\<close>[THEN notE, OF range_eqI] have "S i \<noteq> Top" for i by metis
  then obtain T where T: "S = (\<lambda>i. Of (T i))" using not_Top by meson
  then have "chain T" using \<open>chain S\<close>[THEN chainE, unfolded below_top_def] 
    by (auto intro: chainI)
  from this T show ?thesis by (rule that)
qed

lemma top_chlub_Of: assumes "chain (T::nat\<Rightarrow>'a::cpo)"
  shows "range (\<lambda>i. Of (T i)) <<| Of (\<Squnion>i. T i)"
proof (intro is_lubI is_ubI)
  show "x \<in> range (\<lambda>i. Of (T i)) \<Longrightarrow> x \<sqsubseteq> Of (\<Squnion>i. T i)"
    for x by (auto simp add: is_ub_thelub[OF assms] below_Of)
  show "range (\<lambda>i. Of (T i)) <| u \<Longrightarrow> Of (\<Squnion>i. T i) \<sqsubseteq> u" for u
    apply (induction u)
     apply (fastforce intro: lub_below[OF assms] dest: is_ubD simp add: below_Of)
    apply simp
    .
qed

lemma top_lub_Top:
"Top \<in> X \<Longrightarrow> X <<| Top"
  apply (intro is_lubI is_ubI)
   apply simp
  apply (fastforce dest: is_ubD)
  .

lemma lub_Top_iff: "range (S::nat\<Rightarrow>'a::cpo top) <<| Top \<longleftrightarrow> Top \<in> range S" if "chain S"
proof (cases "Top \<in> range S")
  case True
  then show ?thesis by (simp add: top_lub_Top)
next
  case False
  from \<open>chain S\<close> this obtain T where "chain T" "S = (\<lambda>i. Of (T i))"
    by (rule ch2ch_top)
  then have "range S <<| Of (\<Squnion>i. T i)" by (blast intro: top_chlub_Of)
  with \<open>Top \<notin> range S\<close> show ?thesis by (blast dest: is_lub_unique)
qed

instantiation top :: (cpo) cpo
begin

instance
proof
  fix S :: "nat \<Rightarrow> 'a top" assume "chain S"
  show "\<exists>x. range S <<| x"
  proof (cases "Top \<in> range S")
    case True
    then show ?thesis by (blast intro: top_lub_Top)
  next
    case False
    from \<open>chain S\<close> this show ?thesis by (blast elim: ch2ch_top intro: top_chlub_Of)
  qed
qed

theorem compact_Top: "compact (Top :: 'a top)"
  unfolding compact_def
proof (rule admI)
  fix Y :: "nat \<Rightarrow> 'a top" assume "chain Y"
  assume "\<forall>i. \<not>(Top \<sqsubseteq> Y i)"
  then have "\<And>i. Y i \<noteq> Top" by simp
  then have "Top \<notin> range Y" by (metis rangeE)
  from \<open>chain Y\<close> this have "(\<Squnion>i. Y i) \<noteq> Top"
    using cpo_lubI lub_Top_iff by metis
  then show "\<not>(Top \<sqsubseteq> (\<Squnion>i. Y i))" by simp
qed

end

instantiation top :: (pcpo) pcpo
begin

lemma of_bot_below: "Of \<bottom> \<sqsubseteq> y" by (cases y) (simp_all add: below_Of)

instance by (intro_classes, intro exI[of _ "Of \<bottom>"] allI of_bot_below)


theorem top_bot: "(\<bottom>::'a top) = Of \<bottom>"
  by (rule bottomI[symmetric]) (rule of_bot_below)

end

definition "down \<equiv> (\<Lambda> x. Of x)"

theorem cont_Of[simp]: "cont Of"
  by (rule contI) (rule top_chlub_Of)

theorem down_beta: "down\<cdot>x = Of x"
  unfolding down_def by simp
theorem top_cases[case_names down Top, cases type: top]:
  "(\<And>p. x = down\<cdot>p \<Longrightarrow> P) \<Longrightarrow> (x = Top \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases x) (simp_all add: down_beta)

theorem down_inject: "down\<cdot>x = down\<cdot>y \<Longrightarrow> x = y"
  by (simp add: down_beta)

lemma top_chain_cases [consumes 1]:
  fixes Y :: "nat \<Rightarrow> 'a::cpo top"
  assumes "chain Y"
  obtains (down) X where "chain X" "Y = (\<lambda>i. down\<cdot>(X i))" "(\<Squnion>i. Y i) = down\<cdot>(\<Squnion>i. X i)"
  | (Top) "finite_chain Y" "\<exists>i. Y i = Top" "(\<Squnion>i. Y i) = Top"
proof (cases "Top \<in> range Y")
  assume "Top \<in> range Y"
  then have 3: "(\<Squnion>i. Y i) = Top" using lub_Top_iff[OF assms] lub_eqI by blast
  with assms \<open>Top \<in> range Y\<close> have 1: "finite_chain Y"
    using finite_chain_def maxinch_is_thelub by fastforce
  from \<open>Top \<in> range Y\<close>[THEN rangeE] have 2: "\<exists>i. Y i = Top" by metis
  from 1 2 3 show thesis by (rule that(2))
next
  assume "Top \<notin> range Y"
  from ch2ch_top[OF assms this] obtain X where 1: "chain X" and 2: "Y = (\<lambda>i. Of (X i))" .
  then have "range Y <<| Of (\<Squnion>i. X i)" using top_chlub_Of by blast
  then have 3: "(\<Squnion>i. Y i) = Of (\<Squnion>i. X i)" by (rule lub_eqI)
  from 1 2 3 show thesis by (rule that(1)[unfolded down_beta])
qed

definition "cmap_top \<equiv> (\<Lambda> f x. map_top (\<lambda>x. f\<cdot>x) x)"

lemma cmap_top_cont1[cont2cont]: "cont (map_top f)" if "cont f"
proof (rule contI)
  fix Y :: "nat \<Rightarrow> 'a top" assume "chain Y"
  then show "range (\<lambda>i. map_top f (Y i)) <<| map_top f (\<Squnion>i. Y i)"
  proof (cases rule: top_chain_cases)
    case (down X)
    from that \<open>chain X\<close> have fX: "chain (\<lambda>i. f (X i))" by (rule ch2ch_cont)
    from \<open>Y = (\<lambda>i. down\<cdot>(X i))\<close> have "(\<lambda>i. map_top f (Y i)) = (\<lambda>i. Of (f (X i)))"
      by (simp add: down_beta)
    then have "range (\<lambda>i. map_top f (Y i)) <<| Of (\<Squnion>i. f (X i))" using top_chlub_Of[OF fX]
      by presburger
    also have "(\<Squnion>i. f (X i)) = f (\<Squnion>i. X i)" using that \<open>chain X\<close> by (rule cont2contlubE[symmetric])
    also from \<open>(\<Squnion>i. Y i) = down\<cdot>(\<Squnion>i. X i)\<close> have "Of ... = map_top f (\<Squnion>i. Y i)"
      by (simp add: down_beta)
    finally show ?thesis .
  next
    case Top
    from \<open>finite_chain Y\<close> obtain i where "max_in_chain i Y" by (rule finite_chainE)
    with \<open>(\<Squnion>i. Y i) = Top\<close> have "Y i = Top" using maxinch_is_thelub[OF \<open>chain Y\<close>]
      by simp
    then have "map_top f (Y i) = Top" by simp
    then have "Top \<in> range (\<lambda>i. map_top f (Y i))" using range_eqI by metis
    then have "... <<| Top" by (rule top_lub_Top)
    also have "Top = map_top f (\<Squnion>i. Y i)" using \<open>(\<Squnion>i. Y i) = Top\<close> by simp
    finally show ?thesis .
  qed
qed

lemma cmap_top_cont2[cont2cont]: "cont (\<lambda>f. map_top (\<lambda>x. f\<cdot>x) x)"
  by (cases x) (auto simp add: down_beta intro: cont_compose)

lemma cmap_top_beta: "cmap_top\<cdot>f\<cdot>x = map_top (\<lambda>x. f\<cdot>x) x"
  unfolding cmap_top_def
  by (simp add: cmap_top_cont1 cmap_top_cont2 cont2cont_LAM)

lemma cmap_top_down[simp]: "cmap_top\<cdot>f\<cdot>(down\<cdot>x) = down\<cdot>(f\<cdot>x)" by (simp add: cmap_top_beta down_beta)
lemma cmap_top_Top[simp]: "cmap_top\<cdot>f\<cdot>Top = Top" by (simp add: cmap_top_beta)
lemma cmap_top_ID[simp]: "cmap_top\<cdot>ID = ID"
proof (rule cfun_eqI)
  show "cmap_top\<cdot>ID\<cdot>x = ID\<cdot>x" for x
    by (cases x) simp_all
qed

lemma down_strict: "down\<cdot>\<bottom> = \<bottom>" by (simp add: down_beta top_bot)

lemma down_below_of: "down\<cdot>x \<sqsubseteq> down\<cdot>y \<Longrightarrow> x \<sqsubseteq> y" by (simp add: down_beta below_Of)
lemma down_below_iff[iff]: "down\<cdot>x \<sqsubseteq> down\<cdot>y \<longleftrightarrow> x \<sqsubseteq> y" by (rule iffI) (auto intro: monofun_cfun_arg down_below_of)

lemma down_ne_Top[simp]: "down\<cdot>x \<noteq> Top" "Top \<noteq> down\<cdot>x" by (simp_all add: down_beta)

lemma approx_chain_top:
  assumes "approx_chain a"
  shows "approx_chain (\<lambda>i. cmap_top\<cdot>(a i))"
proof -
  interpret approx_chain a by fact
  show ?thesis
  proof
    show "chain (\<lambda>i. cmap_top\<cdot>(a i))" by (simp add: ch2ch_Rep_cfunR)
    show "(\<Squnion>i. cmap_top\<cdot>(a i)) = ID" by (simp add: contlub_cfun_arg[symmetric])
    show "cmap_top\<cdot>(a i)\<cdot>(cmap_top\<cdot>(a i)\<cdot>x) = cmap_top\<cdot>(a i)\<cdot>x" for i x
      by (cases x) (simp_all add: approx_idem)
    show "cmap_top\<cdot>(a i)\<cdot>x \<sqsubseteq> x" for i x by (cases x) (simp_all add: approx_below)
    show "finite {x. cmap_top\<cdot>(a i)\<cdot>x = x}" for i
    proof -
      have "{x. cmap_top\<cdot>(a i)\<cdot>x = x} = insert Top {down\<cdot>x | x. (a i)\<cdot>x = x}"
        (is "?l = ?r")
      proof (rule set_eqI)
        fix x show "x \<in> ?l \<longleftrightarrow> x \<in> ?r"
          by (cases x) (auto dest: down_inject)
      qed
      also have "finite ..."
        using finite_deflation.finite_fixes[OF finite_deflation_approx]
        by simp
      finally show ?thesis.
    qed
  qed
qed

instance top :: (bifinite) bifinite
  by intro_classes (blast intro: bifinite[THEN exE, THEN approx_chain_top])

definition Iftop where "Iftop t f x \<equiv> case x of Top \<Rightarrow> t | Of x \<Rightarrow> f\<cdot>x"

lemma Iftop_down: "Iftop t f (down\<cdot>x) = f\<cdot>x" by (simp add: Iftop_def down_beta)

lemma Iftop_top: "Iftop t f Top = t" by (simp add: Iftop_def)

lemma cont_Iftop: "cont (\<lambda>x. Iftop t f x)" if t_is_top: "\<And>x. x \<sqsubseteq> t"
proof (rule contI)
  fix Y :: "nat \<Rightarrow> 'b top"  assume "chain Y"
  then show "range (\<lambda>i. Iftop t f (Y i)) <<|
         Iftop t f (\<Squnion>i. Y i)"
  proof (cases Y rule: top_chain_cases)
    case (down X)
    from \<open>Y = (\<lambda>i. down\<cdot>(X i))\<close> have *:"(\<lambda>i. Iftop t f (Y i)) = (\<lambda>i. f\<cdot>(X i))"
      by (simp add: Iftop_down)
    from \<open>(\<Squnion>i. Y i) = down\<cdot>(\<Squnion>i. X i)\<close> have **: "Iftop t f (\<Squnion>i. Y i) = f\<cdot>(\<Squnion>i. X i)"
      by (simp add: Iftop_down)
    from \<open>chain X\<close> show ?thesis  unfolding * **
      by (intro contE) auto
  next
    case Top
    from \<open>finite_chain Y\<close> obtain i where "max_in_chain i Y" by (rule finite_chainE)
    with \<open>(\<Squnion>i. Y i) = Top\<close> have "Top = Y i" using maxinch_is_thelub[OF \<open>chain Y\<close>] by simp
    then have "t = Iftop t f (Y i)" by (simp add: Iftop_top)
    then have "t \<in> range (\<lambda>i. Iftop t f (Y i))" by (rule range_eqI)
    then have "range (\<lambda>i. Iftop t f (Y i)) <<| t"
      unfolding is_lub_def is_ub_def using t_is_top by blast
    moreover have "t = Iftop t f (\<Squnion>i. Y i)" by (simp add: \<open>(\<Squnion>i. Y i) = Top\<close> Iftop_top)
    ultimately show ?thesis by presburger
  qed
qed


definition up_top_to_top_up :: "'a::cpo u top \<rightarrow> 'a top u"
  where "up_top_to_top_up = (\<Lambda> x. Iftop (up\<cdot>Top) (\<Lambda> (up\<cdot>x). up\<cdot>(down\<cdot>x)) x)"

lemma utttu_beta: "up_top_to_top_up\<cdot>x = Iftop (up\<cdot>Top) (\<Lambda> (up\<cdot>x). up\<cdot>(down\<cdot>x)) x"
  unfolding up_top_to_top_up_def
proof (rule beta_cfun, rule cont_Iftop)
  show "x \<sqsubseteq> up\<cdot>Top" for x by (cases x) simp_all
qed

definition top_up_to_up_top :: "'a::cpo top u \<rightarrow> 'a u top"
  where "top_up_to_up_top = (\<Lambda> (up\<cdot>x). Iftop Top (down oo up) x)"

lemma tutut_beta_minor: "(\<Lambda> x. Iftop Top (down oo up) x)\<cdot>x = Iftop Top (down oo up) x"
  by (rule beta_cfun, rule cont_Iftop, rule below_Top)

theorem utttu_cases:
  "up_top_to_top_up\<cdot>Top = up\<cdot>Top"
  "up_top_to_top_up\<cdot>(down\<cdot>\<bottom>) = \<bottom>"
  "up_top_to_top_up\<cdot>(down\<cdot>(up\<cdot>x)) = up\<cdot>(down\<cdot>x)"
  by (simp_all add: utttu_beta Iftop_top Iftop_down)

theorem tutut_cases:
  "top_up_to_up_top\<cdot>(up\<cdot>Top) = Top"
  "top_up_to_up_top\<cdot>(\<bottom>) = down\<cdot>\<bottom>"
  "top_up_to_up_top\<cdot>(up\<cdot>(down\<cdot>x)) = down\<cdot>(up\<cdot>x)"
  unfolding top_up_to_up_top_def
  by (simp_all add: tutut_beta_minor Iftop_top Iftop_down down_strict)

lemma top_up_iso1: "up_top_to_top_up\<cdot>(top_up_to_up_top\<cdot>x) = x"
proof -
  consider "x = up\<cdot>Top" | y where "x = up\<cdot>(down\<cdot>y)" | "x = \<bottom>"
    by (metis top_cases upE)
  then show ?thesis by cases (simp_all add: utttu_cases tutut_cases)
qed

lemma top_up_iso2: "top_up_to_up_top\<cdot>(up_top_to_top_up\<cdot>x) = x"
proof -
  consider "x = Top" | y where "x = down\<cdot>(up\<cdot>y)" | "x = down\<cdot>\<bottom>"
    by (metis top_cases upE)
  then show ?thesis by cases (simp_all add: utttu_cases tutut_cases)
qed

instance top :: (profinite) profinite
proof
  from profinite obtain a :: "nat \<Rightarrow> 'a u \<rightarrow> 'a u" where "approx_chain a" ..
  note this = approx_chain_top[OF this]
  from approx_chain_iso[OF this top_up_iso1 top_up_iso2]
  show "\<exists> (a :: nat \<Rightarrow> 'a top u \<rightarrow> 'a top u). approx_chain a"
    by fast
qed

hide_const (open) Of

end