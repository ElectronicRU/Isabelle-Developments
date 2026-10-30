theory Aggregate
  imports Content_Law
begin

section \<open>Aggregation\<close>

text \<open>An aggregate folds the entries of an inner expression over each fiber of the frame's LOD
  with a commutative semigroup operation.  The fold adjoins a unit for the empty fiber, which
  gives no entry; it is not \<open>\<bottom>\<close>: a monotone operation with unit \<open>\<bottom>\<close> would be inflationary
  (\<open>x = x \<oplus> \<bottom> \<sqsubseteq> x \<oplus> y\<close>), which rules out sums on flat values.  Absent members are the unit,
  so the fold reads the members that may be present.  Finitely many are folded; of infinitely
  many nothing is known but presence: the fold is a present value of which nothing is known when
  some member is definitely present, and otherwise the least result.\<close>

definition agg_fold :: "('v::bifinite \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('a \<Rightarrow> 'v option_pd) \<Rightarrow> 'a set \<Rightarrow> 'v option_pd" where
  "agg_fold f v A = (if finite {a \<in> A. v a \<noteq> Absent}
     then comm_monoid_set.F (\<lambda>x y. combine_option_pd f\<cdot>x\<cdot>y) Absent v {a \<in> A. v a \<noteq> Absent}
     else if \<exists>a\<in>A. Present\<cdot>\<bottom> \<sqsubseteq> v a then Present\<cdot>\<bottom> else \<bottom>)"

context
  fixes f :: "'v::bifinite \<rightarrow> 'v \<rightarrow> 'v"
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
begin

interpretation agg: comm_monoid_set "\<lambda>x y. combine_option_pd f\<cdot>x\<cdot>y" Absent
  unfolding comm_monoid_set_def by (rule comm_monoid_combine_option_pd[OF f])

lemma agg_fold_finite: "finite A \<Longrightarrow> agg_fold f v A = agg.F v A"
  unfolding agg_fold_def by (simp add: agg.mono_neutral_right[of A "{a \<in> A. v a \<noteq> Absent}" v])

lemma agg_fold_empty: "agg_fold f v {} = Absent"
  by (simp add: agg_fold_finite)

lemma agg_fold_singleton: "agg_fold f v {a} = v a"
  by (simp add: agg_fold_finite)

lemma agg_F_Absent_iff: "finite B \<Longrightarrow> (\<And>b. b \<in> B \<Longrightarrow> v b \<noteq> Absent) \<Longrightarrow> agg.F v B = Absent \<longleftrightarrow> B = {}"
  by (induct B rule: finite_induct) (simp_all add: combine_option_pd_Absent_iff)

lemma agg_fold_Absent_iff: "agg_fold f v A = Absent \<longleftrightarrow> (\<forall>a\<in>A. v a = Absent)"
proof (cases "finite {a \<in> A. v a \<noteq> Absent}")
  case True
  have "agg.F v {a \<in> A. v a \<noteq> Absent} = Absent \<longleftrightarrow> {a \<in> A. v a \<noteq> Absent} = {}"
    by (rule agg_F_Absent_iff[OF True]) simp
  then show ?thesis unfolding agg_fold_def using True by auto
next
  case False
  then have "{a \<in> A. v a \<noteq> Absent} \<noteq> {}" by (metis finite.emptyI)
  then have "\<not> (\<forall>a\<in>A. v a = Absent)" by blast
  then show ?thesis unfolding agg_fold_def using False by auto
qed

lemma agg_fold_nonempty: "agg_fold f v A \<noteq> Absent \<Longrightarrow> A \<noteq> {}"
  by (auto simp: agg_fold_Absent_iff)

lemma agg_fold_absent: "(\<And>a. a \<in> A \<Longrightarrow> v a = Absent) \<Longrightarrow> agg_fold f v A = Absent"
  by (simp add: agg_fold_Absent_iff)

lemma agg_fold_cong: "A = B \<Longrightarrow> (\<And>a. a \<in> B \<Longrightarrow> v a = w a) \<Longrightarrow> agg_fold f v A = agg_fold f w B"
proof -
  assume AB: "A = B" and vw: "\<And>a. a \<in> B \<Longrightarrow> v a = w a"
  have s: "{a \<in> A. v a \<noteq> Absent} = {a \<in> B. w a \<noteq> Absent}" using AB vw by auto
  have F: "agg.F v {a \<in> B. w a \<noteq> Absent} = agg.F w {a \<in> B. w a \<noteq> Absent}" by (rule agg.cong) (simp_all add: vw)
  have e: "(\<exists>a\<in>A. Present\<cdot>\<bottom> \<sqsubseteq> v a) = (\<exists>a\<in>B. Present\<cdot>\<bottom> \<sqsubseteq> w a)" using AB vw by auto
  show ?thesis unfolding agg_fold_def s F e ..
qed

text \<open>The fold is continuous in the folded values when their absence is rigid: then the members
  that may be present stay the same along a chain, and presence of a member is decided by a
  compact value.\<close>

lemma cont_agg_fallback:
  assumes v: "\<And>a. cont (\<lambda>x. v x a)"
  shows "cont (\<lambda>x. if \<exists>a\<in>A. Present\<cdot>\<bottom> \<sqsubseteq> v x a then Present\<cdot>\<bottom> else (\<bottom> :: 'v option_pd))"
proof (rule contI2)
  show m: "monofun (\<lambda>x. if \<exists>a\<in>A. Present\<cdot>\<bottom> \<sqsubseteq> v x a then Present\<cdot>\<bottom> else (\<bottom> :: 'v option_pd))"
    by (rule monofunI) (auto intro: below_trans[OF _ cont2monofunE[OF v]])
  fix Y :: "nat \<Rightarrow> 'b" assume Y: "chain Y"
  show "(if \<exists>a\<in>A. Present\<cdot>\<bottom> \<sqsubseteq> v (\<Squnion>i. Y i) a then Present\<cdot>\<bottom> else \<bottom>)
      \<sqsubseteq> (\<Squnion>i. if \<exists>a\<in>A. Present\<cdot>\<bottom> \<sqsubseteq> v (Y i) a then Present\<cdot>\<bottom> else (\<bottom> :: 'v option_pd))"
  proof (cases "\<exists>a\<in>A. Present\<cdot>\<bottom> \<sqsubseteq> v (\<Squnion>i. Y i) a")
    case True
    then obtain a where a: "a \<in> A" and b: "Present\<cdot>\<bottom> \<sqsubseteq> (\<Squnion>i. v (Y i) a)" by (auto simp: cont2contlubE[OF v Y])
    then obtain i where i: "Present\<cdot>\<bottom> \<sqsubseteq> v (Y i) a"
      using compact_below_lub_iff[OF compact_Present_bottom ch2ch_cont[OF v Y]] by blast
    have ub: "(if \<exists>a\<in>A. Present\<cdot>\<bottom> \<sqsubseteq> v (Y i) a then Present\<cdot>\<bottom> else \<bottom>)
        \<sqsubseteq> (\<Squnion>i. if \<exists>a\<in>A. Present\<cdot>\<bottom> \<sqsubseteq> v (Y i) a then Present\<cdot>\<bottom> else (\<bottom> :: 'v option_pd))"
      by (rule is_ub_thelub[OF ch2ch_monofun[OF m Y]])
    have p: "(if \<exists>a\<in>A. Present\<cdot>\<bottom> \<sqsubseteq> v (Y i) a then Present\<cdot>\<bottom> else \<bottom>) = (Present\<cdot>\<bottom> :: 'v option_pd)"
      using a i by auto
    have "Present\<cdot>\<bottom> \<sqsubseteq> (\<Squnion>i. if \<exists>a\<in>A. Present\<cdot>\<bottom> \<sqsubseteq> v (Y i) a then Present\<cdot>\<bottom> else (\<bottom> :: 'v option_pd))"
      using ub unfolding p .
    then show ?thesis by (subst if_P[OF True])
  qed simp
qed

lemma cont_agg_fold:
  assumes v: "\<And>a. cont (\<lambda>x. v x a)" and r: "\<And>a. rigid (\<lambda>x. v x a = Absent)"
  shows "cont (\<lambda>x. agg_fold f (v x) A)"
proof -
  have q: "rigid (\<lambda>x. {a \<in> A. v x a \<noteq> Absent})" by (rule rigidI) (simp add: rigidD[OF r])
  have h: "cont (\<lambda>x. if finite B then agg.F (v x) B
      else if \<exists>a\<in>A. Present\<cdot>\<bottom> \<sqsubseteq> v x a then Present\<cdot>\<bottom> else \<bottom>)" for B
  proof (cases "finite B")
    case True
    have "cont (\<lambda>x. agg.F (v x) B)" using True
    proof (induct B rule: finite_induct)
      case (insert a B)
      show ?case unfolding agg.insert[OF insert(1,2)]
        by (rule cont2cont_APP[OF cont2cont_APP[OF cont_const v] insert(3)])
    qed simp
    then show ?thesis using True by simp
  qed (simp add: cont_agg_fallback[OF v])
  show ?thesis unfolding agg_fold_def by (rule cont_rigid_arg[OF h q])
qed

end

lemma agg_fold_bij:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and h: "bij_betw h A B"
  shows "agg_fold f (v \<circ> h) A = agg_fold f v B"
proof -
  interpret agg: comm_monoid_set "\<lambda>x y. combine_option_pd f\<cdot>x\<cdot>y" Absent
    unfolding comm_monoid_set_def by (rule comm_monoid_combine_option_pd[OF f])
  let ?A = "{a \<in> A. v (h a) \<noteq> Absent}" and ?B = "{b \<in> B. v b \<noteq> Absent}"
  have hAB: "h ` A = B" by (rule bij_betw_imp_surj_on[OF h])
  have b: "bij_betw h ?A ?B"
    by (rule bij_betw_subset[OF h]) (use hAB in auto)
  have fin: "finite ?A \<longleftrightarrow> finite ?B" by (rule bij_betw_finite[OF b])
  have F: "agg.F (v \<circ> h) ?A = agg.F v ?B" unfolding comp_def by (rule agg.reindex_bij_betw[OF b])
  have e: "(\<exists>a\<in>A. Present\<cdot>\<bottom> \<sqsubseteq> v (h a)) = (\<exists>b\<in>B. Present\<cdot>\<bottom> \<sqsubseteq> v b)" using hAB by auto
  show ?thesis unfolding agg_fold_def comp_apply using fin F e by (simp add: comp_def)
qed

context dataspace
begin

text \<open>The rows in the fiber of a key at an LOD.\<close>

definition afiber :: "'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor \<Rightarrow> 'k \<Rightarrow> 'r set" where
  "afiber data F c k = {y \<in> lower_maximal data. rproj c y = k}"

text \<open>\<open>aggregate f E\<close> folds the inner values over the inner keys below each key of the frame:
  the keys at the inner key LOD of the rows below the key.  Each inner value is multiplied by the
  truth of its group being populated by the frame's filters: an inner key no row of which passes
  contributes the fold's unit, and one whose filter is undecided is a maybe member, for which the
  fold takes both the folds with and without it.  Where the
  inner expression is absent the fold sees its unit.  Grouping finer than the frame is the inner
  expression's own (its \<open>GROUP BY\<close> dimensions included).  The aggregate's keys are the frame's, so
  it decides no detail: its entries are the inner ones released (their lower parts move into their
  views' key parts), and the fold reads the fiber's classes at \<open>emind E\<close>.\<close>

definition inner_keys :: "('k, 'f, 'r, 'v::bifinite) expr \<Rightarrow> 'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'k set" where
  "inner_keys E data F k = rproj (kd E F) ` afiber data F (flod F) k"

text \<open>An inner entry, seen from outside the aggregate, is \<^emph>\<open>released\<close>: its lower part, which the
  inner key fixes, moves into its view's key part, so the outer content is keyed by the inner keys
  as well.\<close>

definition release :: "('k, 'p) entry \<Rightarrow> ('k, 'p) entry" where
  "release e = e\<lparr>esel := sel \<bottom> (eupper e), ekeys := ekeys e \<squnion> elower e\<rparr>"

lemma release_simps [simp]:
  "esel (release e) = sel \<bottom> (eupper e)" "ekeys (release e) = ekeys e \<squnion> elower e" "epay (release e) = epay e"
  by (simp_all add: release_def)

lemma keyed_view_raise: "keyed_view (c, a) \<Longrightarrow> keyed_view (c, a \<squnion> W)"
proof -
  assume "keyed_view (c, a)"
  then have "keyed_view ((c, a) \<squnion> (\<bottom>, W))" by (rule keyed_view_sup[OF _ keyed_view_key])
  then show ?thesis by simp
qed

lemma entry_wf_release: "entry_wf e \<Longrightarrow> entry_wf (release e)"
  unfolding entry_wf_def release_simps using keyed_view_raise[of "ecols e" "ekeys e"] by simp

subsection \<open>Reading inner contents off outer ones\<close>

text \<open>Let \<open>X\<close> be the content of the released entry \<open>e\<close>, keyed at \<open>ekeys e \<squnion> elower e\<close>, and \<open>p\<close> an
  inner key.  The inner fiber at \<open>p\<close> is the \<^emph>\<open>slice\<close> of the outer one where the lower part agrees
  with \<open>p\<close>; within it the lower part is constant, so an inner key \<open>q\<close> (at \<open>ekeys e\<close>) has as
  \<^emph>\<open>sources\<close> the outer keys in the slice whose \<open>ekeys e\<close>-part is \<open>q\<close>.  The inner content takes the
  value at the one source, and drops \<open>q\<close> when there is none or more than one.  Which keys collide is
  decided by the domain alone, so the read is continuous; on contents of data nothing collides.\<close>

definition agg_src :: "('k, 'p) entry \<Rightarrow> 'k \<Rightarrow> ('k \<Rightarrow> 'r option) \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> bool" where
  "agg_src e p X q q0 \<longleftrightarrow> q0 \<in> dom X \<and> proj (elower e)\<cdot>q0 = proj (elower e)\<cdot>p \<and> proj (ekeys e)\<cdot>q0 = q"

definition agg_pick :: "('k, 'p) entry \<Rightarrow> 'k \<Rightarrow> ('k \<Rightarrow> 'r option) \<Rightarrow> 'k \<Rightarrow> 'r option" where
  "agg_pick e p X q = (if \<exists>!q0. agg_src e p X q q0 then X (THE q0. agg_src e p X q q0) else None)"

lemma rigid_agg_src: "rigid (\<lambda>X. agg_src e p X q)"
  by (rule rigidI) (simp add: fun_eq_iff agg_src_def map_below_dom)

lemma cont_agg_pick: "cont (agg_pick e p)"
proof -
  have "cont (\<lambda>X. agg_pick e p X q)" for q
    unfolding agg_pick_def
  proof (rule cont_if_rigid)
    have src: "agg_src e p X q = agg_src e p Y q" if "X \<sqsubseteq> Y" for X Y
      by (rule rigidD[OF rigid_agg_src that])
    show "rigid (\<lambda>X. \<exists>!q0. agg_src e p X q q0)" by (rule rigidI) (simp only: src)
    have "rigid (\<lambda>X. THE q0. agg_src e p X q q0)" by (rule rigidI) (simp only: src)
    then show "cont (\<lambda>X. X (THE q0. agg_src e p X q q0))"
      by (rule cont_rigid_arg[where h = "\<lambda>X s. X s", rotated]) (simp add: cont2cont_fun)
  qed simp
  then have "cont (\<lambda>X. \<lambda>q. agg_pick e p X q)" by (rule cont2cont_lambda)
  then show ?thesis by simp
qed

text \<open>A released guard's content is read off likewise: at an inner key part, the existential over
  the keys in the slice with that key part, where there are any; an existential needs no
  uniqueness.\<close>

definition agg_gpick :: "('k, 'p) entry \<Rightarrow> 'k \<Rightarrow> ('k \<Rightarrow> tr option) \<Rightarrow> 'k \<Rightarrow> tr option" where
  "agg_gpick e p G q = gex {q0 \<in> dom G. proj (elower e)\<cdot>q0 = proj (elower e)\<cdot>p \<and> proj (ekeys e)\<cdot>q0 = q} (\<lambda>q0. the (G q0))"

definition agg_inner :: "('k, 'r semi_factor) entry list \<Rightarrow> ('k \<Rightarrow> 'r option) list \<Rightarrow> 'k \<Rightarrow> ('k \<Rightarrow> 'r option) list" where
  "agg_inner es Xs p = map2 (\<lambda>e X. agg_pick e p X) es Xs"

definition agg_ginner :: "('k, 'r guard \<times> 'k guard) entry list \<Rightarrow> ('k \<Rightarrow> tr option) list \<Rightarrow> 'k \<Rightarrow> ('k \<Rightarrow> tr option) list" where
  "agg_ginner gs Gs p = map2 (\<lambda>e G. agg_gpick e p G) gs Gs"

lemma cont_agg_inner: "cont (\<lambda>Xs. agg_inner es Xs p)"
  unfolding agg_inner_def by (rule cont_map2) (simp add: cont_agg_pick[unfolded eta_cfun])

text \<open>The content semantics folds the inner content semantics, multiplied by the fold guard, over
  the keys where the fold guard is defined, reading the inner contents at each off the outer
  ones.\<close>

definition agg_csem :: "('v::bifinite \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k, 'f, 'r, 'v) expr \<Rightarrow> ('k \<Rightarrow> tr option) list \<Rightarrow> ('k \<Rightarrow> 'r option) list \<Rightarrow> 'v option_pd" where
  "agg_csem f E Gs Xs = agg_fold f (\<lambda>p. the (hd Gs p) \<odot> csem E (agg_ginner (eguards E) (tl Gs) p)\<cdot>(agg_inner (evalues E) Xs p))
     (dom (hd Gs))"

text \<open>It is continuous in the value contents: the fold's index set is the fold guard's domain, and
  the fold is continuous in the values.\<close>

lemma rigid_agg_member:
  assumes E: "crigid E"
  shows "rigid (\<lambda>Xs. the (hd Gs p) \<odot> csem E (agg_ginner (eguards E) (tl Gs) p)\<cdot>(agg_inner (evalues E) Xs p) = Absent)"
proof (rule rigidI)
  fix Xs Ys :: "('k \<Rightarrow> 'r option) list" assume "Xs \<sqsubseteq> Ys"
  then show "(the (hd Gs p) \<odot> csem E (agg_ginner (eguards E) (tl Gs) p)\<cdot>(agg_inner (evalues E) Xs p) = Absent) =
      (the (hd Gs p) \<odot> csem E (agg_ginner (eguards E) (tl Gs) p)\<cdot>(agg_inner (evalues E) Ys p) = Absent)"
    by (simp only: tr_mult_Absent_iff rigidD[OF rigid_comp[OF crigidD[OF E] cont2mono[OF cont_agg_inner]]])
qed

lemma cont_agg_csem:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and E: "crigid E"
  shows "cont (agg_csem f E Gs)"
  unfolding agg_csem_def[abs_def]
  by (rule cont_agg_fold[OF f _ rigid_agg_member[OF E]]) (simp add: cont_compose[OF _ cont_agg_inner])

lemma map2_map: "map2 g xs (map h xs) = map (\<lambda>x. g x (h x)) xs"
  by (induct xs) simp_all

definition aggregate :: "('v::bifinite \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k, 'f, 'r, 'v) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "aggregate f E = \<lparr>emind = \<bottom>,
     eguards = mk_guard (sel \<bottom> \<top>) gtrue gtrue (emind E) # map release (eguards E),
     evalues = map release (evalues E),
     esem = \<lambda>data F k. agg_fold f (\<lambda>\<kappa>. populated data (emind E) \<top> F \<kappa> \<odot> esem E data F \<kappa>) (inner_keys E data F k),
     csem = \<lambda>Gs. \<Lambda> Xs. agg_csem f E Gs Xs\<rparr>"

lemma aggregate_simps [simp]:
  "emind (aggregate f E) = \<bottom>"
  "eguards (aggregate f E) = mk_guard (sel \<bottom> \<top>) gtrue gtrue (emind E) # map release (eguards E)"
  "evalues (aggregate f E) = map release (evalues E)"
  "esem (aggregate f E) data F k = agg_fold f (\<lambda>\<kappa>. populated data (emind E) \<top> F \<kappa> \<odot> esem E data F \<kappa>) (inner_keys E data F k)"
  "csem (aggregate f E) Gs = (\<Lambda> Xs. agg_csem f E Gs Xs)"
  by (simp_all add: aggregate_def)

lemma aggregate_csem:
  "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b) \<Longrightarrow> crigid E \<Longrightarrow> csem (aggregate f E) Gs\<cdot>Xs = agg_csem f E Gs Xs"
  by (simp add: cont_agg_csem)

lemma crigid_aggregate:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and E: "crigid E"
  shows "crigid (aggregate f E)"
  unfolding crigid_def
proof (intro allI rigidI)
  fix Gs and Xs Ys :: "('k \<Rightarrow> 'r option) list" assume "Xs \<sqsubseteq> Ys"
  then show "(csem (aggregate f E) Gs\<cdot>Xs = Absent) = (csem (aggregate f E) Gs\<cdot>Ys = Absent)"
    by (simp only: aggregate_csem[OF f E] agg_csem_def agg_fold_Absent_iff[OF f] rigidD[OF rigid_agg_member[OF E]])
qed

subsection \<open>Lawfulness\<close>

text \<open>The fold guard reads the fiber.\<close>

lemma agg_fiber: "proj (flod F)\<cdot>k = k \<Longrightarrow> fiber data \<bottom> \<top> F k = afiber data F (flod F) k"
  by (simp add: fiber_top[of \<bottom>, simplified] afiber_def)

text \<open>An inner fiber is the outer fiber through the same upper part, cut down by the inner key's
  lower part.\<close>

lemma agg_fiber_group:
  assumes y: "rproj (flod F) y = k" and am: "a \<sqsubseteq> m"
  shows "fiber data a \<rho> F (rproj (m \<squnion> flod F) y) = {y' \<in> fiber data \<bottom> \<rho> F k. rproj a y' = rproj a y}"
proof -
  let ?X = "m \<squnion> flod F" and ?L = "\<rho> \<sqinter> flod F"
  have AX: "a \<sqsubseteq> ?X" by (rule below_trans[OF am lattice_join_ge1])
  have LX: "?L \<sqsubseteq> ?X" by (rule below_trans[OF truncate_below lattice_join_ge2])
  have kA: "proj a\<cdot>(rproj ?X y) = rproj a y" by (rule proj_le[OF AX])
  have kL: "proj ?L\<cdot>(rproj ?X y) = proj ?L\<cdot>k"
  proof -
    have "proj ?L\<cdot>(rproj ?X y) = rproj ?L y" by (rule proj_le[OF LX])
    also have "\<dots> = proj ?L\<cdot>(rproj (flod F) y)" by (rule proj_le[OF truncate_below, symmetric])
    finally show ?thesis by (simp only: y)
  qed
  show ?thesis unfolding fiber_def proj_sup_eq kA kL by (auto simp: proj_bot)
qed

text \<open>Inner keys of a fiber correspond to their parts at \<open>m\<close>.\<close>

lemma agg_keys_bij:
  "bij_betw (Rep_cfun (proj m)) (rproj (m \<squnion> flod F) ` afiber data F (flod F) k) (rproj m ` afiber data F (flod F) k)"
proof -
  let ?X = "m \<squnion> flod F" and ?Z = "afiber data F (flod F) k"
  have pr: "proj m\<cdot>(rproj ?X y) = rproj m y" for y by (rule proj_le[OF lattice_join_ge1])
  show ?thesis
  proof (rule bij_betw_imageI)
    show "inj_on (Rep_cfun (proj m)) (rproj ?X ` ?Z)"
    proof (rule inj_onI)
      fix \<kappa>1 \<kappa>2 assume k1: "\<kappa>1 \<in> rproj ?X ` ?Z" and k2: "\<kappa>2 \<in> rproj ?X ` ?Z"
        and e: "proj m\<cdot>\<kappa>1 = proj m\<cdot>\<kappa>2"
      obtain y1 where y1: "y1 \<in> ?Z" "\<kappa>1 = rproj ?X y1" using k1 by blast
      obtain y2 where y2: "y2 \<in> ?Z" "\<kappa>2 = rproj ?X y2" using k2 by blast
      have "rproj m y1 = rproj m y2" using e unfolding y1(2) y2(2) pr .
      moreover have "rproj (flod F) y1 = rproj (flod F) y2" using y1(1) y2(1) by (simp add: afiber_def)
      ultimately show "\<kappa>1 = \<kappa>2" unfolding y1(2) y2(2) by (simp only: rproj_sup_eq)
    qed
    show "Rep_cfun (proj m) ` rproj ?X ` ?Z = rproj m ` ?Z"
      by (simp only: image_image pr)
  qed
qed

text \<open>An inner key \<open>\<kappa>\<close> of a row \<open>y\<close> of the fiber, at the inner minimal LOD \<open>p\<close>: the row's lower
  part of an inner entry is \<open>p\<close>'s, and the inner fibers at \<open>\<kappa>\<close> are the released ones cut down
  there.  A released key's parts are its row's.\<close>

lemma agg_inner_row:
  assumes yZ: "y \<in> afiber data G (flod G) kG" and \<kappa>: "\<kappa> = rproj (m \<squnion> flod G) y" and py: "proj m\<cdot>\<kappa> = p"
    and am: "a \<sqsubseteq> m"
  shows "rproj (flod G) y = kG" and "rproj a y = proj a\<cdot>p"
proof -
  show "rproj (flod G) y = kG" using yZ by (simp add: afiber_def)
  have "proj a\<cdot>p = proj a\<cdot>\<kappa>" unfolding py[symmetric] by (rule proj_le[OF am])
  also have "\<dots> = rproj a y" unfolding \<kappa> by (rule proj_le[OF below_trans[OF am lattice_join_ge1]])
  finally show "rproj a y = proj a\<cdot>p" by simp
qed

lemma agg_vfiber_inner:
  assumes yZ: "y \<in> afiber data G (flod G) kG" and \<kappa>: "\<kappa> = rproj (m \<squnion> flod G) y" and py: "proj m\<cdot>\<kappa> = p"
    and am: "elower e \<sqsubseteq> m"
  shows "vfiber data e G \<kappa> = {y' \<in> vfiber data (release e) G kG. rproj (elower e) y' = proj (elower e)\<cdot>p}"
  unfolding vfiber_def \<kappa> agg_fiber_group[OF agg_inner_row(1)[OF yZ \<kappa> py am] am] agg_inner_row(2)[OF yZ \<kappa> py am]
  by simp

lemma agg_gfiber_inner:
  assumes yZ: "y \<in> afiber data G (flod G) kG" and \<kappa>: "\<kappa> = rproj (m \<squnion> flod G) y" and py: "proj m\<cdot>\<kappa> = p"
    and am: "elower e \<sqsubseteq> m"
  shows "gfiber data e G \<kappa> = {y' \<in> gfiber data (release e) G kG. rproj (elower e) y' = proj (elower e)\<cdot>p}"
  unfolding gfiber_def \<kappa> agg_fiber_group[OF agg_inner_row(1)[OF yZ \<kappa> py am] am] agg_inner_row(2)[OF yZ \<kappa> py am]
  by simp

lemma release_key_parts:
  "proj a\<cdot>(rproj (s \<squnion> a) y) = rproj a y" "proj s\<cdot>(rproj (s \<squnion> a) y) = rproj s y"
  by (rule proj_le[OF lattice_join_ge2], rule proj_le[OF lattice_join_ge1])

text \<open>The content of an inner entry at an inner key is read off the released entry's content: the
  sources of an inner key part are the released keys of the inner fiber's rows with that part, and
  there is at most one, since the inner fiber fixes the lower part.\<close>

lemma agg_content_inner:
  assumes ES: "semilawful E" and e: "e \<in> set (evalues E)" and d: "fconf (evalues E) data G"
    and yZ: "y \<in> afiber data G (flod G) kG"
    and \<kappa>: "\<kappa> = rproj (emind E \<squnion> flod G) y" and py: "proj (emind E)\<cdot>\<kappa> = p"
  shows "content data e G \<kappa> = agg_pick e p (content data (release e) G kG)"
proof
  fix q
  let ?a = "elower e" and ?s = "ekeys e" and ?X = "content data (release e) G kG"
  let ?I = "vfiber data e G \<kappa>" and ?P = "agg_src e p ?X q"
  have fib: "?I = {y' \<in> vfiber data (release e) G kG. rproj ?a y' = proj ?a\<cdot>p}"
    by (rule agg_vfiber_inner[OF yZ \<kappa> py lower_below_mind_value[OF ES e]])
  have ce: "entry_conf e data G" using d e by (simp add: fconf_def)
  then have ce': "entry_conf (release e) data G" by (simp add: entry_conf_def lattice_join_ac truncate_inf_comp)
  have src: "?P q0 \<longleftrightarrow> (\<exists>y'\<in>?I. rproj ?s y' = q \<and> q0 = rproj (?s \<squnion> ?a) y')" for q0
    unfolding agg_src_def dom_content fib by (auto simp: release_key_parts)
  have uniq: "rproj (?s \<squnion> ?a) y1 = rproj (?s \<squnion> ?a) y2"
    if "y1 \<in> ?I" "y2 \<in> ?I" "rproj ?s y1 = rproj ?s y2" for y1 y2
    using that by (simp add: fib rproj_sup_eq)
  show "content data e G \<kappa> q = agg_pick e p ?X q"
  proof (cases "\<exists>y'\<in>?I. rproj ?s y' = q")
    case True
    then obtain y' where y': "y' \<in> ?I" "rproj ?s y' = q" by blast
    have s0: "?P (rproj (?s \<squnion> ?a) y')" unfolding src using y' by blast
    have u: "q1 = rproj (?s \<squnion> ?a) y'" if q1: "?P q1" for q1
    proof -
      obtain y1 where "y1 \<in> ?I" "rproj ?s y1 = q" "q1 = rproj (?s \<squnion> ?a) y1" using q1 unfolding src by blast
      then show ?thesis using uniq[of y1 y'] y' by simp
    qed
    have ex1: "\<exists>!q0. ?P q0" using s0 u by blast
    have th: "(THE q0. ?P q0) = rproj (?s \<squnion> ?a) y'" using s0 u by blast
    have "?X (rproj (?s \<squnion> ?a) y') = Some (y' \<downharpoonright> ecols e)"
      using content_row[OF ce', of y'] y'(1) fib by simp
    then show ?thesis unfolding agg_pick_def using ex1 th content_row[OF ce y'(1)] y'(2) by simp
  next
    case False
    then have "\<not> (\<exists>!q0. ?P q0)" unfolding src by blast
    moreover have "content data e G \<kappa> q = None" using False by (auto simp: content_None_iff)
    ultimately show ?thesis unfolding agg_pick_def by simp
  qed
qed

text \<open>The content of an inner guard at an inner key is read off the released guard's content.\<close>

lemma agg_gcontent_inner:
  assumes ES: "semilawful E" and e: "e \<in> set (eguards E)"
    and yZ: "y \<in> afiber data G (flod G) kG"
    and \<kappa>: "\<kappa> = rproj (emind E \<squnion> flod G) y" and py: "proj (emind E)\<cdot>\<kappa> = p"
  shows "gcontent data e G \<kappa> = agg_gpick e p (gcontent data (release e) G kG)"
  unfolding fun_eq_iff agg_gpick_def gcontent_def[abs_def] gex_classes agg_gfiber_inner[OF yZ \<kappa> py lower_below_mind_guard[OF ES e]]
  by (intro allI gex_cong) (auto simp: release_key_parts gtruth_def)

text \<open>The aggregate is strict: a false fold guard leaves nothing to fold, and a false inner guard
  makes every inner content semantics absent.\<close>

lemma agg_pick_empty: "agg_pick e p Map.empty = Map.empty"
  by (simp add: fun_eq_iff agg_pick_def agg_src_def)

lemma agg_gpick_gfalse: "gfalse G \<Longrightarrow> gfalse (agg_gpick e p G)"
  by (auto simp: gfalse_def agg_gpick_def gex_def kleene_bex_FF_iff)

lemma agg_ginner_gfalse:
  "length Gs = length gs \<Longrightarrow> G \<in> set Gs \<Longrightarrow> gfalse G \<Longrightarrow> \<exists>G'\<in>set (agg_ginner gs Gs p). gfalse G'"
  unfolding agg_ginner_def
proof (induct Gs gs rule: list_induct2)
  case (Cons G0 Gs e gs)
  then show ?case by (cases "G = G0") (auto simp: agg_gpick_gfalse)
qed simp

lemma cstrict_aggregate:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and E: "cstrict E" and R: "crigid E"
  shows "cstrict (aggregate f E)"
proof (rule cstrictI)
  fix Gs :: "('k \<Rightarrow> tr option) list" and Xs :: "('k \<Rightarrow> 'r option) list"
  assume l: "length Gs = length (eguards (aggregate f E))" and lx: "length Xs = length (evalues (aggregate f E))"
    and c: "csem (aggregate f E) Gs\<cdot>Xs \<noteq> Absent"
  then obtain G Gs' where Gs: "Gs = G # Gs'" and l': "length Gs' = length (eguards E)"
    by (auto simp: length_Suc_conv)
  have lx': "length Xs = length (evalues E)" using lx by simp
  let ?\<Phi> = "\<lambda>p. csem E (agg_ginner (eguards E) Gs' p)\<cdot>(agg_inner (evalues E) Xs p)"
  have c': "agg_fold f (\<lambda>p. the (G p) \<odot> ?\<Phi> p) (dom G) \<noteq> Absent" using c unfolding aggregate_csem[OF f R] agg_csem_def Gs list.sel .
  have ne: "\<exists>p\<in>dom G. the (G p) \<odot> ?\<Phi> p \<noteq> Absent"
  proof (rule ccontr)
    assume "\<not> (\<exists>p\<in>dom G. the (G p) \<odot> ?\<Phi> p \<noteq> Absent)"
    then have "agg_fold f (\<lambda>p. the (G p) \<odot> ?\<Phi> p) (dom G) = Absent" by (intro agg_fold_absent[OF f]) blast
    then show False using c' by contradiction
  qed
  then obtain p t where p: "G p = Some t" and pt: "t \<odot> ?\<Phi> p \<noteq> Absent" by (auto simp: dom_def)
  have "\<not> gfalse G" using p tr_mult_not_Absent[OF pt] by (auto simp: gfalse_def)
  moreover have "\<not> gfalse G'" if G': "G' \<in> set Gs'" for G'
  proof
    assume em: "gfalse G'"
    obtain G'' where "G'' \<in> set (agg_ginner (eguards E) Gs' p)" "gfalse G''"
      using agg_ginner_gfalse[OF l' G' em] by blast
    then have "?\<Phi> p = Absent"
      by (intro cstrictD[OF E]) (simp_all add: agg_ginner_def agg_inner_def l' lx')
    then show False using pt by simp
  qed
  ultimately show "\<forall>G\<in>set Gs. \<not> gfalse G" by (simp add: Gs)
qed

lemma fconf_release: "fconf (map release es) data F \<longleftrightarrow> fconf es data F"
  by (simp add: fconf_def entry_conf_def lattice_join_ac)

theorem lawful_aggregate:
  assumes ES: "semilawful E" and R: "crigid E" and f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
  shows "lawful (aggregate f E)"
proof -
  let ?m = "emind E"
  let ?h = "mk_guard (sel \<bottom> \<top>) gtrue gtrue ?m :: ('k, 'r guard \<times> 'k guard) entry"
  let ?gs = "?h # map release (eguards E)" and ?vs = "map release (evalues E)"
  note bij = agg_keys_bij[of ?m]
  show ?thesis
  proof (rule lawfulI, simp_all only: aggregate_simps)
    show "cstrict (aggregate f E)" by (rule cstrict_aggregate[OF f semilawful_cstrict[OF ES] R])
    show "entry_wf e" if "e \<in> set ?vs" for e
      using that by (auto intro: entry_wf_release semilawful_wf[OF ES])
    show "(\<bottom>::'k semi_factor) = fold (\<squnion>) (map lower_part (map esel ?gs @ map esel ?vs)) \<bottom>"
    proof -
      have l: "map lower_part (map esel ?gs @ map esel ?vs) = map (\<lambda>_. \<bottom>) (map esel ?gs @ map esel ?vs)"
        by simp
      show ?thesis by (simp only: l fold_join_bots)
    qed
    show "keyimg data F (\<bottom> \<squnion> flod F) k"
      if d0: "fconf ?vs data F" and
        c: "agg_fold f (\<lambda>\<kappa>. populated data ?m \<top> F \<kappa> \<odot> esem E data F \<kappa>) (inner_keys E data F k) \<noteq> Absent" for data F k
    proof -
      have "\<exists>\<kappa>\<in>inner_keys E data F k. populated data ?m \<top> F \<kappa> \<odot> esem E data F \<kappa> \<noteq> Absent"
      proof (rule ccontr)
        assume "\<not> (\<exists>\<kappa>\<in>inner_keys E data F k. populated data ?m \<top> F \<kappa> \<odot> esem E data F \<kappa> \<noteq> Absent)"
        then have "agg_fold f (\<lambda>\<kappa>. populated data ?m \<top> F \<kappa> \<odot> esem E data F \<kappa>) (inner_keys E data F k) = Absent"
          by (intro agg_fold_absent[OF f]) blast
        then show False using c by contradiction
      qed
      then obtain \<kappa> y0 where y0: "y0 \<in> afiber data F (flod F) k" "\<kappa> = rproj (?m \<squnion> flod F) y0"
        and pk: "populated data ?m \<top> F \<kappa> \<noteq> FF" by (auto simp: inner_keys_def dest: tr_mult_not_Absent)
      then obtain y where y: "y \<in> fiber data ?m \<top> F \<kappa>" "frows F\<cdot>y \<noteq> FF"
        by (auto simp: populated_def kleene_bex_not_FF)
      have \<kappa>\<kappa>: "proj (?m \<squnion> flod F)\<cdot>\<kappa> = \<kappa>" by (simp only: y0(2) proj_idem)
      have yk: "rproj (?m \<squnion> flod F) y = \<kappa>" and ym: "y \<in> lower_maximal data"
        using y(1) by (simp_all add: fiber_top[OF \<kappa>\<kappa>])
      have "rproj (flod F) y = proj (flod F)\<cdot>(rproj (?m \<squnion> flod F) y)" by (rule release_key_parts(1)[symmetric])
      also have "\<dots> = proj (flod F)\<cdot>(rproj (?m \<squnion> flod F) y0)" by (simp only: yk y0(2))
      also have "\<dots> = rproj (flod F) y0" by (rule release_key_parts(1))
      also have "\<dots> = k" using y0(1) by (simp add: afiber_def)
      finally have yL: "rproj (flod F) y = k" .
      show ?thesis unfolding keyimg_def by (rule bexI[OF _ ym]) (simp add: y(2) yL lattice_join_bot_left)
    qed
    show "agg_fold f (\<lambda>\<kappa>. populated data ?m \<top> F \<kappa> \<odot> esem E data F \<kappa>) (inner_keys E data F k)
        = (\<Lambda> Xs. agg_csem f E (gcontents data ?gs F k) Xs)\<cdot>(contents data ?vs F k)"
      if d0: "fconf ?vs data F" and k: "proj (\<bottom> \<squnion> flod F)\<cdot>k = k" for data F k
    proof -
      have d: "fconf (evalues E) data F" using d0 by (simp only: fconf_release)
      have k1: "proj (flod F)\<cdot>k = k" using k by simp
      let ?Z = "afiber data F (flod F) k"
      let ?K = "rproj (?m \<squnion> flod F) ` ?Z"
      let ?P = "rproj ?m ` ?Z" and ?\<pi> = "Rep_cfun (proj ?m)"
      let ?v = "esem E data F" and ?t = "populated data ?m \<top> F"
      let ?G = "gcontents data (map release (eguards E)) F k"
      let ?X = "contents data ?vs F k"
      let ?H = "hd (gcontents data ?gs F k)"
      let ?\<Phi> = "\<lambda>p. csem E (agg_ginner (eguards E) ?G p)\<cdot>(agg_inner (evalues E) ?X p)"
      have hd: "?H = (\<lambda>p. gex {y \<in> ?Z. rproj ?m y = p} (Rep_cfun (frows F)))"
        by (simp add: fun_eq_iff gcontent_gtrue agg_fiber[OF k1])
      have dH: "dom ?H = ?P" unfolding hd by (rule dom_gex_classes)
      have tl: "tl (gcontents data ?gs F k) = ?G"
        by (simp only: list.map(2) list.sel(3))
      have tH: "the (?H (?\<pi> \<kappa>)) = ?t \<kappa>" if \<kappa>: "\<kappa> \<in> ?K" for \<kappa>
      proof -
        obtain y0 where y0: "y0 \<in> ?Z" "\<kappa> = rproj (?m \<squnion> flod F) y0" using \<kappa> by blast
        have \<kappa>\<kappa>: "proj (?m \<squnion> flod F)\<cdot>\<kappa> = \<kappa>" by (simp only: y0(2) proj_idem)
        have Lk: "rproj (flod F) y0 = k" using y0(1) by (simp add: afiber_def)
        have fb: "fiber data ?m \<top> F \<kappa> = {y \<in> ?Z. rproj ?m y = ?\<pi> \<kappa>}"
          unfolding fiber_top[OF \<kappa>\<kappa>] unfolding y0(2) release_key_parts(2) rproj_sup_eq Lk
          by (auto simp: afiber_def)
        have ne: "{y \<in> ?Z. rproj ?m y = ?\<pi> \<kappa>} \<noteq> {}" using y0 by (auto simp: release_key_parts(2))
        show ?thesis unfolding populated_def fguard_top fb hd gex_Some[OF ne] by simp
      qed
      have pt: "?\<Phi> (?\<pi> \<kappa>) = ?v \<kappa>" if \<kappa>: "\<kappa> \<in> ?K" for \<kappa>
      proof -
        obtain y where y: "y \<in> ?Z" "\<kappa> = rproj (?m \<squnion> flod F) y" using \<kappa> by blast
        have py: "proj ?m\<cdot>\<kappa> = ?\<pi> \<kappa>" ..
        have "agg_ginner (eguards E) ?G (?\<pi> \<kappa>) = map (\<lambda>e. agg_gpick e (?\<pi> \<kappa>) (gcontent data (release e) F k)) (eguards E)"
          unfolding agg_ginner_def map_map map2_map by (simp add: comp_def)
        also have "\<dots> = gcontents data (eguards E) F \<kappa>"
          by (rule map_cong[OF refl], rule agg_gcontent_inner[OF ES _ y(1) y(2) py, symmetric])
        finally have g: "agg_ginner (eguards E) ?G (?\<pi> \<kappa>) = gcontents data (eguards E) F \<kappa>" .
        have "agg_inner (evalues E) ?X (?\<pi> \<kappa>) = map (\<lambda>e. agg_pick e (?\<pi> \<kappa>) (content data (release e) F k)) (evalues E)"
          unfolding agg_inner_def map_map map2_map by (simp add: comp_def)
        also have "\<dots> = contents data (evalues E) F \<kappa>"
          by (rule map_cong[OF refl], rule agg_content_inner[OF ES _ d y(1) y(2) py, symmetric])
        finally have c: "agg_inner (evalues E) ?X (?\<pi> \<kappa>) = contents data (evalues E) F \<kappa>" .
        have "proj (kd E F)\<cdot>\<kappa> = \<kappa>" by (simp only: y(2) proj_idem)
        then show ?thesis by (simp only: g c semilawful_csem_conf[OF ES d])
      qed
      have D: "inner_keys E data F k = ?K" by (simp only: inner_keys_def)
      have "agg_fold f (\<lambda>\<kappa>. ?t \<kappa> \<odot> ?v \<kappa>) ?K = agg_fold f ((\<lambda>p. the (?H p) \<odot> ?\<Phi> p) \<circ> ?\<pi>) ?K"
      proof (rule agg_fold_cong[OF f refl])
        fix \<kappa> assume \<kappa>: "\<kappa> \<in> ?K"
        show "?t \<kappa> \<odot> ?v \<kappa> = ((\<lambda>p. the (?H p) \<odot> ?\<Phi> p) \<circ> ?\<pi>) \<kappa>" by (simp only: comp_apply tH[OF \<kappa>] pt[OF \<kappa>])
      qed
      also have "\<dots> = agg_fold f (\<lambda>p. the (?H p) \<odot> ?\<Phi> p) (dom ?H)" unfolding dH by (rule agg_fold_bij[OF f bij])
      finally have "agg_fold f (\<lambda>\<kappa>. ?t \<kappa> \<odot> ?v \<kappa>) (inner_keys E data F k) = agg_csem f E (gcontents data ?gs F k) ?X"
        unfolding agg_csem_def tl D .
      then show ?thesis by (simp only: beta_cfun[OF cont_agg_csem[OF f R]])
    qed
  qed
qed

end

end
