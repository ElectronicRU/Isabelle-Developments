theory UpperPD_Representation imports HOLCF Koenigs Bounded_Complete Directed begin

lemma koenig_construction_aux:
  fixes x Y f
  assumes chain: "\<forall>i. Y i \<le>\<sharp> Y (Suc i)"
    and sup: "x = (\<Squnion>i. upper_principal (Y i))"
    and f_mem: "\<forall>i. f i \<in> Rep_pd_basis (Y i)"
    and f_chain: "\<forall>i. f i \<sqsubseteq> f (Suc i)"
  shows "chain (\<lambda>i. Rep_compact_basis (f i))"
    and "x \<sqsubseteq> {\<Squnion>i. Rep_compact_basis (f i)}\<sharp>"
proof -
  from f_mem have le_unit: "\<And>n. Y n \<le>\<sharp> PDUnit (f n)" unfolding upper_le_def Rep_PDUnit
    using below_refl by blast
  then have principal_below: "\<And>n. upper_principal (Y n) \<sqsubseteq> upper_principal (PDUnit (f n))"
    by simp
  from f_chain show fchain: "chain (\<lambda>i. Rep_compact_basis (f i))" by simp
  then have "chain (\<lambda>i. {Rep_compact_basis (f i)}\<sharp>)" by (rule chain_monofun) 
  with upper_pd.ch2ch_principal[OF chain] principal_below
  have "x \<sqsubseteq> (\<Squnion>n. {Rep_compact_basis (f n)}\<sharp>)"
    unfolding sup
    by (auto intro: lub_mono)
  then show "x \<sqsubseteq> {\<Squnion>i. Rep_compact_basis (f i)}\<sharp>"
    unfolding contlub_cfun_arg[OF fchain] by simp
qed

lemma upper_pd_has_point: "\<exists>x. s \<sqsubseteq> {x}\<sharp>"
proof -
  from upper_pd.obtain_principal_chain
  obtain Y where chain: "\<forall>i. Y i \<le>\<sharp> Y (Suc i)"
    and sup: "s = (\<Squnion>i. upper_principal (Y i))".

  have 1: "Rep_pd_basis (Y i) \<noteq> {}" for i by simp
  have 2: "finite (Rep_pd_basis (Y i))" for i by simp
  have 3: "\<forall>y \<in> Rep_pd_basis (Y (Suc i)). \<exists>x \<in> Rep_pd_basis (Y i). x \<sqsubseteq> y" for i
    using chain[unfolded upper_le_def] ..
   
  obtain f where f: "\<forall>i. f i \<in> Rep_pd_basis (Y i)" "\<forall>i. f i \<sqsubseteq> f (Suc i)"
    by (rule obtain_infinite_path[of "\<lambda>i. Rep_pd_basis (Y i)" "(\<sqsubseteq>)", OF 1 2 3 that])
  from koenig_construction_aux(2)[OF chain sup this]
  have "s \<sqsubseteq> {\<Squnion>n. Rep_compact_basis (f n)}\<sharp>" .
  then show ?thesis ..
qed

theorem upper_pd_extensionality_lemma:
  fixes x k
  defines "y \<equiv> upper_principal k"
  assumes imp: "\<And>p. x \<sqsubseteq> {p}\<sharp> \<Longrightarrow> y \<sqsubseteq> {p}\<sharp>"
  shows "y \<sqsubseteq> x"
proof (rule classical)
  assume not_below: "\<not>(y \<sqsubseteq> x)"

  from upper_pd.obtain_principal_chain
  obtain Y where chain: "\<forall>i. Y i \<le>\<sharp> Y (Suc i)"
    and sup: "x = (\<Squnion>i. upper_principal (Y i))".
  from chain have chain': "chain (\<lambda>i. upper_principal (Y i))"
    by (rule upper_pd.ch2ch_principal)
  from sup not_below chain' have "\<not>(y \<sqsubseteq> upper_principal (Y i))" for i
    using below_lub[OF chain', of y] by iprover
  with y_def have not_below_compact: "\<not>(k \<le>\<sharp> (Y i))" for i by simp

  define Bad where "Bad i = {q \<in> Rep_pd_basis (Y i). (\<forall>r \<in> Rep_pd_basis k. \<not>(r \<sqsubseteq> q))}"
    for i
  from not_below_compact have 1: "Bad i \<noteq> {}" for i
    unfolding upper_le_def Bad_def by fast
  have 2: "finite (Bad i)" for i unfolding Bad_def by simp
  have 3: "\<forall>y \<in> Bad (Suc i). \<exists>x \<in> Bad i. x \<sqsubseteq> y" for i
  proof
    fix y assume y: "y \<in> Bad (Suc i)"
    then have "y \<in> Rep_pd_basis (Y (Suc i))" unfolding Bad_def by auto
    with chain obtain x where "x \<in> Rep_pd_basis (Y i)" "x \<sqsubseteq> y"
      unfolding upper_le_def by blast
    from y have "\<forall>r \<in> Rep_pd_basis k. \<not>(r \<sqsubseteq> y)" unfolding Bad_def by simp
    with \<open>x \<sqsubseteq> y\<close> below_trans
    have "\<forall>r \<in> Rep_pd_basis k. \<not>(r \<sqsubseteq> x)"
      by blast
    with \<open>x \<in> Rep_pd_basis (Y i)\<close> have "x \<in> Bad i" unfolding Bad_def by auto
    with \<open>x \<sqsubseteq> y\<close> show "\<exists>x \<in> Bad i. x \<sqsubseteq> y" ..
  qed

  from obtain_infinite_path[of Bad "(\<sqsubseteq>)", OF 1 2 3]
  obtain f where f_mem: "\<forall>i. f i \<in> Bad i" and f_chain: "\<forall>i. f i \<sqsubseteq> f (Suc i)" .
  from f_mem Bad_def have f_mem': "\<forall>i. f i \<in> Rep_pd_basis (Y i)" by auto
  from koenig_construction_aux[OF chain sup f_mem' f_chain]
  have f_chain: "chain (\<lambda>i. Rep_compact_basis (f i))"
    and x_below: "x \<sqsubseteq> {\<Squnion>i. Rep_compact_basis (f i)}\<sharp>"
    by this+
  from x_below have "y \<sqsubseteq> {\<Squnion>i. Rep_compact_basis (f i)}\<sharp>" by (rule imp)
  with f_chain have y_below: "y \<sqsubseteq> (\<Squnion>i. {Rep_compact_basis (f i)}\<sharp>)"
    by (simp add: contlub_cfun_arg)
  from y_def have "compact y" by simp
  with y_below obtain i where "y \<sqsubseteq> {Rep_compact_basis (f i)}\<sharp>"
    using chain_monofun[OF f_chain] compactD2 by blast
  with y_def have "k \<le>\<sharp> PDUnit (f i)" by simp
  then have "\<exists>q \<in> Rep_pd_basis k. q \<sqsubseteq> f i" unfolding upper_le_def
    by (simp add: Rep_PDUnit)
  with f_mem Bad_def have False by auto
  then show ?thesis ..
qed

theorem upper_pd_ext_subset:
  assumes "\<And>p. x \<sqsubseteq> {p}\<sharp> \<Longrightarrow> y \<sqsubseteq> {p}\<sharp>"
  shows "y \<sqsubseteq> x"
proof -
  have "h \<sqsubseteq> y \<Longrightarrow> h \<sqsubseteq> x" for h
  proof (induct h rule: upper_pd.principal_induct, simp)
    fix k assume "upper_principal k \<sqsubseteq> y"
    from below_trans[OF this assms]
    show "upper_principal k \<sqsubseteq> x"
      by (rule upper_pd_extensionality_lemma)
  qed
  then show ?thesis by simp
qed

theorem upper_pd_below_iff_ext_subset:
"x \<sqsubseteq> y \<longleftrightarrow> (\<forall>p. y \<sqsubseteq> {p}\<sharp> \<longrightarrow> x \<sqsubseteq> {p}\<sharp>)"
  by (auto intro: upper_pd_ext_subset below_trans)

definition upper_set where "upper_set x = {p. x \<sqsubseteq> {p}\<sharp>}"

lemma upper_set_subset_iff: "x \<sqsubseteq> y \<longleftrightarrow> upper_set x \<supseteq> upper_set y"
  unfolding upper_set_def
  by (subst upper_pd_below_iff_ext_subset) auto

lemma upper_set_join[simp]: "x \<Up> y \<Longrightarrow> upper_set (x \<squnion> y) = upper_set x \<inter> upper_set y"
  unfolding upper_set_def using join_belowI joinableD[of x y] below_trans by blast

lemma upper_set_meet[simp]: "upper_set (x \<sqinter> y) = upper_set x \<union> upper_set y"
  unfolding upper_set_def upper_meet_eq upper_plus_below_unit_iff by auto

corollary upper_set_inj: "upper_set x = upper_set y \<Longrightarrow> x = y"
  using upper_set_subset_iff by (auto intro!: below_antisym)

instance upper_pd :: (bifinite) distributive_cpo
proof
  fix a b c :: "'a upper_pd"
  assume "a \<Up> b"
  then show "c \<sqinter> (a \<squnion> b) = (c \<sqinter> a) \<squnion> (c \<sqinter> b)"
    by (auto intro!: upper_set_inj)
qed

lemma upper_principal_below_unit_iff:
  "upper_principal k \<sqsubseteq> {x}\<sharp> \<longleftrightarrow> (\<exists>q \<in> Rep_pd_basis k. Rep_compact_basis q \<sqsubseteq> x)"
proof (induct k rule: pd_basis_induct)
  case (PDUnit a)
  have "upper_principal (PDUnit a) \<sqsubseteq> {x}\<sharp> \<longleftrightarrow> {Rep_compact_basis a}\<sharp> \<sqsubseteq> {x}\<sharp>"
    by (simp only: upper_unit_Rep_compact_basis)
  also have "... \<longleftrightarrow> Rep_compact_basis a \<sqsubseteq> x"
    by (rule upper_unit_below_iff)
  finally show ?case by (simp add: Rep_PDUnit)
next
  case (PDPlus s t)
  have "upper_principal (PDPlus s t) \<sqsubseteq> {x}\<sharp>
        \<longleftrightarrow> upper_principal s \<sqsubseteq> {x}\<sharp> \<or> upper_principal t \<sqsubseteq> {x}\<sharp>"
    by (simp only: upper_plus_principal[symmetric] upper_plus_below_unit_iff)
  also have "... \<longleftrightarrow> (\<exists>q \<in> Rep_pd_basis (PDPlus s t). Rep_compact_basis q \<sqsubseteq> x)"
    using PDPlus by (auto simp: Rep_PDPlus)
  finally show ?case .
qed

lemma chain_finite_nonempty_Inter:
  fixes \<F> :: "'a::type set set"
  assumes ne:    "\<F> \<noteq> {}"
      and chain: "\<And>S T. \<lbrakk>S \<in> \<F>; T \<in> \<F>\<rbrakk> \<Longrightarrow> S \<subseteq> T \<or> T \<subseteq> S"
      and fin:   "\<And>S. S \<in> \<F> \<Longrightarrow> finite S"
      and nemp:  "\<And>S. S \<in> \<F> \<Longrightarrow> S \<noteq> {}"
  shows "\<Inter>\<F> \<noteq> {}"
proof -
  from ne obtain S0 where S0: "S0 \<in> \<F>" by blast
  define \<G> where "\<G> = {S \<in> \<F>. S \<subseteq> S0}"
  have "\<G> \<subseteq> Pow S0" by (auto simp: \<G>_def)
  with fin[OF S0] have "finite \<G>" by (blast intro: finite_subset)
  moreover have "\<G> \<noteq> {}" using S0 by (auto simp: \<G>_def)
  ultimately obtain m where mG: "m \<in> \<G>"
      and m_min: "\<And>T. \<lbrakk>T \<in> \<G>; T \<subseteq> m\<rbrakk> \<Longrightarrow> m = T"
    by (blast dest: finite_has_minimal)
  have least: "m \<subseteq> S" if "S \<in> \<F>" for S
  proof (cases "S \<subseteq> S0")
    case True
    with that have "S \<in> \<G>" by (simp add: \<G>_def)
    with chain mG have "S \<subseteq> m \<or> m \<subseteq> S" by (auto simp: \<G>_def)
    with m_min \<open>S \<in> \<G>\<close> show "m \<subseteq> S" by blast
  next
    case False
    have "m \<subseteq> S0" using mG by (simp add: \<G>_def)
    also from chain[OF that S0] False have "S0 \<subseteq> S" by blast
    finally show "m \<subseteq> S" .
  qed
  from mG have "m \<in> \<F>" by (simp add: \<G>_def)
  with nemp obtain z where "z \<in> m" by blast
  with least have "z \<in> \<Inter>\<F>" by blast
  thus ?thesis by blast
qed

text \<open>Chains have greatest lower bounds in bifinite domains\<close>
lemma bifinite_Chain_glb:
  fixes A :: "'a::bifinite set"
  assumes "Chain A" and "A \<noteq> {}"
  shows "\<exists>a. is_glb A a"
proof -
  from bifinite obtain approx :: "nat \<Rightarrow> 'a \<rightarrow> 'a" where "approx_chain approx" ..
  then interpret approx_chain approx .
  have lub_approx_app[simp]: "(\<Squnion>i. approx i\<cdot>z) = z" for z
    by (simp add: contlub_cfun_fun[OF chain_approx, symmetric])
  define C where "C i = (\<lambda>x. approx i\<cdot>x) ` A" for i
  have C_Chain: "Chain (C i)" for i
    unfolding C_def
    using monofun_Rep_cfun2 assms(1)
    by (rule Chain_mono_image)
  have C_finite: "finite (C i)" for i unfolding C_def
    by (simp add: finite_deflation.finite_image)
  from assms(2) have C_ne: "C i \<noteq> {}" for i by (simp add: C_def)
  have C_glb: "is_glb (C i) (glb (C i))" and C_mem: "glb (C i) \<in> C i" for i
  proof -
    from order.finite_has_minimal[OF below_order C_finite C_ne]
    obtain m where m: "m \<in> C i" and m_min: "\<forall>b \<in> C i. b \<sqsubseteq> m \<longrightarrow> m = b" ..
    then have "\<forall>b \<in> C i. m \<sqsubseteq> b"
      using ChainE[OF C_Chain m] by metis
    with m have m_glb: "is_glb (C i) m"
      by (blast intro: is_glbI)
    then have glb_m: "glb (C i) = m"
      by (rule glb_eqI)
    from m_glb glb_m m show "is_glb (C i) (glb (C i))" and "glb (C i) \<in> C i"
      by simp_all
  qed
  
  define M where "M i = glb (C i)" for i
  have M_mem: "M i \<in> C i" for i unfolding M_def by (rule C_mem)
  have M_obtains: "\<exists>a\<in>A. M i = approx i\<cdot>a" for i
    using M_mem[of i] unfolding C_def by (auto simp: image_iff)
  from C_glb[THEN is_glb_below] have M_below_approx: "M i \<sqsubseteq> approx i\<cdot>x" if "x \<in> A" for i x
    unfolding M_def C_def using that by blast
  have M_chain: "chain M"
    by (rule chainI)
    (metis M_obtains M_below_approx below_trans
      monofun_cfun_fun[OF chainE[OF chain_approx]])
  have "is_glb A (\<Squnion>i. M i)"
  proof (rule is_glbI)
    fix x assume x: "x \<in> A"
    then have  "M i \<sqsubseteq> approx i\<cdot>x" for i
      by (rule M_below_approx)
    then have "(\<Squnion>i. M i) \<sqsubseteq> (\<Squnion>i. approx i\<cdot>x)"
      by (rule lub_mono[OF M_chain ch2ch_Rep_cfunL[OF chain_approx]])
    then show "(\<Squnion>i. M i) \<sqsubseteq> x" by simp
  next
    fix b assume bnd: "\<forall>x \<in> A. b \<sqsubseteq> x"
    have "approx i\<cdot>b \<sqsubseteq> M i" for i
    proof -
      from M_obtains[of i] obtain a where a: "a \<in> A" and Ma: "M i = approx i\<cdot>a" by blast
      from bnd a have "b \<sqsubseteq> a" by blast
      then have "approx i\<cdot>b \<sqsubseteq> approx i\<cdot>a"
        by (rule monofun_cfun_arg)
      with Ma show ?thesis by simp
    qed
    then have "(\<Squnion>i. approx i\<cdot>b) \<sqsubseteq> (\<Squnion>i. M i)"
      by (rule lub_mono[OF ch2ch_Rep_cfunL[OF chain_approx] M_chain]) 
    then show "b \<sqsubseteq> (\<Squnion>i. M i)" by simp
  qed
  then show ?thesis ..
qed

lemma upper_principal_below_chain:
  assumes "Chain C" "C \<noteq> {}" "\<And>x. x \<in> C \<Longrightarrow> upper_principal k \<sqsubseteq> {x}\<sharp>"
    "is_glb C g"
  shows "upper_principal k \<sqsubseteq> {g}\<sharp>"
proof -
  define \<F> where
    "\<F> = (\<lambda>c. {q \<in> Rep_pd_basis k. Rep_compact_basis q \<sqsubseteq> c}) ` C"
  have "\<F> \<noteq> {}" using assms(2) by (simp add: \<F>_def)
  moreover have "S \<subseteq> T \<or> T \<subseteq> S" if "S \<in> \<F>" "T \<in> \<F>" for S T
  proof -
    from that obtain c d where cd: "c \<in> C" "d \<in> C"
      and S: "S = {q \<in> Rep_pd_basis k. Rep_compact_basis q \<sqsubseteq> c}"
      and T: "T = {q \<in> Rep_pd_basis k. Rep_compact_basis q \<sqsubseteq> d}"
      unfolding \<F>_def by blast
    from ChainE[OF assms(1) cd] show ?thesis
      unfolding S T using below_trans by blast
  qed
  moreover have "finite S" if "S \<in> \<F>" for S
    using that unfolding \<F>_def by auto
  moreover have "S \<noteq> {}" if "S \<in> \<F>" for S
  proof -
    from that obtain c where c: "c \<in> C"
      and S: "S = {q \<in> Rep_pd_basis k. Rep_compact_basis q \<sqsubseteq> c}"
      unfolding \<F>_def by blast
    from c have "upper_principal k \<sqsubseteq> {c}\<sharp>" by (rule assms(3))
    then show ?thesis unfolding S by (auto simp add: upper_principal_below_unit_iff)
  qed
  ultimately have "\<Inter>\<F> \<noteq> {}" by (rule chain_finite_nonempty_Inter)
  then obtain q where q: "q \<in> \<Inter>\<F>" by blast
  from assms(2) obtain c0 where "c0 \<in> C" by blast
  with q have qmem: "q \<in> Rep_pd_basis k" unfolding \<F>_def by auto
  have q_lb: "Rep_compact_basis q \<sqsubseteq> c" if "c \<in> C" for c
    using q that unfolding \<F>_def by auto
  from assms(4) q_lb have "Rep_compact_basis q \<sqsubseteq> g"
    by (blast intro: is_glb_greatest)
  with qmem have "\<exists>q\<in>Rep_pd_basis k. Rep_compact_basis q \<sqsubseteq> g" by blast
  then show "upper_principal k \<sqsubseteq> {g}\<sharp>"
    by (simp add: upper_principal_below_unit_iff)
qed

lemma upper_set_glb_closed:
  assumes "Chain C" "C \<noteq> {}" "C \<subseteq> upper_set x" "is_glb C g"
  shows "g \<in> upper_set x"
proof -
  from upper_pd.obtain_principal_chain
  obtain Y where chain: "\<forall>i. Y i \<le>\<sharp> Y (Suc i)"
    and sup: "x = (\<Squnion>i. upper_principal (Y i))" .
  from chain have chain': "chain (\<lambda>i. upper_principal (Y i))"
    by (rule upper_pd.ch2ch_principal)
  have prin_below_x: "upper_principal (Y i) \<sqsubseteq> x" for i
    unfolding sup by (rule is_ub_thelub[OF chain'])
  with assms(3) have "c \<in> C \<Longrightarrow> upper_principal (Y i) \<sqsubseteq> {c}\<sharp>" for i c
    unfolding upper_set_def using below_trans by blast
  with assms(1,2,4) have "upper_principal (Y i) \<sqsubseteq> {g}\<sharp>" for i
    by (intro upper_principal_below_chain[of C "Y i" g])
  with chain' have "x \<sqsubseteq> {g}\<sharp>" unfolding sup
    by (rule lub_below)
  then show ?thesis by (simp add: upper_set_def)
qed

lemma po_Zorn_lemma_min:
  fixes A :: "'a::po set"
  assumes "\<And>C. Chain C \<Longrightarrow> C \<subseteq> A \<Longrightarrow> \<exists>l \<in> A. \<forall>c \<in> C. l \<sqsubseteq> c"
  shows "\<exists>m \<in> A. \<forall>a \<in> A. a \<sqsubseteq> m \<longrightarrow> a = m"
proof (rule predicate_Zorn)
  show "partial_order_on A (relation_of (\<lambda>a b. b \<sqsubseteq> a) A)"
    by (rule partial_order_on_relation_ofI) (auto intro: below_trans below_antisym)
next
  fix C assume "C \<in> Zorn.Chains (relation_of (\<lambda>a b. b \<sqsubseteq> a) A)"
  then have "Chain C" "C \<subseteq> A"
    by (auto simp: Zorn.Chains_def Chain_def relation_of_def)
  then have "\<exists>l \<in> A. \<forall>c \<in> C. l \<sqsubseteq> c" by (rule assms)
  then show "\<exists>u \<in> A. \<forall>a \<in> C. (\<lambda>a b. b \<sqsubseteq> a) a u" by simp
qed

theorem upper_set_above_minimal:
  assumes "p \<in> upper_set x"
  shows "\<exists>y. y \<in> upper_set x \<and> y \<sqsubseteq> p \<and> (\<forall>z \<in> upper_set x. z \<sqsubseteq> y \<longrightarrow> z = y)"
proof -
  define P where "P = {q \<in> upper_set x. q \<sqsubseteq> p}"
  have "\<exists>m \<in> P. \<forall>a \<in> P. a \<sqsubseteq> m \<longrightarrow> a = m"
  proof (rule po_Zorn_lemma_min)
    fix C assume C: "Chain C" "C \<subseteq> P"
    show "\<exists>l \<in> P. \<forall>c \<in> C. l \<sqsubseteq> c"
    proof (cases "C = {}")
      case True
      from assms have "p \<in> P" by (simp add: P_def)
      with True show ?thesis by blast
    next
      case False
      have C_sub: "C \<subseteq> upper_set x" using C(2) by (auto simp: P_def)
      from bifinite_Chain_glb[OF C(1) False] obtain g where g: "is_glb C g" ..
      from C(1) False C_sub g have gA: "g \<in> upper_set x" by (rule upper_set_glb_closed)
      from False obtain c0 where c0: "c0 \<in> C" by blast
      with C(2) have "c0 \<sqsubseteq> p" by (auto simp: P_def)
      with g c0 have "g \<sqsubseteq> p" using is_glb_below below_trans by blast
      with gA have "g \<in> P" by (simp add: P_def)
      moreover have "\<forall>c \<in> C. g \<sqsubseteq> c" using g by (blast intro: is_glb_below)
      ultimately show ?thesis by blast
    qed
  qed
  then obtain m where m: "m \<in> P" and m_min: "\<forall>a \<in> P. a \<sqsubseteq> m \<longrightarrow> a = m" by blast
  from m have mA: "m \<in> upper_set x" and mp: "m \<sqsubseteq> p" by (auto simp: P_def)
  have "z = m" if z: "z \<in> upper_set x" "z \<sqsubseteq> m" for z
  proof -
    from z(2) mp have "z \<sqsubseteq> p" by (rule below_trans)
    with z(1) have "z \<in> P" by (simp add: P_def)
    with m_min z(2) show "z = m" by blast
  qed
  with mA mp show ?thesis by blast
qed

end