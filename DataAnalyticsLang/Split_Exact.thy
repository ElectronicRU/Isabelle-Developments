theory Split_Exact
  imports Split_Csem
begin

section \<open>Exactness of the extended semantics\<close>

text \<open>The extended semantics is below the rigid one at the data a split dataset is definite about.
  It equals it where nothing the expression reads is still open: at a key LOD \<open>K\<close> covering what
  the expression reads, the key mix of the dataset is \<^emph>\<open>saturated\<close>, a finite set of key parts
  maximal at \<open>K\<close>, each both definite and possible.  Then every row's part at \<open>K\<close> is one of them,
  and every possible key's part is a row's.  Row guards are left out: they only confirm, so a group
  whose rows all fail one is still possibly present.\<close>

definition mix_saturated :: "'k::{domain, lod_domain} semi_factor \<Rightarrow> 'k mix_pd \<Rightarrow> bool" where
  "mix_saturated K M \<longleftrightarrow> (\<exists>P. M = mix_principal (MSet P) \<and> (\<forall>v\<in>Rep_pde_basis P. maximal_at K (Rep_compact_basis v)))"

context split_dataspace
begin

subsection \<open>Saturated datasets\<close>

text \<open>At a saturated basis element, the rows' parts are maximal, and the possible keys' parts are
  the rows' parts.\<close>

lemma saturated_row_part:
  assumes s: "mix_saturated K (KM K t)" and x: "x \<in> srows t"
  shows "maximal_at K (rproj K (Rep_compact_basis x))"
proof -
  obtain P where P: "KM K t = mix_principal (MSet P)" and mP: "\<forall>v\<in>Rep_pde_basis P. maximal_at K (Rep_compact_basis v)"
    using s unfolding mix_saturated_def by blast
  obtain u where u: "u \<in> skeys t" and ux: "Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x)"
    using split_basis_consistentD [OF x] by blast
  have "mix_possible (proj K\<cdot>(Rep_compact_basis u)) (KM K t)" unfolding KM_possible using u by blast
  then obtain v where v: "v \<in> Rep_pde_basis P" and vu: "Rep_compact_basis v \<sqsubseteq> proj K\<cdot>(Rep_compact_basis u)"
    unfolding P mix_possible_principal by auto
  have mv: "maximal_at K (Rep_compact_basis v)" using mP v by blast
  have vx: "Rep_compact_basis v \<sqsubseteq> rproj K (Rep_compact_basis x)"
    by (rule below_trans [OF vu monofun_cfun_arg [OF ux]])
  have "rproj K (Rep_compact_basis x) = Rep_compact_basis v" by (rule maximal_at_eq [OF mv _ vx]) simp
  then show ?thesis using mv by simp
qed

lemma saturated_key_part:
  assumes s: "mix_saturated K (KM K t)" and u: "u \<in> skeys t"
  shows "\<exists>x\<in>srows t. proj K\<cdot>(Rep_compact_basis u) = rproj K (Rep_compact_basis x)"
proof -
  obtain P where P: "KM K t = mix_principal (MSet P)" and mP: "\<forall>v\<in>Rep_pde_basis P. maximal_at K (Rep_compact_basis v)"
    using s unfolding mix_saturated_def by blast
  have "mix_possible (proj K\<cdot>(Rep_compact_basis u)) (KM K t)" unfolding KM_possible using u by blast
  then obtain v where v: "v \<in> Rep_pde_basis P" and vu: "Rep_compact_basis v \<sqsubseteq> proj K\<cdot>(Rep_compact_basis u)"
    unfolding P mix_possible_principal by auto
  have mv: "maximal_at K (Rep_compact_basis v)" using mP v by blast
  have uv: "proj K\<cdot>(Rep_compact_basis u) = Rep_compact_basis v" by (rule maximal_at_eq [OF mv _ vu]) simp
  have "mix_definite (Rep_compact_basis v) (KM K t)" unfolding P mix_definite_principal using v by auto
  then obtain x where x: "x \<in> srows t" and vx: "Rep_compact_basis v \<sqsubseteq> rproj K (Rep_compact_basis x)"
    unfolding KM_definite [OF Rep_compact_basis'] by blast
  have xv: "rproj K (Rep_compact_basis x) = Rep_compact_basis v" by (rule maximal_at_eq [OF mv _ vx]) simp
  show ?thesis by (rule bexI [OF _ x]) (simp only: uv xv)
qed

text \<open>The presence test at a part of a coarser LOD, with a key guard reading the keys' parts at
  \<open>K\<close> and no row guard, is the rigid one at the data of a saturated basis element.\<close>

lemma select_test_exact:
  assumes s: "mix_saturated K (KM K t)" and d: "split_rows\<cdot>(split_principal t) = up\<cdot>data"
    and LK: "L \<sqsubseteq> K" and \<kappa>: "proj L\<cdot>\<kappa> = \<kappa>" and hK: "\<And>u. h\<cdot>(proj K\<cdot>u) = h\<cdot>u"
  shows "select_test L \<kappa> (\<Lambda> _. TT) h (split_principal t) = (\<exists>\<^sub>K m\<in>{m \<in> lower_maximal data. rproj L m = \<kappa>}. h\<cdot>(row_key\<cdot>m))"
proof -
  let ?D = "split_principal t" and ?R = "{m \<in> lower_maximal data. rproj L m = \<kappa>}"
  have pk: "proj L\<cdot>(proj K\<cdot>u) = proj L\<cdot>u" for u by (rule proj_le [OF LK])
  have rowL: "maximal_at L (rproj L (Rep_compact_basis x))" if "x \<in> srows t" for x
    using maximal_at_proj [OF LK saturated_row_part [OF s that]] pk by simp
  have pt: "m \<in> lower_maximal data \<Longrightarrow> \<exists>x\<in>srows t. m = Rep_compact_basis x" for m
    by (rule split_maximal_row_generator [OF d])
  have hrow: "h\<cdot>(row_key\<cdot>m) = h\<cdot>(row_key\<cdot>(Rep_compact_basis x))"
    if x: "x \<in> srows t" and m: "Rep_compact_basis x \<sqsubseteq> m" for x m
  proof -
    have xm: "rproj K (Rep_compact_basis x) \<sqsubseteq> rproj K m" by (intro monofun_cfun_arg m)
    have "rproj K m = rproj K (Rep_compact_basis x)" by (rule maximal_at_eq [OF saturated_row_part [OF s x] _ xm]) simp
    then show ?thesis using hK [of "row_key\<cdot>m"] hK [of "row_key\<cdot>(Rep_compact_basis x)"] by simp
  qed
  have defpt: "split_definite (Rep_compact_basis x) ?D" if "x \<in> srows t" for x by (rule generator_definite [OF that])
  have TTiff: "(maximal_at L \<kappa> \<and> (\<exists>y. split_definite y ?D \<and> rproj L y = \<kappa> \<and> (\<Lambda> _. TT)\<cdot>y = TT \<and> h\<cdot>(row_key\<cdot>y) = TT))
      \<longleftrightarrow> (\<exists>m\<in>?R. h\<cdot>(row_key\<cdot>m) = TT)"
  proof
    assume "maximal_at L \<kappa> \<and> (\<exists>y. split_definite y ?D \<and> rproj L y = \<kappa> \<and> (\<Lambda> _. TT)\<cdot>y = TT \<and> h\<cdot>(row_key\<cdot>y) = TT)"
    then obtain y where mx: "maximal_at L \<kappa>" and y: "split_definite y ?D" "rproj L y = \<kappa>" and hy: "h\<cdot>(row_key\<cdot>y) = TT" by auto
    obtain m where m: "m \<in> lower_maximal data" "y \<sqsubseteq> m" "rproj L m = rproj L y"
      using definite_maximal_point [OF below_refl d y(1)] mx y(2) by auto
    have "TT \<sqsubseteq> h\<cdot>(row_key\<cdot>m)" unfolding hy [symmetric] by (intro monofun_cfun_arg m(2))
    then show "\<exists>m\<in>?R. h\<cdot>(row_key\<cdot>m) = TT" using m y(2) by auto
  next
    assume "\<exists>m\<in>?R. h\<cdot>(row_key\<cdot>m) = TT"
    then obtain m where m: "m \<in> lower_maximal data" "rproj L m = \<kappa>" and hm: "h\<cdot>(row_key\<cdot>m) = TT" by blast
    obtain x where x: "x \<in> srows t" and mx: "m = Rep_compact_basis x" using pt [OF m(1)] by blast
    show "maximal_at L \<kappa> \<and> (\<exists>y. split_definite y ?D \<and> rproj L y = \<kappa> \<and> (\<Lambda> _. TT)\<cdot>y = TT \<and> h\<cdot>(row_key\<cdot>y) = TT)"
      using rowL [OF x] defpt [OF x] m(2) hm unfolding mx by auto
  qed
  have FFiff: "split_refuted L \<kappa> h ?D \<longleftrightarrow> (\<forall>m\<in>?R. h\<cdot>(row_key\<cdot>m) = FF)"
  proof -
    have r: "split_refuted L \<kappa> h ?D \<longleftrightarrow> (\<forall>u\<in>skeys t. proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa> \<longrightarrow> h\<cdot>(Rep_compact_basis u) = FF)"
      unfolding split_refuted_keyguard split_select_principal split_keyguard_principal split_keys_principal_Top by auto
    show ?thesis unfolding r
    proof (intro iffI ballI impI)
      fix m assume all: "\<forall>u\<in>skeys t. proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa> \<longrightarrow> h\<cdot>(Rep_compact_basis u) = FF" and "m \<in> ?R"
      then have m: "m \<in> lower_maximal data" "rproj L m = \<kappa>" by simp_all
      obtain x where x: "x \<in> srows t" and mx: "m = Rep_compact_basis x" using pt [OF m(1)] by blast
      obtain u where u: "u \<in> skeys t" and ux: "Rep_compact_basis u \<sqsubseteq> row_key\<cdot>(Rep_compact_basis x)"
        using split_basis_consistentD [OF x] by blast
      have "proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa>" using monofun_cfun_arg [OF ux, of "proj L"] m(2) mx by simp
      then have "h\<cdot>(Rep_compact_basis u) = FF" using all u by blast
      moreover have "h\<cdot>(Rep_compact_basis u) \<sqsubseteq> h\<cdot>(row_key\<cdot>m)" unfolding mx by (rule monofun_cfun_arg [OF ux])
      ultimately show "h\<cdot>(row_key\<cdot>m) = FF" by simp
    next
      fix u assume all: "\<forall>m\<in>?R. h\<cdot>(row_key\<cdot>m) = FF" and u: "u \<in> skeys t" and uk: "proj L\<cdot>(Rep_compact_basis u) \<sqsubseteq> \<kappa>"
      obtain x where x: "x \<in> srows t" and ux: "proj K\<cdot>(Rep_compact_basis u) = rproj K (Rep_compact_basis x)"
        using saturated_key_part [OF s u] by blast
      have le: "rproj L (Rep_compact_basis x) \<sqsubseteq> \<kappa>"
        using uk ux pk [of "Rep_compact_basis u"] pk [of "row_key\<cdot>(Rep_compact_basis x)"] by metis
      have xL: "rproj L (Rep_compact_basis x) = \<kappa>" using maximal_at_eq [OF rowL [OF x] \<kappa> le] by simp
      have rL: "maximal_at L (rproj L (Rep_compact_basis x))" by (rule rowL [OF x])
      obtain m where m: "m \<in> lower_maximal data" "Rep_compact_basis x \<sqsubseteq> m" "rproj L m = rproj L (Rep_compact_basis x)"
        by (rule definite_maximal_point [OF below_refl d defpt [OF x] rL])
      have "h\<cdot>(row_key\<cdot>m) = FF" using all m xL by auto
      then have "h\<cdot>(row_key\<cdot>(Rep_compact_basis x)) = FF" using hrow [OF x m(2)] by simp
      then show "h\<cdot>(Rep_compact_basis u) = FF" using hK [of "Rep_compact_basis u"] hK [of "row_key\<cdot>(Rep_compact_basis x)"] ux by simp
    qed
  qed
  show ?thesis
  proof (cases "\<exists>m\<in>?R. h\<cdot>(row_key\<cdot>m) = TT")
    case True
    then show ?thesis unfolding select_test_def TTiff kleene_bex_def by auto
  next
    case nT: False
    then show ?thesis unfolding select_test_def TTiff FFiff kleene_bex_def by auto
  qed
qed

end

end
