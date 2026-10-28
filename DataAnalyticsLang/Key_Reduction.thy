theory Key_Reduction
  imports Expr_Combinators
begin

section \<open>Evaluating components at their own keys\<close>

text \<open>Collecting evaluates every component under the frame raised by all the components' minimal
  LODs, at the full key.  A component may instead be evaluated under the plain frame at its own key
  when raising the frame does not refine its groups.  Raising by \<open>M\<close> refines the group of an entry
  with selector \<open>(a, \<rho>)\<close> from \<open>a \<squnion> \<rho> \<sqinter> L\<close> to \<open>a \<squnion> \<rho> \<sqinter> (L \<squnion> M)\<close>.  Two cases leave the content alone, as
  long as the full key is a data key: a row entry, whose coarse content has at most one element; and
  an entry whose coarse group LOD determines the masked part of \<open>M\<close> in every conforming dataset.\<close>

context dataspace
begin

definition reducible :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> bool" where
  "reducible M E F \<longleftrightarrow> (\<forall>e\<in>set (edims E).
     row_entry e \<or> universally (\<lambda>P. vfd P (\<bottom>, sel_at (esel e) (flod F)) (\<bottom>, (eupper e \<sqinter> M))))"

end

context dataspace
begin

lemma content_reduce:
  assumes ES: "semilawful E" and d: "conforms data" and M: "emind E \<sqsubseteq> M" and e: "e \<in> set (edims E)"
    and red: "row_entry e \<or> universally (\<lambda>P. vfd P (\<bottom>, sel_at (esel e) (flod F)) (\<bottom>, (eupper e \<sqinter> M)))"
    and ki: "keyimg data F (M \<squnion> flod F) k"
  shows "content data e (finclude M F) k = content data e F (proj (kd E F)\<cdot>k)"
proof -
  let ?a = "elower e" and ?\<rho> = "eupper e"
  let ?Gc = "?a \<squnion> (?\<rho> \<sqinter> flod F)" and ?T = "(?\<rho> \<sqinter> M)"
  let ?Gf = "?a \<squnion> (?\<rho> \<sqinter> (flod F \<squnion> M))" and ?W = "M \<squnion> flod F"
  have Gf: "?Gf = ?Gc \<squnion> ?T" by (simp add: truncate_sup lattice_join_assoc)
  have aM: "?a \<sqsubseteq> M" by (rule below_trans[OF lower_below_mind[OF ES e] M])
  have Gc_kd: "?Gc \<sqsubseteq> kd E F" by (rule group_below_kd[OF ES e])
  have "(?\<rho> \<sqinter> (flod F \<squnion> M)) \<sqsubseteq> ?W"
    using truncate_below[of ?\<rho> "flod F \<squnion> M"] by (simp only: lattice_join_commute)
  then have Gf_W: "?Gf \<sqsubseteq> ?W" by (rule join_belowI[OF below_trans[OF aM lattice_join_ge1]])
  have Gc_W: "?Gc \<sqsubseteq> ?W"
    by (rule below_trans[OF _ Gf_W]) (simp add: Gf lattice_join_ge1)
  obtain x where x: "x \<in> lower_maximal data" "frows F x" and kx: "k = rproj ?W x"
    using ki by (auto simp: keyimg_def)
  have pk: "proj G\<cdot>k = rproj G x" if "G \<sqsubseteq> ?W" for G
    unfolding kx by (rule proj_le[OF that])
  have pkd: "proj ?Gc\<cdot>(proj (kd E F)\<cdot>k) = proj ?Gc\<cdot>k" by (rule proj_le[OF Gc_kd])
  let ?P = "\<lambda>y. y \<in> lower_maximal data \<and> selects (amb F) y \<and> holds (coarsen ?\<rho> (slice F)) (rkey\<cdot>y)"
  have fine: "group data ?a ?\<rho> (finclude M F) k = {y. ?P y \<and> rproj ?Gf y = rproj ?Gf x}"
    by (auto simp: group_def flod_finclude pk[OF Gf_W])
  have coarse: "group data ?a ?\<rho> F (proj (kd E F)\<cdot>k) = {y. ?P y \<and> rproj ?Gc y = rproj ?Gc x}"
    by (auto simp: group_def pkd pk[OF Gc_W])
  have fine_eq: "rproj ?Gf y = rproj ?Gf x \<longleftrightarrow> rproj ?Gc y = rproj ?Gc x \<and> rproj ?T y = rproj ?T x" for y
    unfolding Gf by (rule rproj_sup_eq)
  have Px: "?P x" using x by (auto simp: frows_def intro: holds_coarsen)
  have det: "determines (lower_maximal data) v g" if "universally (\<lambda>P. determines P v g)" for v and g :: "'r \<rightarrow> 'b::cpo"
    using universallyD[OF that] d .
  show ?thesis
    using red
  proof
    assume row: "row_entry e"
    let ?g = "\<lambda>y. ofun (eguard e)\<cdot>y"
    have img: "cpair e ` {y \<in> Y. ?g y = TT} = (if ?g x = TT then {cpair e x} else {})"
      if Y: "Y \<subseteq> {y. ?P y \<and> rproj ?Gc y = rproj ?Gc x}" and xY: "x \<in> Y" for Y
      by (rule row_entry_image[OF semilawful_wf[OF ES e] row d _ xY lattice_join_ge1]) (use Y in blast)+
    have "cgraph data e (finclude M F) k = cpair e ` {y \<in> {y. ?P y \<and> rproj ?Gf y = rproj ?Gf x}. ?g y = TT}"
      unfolding cgraph_def efiber_def fine ..
    also have "\<dots> = (if ?g x = TT then {cpair e x} else {})"
      by (rule img) (use Px in \<open>auto simp: fine_eq\<close>)
    also have "\<dots> = cpair e ` {y \<in> {y. ?P y \<and> rproj ?Gc y = rproj ?Gc x}. ?g y = TT}"
      by (rule img[symmetric]) (use Px in auto)
    also have "\<dots> = cgraph data e F (proj (kd E F)\<cdot>k)"
      unfolding cgraph_def efiber_def coarse ..
    finally show ?thesis unfolding content_def by simp
  next
    assume fd: "universally (\<lambda>P. vfd P (\<bottom>, ?Gc) (\<bottom>, ?T))"
    have "rproj ?T y = rproj ?T x" if y: "?P y" "rproj ?Gc y = rproj ?Gc x" for y
    proof -
      have "vpart (\<bottom>, ?Gc) y = vpart (\<bottom>, ?Gc) x" using y(2) by (simp add: proj_bot)
      then have "vpart (\<bottom>, ?T) y = vpart (\<bottom>, ?T) x"
        using vfdD[OF det[OF fd]] y(1) x(1) by blast
      then show ?thesis by simp
    qed
    then have "{y. ?P y \<and> rproj ?Gf y = rproj ?Gf x} = {y. ?P y \<and> rproj ?Gc y = rproj ?Gc x}"
      unfolding fine_eq by blast
    then show ?thesis by (intro content_group_cong) (simp only: fine coarse)
  qed
qed

theorem sem_reduce:
  assumes ES: "semilawful E" and d: "conforms data" and M: "emind E \<sqsubseteq> M" and red: "reducible M E F"
    and ki: "keyimg data F (M \<squnion> flod F) k"
  shows "esem E data (finclude M F) k = esem E data F (proj (kd E F)\<cdot>k)"
proof (rule semilawful_content_law[OF ES d d])
  have W: "kd E (finclude M F) = M \<squnion> flod F"
  proof -
    have "emind E \<squnion> (flod F \<squnion> M) = (emind E \<squnion> M) \<squnion> flod F" by (simp only: lattice_join_ac)
    then show ?thesis by (simp only: flod_finclude lattice_join_absorb2[OF M])
  qed
  obtain x where "k = rproj (M \<squnion> flod F) x" using ki by (auto simp: keyimg_def)
  then show "proj (kd E (finclude M F))\<cdot>k = k" unfolding W by simp
  show "proj (kd E F)\<cdot>(proj (kd E F)\<cdot>k) = proj (kd E F)\<cdot>k" by simp
  show "contents data (edims E) (finclude M F) k = contents data (edims E) F (proj (kd E F)\<cdot>k)"
  proof (rule map_cong[OF refl])
    fix e assume e: "e \<in> set (edims E)"
    have r: "row_entry e \<or> universally (\<lambda>P. vfd P (\<bottom>, sel_at (esel e) (flod F)) (\<bottom>, (eupper e \<sqinter> M)))"
      using red e by (auto simp: reducible_def)
    show "content data e (finclude M F) k = content data e F (proj (kd E F)\<cdot>k)"
      by (rule content_reduce[OF ES d M e r ki])
  qed
qed

end

text \<open>The gate without widening: under reducibility by its own minimal LOD, the gate evaluates
  the expression under the plain frame, at its own key.\<close>

context dataspace
begin

theorem gate_reduce:
  assumes E: "semilawful E" and d: "conforms data" and red: "reducible (emind E) E F"
  shows "esem (gate \<bottom> E) data F k = (if keyimg data F (emind E \<squnion> flod F) k
      then esem E data F (proj (emind E \<squnion> flod F)\<cdot>k) else None)"
proof -
  have ES: "semilawful E" by (fact E)
  show ?thesis using sem_reduce[OF ES d below_refl red] by simp
qed

end

text \<open>A collection is reducible when its components are; then \<open>gate_reduce\<close> evaluates the gated
  collection under the plain frame, each component at its own key.\<close>

context dataspace
begin

lemma reducible_collect: "reducible M (collect Es) F \<longleftrightarrow> (\<forall>E\<in>set Es. reducible M E F)"
  unfolding reducible_def by auto

end

end
