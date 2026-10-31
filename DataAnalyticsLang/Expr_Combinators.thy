theory Expr_Combinators
  imports Content_Law
begin

section \<open>Combinators\<close>

text \<open>Each combinator transforms the entries of its inner expressions along with their semantics,
  and is lawful on lawful inner expressions.  Collecting a list of expressions into a tuple,
  followed by a map, expresses every operator of any arity.\<close>

subsection \<open>Tuples\<close>

text \<open>A collected expression is present where every component is; its value is the list of the
  components' values.  Absence is the expression's, so the list needs no bottom: tuples are plain
  lists, ordered componentwise at equal length.\<close>



context dataspace
begin

subsection \<open>Keys\<close>

text \<open>The key at an LOD \<open>c\<close>.  It has no guard: the frame's filters reach expressions only through
  the guards aggregations expose.  Its value entry reads no columns and is keyed at \<open>c\<close>, so its
  content's one key is that key part; it is present where some row of the data has that key part.\<close>

lemma join_meet_self: "c \<squnion> (c \<sqinter> L) = c" for c :: "'k semi_factor"
  by (rule lattice_join_absorb1[OF lattice_meet_le1])

lemma rigid_dom_empty: "rigid (\<lambda>Xs :: ('k \<Rightarrow> 'r option) list. dom (hd Xs) = {})"
  by (rule rigidI) (simp only: rigidD[OF rigid_comp[OF rigid_dom cont2mono[OF cont_hd]]])

lemma cont_key_value: "cont (\<lambda>Xs :: ('k \<Rightarrow> 'r option) list. Present\<cdot>(the_elem (dom (hd Xs))))"
  by (rule cont_rigid, rule rigidI) (simp only: rigidD[OF rigid_comp[OF rigid_dom cont2mono[OF cont_hd]]])

lemma cont_key_at_csem:
  "cont (\<lambda>Xs :: ('k \<Rightarrow> 'r option) list. if dom (hd Xs) = {} then Absent else Present\<cdot>(the_elem (dom (hd Xs))))"
  by (rule cont_if_rigid[OF rigid_dom_empty cont_const cont_key_value])

definition key_at :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'k) expr" where
  "key_at c = \<lparr>emind = c, eguards = [], evalues = [mk_value (sel c c) \<bottom> c],
     esem = \<lambda>data F k. if fiber data c c F k = {} then Absent else Present\<cdot>(proj c\<cdot>k),
     csem = \<lambda>Gs. \<Lambda> Xs. if dom (hd Xs) = {} then Absent else Present\<cdot>(the_elem (dom (hd Xs)))\<rparr>"

lemma key_at_simps [simp]:
  "emind (key_at c) = c" "eguards (key_at c) = []" "evalues (key_at c) = [mk_value (sel c c) \<bottom> c]"
  "esem (key_at c) data F k = (if fiber data c c F k = {} then Absent else Present\<cdot>(proj c\<cdot>k))"
  "csem (key_at c) Gs\<cdot>Xs = (if dom (hd Xs) = {} then Absent else Present\<cdot>(the_elem (dom (hd Xs))))"
  by (simp_all only: key_at_def expr.select_convs beta_cfun[OF cont_key_at_csem])

lemma fiber_own: "y \<in> fiber data c c F k \<Longrightarrow> rproj c y = proj c\<cdot>k"
  by (simp add: fiber_def join_meet_self)

lemma dom_content_own:
  "dom (content data (mk_value (sel c c) b c) F k) = (\<lambda>_. proj c\<cdot>k) ` fiber data c c F k"
  unfolding content_def dom_gmap cgraph_def image_image cpair_def
  by (rule image_cong) (simp_all add: vfiber_def fiber_own)

lemma dom_content_own_empty: "dom (content data (mk_value (sel c c) b c) F k) = {} \<longleftrightarrow> fiber data c c F k = {}"
  by (simp add: dom_content_own)

lemma dom_content_key_at:
  assumes "fiber data c c F k \<noteq> {}"
  shows "dom (content data (mk_value (sel c c) \<bottom> c) F k) = {proj c\<cdot>k}"
  using assms by (simp add: dom_content_own image_constant_conv)

lemma cstrict_key_at: "cstrict (key_at c)"
  by (rule cstrictI) simp

theorem semilawful_key_at: "semilawful (key_at c)"
proof (rule semilawfulI, simp_all only: key_at_simps)
  let ?e = "mk_value (sel c c) \<bottom> c"
  show "cstrict (key_at c)" by (rule cstrict_key_at)
  show "entry_wf e" if "e \<in> set [?e]" for e using that by (simp add: entry_wf_view keyed_view_key)
  show "c = fold (\<squnion>) (map lower_part (map esel [] @ map esel [?e])) \<bottom>"
    by (simp add: lattice_join_bot_right)
  show "(if fiber data c c F k = {} then Absent else Present\<cdot>(proj c\<cdot>k))
      = (if dom (hd (contents data [?e] F k)) = {} then Absent else Present\<cdot>(the_elem (dom (hd (contents data [?e] F k)))))"
    for data F k
  proof (cases "fiber data c c F k = {}")
    case False
    then show ?thesis by (simp only: list.map list.sel dom_content_key_at[OF False]) simp
  qed (simp add: content_def cgraph_def vfiber_def)
qed

subsection \<open>Table columns\<close>

text \<open>A table column reads a section of the row.  An external oracle names the key part that
  determines it in every conforming dataset; then the rows of a key's fiber carry one section,
  and the column's value is the column function of it.  Its value entry is that section, keyed at
  the oracle's key part; like a key, it has no guard.\<close>

lemma cont_column_value:
  "cont (\<lambda>Xs :: ('k \<Rightarrow> 'r option) list. Present\<cdot>(v\<cdot>(the (hd Xs (the_elem (dom (hd Xs)))))))"
proof -
  have "cont (\<lambda>Xs :: ('k \<Rightarrow> 'r option) list. hd Xs (the_elem (dom (hd Xs))))"
    by (rule cont_rigid_arg[OF _ rigid_comp[OF rigid_dom cont2mono[OF cont_hd]]]) (simp add: cont2cont_fun)
  then show ?thesis by (simp add: cont_compose[OF cont_the])
qed

lemma cont_column_csem:
  "cont (\<lambda>Xs :: ('k \<Rightarrow> 'r option) list. if dom (hd Xs) = {} then Absent
     else Present\<cdot>(v\<cdot>(the (hd Xs (the_elem (dom (hd Xs)))))))"
  by (rule cont_if_rigid[OF rigid_dom_empty cont_const cont_column_value])

definition column :: "'r semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('r \<rightarrow> 'w::bifinite) \<Rightarrow> ('k, 'f, 'r, 'w) expr" where
  "column c a v = \<lparr>emind = a, eguards = [], evalues = [mk_value (sel a a) c a],
     esem = \<lambda>data F k. if fiber data a a F k = {} then Absent
       else Present\<cdot>(THE w. w \<in> (\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` fiber data a a F k),
     csem = \<lambda>Gs. \<Lambda> Xs. if dom (hd Xs) = {} then Absent else Present\<cdot>(v\<cdot>(the (hd Xs (the_elem (dom (hd Xs))))))\<rparr>"

lemma column_simps [simp]:
  "emind (column c a v) = a" "eguards (column c a v) = []" "evalues (column c a v) = [mk_value (sel a a) c a]"
  "esem (column c a v) data F k = (if fiber data a a F k = {} then Absent
       else Present\<cdot>(THE w. w \<in> (\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` fiber data a a F k))"
  "csem (column c a v) Gs\<cdot>Xs = (if dom (hd Xs) = {} then Absent else Present\<cdot>(v\<cdot>(the (hd Xs (the_elem (dom (hd Xs)))))))"
  by (simp_all only: column_def expr.select_convs beta_cfun[OF cont_column_csem])

text \<open>The rows of a column's fiber carry one section.\<close>

lemma column_fiber_section:
  assumes cf: "entry_conf (mk_value (sel a a) c a) data F"
    and x: "x \<in> fiber data a a F k" and y: "y \<in> fiber data a a F k"
  shows "y \<downharpoonright> c = x \<downharpoonright> c"
proof -
  have G: "sel_at (sel a a) (flod F) \<squnion> a = a" by (simp add: join_meet_self lattice_join_absorb1[OF below_refl])
  have m: "x \<in> lower_maximal data" "y \<in> lower_maximal data" using x y by (simp_all add: fiber_def)
  have cf': "vfd (lower_maximal data) (\<bottom>, a) (c, \<bottom>)" using cf G by (simp add: entry_conf_def)
  have "vpart (\<bottom>, a) y = vpart (\<bottom>, a) x" using x y by (simp add: fiber_own semi_factor_p_bot)
  from vfdD[OF cf' m(2) m(1) this] show ?thesis by simp
qed

lemma cstrict_column: "cstrict (column c a v)"
  by (rule cstrictI) simp

theorem semilawful_column:
  assumes fd: "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>))"
  shows "semilawful (column c a v)"
proof (rule semilawfulI, simp_all only: column_simps)
  let ?e = "mk_value (sel a a) c a"
  show "cstrict (column c a v)" by (rule cstrict_column)
  show "entry_wf e" if "e \<in> set [?e]" for e
    using that by (simp add: entry_wf_view keyed_view_columns[OF fd])
  show "a = fold (\<squnion>) (map lower_part (map esel [] @ map esel [?e])) \<bottom>"
    by (simp add: lattice_join_bot_right)
  show "(if fiber data a a F k = {} then Absent else Present\<cdot>(THE w. w \<in> (\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` fiber data a a F k))
      = (if dom (hd (contents data [?e] F k)) = {} then Absent
         else Present\<cdot>(v\<cdot>(the (hd (contents data [?e] F k) (the_elem (dom (hd (contents data [?e] F k))))))))"
    if d: "fconf [?e] data F" for data F k
  proof (cases "fiber data a a F k = {}")
    case False
    then obtain x where x: "x \<in> fiber data a a F k" by blast
    have cf: "entry_conf ?e data F" using d by (simp add: fconf_def)
    have "cgraph data ?e F k = (\<lambda>_. (proj a\<cdot>k, x \<downharpoonright> c)) ` fiber data a a F k"
      unfolding cgraph_def vfiber_def cpair_def
      by (rule image_cong) (simp_all add: fiber_own column_fiber_section[OF cf x])
    then have C: "content data ?e F k = [proj a\<cdot>k \<mapsto> x \<downharpoonright> c]"
      unfolding content_def using x by (auto simp: image_constant_conv)
    have "(\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` fiber data a a F k = (\<lambda>_. v\<cdot>(x \<downharpoonright> c)) ` fiber data a a F k"
      by (rule image_cong[OF refl]) (simp add: column_fiber_section[OF cf x])
    then have V: "(\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` fiber data a a F k = {v\<cdot>(x \<downharpoonright> c)}"
      using False by (simp add: image_constant_conv)
    show ?thesis using False by (simp only: list.map list.sel C V) simp
  next
    case True
    then show ?thesis by (simp add: content_def cgraph_def vfiber_def)
  qed
qed

subsection \<open>Maps\<close>

definition smap :: "('v::bifinite \<rightarrow> 'w::bifinite) \<Rightarrow> ('k, 'f, 'r, 'v, 'z) expr_scheme \<Rightarrow> ('k, 'f, 'r, 'w) expr" where
  "smap g E = \<lparr>emind = emind E, eguards = eguards E, evalues = evalues E,
     esem = \<lambda>data F k. map_option_pd g\<cdot>(esem E data F k),
     csem = \<lambda>Gs. \<Lambda> Xs. map_option_pd g\<cdot>(csem E Gs\<cdot>Xs)\<rparr>"

lemma smap_simps [simp]:
  "emind (smap g E) = emind E" "eguards (smap g E) = eguards E" "evalues (smap g E) = evalues E"
  "esem (smap g E) data F k = map_option_pd g\<cdot>(esem E data F k)"
  "csem (smap g E) Gs\<cdot>Xs = map_option_pd g\<cdot>(csem E Gs\<cdot>Xs)"
  by (simp_all add: smap_def)

lemma map_option_pd_not_Absent: "map_option_pd g\<cdot>x \<noteq> Absent \<Longrightarrow> x \<noteq> Absent"
  by auto

lemma cstrict_smap: "cstrict E \<Longrightarrow> cstrict (smap g E)"
  unfolding cstrict_def smap_simps by (blast dest: map_option_pd_not_Absent)

theorem semilawful_smap: assumes "semilawful E" shows "semilawful (smap g E)"
proof -
  have ES: "semilawful E" by (fact assms)
  show ?thesis
  proof (rule semilawfulI, simp_all only: smap_simps)
    show "cstrict (smap g E)" by (rule cstrict_smap[OF semilawful_cstrict[OF ES]])
    show "entry_wf e" if "e \<in> set (evalues E)" for e by (rule semilawful_wf[OF ES that])
    show "emind E = fold (\<squnion>) (map lower_part (esels E)) \<bottom>" by (rule semilawful_mind_lub[OF ES])
    show "map_option_pd g\<cdot>(esem E data F k) = map_option_pd g\<cdot>(csem_at E data F k)"
      if "fconf (evalues E) data F" "proj (emind E \<squnion> flod F)\<cdot>k = k" for data F k
      by (simp only: semilawful_csem_conf[OF ES that])
  qed
qed

theorem lawful_smap: assumes "lawful E" shows "lawful (smap g E)"
proof -
  have EL: "lawful E" by (fact assms)
  show ?thesis
  proof (rule lawful_semiI[OF semilawful_smap[OF lawful_semilawful[OF assms]]], simp_all only: smap_simps)
    show "keyimg data F (emind E \<squnion> flod F) k" if d: "fconf (evalues E) data F" and k: "proj (emind E \<squnion> flod F)\<cdot>k = k"
      and "map_option_pd g\<cdot>(esem E data F k) \<noteq> Absent" for data F k
      by (rule lawful_key_law_conf[OF EL d k map_option_pd_not_Absent[OF that(3)]])
  qed
qed

text \<open>A function of the key at an LOD.\<close>

definition value_at :: "'k semi_factor \<Rightarrow> ('k \<rightarrow> 'v::bifinite) \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "value_at c g = smap g (key_at c)"

lemma value_at_simps [simp]:
  "emind (value_at c g) = c" "eguards (value_at c g) = []" "evalues (value_at c g) = [mk_value (sel c c) \<bottom> c]"
  "esem (value_at c g) data F k = (if fiber data c c F k = {} then Absent else Present\<cdot>(g\<cdot>(proj c\<cdot>k)))"
  "csem (value_at c g) Gs\<cdot>Xs = (if dom (hd Xs) = {} then Absent else Present\<cdot>(g\<cdot>(the_elem (dom (hd Xs)))))"
  by (simp_all add: value_at_def)

theorem semilawful_value_at: "semilawful (value_at c g)"
  unfolding value_at_def by (rule semilawful_smap[OF semilawful_key_at])

subsection \<open>\<open>RESTRICT\<close>\<close>

text \<open>Restricting conjoins a test, three-valued, to the ambient filter.  Only guards see the frame's
  filters: the test is conjoined to each row guard, and value entries are left alone.\<close>

definition restrict_entry :: "'r guard \<Rightarrow> ('k, 'r guard \<times> 'k guard) entry \<Rightarrow> ('k, 'r guard \<times> 'k guard) entry" where
  "restrict_entry \<gamma> e = e\<lparr>epay := (gand \<gamma> (eguard e), ekguard e)\<rparr>"

lemma restrict_entry_simps [simp]:
  "esel (restrict_entry \<gamma> e) = esel e" "ekeys (restrict_entry \<gamma> e) = ekeys e"
  "eguard (restrict_entry \<gamma> e) = gand \<gamma> (eguard e)" "ekguard (restrict_entry \<gamma> e) = ekguard e"
  by (simp_all add: restrict_entry_def)

definition restrict :: "'r guard \<Rightarrow> ('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "restrict \<gamma> E = \<lparr>emind = emind E, eguards = map (restrict_entry \<gamma>) (eguards E), evalues = evalues E,
     esem = \<lambda>data F. esem E data (frestrict \<gamma> F), csem = csem E\<rparr>"

lemma restrict_simps [simp]:
  "emind (restrict \<gamma> E) = emind E"
  "eguards (restrict \<gamma> E) = map (restrict_entry \<gamma>) (eguards E)" "evalues (restrict \<gamma> E) = evalues E"
  "esem (restrict \<gamma> E) data F = esem E data (frestrict \<gamma> F)"
  "csem (restrict \<gamma> E) = csem E"
  by (simp_all add: restrict_def)

lemma fiber_frestrict: "fiber data a \<rho> (frestrict \<phi> F) k = fiber data a \<rho> F k"
  by (simp add: fiber_def)

lemma gcontent_frestrict:
  "gcontent data e (frestrict \<gamma> F) k = gcontent data (restrict_entry \<gamma> e) F k"
  by (simp add: fun_eq_iff gcontent_def gfiber_def gtruth_def fiber_frestrict gand_assoc)

lemma content_frestrict: "content data e (frestrict \<phi> F) k = content data e F k"
  by (simp add: content_def cgraph_def vfiber_def fiber_frestrict)

lemma cstrict_restrict: "cstrict E \<Longrightarrow> cstrict (restrict \<gamma> E)"
  unfolding cstrict_def by simp

lemma fconf_frestrict: "fconf es data (frestrict \<phi> F) \<longleftrightarrow> fconf es data F"
  by (simp add: fconf_def entry_conf_def)

theorem semilawful_restrict:
  assumes ES: "semilawful E"
  shows "semilawful (restrict \<gamma> E)"
proof (rule semilawfulI, simp_all only: restrict_simps)
  show "cstrict (restrict \<gamma> E)" by (rule cstrict_restrict[OF semilawful_cstrict[OF ES]])
  show "entry_wf e" if "e \<in> set (evalues E)" for e by (rule semilawful_wf[OF ES that])
  show "emind E = fold (\<squnion>) (map lower_part (map esel (map (restrict_entry \<gamma>) (eguards E)) @ map esel (evalues E))) \<bottom>"
    by (simp add: comp_def semilawful_mind_lub[OF ES])
  show "esem E data (frestrict \<gamma> F) k
      = csem E (gcontents data (map (restrict_entry \<gamma>) (eguards E)) F k)\<cdot>(contents data (evalues E) F k)"
    if d: "fconf (evalues E) data F" and k: "proj (emind E \<squnion> flod F)\<cdot>k = k" for data F k
  proof -
    have d': "fconf (evalues E) data (frestrict \<gamma> F)" using d by (simp only: fconf_frestrict)
    have "proj (emind E \<squnion> flod (frestrict \<gamma> F))\<cdot>k = k" using k by simp
    then show ?thesis
      by (simp add: semilawful_csem_conf[OF ES d'] gcontent_frestrict content_frestrict comp_def)
  qed
qed

theorem lawful_restrict:
  assumes EL: "lawful E"
  shows "lawful (restrict \<gamma> E)"
proof (rule lawful_semiI[OF semilawful_restrict[OF lawful_semilawful[OF EL]]], simp_all only: restrict_simps)
  show "keyimg data F (emind E \<squnion> flod F) k" if d: "fconf (evalues E) data F" and k: "proj (emind E \<squnion> flod F)\<cdot>k = k"
    and "esem E data (frestrict \<gamma> F) k \<noteq> Absent" for data F k
  proof -
    have d': "fconf (evalues E) data (frestrict \<gamma> F)" using d by (simp only: fconf_frestrict)
    have "keyimg data (frestrict \<gamma> F) (emind E \<squnion> flod F) k"
      using lawful_key_law_conf[OF EL d' _ that(3)] k by simp
    then show ?thesis by (rule keyimg_mono[rotated]) (simp add: frows_frestrict)
  qed
qed

subsection \<open>\<open>FOR\<close> and \<open>FIXED\<close>\<close>

text \<open>\<open>E FOR \<tau> G\<close>: the inner expression under the frame with LOD and slice truncated to \<open>\<tau>\<close>
  and \<open>G\<close> conjoined, at the truncated key.  Its upper parts meet \<open>\<tau>\<close>; each key guard is conjoined
  with \<open>G\<close> coarsened to the guard's upper part.  It is not gated: the result is broadcast over the
  dropped detail.  \<open>FIXED D\<close> is \<open>FOR D\<close> without a filter.\<close>

definition for_entry :: "'k semi_factor \<Rightarrow> 'f \<Rightarrow> ('k, 'r guard \<times> 'k guard) entry \<Rightarrow> ('k, 'r guard \<times> 'k guard) entry" where
  "for_entry \<tau> G e = e\<lparr>esel := trunc_sel \<tau> (esel e), epay := (eguard e, gand (sopen (coarsen (eupper e) G)) (ekguard e))\<rparr>"

definition for_value :: "'k semi_factor \<Rightarrow> ('k, 'r semi_factor) entry \<Rightarrow> ('k, 'r semi_factor) entry" where
  "for_value \<tau> e = e\<lparr>esel := trunc_sel \<tau> (esel e)\<rparr>"

lemma for_entry_simps [simp]:
  "esel (for_entry \<tau> G e) = trunc_sel \<tau> (esel e)" "ekeys (for_entry \<tau> G e) = ekeys e"
  "eguard (for_entry \<tau> G e) = eguard e" "ekguard (for_entry \<tau> G e) = gand (sopen (coarsen (eupper e) G)) (ekguard e)"
  by (simp_all add: for_entry_def)

lemma for_value_simps [simp]:
  "esel (for_value \<tau> e) = trunc_sel \<tau> (esel e)" "ekeys (for_value \<tau> e) = ekeys e" "ecols (for_value \<tau> e) = ecols e"
  by (simp_all add: for_value_def)

definition filtfor :: "'k semi_factor \<Rightarrow> 'f \<Rightarrow> ('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "filtfor \<tau> G E = \<lparr>emind = emind E, eguards = map (for_entry \<tau> G) (eguards E),
     evalues = map (for_value \<tau>) (evalues E),
     esem = \<lambda>data F k. esem E data (ffor \<tau> G F) (proj (emind E \<squnion> flod (ffor \<tau> G F))\<cdot>k), csem = csem E\<rparr>"

abbreviation fixed :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "fixed D \<equiv> filtfor D \<^bold>1"

lemma filtfor_simps [simp]:
  "emind (filtfor \<tau> G E) = emind E"
  "eguards (filtfor \<tau> G E) = map (for_entry \<tau> G) (eguards E)"
  "evalues (filtfor \<tau> G E) = map (for_value \<tau>) (evalues E)"
  "esem (filtfor \<tau> G E) data F k = esem E data (ffor \<tau> G F) (proj (emind E \<squnion> flod (ffor \<tau> G F))\<cdot>k)"
  "csem (filtfor \<tau> G E) = csem E"
  by (simp_all add: filtfor_def)

text \<open>Inside the truncated frame, at the truncated key, a fiber is the outer fiber through the
  composite mask, and the frame's filter at an upper part moreover conjoins the filter coarsened
  there.\<close>

lemma ffor_key:
  assumes am: "a \<sqsubseteq> m"
  shows "a \<squnion> (\<rho> \<sqinter> flod (ffor \<tau> G F)) = a \<squnion> ((\<rho> \<sqinter> \<tau>) \<sqinter> flod F)"
    and "proj (a \<squnion> ((\<rho> \<sqinter> \<tau>) \<sqinter> flod F))\<cdot>(proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k) = proj (a \<squnion> ((\<rho> \<sqinter> \<tau>) \<sqinter> flod F))\<cdot>k"
proof -
  show "a \<squnion> (\<rho> \<sqinter> flod (ffor \<tau> G F)) = a \<squnion> ((\<rho> \<sqinter> \<tau>) \<sqinter> flod F)" by (simp add: truncate_inf_comp)
  have le: "a \<squnion> ((\<rho> \<sqinter> \<tau>) \<sqinter> flod F) \<sqsubseteq> m \<squnion> flod (ffor \<tau> G F)"
    unfolding flod_ffor truncate_inf_comp by (rule lattice_join_mono[OF am truncate_below])
  show "proj (a \<squnion> ((\<rho> \<sqinter> \<tau>) \<sqinter> flod F))\<cdot>(proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k) = proj (a \<squnion> ((\<rho> \<sqinter> \<tau>) \<sqinter> flod F))\<cdot>k"
    by (rule proj_le[OF le])
qed

lemma fiber_ffor:
  assumes am: "a \<sqsubseteq> m"
  shows "fiber data a \<rho> (ffor \<tau> G F) (proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k) = fiber data a (\<rho> \<sqinter> \<tau>) F k"
  unfolding fiber_def ffor_key[OF am] ..

lemma gcontent_ffor:
  assumes "elower e \<sqsubseteq> m"
  shows "gcontent data e (ffor \<tau> G F) (proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k) = gcontent data (for_entry \<tau> G e) F k"
  unfolding fun_eq_iff gcontent_def gfiber_def fiber_ffor[OF assms]
  by (simp add: gtruth_def coarsen_conj coarsen_coarsen sopen_gand gand_assoc)

lemma content_ffor:
  assumes "elower e \<sqsubseteq> m"
  shows "content data e (ffor \<tau> G F) (proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k) = content data (for_value \<tau> e) F k"
  unfolding content_def cgraph_def vfiber_def fiber_ffor[OF assms] cpair_def by simp

lemma cstrict_filtfor: "cstrict E \<Longrightarrow> cstrict (filtfor \<tau> G E)"
  unfolding cstrict_def by simp

lemma fconf_filtfor: "fconf (map (for_value \<tau>) es) data F \<longleftrightarrow> fconf es data (ffor \<tau> G F)"
  by (simp add: fconf_def entry_conf_def lattice_meet_assoc)

theorem semilawful_filtfor: assumes "semilawful E" shows "semilawful (filtfor \<tau> G E)"
proof -
  have ES: "semilawful E" by (fact assms)
  let ?m = "emind E"
  have ginner: "gcontents data (eguards E) (ffor \<tau> G H) (proj (?m \<squnion> flod (ffor \<tau> G H))\<cdot>\<kappa>)
      = gcontents data (map (for_entry \<tau> G) (eguards E)) H \<kappa>" for data H \<kappa>
    unfolding map_map comp_def by (rule map_cong[OF refl], rule gcontent_ffor[OF lower_below_mind_guard[OF ES]])
  have inner: "contents data (evalues E) (ffor \<tau> G H) (proj (?m \<squnion> flod (ffor \<tau> G H))\<cdot>\<kappa>)
      = contents data (map (for_value \<tau>) (evalues E)) H \<kappa>" for data H \<kappa>
    unfolding map_map comp_def by (rule map_cong[OF refl], rule content_ffor[OF lower_below_mind_value[OF ES]])
  show ?thesis
  proof (rule semilawfulI, simp_all only: filtfor_simps)
    show "cstrict (filtfor \<tau> G E)" by (rule cstrict_filtfor[OF semilawful_cstrict[OF ES]])
    show "entry_wf e" if "e \<in> set (map (for_value \<tau>) (evalues E))" for e
      using that semilawful_wf[OF ES] by (auto simp: entry_wf_def)
    show "?m = fold (\<squnion>) (map lower_part (map esel (map (for_entry \<tau> G) (eguards E)) @ map esel (map (for_value \<tau>) (evalues E)))) \<bottom>"
      by (simp add: comp_def semilawful_mind_lub[OF ES])
    show "esem E data (ffor \<tau> G F) (proj (?m \<squnion> flod (ffor \<tau> G F))\<cdot>k)
        = csem E (gcontents data (map (for_entry \<tau> G) (eguards E)) F k)\<cdot>(contents data (map (for_value \<tau>) (evalues E)) F k)"
      if d: "fconf (map (for_value \<tau>) (evalues E)) data F" for data F k
      by (simp only: semilawful_csem_conf[OF ES d[unfolded fconf_filtfor[of _ _ _ _ G]] proj_idem] ginner inner)
  qed
qed

subsection \<open>Including dimensions\<close>

text \<open>Evaluating under the frame raised by \<open>M\<close> is the same as raising each entry's lower part by
  its masked part of \<open>M\<close>: the entry-level form of \<open>finclude\<close>.\<close>

definition include_entry :: "'k semi_factor \<Rightarrow> ('k, 'p) entry \<Rightarrow> ('k, 'p) entry" where
  "include_entry M e = e\<lparr>esel := include_sel M (esel e)\<rparr>"

lemma include_entry_simps [simp]:
  "esel (include_entry M e) = include_sel M (esel e)" "ekeys (include_entry M e) = ekeys e"
  "epay (include_entry M e) = epay e"
  by (simp_all add: include_entry_def)

lemma include_lod: "sel_at (include_sel M S) (flod F) = sel_at S (flod (finclude M F))"
  by (simp add: flod_finclude truncate_sup lattice_join_ac)

lemma gcontent_include_entry: "gcontent data (include_entry M e) F k = gcontent data e (finclude M F) k"
proof -
  have "fiber data (sel_at (esel e) M) (eupper e) F k = fiber data (elower e) (eupper e) (finclude M F) k"
    by (rule fiber_cong) (simp_all only: include_lod[unfolded include_sel_simps])
  then show ?thesis by (simp add: fun_eq_iff gcontent_def gfiber_def gtruth_def)
qed

lemma content_include_entry: "content data (include_entry M e) F k = content data e (finclude M F) k"
proof -
  have "fiber data (sel_at (esel e) M) (eupper e) F k = fiber data (elower e) (eupper e) (finclude M F) k"
    by (rule fiber_cong) (simp_all only: include_lod[unfolded include_sel_simps])
  then show ?thesis unfolding content_def cgraph_def vfiber_def cpair_def by simp
qed

lemma fconf_include: "fconf (map (include_entry m) es) data F \<longleftrightarrow> fconf es data (finclude m F)"
  by (simp add: fconf_def entry_conf_def flod_finclude truncate_sup lattice_join_ac)

lemma entry_wf_include_entry: "entry_wf e \<Longrightarrow> entry_wf (include_entry M e)"
  by (simp add: entry_wf_def)

text \<open>The raised lower part stays below the raising LOD when the old one is.\<close>

lemma include_lower_below: "lower_part S \<sqsubseteq> m \<Longrightarrow> lower_part (include_sel m S) \<sqsubseteq> m"
  by (simp add: lattice_join_least truncate_below)

lemma include_saturates: "upper_part (include_sel m S) \<sqinter> m \<sqsubseteq> lower_part (include_sel m S)"
  by (simp add: lattice_join_ge2)

subsection \<open>Presence and raising\<close>

text \<open>An expression becomes lawful by the presence test on its full group, at the root: the one
  combinator that reads a key's realisation.  Raising the frame is separate: including dimensions
  \<open>M\<close> evaluates under the frame raised by \<open>M\<close>, which refines the groups by them where the
  expression does not mask them (\<open>GROUP BY\<close>).\<close>

text \<open>The contents of a semilawful expression only see the key at its own key LOD.\<close>

lemma contents_own_key:
  assumes E: "semilawful E"
  shows "gcontents data (eguards E) F (proj (kd E F)\<cdot>k) = gcontents data (eguards E) F k"
    and "contents data (evalues E) F (proj (kd E F)\<cdot>k) = contents data (evalues E) F k"
proof -
  have at: "proj (sel_at S (flod F))\<cdot>(proj (kd E F)\<cdot>k) = proj (sel_at S (flod F))\<cdot>k" if "S \<in> set (esels E)" for S
    by (rule proj_le[OF group_below_kd[OF E that]])
  show "gcontents data (eguards E) F (proj (kd E F)\<cdot>k) = gcontents data (eguards E) F k"
  proof (rule map_cong[OF refl])
    fix e assume e: "e \<in> set (eguards E)"
    show "gcontent data e F (proj (kd E F)\<cdot>k) = gcontent data e F k"
      using at[OF esels_guardI[OF e]] by (intro gcontent_fiber_cong) (simp_all add: fiber_def)
  qed
  show "contents data (evalues E) F (proj (kd E F)\<cdot>k) = contents data (evalues E) F k"
  proof (rule map_cong[OF refl])
    fix e assume e: "e \<in> set (evalues E)"
    show "content data e F (proj (kd E F)\<cdot>k) = content data e F k"
      using at[OF esels_valueI[OF e]] by (intro content_fiber_cong) (simp add: fiber_def)
  qed
qed

text \<open>The presence test at a selector: a true guard keyed at nothing, whose lower part also raises
  the minimal LOD.  The expression is evaluated at its own key and multiplied by whether the group
  is populated: absent where it is not, possibly absent where that is undecided.  At
  \<open>(\<bottom>, \<top>)\<close> it is the test on the full group, the key's realisation.\<close>

definition present_at :: "'k semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "present_at a \<rho> E = \<lparr>emind = emind E \<squnion> a, eguards = mk_guard (sel (emind E \<squnion> a) \<rho>) gtrue gtrue \<bottom> # eguards E,
     evalues = evalues E,
     esem = \<lambda>data F k. populated data (emind E \<squnion> a) \<rho> F k \<odot> esem E data F (proj (kd E F)\<cdot>k),
     csem = \<lambda>Gs. \<Lambda> Xs. case hd Gs \<bottom> of None \<Rightarrow> Absent | Some t \<Rightarrow> t \<odot> csem E (tl Gs)\<cdot>Xs\<rparr>"

abbreviation present :: "('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "present E \<equiv> present_at \<bottom> \<top> E"

lemma present_at_simps [simp]:
  "emind (present_at a \<rho> E) = emind E \<squnion> a"
  "eguards (present_at a \<rho> E) = mk_guard (sel (emind E \<squnion> a) \<rho>) gtrue gtrue \<bottom> # eguards E"
  "evalues (present_at a \<rho> E) = evalues E"
  "esem (present_at a \<rho> E) data F k = populated data (emind E \<squnion> a) \<rho> F k \<odot> esem E data F (proj (kd E F)\<cdot>k)"
  "csem (present_at a \<rho> E) Gs\<cdot>Xs = (case hd Gs \<bottom> of None \<Rightarrow> Absent | Some t \<Rightarrow> t \<odot> csem E (tl Gs)\<cdot>Xs)"
  by (simp_all add: present_at_def split: option.split)

lemma cstrict_present_at:
  assumes E: "cstrict E"
  shows "cstrict (present_at a \<rho> E)"
proof (rule cstrictI)
  fix Gs :: "('k \<Rightarrow> tr option) list" and Xs :: "('k \<Rightarrow> 'r option) list"
  assume l: "length Gs = length (eguards (present_at a \<rho> E))" and lx: "length Xs = length (evalues (present_at a \<rho> E))"
    and fin: "gfinite Gs" and c: "csem (present_at a \<rho> E) Gs\<cdot>Xs \<noteq> Absent"
  then obtain G Gs' where Gs: "Gs = G # Gs'" and l': "length Gs' = length (eguards E)"
    by (auto simp: length_Suc_conv)
  have fin': "gfinite Gs'" using fin by (simp add: Gs)
  have lx': "length Xs = length (evalues E)" using lx by simp
  obtain t where t: "G \<bottom> = Some t" and c': "t \<odot> csem E Gs'\<cdot>Xs \<noteq> Absent"
    using c by (cases "G \<bottom>") (simp_all add: Gs)
  have tF: "t \<noteq> FF" and cE: "csem E Gs'\<cdot>Xs \<noteq> Absent" using tr_mult_not_Absent[OF c'] by simp_all
  have "\<not> gfalse G'" if "G' \<in> set Gs'" for G' using cstrictD[OF E l' lx' fin' that] cE by blast
  moreover have "\<not> gfalse G" using t tF by (auto simp: gfalse_def)
  ultimately show "\<forall>G\<in>set Gs. \<not> gfalse G" by (simp add: Gs)
qed

theorem semilawful_present_at:
  assumes ES: "semilawful E"
  shows "semilawful (present_at a \<rho> E)"
proof (rule semilawfulI, simp_all only: present_at_simps)
  let ?h = "mk_guard (sel (emind E \<squnion> a) \<rho>) gtrue gtrue \<bottom> :: ('k, 'r guard \<times> 'k guard) entry"
  show "cstrict (present_at a \<rho> E)" by (rule cstrict_present_at[OF semilawful_cstrict[OF ES]])
  show "entry_wf e" if "e \<in> set (evalues E)" for e by (rule semilawful_wf[OF ES that])
  have "fold (\<squnion>) (map lower_part (esels E)) (emind E \<squnion> a) = emind E \<squnion> a"
    by (rule fold_join_absorb) (auto intro: below_trans[OF lower_below_mind[OF ES] lattice_join_ge1])
  then show "emind E \<squnion> a = fold (\<squnion>) (map lower_part (map esel (?h # eguards E) @ map esel (evalues E))) \<bottom>"
    by (simp add: lattice_join_bot_right)
  show "populated data (emind E \<squnion> a) \<rho> F k \<odot> esem E data F (proj (kd E F)\<cdot>k)
      = (case hd (gcontents data (?h # eguards E) F k) \<bottom> of None \<Rightarrow> Absent
         | Some t \<Rightarrow> t \<odot> csem E (tl (gcontents data (?h # eguards E) F k))\<cdot>(contents data (evalues E) F k))"
    if d: "fconf (evalues E) data F" for data F k
  proof -
    have h: "hd (gcontents data (?h # eguards E) F k) \<bottom> =
        gex (fiber data (emind E \<squnion> a) \<rho> F k) (Rep_cfun (fguard \<rho> F))"
      by (simp add: gcontent_gtrue_bot)
    have t: "tl (gcontents data (?h # eguards E) F k) = gcontents data (eguards E) F k" by simp
    have v: "esem E data F (proj (kd E F)\<cdot>k) = csem_at E data F k"
      by (simp only: semilawful_csem_conf[OF ES d proj_idem] contents_own_key[OF ES])
    show ?thesis by (simp only: h t v gex_mult populated_def)
  qed
qed

text \<open>Including dimensions: evaluating under the frame raised by \<open>M\<close>, with each entry's lower
  part raised by its masked part of \<open>M\<close>.  The minimal LOD is the join of the raised lower parts.\<close>

definition include_dims :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "include_dims M E = \<lparr>emind = fold (\<squnion>) (map (\<lambda>S. lower_part (include_sel M S)) (esels E)) \<bottom>,
     eguards = map (include_entry M) (eguards E), evalues = map (include_entry M) (evalues E),
     esem = \<lambda>data F. esem E data (finclude M F), csem = csem E\<rparr>"

lemma include_dims_simps [simp]:
  "emind (include_dims M E) = fold (\<squnion>) (map (\<lambda>S. lower_part (include_sel M S)) (esels E)) \<bottom>"
  "eguards (include_dims M E) = map (include_entry M) (eguards E)"
  "evalues (include_dims M E) = map (include_entry M) (evalues E)"
  "esem (include_dims M E) data F = esem E data (finclude M F)"
  "csem (include_dims M E) = csem E"
  by (simp_all add: include_dims_def)

lemma proj_fix_mono: "a \<sqsubseteq> b \<Longrightarrow> proj a\<cdot>k = k \<Longrightarrow> proj b\<cdot>k = k"
  by (metis proj_absorb)

theorem semilawful_include_dims:
  assumes ES: "semilawful E"
  shows "semilawful (include_dims M E)"
proof (rule semilawfulI, simp_all only: include_dims_simps)
  let ?n = "fold (\<squnion>) (map (\<lambda>S. lower_part (include_sel M S)) (esels E)) \<bottom>"
  show "cstrict (include_dims M E)" using semilawful_cstrict[OF ES] by (simp add: cstrict_def)
  show "entry_wf e" if "e \<in> set (map (include_entry M) (evalues E))" for e
    using that by (auto intro: entry_wf_include_entry semilawful_wf[OF ES])
  show "?n = fold (\<squnion>) (map lower_part (map esel (map (include_entry M) (eguards E)) @ map esel (map (include_entry M) (evalues E)))) \<bottom>"
    by (simp add: comp_def)
  show "esem E data (finclude M F) k
      = csem E (gcontents data (map (include_entry M) (eguards E)) F k)\<cdot>(contents data (map (include_entry M) (evalues E)) F k)"
    if d: "fconf (map (include_entry M) (evalues E)) data F" and k: "proj (?n \<squnion> flod F)\<cdot>k = k" for data F k
  proof -
    have d': "fconf (evalues E) data (finclude M F)" using d by (simp only: fconf_include)
    have le: "?n \<sqsubseteq> emind E \<squnion> M"
    proof (rule fold_join_least)
      fix x assume "x \<in> set (map (\<lambda>S. lower_part (include_sel M S)) (esels E))"
      then obtain S where S: "S \<in> set (esels E)" and x: "x = lower_part (include_sel M S)" by auto
      show "x \<sqsubseteq> emind E \<squnion> M" unfolding x include_sel_simps
        by (rule lattice_join_mono[OF lower_below_mind[OF ES S] truncate_below])
    qed simp
    have "?n \<squnion> flod F \<sqsubseteq> emind E \<squnion> flod (finclude M F)"
    proof -
      have "?n \<squnion> flod F \<sqsubseteq> (emind E \<squnion> M) \<squnion> flod F" by (rule lattice_join_mono[OF le below_refl])
      also have "\<dots> = emind E \<squnion> flod (finclude M F)" unfolding flod_finclude by (simp only: lattice_join_ac)
      finally show ?thesis .
    qed
    then have "proj (emind E \<squnion> flod (finclude M F))\<cdot>k = k" by (rule proj_fix_mono[OF _ k])
    then have "esem E data (finclude M F) k = csem_at E data (finclude M F) k" by (rule semilawful_csem_conf[OF ES d'])
    then show ?thesis by (simp add: comp_def gcontent_include_entry content_include_entry)
  qed
qed

text \<open>Covering is necessary, given rich enough data.  A lawful expression present at every
  realised key cannot see the same contents at a realised and at an unrealised key.  If no guard of
  a row-level expression has upper part \<open>\<top>\<close>, rich data gives exactly such a pair: over keys that are
  tuples of independent dimensions with rows equal to keys, take the rows that differ from a key
  \<open>k\<close> in exactly one dimension.  Then \<open>k\<close> is not realised, but every group LOD misses a dimension, so
  every fiber at \<open>k\<close> holds the row changed there, and a row entry reads only the part of it its
  group fixes, which is \<open>k\<close>'s; adding the row \<open>k\<close> itself changes no content.  (The construction is
  not yet formalised; the general case needs views keyed within their group LODs: subdividing
  entries can jointly reveal a realising row.)\<close>

definition total :: "('k, 'f, 'r, 'v::bifinite, 'z) expr_scheme \<Rightarrow> bool" where
  "total E \<longleftrightarrow> (\<forall>data F k. conforms data \<longrightarrow> keyimg data F (kd E F) k \<longrightarrow> esem E data F k \<noteq> Absent)"

theorem lawful_total_separates:
  assumes EL: "lawful E" and T: "total E" and d: "conforms data" "conforms data'"
    and k: "proj (kd E F)\<cdot>k = k"
    and nk: "\<not> keyimg data F (kd E F) k" and rk: "keyimg data' F (kd E F) k"
  shows "\<not> (gcontents data (eguards E) F k = gcontents data' (eguards E) F k \<and>
    contents data (evalues E) F k = contents data' (evalues E) F k)"
proof
  assume c: "gcontents data (eguards E) F k = gcontents data' (eguards E) F k \<and>
    contents data (evalues E) F k = contents data' (evalues E) F k"
  have ES: "semilawful E" by (rule lawful_semilawful[OF EL])
  have "esem E data F k = Absent" using lawful_key_law[OF EL d(1) k] nk by blast
  moreover have "esem E data' F k \<noteq> Absent" using T d(2) rk by (simp add: total_def)
  ultimately show False using c by (simp add: semilawful_csem[OF ES d(1) k] semilawful_csem[OF ES d(2) k])
qed

text \<open>The entry-level half of the construction: a row entry's content at a key is the point
  content of any row of its fiber, so two datasets whose fibers are both non-empty and carry the
  same section at the view's key give the same content; likewise for row guard entries, whose rows
  agree on the guard, given that the frame's filters are as populated in both fibers.\<close>

lemma row_entry_content_eq:
  assumes e: "entry_wf e" and r: "row_entry e" and d: "conforms data" "conforms data'"
    and x: "x \<in> vfiber data e F k" and x': "x' \<in> vfiber data' e F k"
    and s: "cpair e x = cpair e x'"
  shows "content data e F k = content data' e F k"
proof -
  have one: "cgraph D e F k = {cpair e y}" if dD: "conforms D" and y: "y \<in> vfiber D e F k" for D y
    unfolding cgraph_def
    by (rule row_entry_image[OF e r dD _ y lattice_join_ge1[of "elower e" "eupper e \<sqinter> flod F"]])
      (use y in \<open>auto simp: vfiber_def fiber_def\<close>)
  show ?thesis unfolding content_def one[OF d(1) x] one[OF d(2) x'] s ..
qed

lemma row_guard_entry_gcontent_eq:
  assumes r: "row_guard_entry e" and d: "conforms data" "conforms data'"
    and x: "x \<in> gfiber data e F k" and x': "x' \<in> gfiber data' e F k"
    and s: "rproj (ekeys e) x = rproj (ekeys e) x'"
    and g: "eguard e\<cdot>x = eguard e\<cdot>x'" and kg: "ekguard e\<cdot>(rkey\<cdot>x) = ekguard e\<cdot>(rkey\<cdot>x')"
    and f: "(\<exists>\<^sub>K y\<in>gfiber data e F k. fguard (eupper e) F\<cdot>y) = (\<exists>\<^sub>K y\<in>gfiber data' e F k. fguard (eupper e) F\<cdot>y)"
  shows "gcontent data e F k = gcontent data' e F k"
proof -
  have t: "Rep_cfun (gtruth e F) = (\<lambda>y. pand\<cdot>(fguard (eupper e) F\<cdot>y)\<cdot>(pand\<cdot>(eguard e\<cdot>y)\<cdot>(ekguard e\<cdot>(rkey\<cdot>y))))"
    by (simp add: fun_eq_iff gtruth_split)
  have one: "gcontent D e F k = (\<lambda>q. if q = rproj (ekeys e) y
      then Some (pand\<cdot>(\<exists>\<^sub>K z\<in>gfiber D e F k. fguard (eupper e) F\<cdot>z)\<cdot>(pand\<cdot>(eguard e\<cdot>y)\<cdot>(ekguard e\<cdot>(rkey\<cdot>y)))) else None)"
    if dD: "conforms D" and y: "y \<in> gfiber D e F k" for D y
    unfolding fun_eq_iff gcontent_def t
    by (intro allI row_guard_entry_image[OF r dD _ y lattice_join_ge1[of "elower e" "eupper e \<sqinter> flod F"]])
      (use y in \<open>auto simp: gfiber_def fiber_def\<close>)
  show ?thesis unfolding one[OF d(1) x] one[OF d(2) x'] s g kg f ..
qed

subsection \<open>Combining\<close>

text \<open>A binary function of two expressions: each is evaluated under the frame itself, at its own
  key, and the result is present where both are.  The entries are the two lists of entries, one
  after the other.  Any operator of any arity is a map after combining.\<close>

definition combine_csem :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<Rightarrow> ('k, 'f, 'r, 'a::bifinite, 'z) expr_scheme \<Rightarrow> ('k, 'f, 'r, 'b::bifinite, 'y) expr_scheme \<Rightarrow>
    ('k \<Rightarrow> tr option) list \<Rightarrow> ('k \<Rightarrow> 'r option) list \<Rightarrow> 'c::bifinite option_pd" where
  "combine_csem f E\<^sub>1 E\<^sub>2 Gs Xs = lift2_option_pd f\<cdot>
     (csem E\<^sub>1 (take (length (eguards E\<^sub>1)) Gs)\<cdot>(take (length (evalues E\<^sub>1)) Xs))\<cdot>
     (csem E\<^sub>2 (drop (length (eguards E\<^sub>1)) Gs)\<cdot>(drop (length (evalues E\<^sub>1)) Xs))"

lemma cont_combine_csem: "cont (combine_csem f E\<^sub>1 E\<^sub>2 Gs)"
  unfolding combine_csem_def[abs_def] by (simp add: cont_take cont_drop)

definition combine :: "('a \<rightarrow> 'b \<rightarrow> 'c) \<Rightarrow> ('k, 'f, 'r, 'a::bifinite, 'z) expr_scheme \<Rightarrow> ('k, 'f, 'r, 'b::bifinite, 'y) expr_scheme \<Rightarrow>
    ('k, 'f, 'r, 'c::bifinite) expr" where
  "combine f E\<^sub>1 E\<^sub>2 = \<lparr>emind = emind E\<^sub>1 \<squnion> emind E\<^sub>2,
     eguards = eguards E\<^sub>1 @ eguards E\<^sub>2, evalues = evalues E\<^sub>1 @ evalues E\<^sub>2,
     esem = \<lambda>data F k. lift2_option_pd f\<cdot>(esem E\<^sub>1 data F (proj (kd E\<^sub>1 F)\<cdot>k))\<cdot>(esem E\<^sub>2 data F (proj (kd E\<^sub>2 F)\<cdot>k)),
     csem = \<lambda>Gs. \<Lambda> Xs. combine_csem f E\<^sub>1 E\<^sub>2 Gs Xs\<rparr>"

lemma combine_simps [simp]:
  "emind (combine f E\<^sub>1 E\<^sub>2) = emind E\<^sub>1 \<squnion> emind E\<^sub>2"
  "eguards (combine f E\<^sub>1 E\<^sub>2) = eguards E\<^sub>1 @ eguards E\<^sub>2" "evalues (combine f E\<^sub>1 E\<^sub>2) = evalues E\<^sub>1 @ evalues E\<^sub>2"
  "esem (combine f E\<^sub>1 E\<^sub>2) data F k = lift2_option_pd f\<cdot>(esem E\<^sub>1 data F (proj (kd E\<^sub>1 F)\<cdot>k))\<cdot>(esem E\<^sub>2 data F (proj (kd E\<^sub>2 F)\<cdot>k))"
  "csem (combine f E\<^sub>1 E\<^sub>2) Gs\<cdot>Xs = combine_csem f E\<^sub>1 E\<^sub>2 Gs Xs"
  by (simp_all add: combine_def cont_combine_csem[unfolded eta_cfun])

lemma cstrict_combine:
  assumes E\<^sub>1: "cstrict E\<^sub>1" and E\<^sub>2: "cstrict E\<^sub>2"
  shows "cstrict (combine f E\<^sub>1 E\<^sub>2)"
proof (rule cstrictI)
  fix Gs :: "('k \<Rightarrow> tr option) list" and Xs :: "('k \<Rightarrow> 'r option) list"
  assume l: "length Gs = length (eguards (combine f E\<^sub>1 E\<^sub>2))" and lx: "length Xs = length (evalues (combine f E\<^sub>1 E\<^sub>2))"
    and fin: "gfinite Gs" and c: "csem (combine f E\<^sub>1 E\<^sub>2) Gs\<cdot>Xs \<noteq> Absent"
  let ?n = "length (eguards E\<^sub>1)" and ?m = "length (evalues E\<^sub>1)"
  have c1: "csem E\<^sub>1 (take ?n Gs)\<cdot>(take ?m Xs) \<noteq> Absent" and c2: "csem E\<^sub>2 (drop ?n Gs)\<cdot>(drop ?m Xs) \<noteq> Absent"
    using c by (auto simp: combine_csem_def)
  have "\<not> gfalse G" if "G \<in> set (take ?n Gs)" for G
    by (rule notI, rule c1[THEN notE], rule cstrictD[OF E\<^sub>1 _ _ gfinite_take[OF fin] that]) (use l lx in simp_all)
  moreover have "\<not> gfalse G" if "G \<in> set (drop ?n Gs)" for G
    by (rule notI, rule c2[THEN notE], rule cstrictD[OF E\<^sub>2 _ _ gfinite_drop[OF fin] that]) (use l lx in simp_all)
  ultimately show "\<forall>G\<in>set Gs. \<not> gfalse G" using set_append[of "take ?n Gs" "drop ?n Gs"] by auto
qed

theorem semilawful_combine:
  assumes E\<^sub>1: "semilawful E\<^sub>1" and E\<^sub>2: "semilawful E\<^sub>2"
  shows "semilawful (combine f E\<^sub>1 E\<^sub>2)"
proof (rule semilawfulI, simp_all only: combine_simps)
  show "cstrict (combine f E\<^sub>1 E\<^sub>2)" by (rule cstrict_combine[OF semilawful_cstrict[OF E\<^sub>1] semilawful_cstrict[OF E\<^sub>2]])
  show "entry_wf e" if "e \<in> set (evalues E\<^sub>1 @ evalues E\<^sub>2)" for e
    using that by (auto intro: semilawful_wf[OF E\<^sub>1] semilawful_wf[OF E\<^sub>2])
  let ?R = "fold (\<squnion>) (map lower_part (map esel (eguards E\<^sub>1 @ eguards E\<^sub>2) @ map esel (evalues E\<^sub>1 @ evalues E\<^sub>2))) \<bottom>"
  have up1: "emind E\<^sub>1 \<sqsubseteq> ?R" unfolding semilawful_mind_lub[OF E\<^sub>1]
  proof (rule fold_join_least)
    fix a assume "a \<in> set (map lower_part (esels E\<^sub>1))"
    then show "a \<sqsubseteq> ?R" by (intro fold_join_upper) force
  qed simp
  have up2: "emind E\<^sub>2 \<sqsubseteq> ?R" unfolding semilawful_mind_lub[OF E\<^sub>2]
  proof (rule fold_join_least)
    fix a assume "a \<in> set (map lower_part (esels E\<^sub>2))"
    then show "a \<sqsubseteq> ?R" by (intro fold_join_upper) force
  qed simp
  have lo: "?R \<sqsubseteq> emind E\<^sub>1 \<squnion> emind E\<^sub>2"
  proof (rule fold_join_least)
    fix a assume "a \<in> set (map lower_part (map esel (eguards E\<^sub>1 @ eguards E\<^sub>2) @ map esel (evalues E\<^sub>1 @ evalues E\<^sub>2)))"
    then have "a \<in> lower_part ` set (esels E\<^sub>1) \<or> a \<in> lower_part ` set (esels E\<^sub>2)" by auto
    then show "a \<sqsubseteq> emind E\<^sub>1 \<squnion> emind E\<^sub>2"
      by (auto intro: below_trans[OF lower_below_mind[OF E\<^sub>1] lattice_join_ge1]
          below_trans[OF lower_below_mind[OF E\<^sub>2] lattice_join_ge2])
  qed simp
  show "emind E\<^sub>1 \<squnion> emind E\<^sub>2 = ?R" by (rule below_antisym[OF lattice_join_least[OF up1 up2] lo])
  show "lift2_option_pd f\<cdot>(esem E\<^sub>1 data F (proj (kd E\<^sub>1 F)\<cdot>k))\<cdot>(esem E\<^sub>2 data F (proj (kd E\<^sub>2 F)\<cdot>k))
      = combine_csem f E\<^sub>1 E\<^sub>2 (gcontents data (eguards E\<^sub>1 @ eguards E\<^sub>2) F k) (contents data (evalues E\<^sub>1 @ evalues E\<^sub>2) F k)"
    if d: "fconf (evalues E\<^sub>1 @ evalues E\<^sub>2) data F" for data F k
  proof -
    have d1: "fconf (evalues E\<^sub>1) data F" and d2: "fconf (evalues E\<^sub>2) data F" using d by (simp_all add: fconf_def)
    show ?thesis unfolding combine_csem_def
      by (simp add: semilawful_csem_conf[OF E\<^sub>1 d1 proj_idem] semilawful_csem_conf[OF E\<^sub>2 d2 proj_idem]
          contents_own_key[OF E\<^sub>1] contents_own_key[OF E\<^sub>2])
  qed
qed

text \<open>A constant, present everywhere, with no entries.\<close>

definition const_expr :: "'v::bifinite \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "const_expr v = \<lparr>emind = \<bottom>, eguards = [], evalues = [], esem = \<lambda>data F k. Present\<cdot>v, csem = \<lambda>Gs. \<Lambda> Xs. Present\<cdot>v\<rparr>"

lemma const_expr_simps [simp]:
  "emind (const_expr v) = \<bottom>" "eguards (const_expr v) = []" "evalues (const_expr v) = []"
  "esem (const_expr v) data F k = Present\<cdot>v" "csem (const_expr v) Gs\<cdot>Xs = Present\<cdot>v"
  by (simp_all add: const_expr_def)

theorem semilawful_const_expr: "semilawful (const_expr v)"
  by (rule semilawfulI) (simp_all add: cstrict_def)

text \<open>Tuples, as lifted lists: combining with cons from the empty one.\<close>

primrec tuple :: "('k, 'f, 'r, 'a::domain) expr list \<Rightarrow> ('k, 'f, 'r, 'a list u) expr" where
  "tuple [] = const_expr (up\<cdot>[])"
| "tuple (E # Es) = combine (\<Lambda> v w. fup\<cdot>(\<Lambda> ys. up\<cdot>(v # ys))\<cdot>w) E (tuple Es)"

lemma set_entries_tuple [simp]:
  "set (eguards (tuple Es)) = (\<Union>E\<in>set Es. set (eguards E))"
  "set (evalues (tuple Es)) = (\<Union>E\<in>set Es. set (evalues E))"
  by (induct Es) auto

lemma semilawful_tuple: "(\<And>E. E \<in> set Es \<Longrightarrow> semilawful E) \<Longrightarrow> semilawful (tuple Es)"
  by (induct Es) (simp_all add: semilawful_const_expr semilawful_combine)

subsection \<open>The presence test is lawful\<close>

lemma present_at_keyimg:
  assumes k: "proj (emind E \<squnion> a \<squnion> flod F)\<cdot>k = k" and p: "esem (present_at a \<top> E) data F k \<noteq> Absent"
  shows "keyimg data F (emind E \<squnion> a \<squnion> flod F) k"
  using p keyimg_populated_top[OF k] by (auto dest: tr_mult_not_Absent)

theorem lawful_present_at:
  assumes ES: "semilawful E"
  shows "lawful (present_at a \<top> E)"
proof (rule lawful_semiI[OF semilawful_present_at[OF ES]])
  fix data F k assume k: "proj (emind (present_at a \<top> E) \<squnion> flod F)\<cdot>k = k"
    and p: "esem (present_at a \<top> E) data F k \<noteq> Absent"
  have k': "proj (emind E \<squnion> a \<squnion> flod F)\<cdot>k = k" using k by simp
  show "keyimg data F (emind (present_at a \<top> E) \<squnion> flod F) k" using present_at_keyimg[OF k' p] by simp
qed

end

end
