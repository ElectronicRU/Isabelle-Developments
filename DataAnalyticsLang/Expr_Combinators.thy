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

lemma those_not_None_iff: "those xs \<noteq> None \<longleftrightarrow> (\<forall>x\<in>set xs. x \<noteq> None)"
  by (induct xs) (auto split: option.splits)

context dataspace
begin

subsection \<open>Keys\<close>

text \<open>The key at an LOD \<open>c\<close>.  Its presence is a true guard on the group of rows with that key
  part, the frame's filters coarsened to \<open>c\<close>; its value entry reads no columns and is keyed at
  \<open>c\<close>, so its content's one key is that key part.  It is present where that group is nonempty, so
  it is gated at its own row LOD, not at the frame's keys.\<close>

lemma join_meet_self: "c \<squnion> (c \<sqinter> L) = c" for c :: "'k semi_factor"
  by (rule lattice_join_absorb1[OF lattice_meet_le1])

lemma cont_key_value: "cont (\<lambda>Xs :: ('k \<Rightarrow> 'r option) list. Some (the_elem (dom (hd Xs))))"
  by (rule cont_rigid, rule rigidI) (simp only: rigidD[OF rigid_comp[OF rigid_dom cont2mono[OF cont_hd]]])

definition key_at :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'k) expr" where
  "key_at c = \<lparr>emind = c, eguards = [mk_guard (sel c c) gtrue \<bottom>], evalues = [mk_value (sel c c) \<bottom> c],
     esem = \<lambda>data F k. if group data c c F k = {} then None else Some (proj c\<cdot>k),
     csem = \<lambda>Gs. \<Lambda> Xs. if hd Gs = {} then None else Some (the_elem (dom (hd Xs)))\<rparr>"

lemma key_at_simps [simp]:
  "emind (key_at c) = c" "eguards (key_at c) = [mk_guard (sel c c) gtrue \<bottom>]"
  "evalues (key_at c) = [mk_value (sel c c) \<bottom> c]"
  "esem (key_at c) data F k = (if group data c c F k = {} then None else Some (proj c\<cdot>k))"
  "csem (key_at c) Gs\<cdot>Xs = (if hd Gs = {} then None else Some (the_elem (dom (hd Xs))))"
  by (simp_all add: key_at_def cont_key_value)

lemma group_own: "y \<in> group data c c F k \<Longrightarrow> rproj c y = proj c\<cdot>k"
  by (simp add: group_def join_meet_self)

lemma fiber_own: "y \<in> fiber data c c F k \<Longrightarrow> rproj c y = proj c\<cdot>k"
  by (simp add: fiber_def join_meet_self)

lemma dom_content_key_at:
  assumes "fiber data c c F k \<noteq> {}"
  shows "dom (content data (mk_value (sel c c) \<bottom> c) F k) = {proj c\<cdot>k}"
proof -
  have "dom (content data (mk_value (sel c c) \<bottom> c) F k) = (\<lambda>_. proj c\<cdot>k) ` fiber data c c F k"
    unfolding content_def dom_gmap cgraph_def image_image cpair_def
    by (rule image_cong) (simp_all add: vfiber_def fiber_own)
  then show ?thesis using assms by (simp add: image_constant_conv)
qed

lemma cstrict_key_at: "cstrict (key_at c)"
  by (rule cstrictI) (auto simp: length_Suc_conv)

theorem semilawful_key_at: "semilawful (key_at c)"
proof (rule semilawfulI, simp_all only: key_at_simps)
  let ?g = "mk_guard (sel c c) gtrue \<bottom> :: ('k, 'r guard) entry" and ?e = "mk_value (sel c c) \<bottom> c"
  show "cstrict (key_at c)" by (rule cstrict_key_at)
  show "entry_wf e" if "e \<in> set [?e]" for e using that by (simp add: entry_wf_view keyed_view_key)
  show "c = fold (\<squnion>) (map lower_part (map esel [?g] @ map esel [?e])) \<bottom>"
    by (simp add: lattice_join_bot_right lattice_join_absorb1[OF below_refl])
  show "(if group data c c F k = {} then None else Some (proj c\<cdot>k))
      = (if hd (gcontents data [?g] F k) = {} then None
         else Some (the_elem (dom (hd (contents data [?e] F k)))))" for data F k
  proof (cases "group data c c F k = {}")
    case False
    then have f: "fiber data c c F k \<noteq> {}" using group_sub_fiber by blast
    show ?thesis using False by (simp only: list.map list.sel gcontent_gtrue_bot dom_content_key_at[OF f]) simp
  qed (simp add: gcontent_gtrue_bot)
qed

subsection \<open>Table columns\<close>

text \<open>A table column reads a section of the row.  An external oracle names the key part that
  determines it in every conforming dataset; then the rows of a key's fiber carry one section,
  and the column's value is the column function of it.  Its value entry is that section, keyed at
  the oracle's key part; its presence is a guard on the same selector.\<close>

lemma cont_column_value:
  "cont (\<lambda>Xs :: ('k \<Rightarrow> 'r option) list. Some (v\<cdot>(the (hd Xs (the_elem (dom (hd Xs)))))))"
proof -
  have "cont (\<lambda>Xs :: ('k \<Rightarrow> 'r option) list. hd Xs (the_elem (dom (hd Xs))))"
    by (rule cont_rigid_arg[OF _ rigid_comp[OF rigid_dom cont2mono[OF cont_hd]]]) (simp add: cont2cont_fun)
  then show ?thesis by (simp add: cont_compose[OF cont_the])
qed

definition column :: "'r semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('r \<rightarrow> 'w::cpo) \<Rightarrow> ('k, 'f, 'r, 'w) expr" where
  "column c a v = \<lparr>emind = a, eguards = [mk_guard (sel a a) gtrue \<bottom>], evalues = [mk_value (sel a a) c a],
     esem = \<lambda>data F k. if group data a a F k = {} then None
       else Some (THE w. w \<in> (\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` group data a a F k),
     csem = \<lambda>Gs. \<Lambda> Xs. if hd Gs = {} then None else Some (v\<cdot>(the (hd Xs (the_elem (dom (hd Xs))))))\<rparr>"

lemma column_simps [simp]:
  "emind (column c a v) = a" "eguards (column c a v) = [mk_guard (sel a a) gtrue \<bottom>]"
  "evalues (column c a v) = [mk_value (sel a a) c a]"
  "esem (column c a v) data F k = (if group data a a F k = {} then None
       else Some (THE w. w \<in> (\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` group data a a F k))"
  "csem (column c a v) Gs\<cdot>Xs = (if hd Gs = {} then None else Some (v\<cdot>(the (hd Xs (the_elem (dom (hd Xs)))))))"
  by (simp_all add: column_def cont_column_value)

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
  by (rule cstrictI) (auto simp: length_Suc_conv)

theorem semilawful_column:
  assumes fd: "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>))"
  shows "semilawful (column c a v)"
proof (rule semilawfulI, simp_all only: column_simps)
  let ?g = "mk_guard (sel a a) gtrue \<bottom> :: ('k, 'r guard) entry" and ?e = "mk_value (sel a a) c a"
  show "cstrict (column c a v)" by (rule cstrict_column)
  show "entry_wf e" if "e \<in> set [?e]" for e
    using that by (simp add: entry_wf_view keyed_view_columns[OF fd])
  show "a = fold (\<squnion>) (map lower_part (map esel [?g] @ map esel [?e])) \<bottom>"
    by (simp add: lattice_join_bot_right lattice_join_absorb1[OF below_refl])
  show "(if group data a a F k = {} then None else Some (THE w. w \<in> (\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` group data a a F k))
      = (if hd (gcontents data [?g] F k) = {} then None
         else Some (v\<cdot>(the (hd (contents data [?e] F k) (the_elem (dom (hd (contents data [?e] F k))))))))"
    if d: "fconf [?e] data F" for data F k
  proof (cases "group data a a F k = {}")
    case False
    then obtain x where xg: "x \<in> group data a a F k" by blast
    have x: "x \<in> fiber data a a F k" using xg group_sub_fiber by blast
    have cf: "entry_conf ?e data F" using d by (simp add: fconf_def)
    have "cgraph data ?e F k = (\<lambda>_. (proj a\<cdot>k, x \<downharpoonright> c)) ` fiber data a a F k"
      unfolding cgraph_def vfiber_def cpair_def
      by (rule image_cong) (simp_all add: fiber_own column_fiber_section[OF cf x])
    then have C: "content data ?e F k = [proj a\<cdot>k \<mapsto> x \<downharpoonright> c]"
      unfolding content_def using x by (auto simp: image_constant_conv)
    have "(\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` group data a a F k = (\<lambda>_. v\<cdot>(x \<downharpoonright> c)) ` group data a a F k"
      by (rule image_cong[OF refl]) (simp add: column_fiber_section[OF cf x] subsetD[OF group_sub_fiber])
    then have V: "(\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` group data a a F k = {v\<cdot>(x \<downharpoonright> c)}"
      using False by (simp add: image_constant_conv)
    have g: "gcontent data ?g F k \<noteq> {}" using False by (simp add: gcontent_gtrue_bot)
    show ?thesis using False g by (simp only: list.map list.sel C V) simp
  next
    case True
    then show ?thesis by (simp add: gcontent_gtrue_bot)
  qed
qed

subsection \<open>Maps\<close>

definition smap :: "('v::cpo \<rightarrow> 'w::cpo) \<Rightarrow> ('k, 'f, 'r, 'v) expr \<Rightarrow> ('k, 'f, 'r, 'w) expr" where
  "smap g E = \<lparr>emind = emind E, eguards = eguards E, evalues = evalues E,
     esem = \<lambda>data F k. map_option (Rep_cfun g) (esem E data F k),
     csem = \<lambda>Gs. \<Lambda> Xs. map_option (Rep_cfun g) (csem E Gs\<cdot>Xs)\<rparr>"

lemma smap_simps [simp]:
  "emind (smap g E) = emind E" "eguards (smap g E) = eguards E" "evalues (smap g E) = evalues E"
  "esem (smap g E) data F k = map_option (Rep_cfun g) (esem E data F k)"
  "csem (smap g E) Gs\<cdot>Xs = map_option (Rep_cfun g) (csem E Gs\<cdot>Xs)"
  by (simp_all add: smap_def)

lemma cstrict_smap: "cstrict E \<Longrightarrow> cstrict (smap g E)"
  unfolding cstrict_def by simp

theorem semilawful_smap: assumes "semilawful E" shows "semilawful (smap g E)"
proof -
  have ES: "semilawful E" by (fact assms)
  show ?thesis
  proof (rule semilawfulI, simp_all only: smap_simps)
    show "cstrict (smap g E)" by (rule cstrict_smap[OF semilawful_cstrict[OF ES]])
    show "entry_wf e" if "e \<in> set (evalues E)" for e by (rule semilawful_wf[OF ES that])
    show "emind E = fold (\<squnion>) (map lower_part (esels E)) \<bottom>" by (rule semilawful_mind_lub[OF ES])
    show "map_option (Rep_cfun g) (esem E data F k) = map_option (Rep_cfun g) (csem_at E data F k)"
      if "fconf (evalues E) data F" "proj (emind E \<squnion> flod F)\<cdot>k = k" for data F k
      by (simp only: semilawful_csem_conf[OF ES that])
  qed
qed

theorem lawful_smap: assumes "lawful E" shows "lawful (smap g E)"
proof -
  have EL: "lawful E" by (fact assms)
  show ?thesis
  proof (rule lawful_semiI[OF semilawful_smap[OF lawful_semilawful[OF assms]]], simp_all only: smap_simps)
    show "(upper_part S \<sqinter> emind E) \<sqsubseteq> lower_part S" if "S \<in> set (esels E)" for S
      by (rule lawful_saturated[OF EL that])
    show "keyimg data F (emind E \<squnion> flod F) k" if d: "fconf (evalues E) data F" and "map_option (Rep_cfun g) (esem E data F k) \<noteq> None" for data F k
      using that(2) by (intro lawful_key_law_conf[OF EL d]) simp
  qed
qed

text \<open>A function of the key at an LOD.\<close>

definition value_at :: "'k semi_factor \<Rightarrow> ('k \<rightarrow> 'v::cpo) \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "value_at c g = smap g (key_at c)"

lemma value_at_simps [simp]:
  "emind (value_at c g) = c" "eguards (value_at c g) = [mk_guard (sel c c) gtrue \<bottom>]"
  "evalues (value_at c g) = [mk_value (sel c c) \<bottom> c]"
  "esem (value_at c g) data F k = (if group data c c F k = {} then None else Some (g\<cdot>(proj c\<cdot>k)))"
  "csem (value_at c g) Gs\<cdot>Xs = (if hd Gs = {} then None else Some (g\<cdot>(the_elem (dom (hd Xs)))))"
  by (simp_all add: value_at_def)

theorem semilawful_value_at: "semilawful (value_at c g)"
  unfolding value_at_def by (rule semilawful_smap[OF semilawful_key_at])

subsection \<open>\<open>RESTRICT\<close>\<close>

text \<open>Restricting conjoins the rows a test passes to the ambient filter.  Only guards see the
  frame's filters: the test is conjoined to each guard, and value entries are left alone.\<close>

definition restrict_entry :: "'r guard \<Rightarrow> ('k, 'r guard) entry \<Rightarrow> ('k, 'r guard) entry" where
  "restrict_entry \<gamma> e = e\<lparr>epay := gand \<gamma> (eguard e)\<rparr>"

lemma restrict_entry_simps [simp]:
  "esel (restrict_entry \<gamma> e) = esel e" "ekeys (restrict_entry \<gamma> e) = ekeys e"
  "eguard (restrict_entry \<gamma> e) = gand \<gamma> (eguard e)"
  by (simp_all add: restrict_entry_def)

definition restrict :: "'r guard \<Rightarrow> ('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "restrict \<gamma> E = \<lparr>emind = emind E, eguards = map (restrict_entry \<gamma>) (eguards E), evalues = evalues E,
     esem = \<lambda>data F. esem E data (frestrict (gsel \<gamma>) F), csem = csem E\<rparr>"

lemma restrict_simps [simp]:
  "emind (restrict \<gamma> E) = emind E"
  "eguards (restrict \<gamma> E) = map (restrict_entry \<gamma>) (eguards E)" "evalues (restrict \<gamma> E) = evalues E"
  "esem (restrict \<gamma> E) data F = esem E data (frestrict (gsel \<gamma>) F)"
  "csem (restrict \<gamma> E) = csem E"
  by (simp_all add: restrict_def)

lemma group_frestrict:
  "group data a \<rho> (frestrict \<phi> F) k = {y \<in> group data a \<rho> F k. selects \<phi> y}"
  by (auto simp: group_def)

lemma fiber_frestrict: "fiber data a \<rho> (frestrict \<phi> F) k = fiber data a \<rho> F k"
  by (simp add: fiber_def)

lemma gcontent_frestrict:
  "gcontent data e (frestrict (gsel \<gamma>) F) k = gcontent data (restrict_entry \<gamma> e) F k"
  unfolding gcontent_def gfiber_def by (auto simp: group_frestrict)

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
  show "esem E data (frestrict (gsel \<gamma>) F) k
      = csem E (gcontents data (map (restrict_entry \<gamma>) (eguards E)) F k)\<cdot>(contents data (evalues E) F k)"
    if d: "fconf (evalues E) data F" and k: "proj (emind E \<squnion> flod F)\<cdot>k = k" for data F k
  proof -
    have d': "fconf (evalues E) data (frestrict (gsel \<gamma>) F)" using d by (simp only: fconf_frestrict)
    have "proj (emind E \<squnion> flod (frestrict (gsel \<gamma>) F))\<cdot>k = k" using k by simp
    then show ?thesis
      by (simp add: semilawful_csem_conf[OF ES d'] gcontent_frestrict content_frestrict comp_def)
  qed
qed

theorem lawful_restrict:
  assumes EL: "lawful E"
  shows "lawful (restrict \<gamma> E)"
proof (rule lawful_semiI[OF semilawful_restrict[OF lawful_semilawful[OF EL]]], simp_all only: restrict_simps)
  show "(upper_part S \<sqinter> emind E) \<sqsubseteq> lower_part S"
    if "S \<in> set (map esel (map (restrict_entry \<gamma>) (eguards E)) @ map esel (evalues E))" for S
    using that lawful_saturated[OF EL] by (auto simp: comp_def)
  show "keyimg data F (emind E \<squnion> flod F) k" if d: "fconf (evalues E) data F"
    and "esem E data (frestrict (gsel \<gamma>) F) k \<noteq> None" for data F k
  proof -
    have d': "fconf (evalues E) data (frestrict (gsel \<gamma>) F)" using d by (simp only: fconf_frestrict)
    have "keyimg data (frestrict (gsel \<gamma>) F) (emind E \<squnion> flod F) k"
      using lawful_key_law_conf[OF EL d' that(2)] by simp
    then show ?thesis by (rule keyimg_mono[rotated]) (simp add: frows_frestrict)
  qed
qed

subsection \<open>\<open>FOR\<close> and \<open>FIXED\<close>\<close>

text \<open>\<open>E FOR \<tau> G\<close>: the inner expression under the frame with LOD and slice truncated to \<open>\<tau>\<close>
  and \<open>G\<close> conjoined, at the truncated key.  Its upper parts meet \<open>\<tau>\<close>; each guard is conjoined
  with \<open>G\<close> coarsened to the guard's upper part.  It is not gated: the result is broadcast over the
  dropped detail.  \<open>FIXED D\<close> is \<open>FOR D\<close> without a filter.\<close>

definition for_entry :: "'k semi_factor \<Rightarrow> 'f \<Rightarrow> ('k, 'r guard) entry \<Rightarrow> ('k, 'r guard) entry" where
  "for_entry \<tau> G e = e\<lparr>esel := trunc_sel \<tau> (esel e), epay := gand (guard_holds (coarsen (eupper e) G)) (eguard e)\<rparr>"

definition for_value :: "'k semi_factor \<Rightarrow> ('k, 'r semi_factor) entry \<Rightarrow> ('k, 'r semi_factor) entry" where
  "for_value \<tau> e = e\<lparr>esel := trunc_sel \<tau> (esel e)\<rparr>"

lemma for_entry_simps [simp]:
  "esel (for_entry \<tau> G e) = trunc_sel \<tau> (esel e)" "ekeys (for_entry \<tau> G e) = ekeys e"
  "eguard (for_entry \<tau> G e) = gand (guard_holds (coarsen (eupper e) G)) (eguard e)"
  by (simp_all add: for_entry_def)

lemma for_value_simps [simp]:
  "esel (for_value \<tau> e) = trunc_sel \<tau> (esel e)" "ekeys (for_value \<tau> e) = ekeys e" "ecols (for_value \<tau> e) = ecols e"
  by (simp_all add: for_value_def)

definition filtfor :: "'k semi_factor \<Rightarrow> 'f \<Rightarrow> ('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "filtfor \<tau> G E = \<lparr>emind = emind E, eguards = map (for_entry \<tau> G) (eguards E),
     evalues = map (for_value \<tau>) (evalues E),
     esem = \<lambda>data F k. esem E data (ffor \<tau> G F) (proj (emind E \<squnion> flod (ffor \<tau> G F))\<cdot>k), csem = csem E\<rparr>"

abbreviation fixed :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "fixed D \<equiv> filtfor D \<^bold>1"

lemma filtfor_simps [simp]:
  "emind (filtfor \<tau> G E) = emind E"
  "eguards (filtfor \<tau> G E) = map (for_entry \<tau> G) (eguards E)"
  "evalues (filtfor \<tau> G E) = map (for_value \<tau>) (evalues E)"
  "esem (filtfor \<tau> G E) data F k = esem E data (ffor \<tau> G F) (proj (emind E \<squnion> flod (ffor \<tau> G F))\<cdot>k)"
  "csem (filtfor \<tau> G E) = csem E"
  by (simp_all add: filtfor_def)

text \<open>Inside the truncated frame, at the truncated key, a fiber is the outer fiber through the
  composite mask, and a group is moreover cut down by the filter coarsened to the inner upper part.\<close>

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

lemma group_ffor:
  assumes am: "a \<sqsubseteq> m"
  shows "group data a \<rho> (ffor \<tau> G F) (proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k)
       = {y \<in> group data a (\<rho> \<sqinter> \<tau>) F k. holds (coarsen \<rho> G) (rkey\<cdot>y)}"
proof -
  have sl: "holds (coarsen \<rho> (slice (ffor \<tau> G F))) k' \<longleftrightarrow>
      holds (coarsen (\<rho> \<sqinter> \<tau>) (slice F)) k' \<and> holds (coarsen \<rho> G) k'" for k'
    by (simp add: coarsen_conj coarsen_coarsen)
  show ?thesis unfolding group_def ffor_key[OF am] sl by auto
qed

lemma gcontent_ffor:
  assumes "elower e \<sqsubseteq> m"
  shows "gcontent data e (ffor \<tau> G F) (proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k) = gcontent data (for_entry \<tau> G e) F k"
  unfolding gcontent_def gfiber_def group_ffor[OF assms] by auto

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
  have "group data (sel_at (esel e) M) (eupper e) F k = group data (elower e) (eupper e) (finclude M F) k"
    by (rule group_cong) (simp_all only: amb_finclude slice_finclude include_lod[unfolded include_sel_simps])
  then show ?thesis unfolding gcontent_def gfiber_def by simp
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

subsection \<open>The gate\<close>

text \<open>The gate at \<open>M\<close> turns a semilawful expression into a lawful one: it evaluates under the
  frame including the minimal LOD and \<open>M\<close>, which saturates the entries (their lower parts take in
  the masked minimal LOD and \<open>M\<close>), and it is present exactly at the frame's data keys at that LOD,
  which a presence guard at the full key records.  \<open>gate \<bottom>\<close> is the plain gate; a larger \<open>M\<close>
  refines the expression's groups by further dimensions (requested ones, inside an aggregation).\<close>

definition gate_presence :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "gate_presence M E = \<lparr>emind = emind E \<squnion> M,
     eguards = mk_guard (sel (emind E \<squnion> M) \<top>) gtrue \<bottom> # map (include_entry (emind E \<squnion> M)) (eguards E),
     evalues = map (include_entry (emind E \<squnion> M)) (evalues E),
     esem = \<lambda>data F k. if keyimg data F (emind E \<squnion> M \<squnion> flod F) k
       then esem E data (finclude (emind E \<squnion> M) F) k else None,
     csem = \<lambda>Gs. \<Lambda> Xs. if hd Gs = {} then None else csem E (tl Gs)\<cdot>Xs\<rparr>"

lemma gate_presence_simps [simp]:
  "emind (gate_presence M E) = emind E \<squnion> M"
  "eguards (gate_presence M E) = mk_guard (sel (emind E \<squnion> M) \<top>) gtrue \<bottom> # map (include_entry (emind E \<squnion> M)) (eguards E)"
  "evalues (gate_presence M E) = map (include_entry (emind E \<squnion> M)) (evalues E)"
  "esem (gate_presence M E) data F k = (if keyimg data F (emind E \<squnion> M \<squnion> flod F) k
       then esem E data (finclude (emind E \<squnion> M) F) k else None)"
  "csem (gate_presence M E) Gs\<cdot>Xs = (if hd Gs = {} then None else csem E (tl Gs)\<cdot>Xs)"
  by (simp_all add: gate_presence_def)

lemma cstrict_gate_presence:
  assumes E: "cstrict E"
  shows "cstrict (gate_presence M E)"
proof (rule cstrictI)
  fix Gs :: "'k set list" and Xs :: "('k \<Rightarrow> 'r option) list"
  assume l: "length Gs = length (eguards (gate_presence M E))" and lx: "length Xs = length (evalues (gate_presence M E))"
    and c: "csem (gate_presence M E) Gs\<cdot>Xs \<noteq> None"
  then obtain G Gs' where Gs: "Gs = G # Gs'" and l': "length Gs' = length (eguards E)"
    by (auto simp: length_Suc_conv)
  have lx': "length Xs = length (evalues E)" using lx by simp
  have "G \<noteq> {}" and "csem E Gs'\<cdot>Xs \<noteq> None" using c by (simp_all add: Gs split: if_splits)
  then show "{} \<notin> set Gs" using cstrictD[OF E l' lx'] by (auto simp: Gs)
qed

text \<open>The presence guard at the full key is the key's realisation.\<close>

lemma gcontent_const_top:
  assumes "proj (c \<squnion> flod F)\<cdot>k = k"
  shows "gcontent data (mk_guard (sel c \<top>) gtrue \<bottom>) F k = (if keyimg data F (c \<squnion> flod F) k then {\<bottom>} else {})"
  by (simp add: gcontent_gtrue_bot keyimg_group_top[OF assms])

lemma kd_finclude_mind: "emind E \<squnion> flod (finclude (emind E \<squnion> M) F) = (emind E \<squnion> M) \<squnion> flod F"
proof -
  have "emind E \<sqsubseteq> flod F \<squnion> (emind E \<squnion> M)" by (rule below_trans[OF lattice_join_ge1 lattice_join_ge2])
  then show ?thesis unfolding flod_finclude by (simp only: lattice_join_absorb2 lattice_join_commute)
qed

lemma include_mind:
  assumes ES: "semilawful E"
  shows "fold (\<squnion>) (map lower_part (map esel (map (include_entry (emind E \<squnion> M)) (eguards E))
      @ map esel (map (include_entry (emind E \<squnion> M)) (evalues E)))) (emind E \<squnion> M) = emind E \<squnion> M"
proof (rule fold_join_absorb)
  let ?m = "emind E \<squnion> M"
  fix x assume "x \<in> set (map lower_part (map esel (map (include_entry ?m) (eguards E)) @ map esel (map (include_entry ?m) (evalues E))))"
  then obtain S where S: "S \<in> set (esels E)" and x: "x = lower_part (include_sel ?m S)" by auto
  show "x \<sqsubseteq> ?m" unfolding x by (rule include_lower_below[OF below_trans[OF lower_below_mind[OF ES S] lattice_join_ge1]])
qed

theorem lawful_gate_presence: assumes "semilawful E" shows "lawful (gate_presence M E)"
proof -
  have ES: "semilawful E" by (fact assms)
  let ?m = "emind E \<squnion> M"
  let ?h = "mk_guard (sel ?m \<top>) gtrue \<bottom> :: ('k, 'r guard) entry"
  show ?thesis
  proof (rule lawfulI, simp_all only: gate_presence_simps)
    show "cstrict (gate_presence M E)" by (rule cstrict_gate_presence[OF semilawful_cstrict[OF ES]])
    show "entry_wf e" if "e \<in> set (map (include_entry ?m) (evalues E))" for e
      using that by (auto intro: entry_wf_include_entry semilawful_wf[OF ES])
    show "(upper_part S \<sqinter> ?m) \<sqsubseteq> lower_part S"
      if "S \<in> set (map esel (?h # map (include_entry ?m) (eguards E)) @ map esel (map (include_entry ?m) (evalues E)))" for S
      using that by (auto simp: truncate_top intro: include_saturates[of ?m])
    show "?m = fold (\<squnion>) (map lower_part (map esel (?h # map (include_entry ?m) (eguards E))
        @ map esel (map (include_entry ?m) (evalues E)))) \<bottom>"
      using include_mind[OF ES, of M] by (simp add: lattice_join_bot_right)
    show "keyimg data F (?m \<squnion> flod F) k"
      if "fconf (map (include_entry ?m) (evalues E)) data F" and "(if keyimg data F (?m \<squnion> flod F) k then esem E data (finclude ?m F) k else None) \<noteq> None"
      for data F k
      using that by (simp split: if_splits)
    show "(if keyimg data F (?m \<squnion> flod F) k then esem E data (finclude ?m F) k else None)
        = (if hd (gcontents data (?h # map (include_entry ?m) (eguards E)) F k) = {} then None
           else csem E (tl (gcontents data (?h # map (include_entry ?m) (eguards E)) F k))\<cdot>(contents data (map (include_entry ?m) (evalues E)) F k))"
      if d: "fconf (map (include_entry ?m) (evalues E)) data F" and k: "proj (?m \<squnion> flod F)\<cdot>k = k" for data F k
    proof -
      have d': "fconf (evalues E) data (finclude ?m F)" using d by (simp only: fconf_include)
      have h: "hd (gcontents data (?h # map (include_entry ?m) (eguards E)) F k) = {}
          \<longleftrightarrow> \<not> keyimg data F (?m \<squnion> flod F) k"
        by (simp only: list.map list.sel gcontent_const_top[OF k]) simp
      have t: "tl (gcontents data (?h # map (include_entry ?m) (eguards E)) F k)
          = gcontents data (eguards E) (finclude ?m F) k"
        by (simp add: comp_def gcontent_include_entry)
      have v: "contents data (map (include_entry ?m) (evalues E)) F k = contents data (evalues E) (finclude ?m F) k"
        by (simp add: comp_def content_include_entry)
      have "proj (emind E \<squnion> flod (finclude ?m F))\<cdot>k = k" by (simp only: kd_finclude_mind k)
      then show ?thesis by (simp only: h t v semilawful_csem_conf[OF ES d']) simp
    qed
  qed
qed

text \<open>An expression \<^emph>\<open>covers\<close> the key space when one of its guards has upper part \<open>\<top>\<close>: raised
  by the minimal LOD, that guard's group is all rows at the key, so by strictness its expression is
  absent wherever the key is not realised, whatever the guard.  Then the gate needs no presence
  guard: it only raises the entries.\<close>

definition covering :: "('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> bool" where
  "covering E \<longleftrightarrow> (\<exists>e\<in>set (eguards E). eupper e = \<top>)"

lemma gcontent_include_top:
  assumes e: "eupper e = \<top>" and am: "elower e \<sqsubseteq> m" and k: "proj (m \<squnion> flod F)\<cdot>k = k"
    and nk: "\<not> keyimg data F (m \<squnion> flod F) k"
  shows "gcontent data (include_entry m e) F k = {}"
proof -
  have lo: "elower (include_entry m e) = m" using am by (simp add: e truncate_top lattice_join_absorb2)
  have g: "group data m \<top> F k = {}" using keyimg_group_top[OF k] nk by simp
  have "group data (elower (include_entry m e)) (eupper (include_entry m e)) F k = {}"
    by (simp only: lo) (simp add: e g)
  then show ?thesis by (simp add: gcontent_def gfiber_def)
qed

definition gate_raise :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "gate_raise M E = \<lparr>emind = emind E \<squnion> M,
     eguards = map (include_entry (emind E \<squnion> M)) (eguards E),
     evalues = map (include_entry (emind E \<squnion> M)) (evalues E),
     esem = \<lambda>data F k. if keyimg data F (emind E \<squnion> M \<squnion> flod F) k
       then esem E data (finclude (emind E \<squnion> M) F) k else None,
     csem = csem E\<rparr>"

lemma gate_raise_simps [simp]:
  "emind (gate_raise M E) = emind E \<squnion> M"
  "eguards (gate_raise M E) = map (include_entry (emind E \<squnion> M)) (eguards E)"
  "evalues (gate_raise M E) = map (include_entry (emind E \<squnion> M)) (evalues E)"
  "esem (gate_raise M E) data F k = (if keyimg data F (emind E \<squnion> M \<squnion> flod F) k
       then esem E data (finclude (emind E \<squnion> M) F) k else None)"
  "csem (gate_raise M E) = csem E"
  by (simp_all add: gate_raise_def)

theorem lawful_gate_raise:
  assumes ES: "semilawful E" and cov: "covering E"
  shows "lawful (gate_raise M E)"
proof -
  let ?m = "emind E \<squnion> M"
  obtain t where t: "t \<in> set (eguards E)" "eupper t = \<top>" using cov by (auto simp: covering_def)
  have tm: "elower t \<sqsubseteq> ?m" by (rule below_trans[OF lower_below_mind_guard[OF ES t(1)] lattice_join_ge1])
  show ?thesis
  proof (rule lawfulI, simp_all only: gate_raise_simps)
    show "cstrict (gate_raise M E)"
      using semilawful_cstrict[OF ES] by (simp add: cstrict_def)
    show "entry_wf e" if "e \<in> set (map (include_entry ?m) (evalues E))" for e
      using that by (auto intro: entry_wf_include_entry semilawful_wf[OF ES])
    show "(upper_part S \<sqinter> ?m) \<sqsubseteq> lower_part S"
      if "S \<in> set (map esel (map (include_entry ?m) (eguards E)) @ map esel (map (include_entry ?m) (evalues E)))" for S
      using that by (auto intro: include_saturates[of ?m])
    show "?m = fold (\<squnion>) (map lower_part (map esel (map (include_entry ?m) (eguards E))
        @ map esel (map (include_entry ?m) (evalues E)))) \<bottom>"
    proof (rule below_antisym)
      let ?L = "map lower_part (map esel (map (include_entry ?m) (eguards E)) @ map esel (map (include_entry ?m) (evalues E)))"
      have lo: "elower (include_entry ?m t) = ?m" using tm by (simp add: t(2) truncate_top lattice_join_absorb2)
      have "elower (include_entry ?m t) \<in> set ?L" using t(1) by auto
      then show "?m \<sqsubseteq> fold (\<squnion>) ?L \<bottom>" unfolding lo by (rule fold_join_upper)
      show "fold (\<squnion>) ?L \<bottom> \<sqsubseteq> ?m"
      proof (rule fold_join_least)
        fix x assume "x \<in> set ?L"
        then obtain S where S: "S \<in> set (esels E)" and x: "x = lower_part (include_sel ?m S)" by auto
        show "x \<sqsubseteq> ?m" unfolding x by (rule include_lower_below[OF below_trans[OF lower_below_mind[OF ES S] lattice_join_ge1]])
      qed simp
    qed
    show "keyimg data F (?m \<squnion> flod F) k"
      if "fconf (map (include_entry ?m) (evalues E)) data F" and "(if keyimg data F (?m \<squnion> flod F) k then esem E data (finclude ?m F) k else None) \<noteq> None"
      for data F k
      using that by (simp split: if_splits)
    show "(if keyimg data F (?m \<squnion> flod F) k then esem E data (finclude ?m F) k else None)
        = csem E (gcontents data (map (include_entry ?m) (eguards E)) F k)\<cdot>(contents data (map (include_entry ?m) (evalues E)) F k)"
      if d: "fconf (map (include_entry ?m) (evalues E)) data F" and k: "proj (?m \<squnion> flod F)\<cdot>k = k" for data F k
    proof -
      have d': "fconf (evalues E) data (finclude ?m F)" using d by (simp only: fconf_include)
      have g: "gcontents data (map (include_entry ?m) (eguards E)) F k = gcontents data (eguards E) (finclude ?m F) k"
        by (simp add: comp_def gcontent_include_entry)
      have c: "contents data (map (include_entry ?m) (evalues E)) F k = contents data (evalues E) (finclude ?m F) k"
        by (simp add: comp_def content_include_entry)
      have "proj (emind E \<squnion> flod (finclude ?m F))\<cdot>k = k" by (simp only: kd_finclude_mind k)
      then have v: "esem E data (finclude ?m F) k
          = csem E (gcontents data (map (include_entry ?m) (eguards E)) F k)\<cdot>(contents data (map (include_entry ?m) (evalues E)) F k)"
        by (simp only: g c semilawful_csem_conf[OF ES d'])
      show ?thesis
      proof (cases "keyimg data F (?m \<squnion> flod F) k")
        case False
        have "{} \<in> set (gcontents data (map (include_entry ?m) (eguards E)) F k)"
          using gcontent_include_top[OF t(2) tm k False] t(1) by force
        then have "csem E (gcontents data (map (include_entry ?m) (eguards E)) F k)\<cdot>(contents data (map (include_entry ?m) (evalues E)) F k) = None"
          by (rule cstrictD[OF semilawful_cstrict[OF ES], rotated 2]) simp_all
        then show ?thesis using False by simp
      qed (simp add: v)
    qed
  qed
qed

text \<open>The gate at \<open>M\<close>: raising alone for covering expressions, else with a presence guard.\<close>

definition gate :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "gate M E = (if covering E then gate_raise M E else gate_presence M E)"

lemma gate_simps [simp]:
  "emind (gate M E) = emind E \<squnion> M"
  "evalues (gate M E) = map (include_entry (emind E \<squnion> M)) (evalues E)"
  "esem (gate M E) data F k = (if keyimg data F (emind E \<squnion> M \<squnion> flod F) k
       then esem E data (finclude (emind E \<squnion> M) F) k else None)"
  by (simp_all add: gate_def)

theorem lawful_gate: "semilawful E \<Longrightarrow> lawful (gate M E)"
  unfolding gate_def by (simp add: lawful_gate_raise lawful_gate_presence)

text \<open>Gating is idempotent: a gated expression covers, so gating it again only raises its entries,
  which are raised already.  A lawful covering expression is left alone by the plain gate: its
  entries are saturated, so raising does not change them, and the presence test and the frame
  refinement are already implied by the key law.\<close>

lemma include_entry_saturated: "eupper e \<sqinter> m \<sqsubseteq> elower e \<Longrightarrow> include_entry m e = e"
  by (simp add: include_entry_def include_sel_def lattice_join_absorb1)

lemma include_entry_idem: "include_entry m (include_entry m e) = include_entry m e"
  by (rule include_entry_saturated) (simp add: lattice_join_ge2)

lemma covering_gate: "covering (gate M E)"
proof (cases "covering E")
  case True
  then obtain t where "t \<in> set (eguards E)" "eupper t = \<top>" by (auto simp: covering_def)
  then show ?thesis using True by (force simp: gate_def covering_def)
qed (simp add: gate_def covering_def)

lemma finclude_finclude_same: "finclude (m :: 'k semi_factor) (finclude m F) = finclude m F"
proof -
  have "flod F \<squnion> m \<squnion> m = flod F \<squnion> m" by (rule lattice_join_absorb1[OF lattice_join_ge2])
  then show ?thesis by (simp add: finclude_def)
qed

lemma keyimg_finclude: "keyimg data (finclude m F) c k = keyimg data F c k"
  by (simp add: keyimg_def frows_def)

theorem gate_idem: "gate M (gate M E) = gate M E"
proof -
  let ?m = "emind E \<squnion> M"
  have mM: "?m \<squnion> M = ?m" by (rule lattice_join_absorb1[OF lattice_join_ge2])
  have kd: "?m \<squnion> flod (finclude ?m F) = ?m \<squnion> flod F" for F
  proof -
    have "?m \<squnion> (flod F \<squnion> ?m) = (?m \<squnion> flod F) \<squnion> ?m" by (metis lattice_join_assoc)
    also have "\<dots> = ?m \<squnion> flod F" by (rule lattice_join_absorb1[OF lattice_join_ge1])
    finally show ?thesis by (simp only: flod_finclude)
  qed
  have head: "include_entry ?m (mk_guard (sel ?m \<top>) gtrue \<bottom>) = mk_guard (sel ?m \<top>) gtrue \<bottom>"
    by (rule include_entry_saturated) (simp add: truncate_top)
  have es: "esem (gate_raise M (gate M E)) = esem (gate M E)"
    by (simp add: fun_eq_iff mM kd keyimg_finclude finclude_finclude_same)
  show ?thesis
  proof (cases "covering E")
    case True
    show ?thesis unfolding gate_def[of M "gate M E"] using covering_gate[of M E] es True
      by (simp add: gate_def mM include_entry_idem comp_def)
  next
    case False
    show ?thesis unfolding gate_def[of M "gate M E"] using covering_gate[of M E] es False
      by (simp add: gate_def mM include_entry_idem comp_def head)
  qed
qed

text \<open>The plain gate leaves a lawful covering expression alone: its entries are saturated, so
  raising does not change them, the frame refinement does not change its contents, and off the
  realised keys it is absent already by the key law.\<close>

theorem gate_lawful_covering:
  assumes EL: "lawful E" and cov: "covering E"
  shows "eguards (gate \<bottom> E) = eguards E" and "evalues (gate \<bottom> E) = evalues E" and "csem (gate \<bottom> E) = csem E"
    and "conforms data \<Longrightarrow> esem (gate \<bottom> E) data F k = esem E data F k"
proof -
  let ?m = "emind E"
  have g: "gate \<bottom> E = gate_raise \<bottom> E" using cov by (simp add: gate_def)
  have "map (include_entry ?m) (eguards E) = eguards E"
    by (rule map_idI) (rule include_entry_saturated[OF lawful_saturated[OF EL esels_guardI]])
  then show "eguards (gate \<bottom> E) = eguards E" by (simp add: g)
  have "map (include_entry ?m) (evalues E) = evalues E"
    by (rule map_idI) (rule include_entry_saturated[OF lawful_saturated[OF EL esels_valueI]])
  then show "evalues (gate \<bottom> E) = evalues E" by (simp add: g)
  show "csem (gate \<bottom> E) = csem E" by (simp add: g)
  assume d: "conforms data"
  have ES: "semilawful E" by (rule lawful_semilawful[OF EL])
  show "esem (gate \<bottom> E) data F k = esem E data F k"
  proof (cases "keyimg data F (?m \<squnion> flod F) k")
    case True
    then obtain x where kx: "k = rproj (kd E F) x" by (auto simp: keyimg_def)
    have kd: "kd E (finclude ?m F) = kd E F"
    proof -
      have "?m \<squnion> (flod F \<squnion> ?m) = (?m \<squnion> flod F) \<squnion> ?m" by (metis lattice_join_assoc)
      also have "\<dots> = ?m \<squnion> flod F" by (rule lattice_join_absorb1[OF lattice_join_ge1])
      finally show ?thesis by (simp only: flod_finclude)
    qed
    have k: "proj (kd E F)\<cdot>k = k" by (simp add: kx)
    have "esem E data (finclude ?m F) k = esem E data F k"
      using contents_kd[OF EL amb_finclude slice_finclude kd]
      by (simp only: semilawful_csem[OF ES d k] semilawful_csem[OF ES d k[folded kd]])
    then show ?thesis using True by (simp add: g)
  next
    case False
    have "esem E data F k = None" using lawful_key_law[OF EL d] False by blast
    then show ?thesis using False by (simp add: g)
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

definition total :: "('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> bool" where
  "total E \<longleftrightarrow> (\<forall>data F k. conforms data \<longrightarrow> keyimg data F (kd E F) k \<longrightarrow> esem E data F k \<noteq> None)"

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
  have "esem E data F k = None" using lawful_key_law[OF EL d(1)] nk by blast
  moreover have "esem E data' F k \<noteq> None" using T d(2) rk by (simp add: total_def)
  ultimately show False using c by (simp add: semilawful_csem[OF ES d(1) k] semilawful_csem[OF ES d(2) k])
qed

text \<open>The entry-level half of the construction: a row entry's content at a key is the point
  content of any row of its fiber, so two datasets whose fibers are both non-empty and carry the
  same section at the view's key give the same content; likewise for row guard entries.\<close>

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
  shows "gcontent data e F k = gcontent data' e F k"
proof -
  have one: "gcontent D e F k = {rproj (ekeys e) y}" if dD: "conforms D" and y: "y \<in> gfiber D e F k" for D y
  proof -
    let ?Y = "group D (elower e) (eupper e) F k"
    have yY: "y \<in> ?Y" and gy: "eguard e\<cdot>y = TT" using y by (simp_all add: gfiber_def)
    have "(\<lambda>z. rproj (ekeys e) z) ` {z \<in> ?Y. eguard e\<cdot>z = TT} = (if eguard e\<cdot>y = TT then {rproj (ekeys e) y} else {})"
      by (rule row_guard_entry_image[OF r dD _ yY lattice_join_ge1[of "elower e" "eupper e \<sqinter> flod F"]])
        (use yY in \<open>auto simp: group_def\<close>)
    then show ?thesis using gy by (simp add: gcontent_def gfiber_def)
  qed
  show ?thesis unfolding one[OF d(1) x] one[OF d(2) x'] s ..
qed

subsection \<open>Collect\<close>

text \<open>The components are evaluated under the frame itself, each at its own key; their entries are
  the collected expression's entries, unchanged.  Collecting is semilawful: it is not gated, and a
  component sees nothing of the others' minimal LODs.  The gate widens it back to the full key.\<close>

text \<open>Cutting a list into consecutive blocks of given lengths.\<close>

fun blocks :: "nat list \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "blocks [] xs = []"
| "blocks (n # ns) xs = take n xs # blocks ns (drop n xs)"

lemma cont_blocks: "cont (blocks ns :: 'a::cpo list \<Rightarrow> 'a list list)"
proof (induct ns)
  case (Cons n ns)
  show ?case by (simp add: cont_compose[OF Cons cont_drop] cont_take)
qed simp

lemma blocks_concat: "blocks (map (\<lambda>x. length (f x)) xs) (concat (map f xs)) = map f xs"
  by (induct xs) simp_all

text \<open>The components' content semantics, each at its blocks of guard and value contents.\<close>

definition collect_csem :: "('k, 'f, 'r, 'a::cpo) expr list \<Rightarrow> 'k set list \<Rightarrow> ('k \<Rightarrow> 'r option) list \<Rightarrow> 'a list option" where
  "collect_csem Es Gs Xs = those (map2 (\<lambda>p Ys. csem (fst p) (snd p)\<cdot>Ys)
     (zip Es (blocks (map (\<lambda>E. length (eguards E)) Es) Gs)) (blocks (map (\<lambda>E. length (evalues E)) Es) Xs))"

lemma cont_collect_csem: "cont (collect_csem Es Gs)"
proof -
  have "cont (\<lambda>Xs. map2 (\<lambda>p Ys. csem (fst p) (snd p)\<cdot>Ys)
      (zip Es (blocks (map (\<lambda>E. length (eguards E)) Es) Gs)) (blocks (map (\<lambda>E. length (evalues E)) Es) Xs))"
    by (rule cont_compose[OF cont_map2 cont_blocks]) simp
  then show ?thesis unfolding collect_csem_def[abs_def] by (rule cont_compose[OF cont_those])
qed

definition collect :: "('k, 'f, 'r, 'a::cpo) expr list \<Rightarrow> ('k, 'f, 'r, 'a list) expr" where
  "collect Es = \<lparr>emind = fold (\<squnion>) (map emind Es) \<bottom>,
     eguards = concat (map eguards Es), evalues = concat (map evalues Es),
     esem = \<lambda>data F k. those (map (\<lambda>E. esem E data F (proj (kd E F)\<cdot>k)) Es),
     csem = \<lambda>Gs. \<Lambda> Xs. collect_csem Es Gs Xs\<rparr>"

lemma collect_simps [simp]:
  "emind (collect Es) = fold (\<squnion>) (map emind Es) \<bottom>"
  "eguards (collect Es) = concat (map eguards Es)" "evalues (collect Es) = concat (map evalues Es)"
  "esem (collect Es) data F k = those (map (\<lambda>E. esem E data F (proj (kd E F)\<cdot>k)) Es)"
  "csem (collect Es) Gs\<cdot>Xs = collect_csem Es Gs Xs"
  by (simp_all add: collect_def cont_collect_csem[unfolded eta_cfun])

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
      using at[OF esels_guardI[OF e]] by (intro gcontent_group_cong) (simp add: group_def)
  qed
  show "contents data (evalues E) F (proj (kd E F)\<cdot>k) = contents data (evalues E) F k"
  proof (rule map_cong[OF refl])
    fix e assume e: "e \<in> set (evalues E)"
    show "content data e F (proj (kd E F)\<cdot>k) = content data e F k"
      using at[OF esels_valueI[OF e]] by (intro content_fiber_cong) (simp add: fiber_def)
  qed
qed

lemma collect_blocks_strict:
  assumes "\<And>E. E \<in> set Es \<Longrightarrow> cstrict E"
    and "length Gs = sum_list (map (\<lambda>E. length (eguards E)) Es)"
    and "length Xs = sum_list (map (\<lambda>E. length (evalues E)) Es)"
    and "collect_csem Es Gs Xs \<noteq> None"
  shows "{} \<notin> set Gs"
  using assms
proof (induct Es arbitrary: Gs Xs)
  case (Cons E Es)
  let ?n = "length (eguards E)" and ?l = "length (evalues E)"
  have t: "csem E (take ?n Gs)\<cdot>(take ?l Xs) \<noteq> None" and r: "collect_csem Es (drop ?n Gs) (drop ?l Xs) \<noteq> None"
    using Cons.prems(4) by (auto simp: collect_csem_def split: option.splits)
  have "{} \<notin> set (take ?n Gs)"
    using cstrictD[OF Cons.prems(1)[of E] _ _] t Cons.prems(2,3) by force
  moreover have "{} \<notin> set (drop ?n Gs)"
    by (rule Cons.hyps) (use Cons.prems(1,2,3) r in auto)
  ultimately show ?case using set_append[of "take ?n Gs" "drop ?n Gs"] by auto
qed simp

lemma cstrict_collect: "(\<And>E. E \<in> set Es \<Longrightarrow> cstrict E) \<Longrightarrow> cstrict (collect Es)"
  by (rule cstrictI) (auto intro: collect_blocks_strict[THEN notE] simp: length_concat comp_def)

lemma map2_zip_map: "map2 h (zip xs (map g xs)) (map v xs) = map (\<lambda>x. h (x, g x) (v x)) xs"
  by (induct xs) simp_all

theorem semilawful_collect:
  assumes law: "\<And>E. E \<in> set Es \<Longrightarrow> semilawful E"
  shows "semilawful (collect Es)"
proof (rule semilawfulI, simp_all only: collect_simps)
  show "cstrict (collect Es)" by (rule cstrict_collect[OF semilawful_cstrict[OF law]])
  show "entry_wf e" if "e \<in> set (concat (map evalues Es))" for e
    using that by (auto intro: semilawful_wf[OF law])
  let ?R = "fold (\<squnion>) (map lower_part (map esel (concat (map eguards Es)) @ map esel (concat (map evalues Es)))) \<bottom>"
  show "fold (\<squnion>) (map emind Es) \<bottom> = ?R"
  proof (rule below_antisym)
    show "fold (\<squnion>) (map emind Es) \<bottom> \<sqsubseteq> ?R"
    proof (rule fold_join_least)
      fix x assume "x \<in> set (map emind Es)"
      then obtain E where E: "E \<in> set Es" and x: "x = emind E" by auto
      show "x \<sqsubseteq> ?R" unfolding x semilawful_mind_lub[OF law[OF E]]
      proof (rule fold_join_least)
        fix a assume "a \<in> set (map lower_part (esels E))"
        then show "a \<sqsubseteq> ?R" by (intro fold_join_upper) (use E in force)
      qed simp
    qed simp
    show "?R \<sqsubseteq> fold (\<squnion>) (map emind Es) \<bottom>"
    proof (rule fold_join_least)
      fix a assume "a \<in> set (map lower_part (map esel (concat (map eguards Es)) @ map esel (concat (map evalues Es))))"
      then obtain E S where E: "E \<in> set Es" and S: "S \<in> set (esels E)" and a: "a = lower_part S" by auto
      show "a \<sqsubseteq> fold (\<squnion>) (map emind Es) \<bottom>"
        unfolding a by (rule below_trans[OF lower_below_mind[OF law[OF E] S] fold_join_upper]) (simp add: E)
    qed simp
  qed
  show "those (map (\<lambda>E. esem E data F (proj (kd E F)\<cdot>k)) Es)
      = collect_csem Es (gcontents data (concat (map eguards Es)) F k) (contents data (concat (map evalues Es)) F k)"
    if d: "fconf (concat (map evalues Es)) data F" for data F k
  proof -
    have bg: "blocks (map (\<lambda>E. length (eguards E)) Es) (gcontents data (concat (map eguards Es)) F k)
        = map (\<lambda>E. gcontents data (eguards E) F k) Es"
      using blocks_concat[of "\<lambda>E. gcontents data (eguards E) F k" Es] by (simp add: map_concat comp_def)
    have bv: "blocks (map (\<lambda>E. length (evalues E)) Es) (contents data (concat (map evalues Es)) F k)
        = map (\<lambda>E. contents data (evalues E) F k) Es"
      using blocks_concat[of "\<lambda>E. contents data (evalues E) F k" Es] by (simp add: map_concat comp_def)
    have "esem E data F (proj (kd E F)\<cdot>k) = csem_at E data F k" if E: "E \<in> set Es" for E
    proof -
      have dE: "fconf (evalues E) data F" using d E by (auto simp: fconf_def)
      show ?thesis
        by (simp only: semilawful_csem_conf[OF law[OF E] dE proj_idem] contents_own_key[OF law[OF E]])
    qed
    then show ?thesis unfolding collect_csem_def bg bv map2_zip_map fst_conv snd_conv by (simp cong: map_cong)
  qed
qed

subsection \<open>Joint presence\<close>

text \<open>Leaves, maps, \<open>RESTRICT\<close> and \<open>FOR\<close> keep joint presence; lawful expressions have it.
  Collecting does not: each component is present on its own rows.\<close>

lemma jointly_lawful_key_at: "jointly_lawful (key_at c)"
proof (rule jointly_lawfulI[OF semilawful_key_at])
  fix data F k assume "esem (key_at c) data F k \<noteq> None"
  then obtain y where "y \<in> group data c c F k" by (auto split: if_splits)
  then show "jointly_present data (key_at c) F k" by (auto simp: jointly_present_def)
qed

lemma jointly_lawful_column:
  assumes fd: "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>))"
  shows "jointly_lawful (column c a v)"
proof (rule jointly_lawfulI[OF semilawful_column[OF fd]])
  fix data F k assume "esem (column c a v) data F k \<noteq> None"
  then obtain y where "y \<in> group data a a F k" by (auto split: if_splits)
  then show "jointly_present data (column c a v) F k" by (auto simp: jointly_present_def)
qed

lemma jointly_lawful_smap:
  assumes E: "jointly_lawful E"
  shows "jointly_lawful (smap g E)"
proof (rule jointly_lawfulI[OF semilawful_smap[OF jointly_lawful_semilawful[OF E]]])
  fix data F k assume "fconf (evalues (smap g E)) data F" and "proj (kd (smap g E) F)\<cdot>k = k"
    and "esem (smap g E) data F k \<noteq> None"
  then have "jointly_present data E F k" by (intro jointly_lawful_present[OF E]) simp_all
  then show "jointly_present data (smap g E) F k" by (simp add: jointly_present_def)
qed

lemma jointly_lawful_value_at: "jointly_lawful (value_at c g)"
  unfolding value_at_def by (rule jointly_lawful_smap[OF jointly_lawful_key_at])

lemma jointly_lawful_restrict:
  assumes E: "jointly_lawful E"
  shows "jointly_lawful (restrict \<gamma> E)"
proof (rule jointly_lawfulI[OF semilawful_restrict[OF jointly_lawful_semilawful[OF E]]])
  fix data F k assume "fconf (evalues (restrict \<gamma> E)) data F" and "proj (kd (restrict \<gamma> E) F)\<cdot>k = k"
    and "esem (restrict \<gamma> E) data F k \<noteq> None"
  then have "jointly_present data E (frestrict (gsel \<gamma>) F) k"
    by (intro jointly_lawful_present[OF E]) (simp_all add: fconf_frestrict)
  then show "jointly_present data (restrict \<gamma> E) F k"
    by (auto simp: jointly_present_def group_frestrict comp_def)
qed

lemma jointly_lawful_filtfor:
  assumes E: "jointly_lawful E"
  shows "jointly_lawful (filtfor \<tau> G E)"
proof (rule jointly_lawfulI[OF semilawful_filtfor[OF jointly_lawful_semilawful[OF E]]])
  have ES: "semilawful E" by (rule jointly_lawful_semilawful[OF E])
  fix data F k assume d: "fconf (evalues (filtfor \<tau> G E)) data F" and p: "esem (filtfor \<tau> G E) data F k \<noteq> None"
  let ?k = "proj (emind E \<squnion> flod (ffor \<tau> G F))\<cdot>k"
  have d': "fconf (evalues E) data (ffor \<tau> G F)" using d by (simp add: fconf_filtfor[of _ _ _ _ G])
  have "jointly_present data E (ffor \<tau> G F) ?k"
    using p by (intro jointly_lawful_present[OF E d' proj_idem]) simp
  then obtain y where y: "\<And>S. S \<in> set (esels E) \<Longrightarrow> y \<in> group data (lower_part S) (upper_part S) (ffor \<tau> G F) ?k"
    by (auto simp: jointly_present_def)
  show "jointly_present data (filtfor \<tau> G E) F k" unfolding jointly_present_def
  proof (intro exI ballI)
    fix S assume "S \<in> set (esels (filtfor \<tau> G E))"
    then obtain S0 where S0: "S0 \<in> set (esels E)" and S: "S = trunc_sel \<tau> S0" by auto
    show "y \<in> group data (lower_part S) (upper_part S) F k"
      using y[OF S0] unfolding S group_ffor[OF lower_below_mind[OF ES S0]] by simp
  qed
qed

lemma jointly_lawful_gate: "semilawful E \<Longrightarrow> jointly_lawful (gate M E)"
  by (rule lawful_jointly_lawful[OF lawful_gate])

text \<open>The gate without a presence test only raises the entries and evaluates under the raised
  frame.  It is lawful as soon as presence under the raised frame has a witness in the full group:
  for a jointly lawful expression with a selector whose upper part is \<open>\<top>\<close>, a guard's or a value
  entry's, and for a collection with one such component, whatever the others.\<close>

definition gate_joint :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "gate_joint M E = \<lparr>emind = emind E \<squnion> M,
     eguards = map (include_entry (emind E \<squnion> M)) (eguards E),
     evalues = map (include_entry (emind E \<squnion> M)) (evalues E),
     esem = \<lambda>data F k. if proj (emind E \<squnion> M \<squnion> flod F)\<cdot>k = k
       then esem E data (finclude (emind E \<squnion> M) F) k else None,
     csem = csem E\<rparr>"

lemma gate_joint_simps [simp]:
  "emind (gate_joint M E) = emind E \<squnion> M"
  "eguards (gate_joint M E) = map (include_entry (emind E \<squnion> M)) (eguards E)"
  "evalues (gate_joint M E) = map (include_entry (emind E \<squnion> M)) (evalues E)"
  "esem (gate_joint M E) data F k = (if proj (emind E \<squnion> M \<squnion> flod F)\<cdot>k = k
       then esem E data (finclude (emind E \<squnion> M) F) k else None)"
  "csem (gate_joint M E) = csem E"
  by (simp_all add: gate_joint_def)

theorem lawful_gate_joint_witness:
  assumes ES: "semilawful E" and t: "S \<in> set (esels E)" "upper_part S = \<top>"
    and W: "\<And>data F k. \<lbrakk>fconf (evalues E) data (finclude (emind E \<squnion> M) F); proj (emind E \<squnion> M \<squnion> flod F)\<cdot>k = k;
        esem E data (finclude (emind E \<squnion> M) F) k \<noteq> None\<rbrakk> \<Longrightarrow> group data (emind E \<squnion> M) \<top> F k \<noteq> {}"
  shows "lawful (gate_joint M E)"
proof -
  let ?m = "emind E \<squnion> M"
  have tm: "lower_part S \<sqsubseteq> ?m" by (rule below_trans[OF lower_below_mind[OF ES t(1)] lattice_join_ge1])
  show ?thesis
  proof (rule lawfulI, simp_all only: gate_joint_simps)
    show "cstrict (gate_joint M E)"
      using semilawful_cstrict[OF ES] by (simp add: cstrict_def)
    show "entry_wf e" if "e \<in> set (map (include_entry ?m) (evalues E))" for e
      using that by (auto intro: entry_wf_include_entry semilawful_wf[OF ES])
    show "(upper_part S' \<sqinter> ?m) \<sqsubseteq> lower_part S'"
      if "S' \<in> set (map esel (map (include_entry ?m) (eguards E)) @ map esel (map (include_entry ?m) (evalues E)))" for S'
      using that by (auto intro: include_saturates[of ?m])
    show "?m = fold (\<squnion>) (map lower_part (map esel (map (include_entry ?m) (eguards E))
        @ map esel (map (include_entry ?m) (evalues E)))) \<bottom>"
    proof (rule below_antisym)
      let ?L = "map lower_part (map esel (map (include_entry ?m) (eguards E)) @ map esel (map (include_entry ?m) (evalues E)))"
      have lo: "lower_part (include_sel ?m S) = ?m" using tm by (simp add: t(2) truncate_top lattice_join_absorb2)
      have "lower_part (include_sel ?m S) \<in> set ?L" using t(1) by auto
      then show "?m \<sqsubseteq> fold (\<squnion>) ?L \<bottom>" unfolding lo by (rule fold_join_upper)
      show "fold (\<squnion>) ?L \<bottom> \<sqsubseteq> ?m"
      proof (rule fold_join_least)
        fix x assume "x \<in> set ?L"
        then obtain S' where S': "S' \<in> set (esels E)" and x: "x = lower_part (include_sel ?m S')" by auto
        show "x \<sqsubseteq> ?m" unfolding x by (rule include_lower_below[OF below_trans[OF lower_below_mind[OF ES S'] lattice_join_ge1]])
      qed simp
    qed
    show "keyimg data F (?m \<squnion> flod F) k"
      if d: "fconf (map (include_entry ?m) (evalues E)) data F"
        and p: "(if proj (?m \<squnion> flod F)\<cdot>k = k then esem E data (finclude ?m F) k else None) \<noteq> None" for data F k
    proof -
      have k: "proj (?m \<squnion> flod F)\<cdot>k = k" using p by (simp split: if_splits)
      have "esem E data (finclude ?m F) k \<noteq> None" using p k by simp
      then show ?thesis using W[OF d[unfolded fconf_include] k] keyimg_group_top[OF k] by blast
    qed
    show "(if k = k then esem E data (finclude ?m F) k else None)
        = csem E (gcontents data (map (include_entry ?m) (eguards E)) F k)\<cdot>(contents data (map (include_entry ?m) (evalues E)) F k)"
      if d: "fconf (map (include_entry ?m) (evalues E)) data F" and k: "proj (?m \<squnion> flod F)\<cdot>k = k" for data F k
    proof -
      have d': "fconf (evalues E) data (finclude ?m F)" using d by (simp only: fconf_include)
      have g: "gcontents data (map (include_entry ?m) (eguards E)) F k = gcontents data (eguards E) (finclude ?m F) k"
        by (simp add: comp_def gcontent_include_entry)
      have c: "contents data (map (include_entry ?m) (evalues E)) F k = contents data (evalues E) (finclude ?m F) k"
        by (simp add: comp_def content_include_entry)
      have "proj (emind E \<squnion> flod (finclude ?m F))\<cdot>k = k" by (simp only: kd_finclude_mind k)
      then show ?thesis by (simp only: g c semilawful_csem_conf[OF ES d'] simp_thms if_True)
    qed
  qed
qed

corollary lawful_gate_joint:
  assumes E: "jointly_lawful E" and t: "S \<in> set (esels E)" "upper_part S = \<top>"
  shows "lawful (gate_joint M E)"
proof (rule lawful_gate_joint_witness[OF jointly_lawful_semilawful[OF E] t])
  let ?m = "emind E \<squnion> M"
  have tm: "lower_part S \<sqsubseteq> ?m"
    by (rule below_trans[OF lower_below_mind[OF jointly_lawful_semilawful[OF E] t(1)] lattice_join_ge1])
  fix data F k assume d: "fconf (evalues E) data (finclude ?m F)" and k: "proj (?m \<squnion> flod F)\<cdot>k = k"
    and p: "esem E data (finclude ?m F) k \<noteq> None"
  have k': "proj (kd E (finclude ?m F))\<cdot>k = k" by (simp only: kd_finclude_mind k)
  obtain y where "\<And>S'. S' \<in> set (esels E) \<Longrightarrow> y \<in> group data (lower_part S') (upper_part S') (finclude ?m F) k"
    using jointly_lawful_present[OF E d k' p] by (auto simp: jointly_present_def)
  then have "y \<in> group data (lower_part S) \<top> (finclude ?m F) k" using t by fastforce
  then show "group data ?m \<top> F k \<noteq> {}" unfolding group_top_finclude[OF tm] by blast
qed

theorem lawful_gate_joint_collect:
  assumes law: "\<And>E. E \<in> set Es \<Longrightarrow> semilawful E" and E0: "E0 \<in> set Es" "jointly_lawful E0"
    and t: "S \<in> set (esels E0)" "upper_part S = \<top>"
  shows "lawful (gate_joint M (collect Es))"
proof (rule lawful_gate_joint_witness[OF semilawful_collect[OF law]])
  show "S \<in> set (esels (collect Es))" using t(1) E0(1) by auto
  show "upper_part S = \<top>" by (fact t(2))
  let ?m = "emind (collect Es) \<squnion> M"
  have m0: "emind E0 \<sqsubseteq> ?m" unfolding collect_simps
    by (rule below_trans[OF fold_join_upper lattice_join_ge1]) (simp add: E0(1))
  have tm: "lower_part S \<sqsubseteq> ?m"
    by (rule below_trans[OF lower_below_mind[OF jointly_lawful_semilawful[OF E0(2)] t(1)] m0])
  fix data F k assume d: "fconf (evalues (collect Es)) data (finclude ?m F)" and k: "proj (?m \<squnion> flod F)\<cdot>k = k"
    and p: "esem (collect Es) data (finclude ?m F) k \<noteq> None"
  have kk: "proj (kd E0 (finclude ?m F))\<cdot>k = k" by (simp only: join_finclude_absorb[OF m0] k)
  have "esem E0 data (finclude ?m F) (proj (kd E0 (finclude ?m F))\<cdot>k) \<noteq> None"
    using p E0(1) unfolding collect_simps those_not_None_iff by auto
  then have p0: "esem E0 data (finclude ?m F) k \<noteq> None" unfolding kk .
  have d0: "fconf (evalues E0) data (finclude ?m F)" using d E0(1) by (auto simp: fconf_def)
  obtain y where "\<And>S'. S' \<in> set (esels E0) \<Longrightarrow> y \<in> group data (lower_part S') (upper_part S') (finclude ?m F) k"
    using jointly_lawful_present[OF E0(2) d0 kk p0] by (auto simp: jointly_present_def)
  then have "y \<in> group data (lower_part S) \<top> (finclude ?m F) k" using t by fastforce
  then show "group data ?m \<top> F k \<noteq> {}" unfolding group_top_finclude[OF tm] by blast
qed

end

end
