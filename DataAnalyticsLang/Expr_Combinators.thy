theory Expr_Combinators
  imports Content_Law
begin

section \<open>Combinators\<close>

text \<open>Each combinator transforms the entries of its inner expressions' dims along with their
  semantics, and is lawful on lawful inner expressions.  Collecting a list of expressions into a
  tuple, followed by a map, expresses every operator of any arity.\<close>

subsection \<open>Tuples\<close>

text \<open>A collected entry is present where every component is; its value is the list of the
  components' values.  Absence is the entry's, so the list needs no bottom: tuples are plain lists,
  ordered componentwise at equal length.\<close>

lemma those_not_None_iff: "those xs \<noteq> None \<longleftrightarrow> (\<forall>x\<in>set xs. x \<noteq> None)"
  by (induct xs) (auto split: option.splits)

context dataspace
begin

subsection \<open>Keys\<close>

text \<open>The key at an LOD \<open>c\<close>.  Its only entry is the group of rows with that key part, the frame's
  filters coarsened to \<open>c\<close>, keyed there and reading no columns, so its content is that key part;
  it is present where that group is nonempty, so it is gated at its own row LOD, not at the frame's
  keys.\<close>

lemma join_meet_self: "c \<squnion> (c \<sqinter> L) = c" for c :: "'k semi_factor"
  by (rule lattice_join_absorb1[OF lattice_meet_le1])

text \<open>Whether a content is empty is rigid; so is everything read off its keys.\<close>

lemma rigid_empty: "rigid (\<lambda>X :: 'k \<Rightarrow> 'r option. X = Map.empty)"
  by (rule rigidI) (metis dom_eq_empty_conv map_below_dom)

lemma rigid_hd_empty: "rigid (\<lambda>Xs :: ('k \<Rightarrow> 'r option) list. hd Xs = Map.empty)"
  by (rule rigid_comp[OF rigid_empty cont2mono[OF cont_hd]])

lemma cont_key_at_csem:
  "cont (\<lambda>Xs :: ('k \<Rightarrow> 'r option) list. if hd Xs = Map.empty then None else Some (the_elem (dom (hd Xs))))"
proof (rule cont_rigid, rule rigidI)
  fix Xs Ys :: "('k \<Rightarrow> 'r option) list" assume "Xs \<sqsubseteq> Ys"
  then have b: "hd Xs \<sqsubseteq> hd Ys" by (rule hd_mono)
  show "(if hd Xs = Map.empty then None else Some (the_elem (dom (hd Xs))))
      = (if hd Ys = Map.empty then None else Some (the_elem (dom (hd Ys))))"
    using rigidD[OF rigid_empty b] map_below_dom[OF b] by simp
qed

definition key_at :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'k) expr" where
  "key_at c = \<lparr>emind = c, edims = [mk_entry (sel c c) gtrue (\<bottom>, c)],
     esem = \<lambda>data F k. if group data c c F k = {} then None else Some (proj c\<cdot>k),
     csem = \<Lambda> Xs. if hd Xs = Map.empty then None else Some (the_elem (dom (hd Xs)))\<rparr>"

lemma key_at_simps [simp]:
  "emind (key_at c) = c" "edims (key_at c) = [mk_entry (sel c c) gtrue (\<bottom>, c)]"
  "esem (key_at c) data F k = (if group data c c F k = {} then None else Some (proj c\<cdot>k))"
  "csem (key_at c)\<cdot>Xs = (if hd Xs = Map.empty then None else Some (the_elem (dom (hd Xs))))"
  by (simp_all add: key_at_def cont_key_at_csem)

lemma group_own: "y \<in> group data c c F k \<Longrightarrow> rproj c y = proj c\<cdot>k"
  by (simp add: group_def join_meet_self)

lemma content_key_at:
  "content data (mk_entry (sel c c) gtrue (\<bottom>, c)) F k = (if group data c c F k = {} then Map.empty else [proj c\<cdot>k \<mapsto> \<bottom>])"
proof -
  have "cgraph data (mk_entry (sel c c) gtrue (\<bottom>, c)) F k = (\<lambda>_. (proj c\<cdot>k, \<bottom>)) ` group data c c F k"
    unfolding cgraph_def efiber_def cpair_def by (rule image_cong) (simp_all add: group_own semi_factor_p_bot)
  then show ?thesis unfolding content_def by (simp add: image_constant_conv)
qed

lemma cstrict_key_at: "cstrict (key_at c)"
  by (rule cstrictI) (auto simp: length_Suc_conv)

theorem semilawful_key_at: "semilawful (key_at c)"
proof (rule semilawfulI, simp_all only: key_at_simps)
  show "cstrict (key_at c)" by (rule cstrict_key_at)
  show "entry_wf e" if "e \<in> set [mk_entry (sel c c) gtrue (\<bottom>, c)]" for e
    using that by (simp add: entry_wf_view keyed_view_key)
  show "c = fold (\<squnion>) (map elower [mk_entry (sel c c) gtrue (\<bottom>, c)]) \<bottom>" by (simp add: lattice_join_bot_right)
  show "(if group data c c F k = {} then None else Some (proj c\<cdot>k))
      = (if hd (contents data [mk_entry (sel c c) gtrue (\<bottom>, c)] F k) = Map.empty then None
         else Some (the_elem (dom (hd (contents data [mk_entry (sel c c) gtrue (\<bottom>, c)] F k)))))" for data F k
    by (simp only: list.map list.sel content_key_at) simp
qed

subsection \<open>Table columns\<close>

text \<open>A table column reads a section of the row.  An external oracle names the key part that
  determines it in every conforming dataset; then the rows of a key's group carry one section,
  and the column's value is the column function of it.  Its view is that section, keyed at the
  oracle's key part.\<close>

lemma cont_column_csem:
  "cont (\<lambda>Xs :: ('k \<Rightarrow> 'r option) list. if hd Xs = Map.empty then None else Some (v\<cdot>(the (hd Xs (the_elem (dom (hd Xs)))))))"
proof (rule cont_if_rigid[OF rigid_hd_empty])
  have "cont (\<lambda>Xs :: ('k \<Rightarrow> 'r option) list. hd Xs (the_elem (dom (hd Xs))))"
    by (rule cont_rigid_arg[OF _ rigid_comp[OF rigid_dom cont2mono[OF cont_hd]]]) (simp add: cont2cont_fun)
  then show "cont (\<lambda>Xs :: ('k \<Rightarrow> 'r option) list. Some (v\<cdot>(the (hd Xs (the_elem (dom (hd Xs)))))))"
    by (simp add: cont_compose[OF cont_the])
qed simp

definition column :: "'r semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('r \<rightarrow> 'w::cpo) \<Rightarrow> ('k, 'f, 'r, 'w) expr" where
  "column c a v = \<lparr>emind = a, edims = [mk_entry (sel a a) gtrue (c, a)],
     esem = \<lambda>data F k. if group data a a F k = {} then None
       else Some (THE w. w \<in> (\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` group data a a F k),
     csem = \<Lambda> Xs. if hd Xs = Map.empty then None else Some (v\<cdot>(the (hd Xs (the_elem (dom (hd Xs))))))\<rparr>"

lemma column_simps [simp]:
  "emind (column c a v) = a" "edims (column c a v) = [mk_entry (sel a a) gtrue (c, a)]"
  "esem (column c a v) data F k = (if group data a a F k = {} then None
       else Some (THE w. w \<in> (\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` group data a a F k))"
  "csem (column c a v)\<cdot>Xs = (if hd Xs = Map.empty then None else Some (v\<cdot>(the (hd Xs (the_elem (dom (hd Xs)))))))"
  by (simp_all add: column_def cont_column_csem)

text \<open>The rows of a column's group carry one section.\<close>

lemma column_group_section:
  assumes fd: "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>))"
    and d: "conforms data" and x: "x \<in> group data a a F k" and y: "y \<in> group data a a F k"
  shows "y \<downharpoonright> c = x \<downharpoonright> c"
proof -
  have "y \<downharpoonright> fst (c, a) = x \<downharpoonright> fst (c, a)"
  proof (rule view_agree[OF keyed_view_columns[OF fd] d])
    show "x \<in> lower_maximal data" "y \<in> lower_maximal data" using x y by (simp_all add: group_def)
    show "rproj a y = rproj a x" using x y by (simp add: group_own)
  qed simp
  then show ?thesis by simp
qed

lemma cstrict_column: "cstrict (column c a v)"
  by (rule cstrictI) (auto simp: length_Suc_conv)

theorem semilawful_column:
  assumes fd: "universally (\<lambda>P. vfd P (\<bottom>, a) (c, \<bottom>))"
  shows "semilawful (column c a v)"
proof (rule semilawfulI, simp_all only: column_simps)
  show "cstrict (column c a v)" by (rule cstrict_column)
  show "entry_wf e" if "e \<in> set [mk_entry (sel a a) gtrue (c, a)]" for e
    using that by (simp add: entry_wf_view keyed_view_columns[OF fd])
  show "a = fold (\<squnion>) (map elower [mk_entry (sel a a) gtrue (c, a)]) \<bottom>"
    by (simp add: lattice_join_bot_right)
  show "(if group data a a F k = {} then None else Some (THE w. w \<in> (\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` group data a a F k))
      = (if hd (contents data [mk_entry (sel a a) gtrue (c, a)] F k) = Map.empty then None
         else Some (v\<cdot>(the (hd (contents data [mk_entry (sel a a) gtrue (c, a)] F k)
           (the_elem (dom (hd (contents data [mk_entry (sel a a) gtrue (c, a)] F k))))))))"
    if d: "conforms data" for data F k
  proof (cases "group data a a F k = {}")
    case False
    then obtain x where x: "x \<in> group data a a F k" by blast
    have sec: "(\<lambda>y. y \<downharpoonright> c) ` group data a a F k = {x \<downharpoonright> c}"
      using column_group_section[OF fd d x] x by blast
    have "cgraph data (mk_entry (sel a a) gtrue (c, a)) F k = (\<lambda>_. (proj a\<cdot>k, x \<downharpoonright> c)) ` group data a a F k"
      unfolding cgraph_def efiber_def cpair_def
      by (rule image_cong) (simp_all add: group_own column_group_section[OF fd d x])
    then have C: "content data (mk_entry (sel a a) gtrue (c, a)) F k = [proj a\<cdot>k \<mapsto> x \<downharpoonright> c]"
      unfolding content_def using False by (simp add: image_constant_conv)
    have V: "(\<lambda>y. v\<cdot>(y \<downharpoonright> c)) ` group data a a F k = {v\<cdot>(x \<downharpoonright> c)}"
      using sec by (simp only: image_image[of "Rep_cfun v" "\<lambda>y. y \<downharpoonright> c", symmetric, unfolded comp_def]) simp
    show ?thesis using False by (simp only: list.map list.sel C V) simp
  next
    case True
    have "cgraph data (mk_entry (sel a a) gtrue (c, a)) F k = {}" using True by (simp add: cgraph_def efiber_def)
    then show ?thesis using True by (simp add: content_def)
  qed
qed

subsection \<open>Maps\<close>

definition smap :: "('v::cpo \<rightarrow> 'w::cpo) \<Rightarrow> ('k, 'f, 'r, 'v) expr \<Rightarrow> ('k, 'f, 'r, 'w) expr" where
  "smap g E = \<lparr>emind = emind E, edims = edims E, esem = \<lambda>data F k. map_option (Rep_cfun g) (esem E data F k),
     csem = \<Lambda> Xs. map_option (Rep_cfun g) (csem E\<cdot>Xs)\<rparr>"

lemma smap_simps [simp]:
  "emind (smap g E) = emind E" "edims (smap g E) = edims E"
  "esem (smap g E) data F k = map_option (Rep_cfun g) (esem E data F k)"
  "csem (smap g E)\<cdot>Xs = map_option (Rep_cfun g) (csem E\<cdot>Xs)"
  by (simp_all add: smap_def)

lemma cstrict_smap: "cstrict E \<Longrightarrow> cstrict (smap g E)"
  unfolding cstrict_def by simp

theorem semilawful_smap: assumes "semilawful E" shows "semilawful (smap g E)"
proof -
  have ES: "semilawful E" by (fact assms)
  show ?thesis
  proof (rule semilawfulI, simp_all only: smap_simps)
    show "cstrict (smap g E)" by (rule cstrict_smap[OF semilawful_cstrict[OF ES]])
    show "entry_wf e" if "e \<in> set (edims E)" for e by (rule semilawful_wf[OF ES that])
    show "emind E = fold (\<squnion>) (map elower (edims E)) \<bottom>" by (rule semilawful_mind_lub[OF ES])
    show "map_option (Rep_cfun g) (esem E data F k) = map_option (Rep_cfun g) (csem E\<cdot>(contents data (edims E) F k))"
      if "conforms data" "proj (emind E \<squnion> flod F)\<cdot>k = k" for data F k
      by (simp only: semilawful_csem[OF ES that])
  qed
qed

theorem lawful_smap: assumes "lawful E" shows "lawful (smap g E)"
proof -
  have EL: "lawful E" by (fact assms)
  show ?thesis
  proof (rule lawful_semiI[OF semilawful_smap[OF lawful_semilawful[OF assms]]], simp_all only: smap_simps)
    show "(eupper e \<sqinter> emind E) \<sqsubseteq> elower e" if "e \<in> set (edims E)" for e
      by (rule lawful_saturated[OF EL that])
    show "keyimg data F (emind E \<squnion> flod F) k" if d: "conforms data" and "map_option (Rep_cfun g) (esem E data F k) \<noteq> None" for data F k
      using that(2) by (intro lawful_key_law[OF EL d]) simp
  qed
qed

text \<open>A function of the key at an LOD.\<close>

definition value_at :: "'k semi_factor \<Rightarrow> ('k \<rightarrow> 'v::cpo) \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "value_at c g = smap g (key_at c)"

lemma value_at_simps [simp]:
  "emind (value_at c g) = c" "edims (value_at c g) = [mk_entry (sel c c) gtrue (\<bottom>, c)]"
  "esem (value_at c g) data F k = (if group data c c F k = {} then None else Some (g\<cdot>(proj c\<cdot>k)))"
  "csem (value_at c g)\<cdot>Xs = (if hd Xs = Map.empty then None else Some (g\<cdot>(the_elem (dom (hd Xs)))))"
  by (simp_all add: value_at_def)

theorem semilawful_value_at: "semilawful (value_at c g)"
  unfolding value_at_def by (rule semilawful_smap[OF semilawful_key_at])

subsection \<open>\<open>RESTRICT\<close>\<close>

text \<open>Restricting conjoins the rows a test passes to the ambient filter: inner fibers are the
  outer fibers' rows passing it, so the test is conjoined to each entry's guard.\<close>

definition restrict_entry :: "'r guard \<Rightarrow> ('k, 'r) entry \<Rightarrow> ('k, 'r) entry" where
  "restrict_entry \<gamma> e = e\<lparr>eguard := gand \<gamma> (eguard e)\<rparr>"

lemma restrict_entry_simps [simp]:
  "esel (restrict_entry \<gamma> e) = esel e"
  "eguard (restrict_entry \<gamma> e) = gand \<gamma> (eguard e)" "eview (restrict_entry \<gamma> e) = eview e"
  by (simp_all add: restrict_entry_def)

definition restrict :: "'r guard \<Rightarrow> ('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "restrict \<gamma> E = \<lparr>emind = emind E, edims = map (restrict_entry \<gamma>) (edims E),
     esem = \<lambda>data F. esem E data (frestrict (gsel \<gamma>) F), csem = csem E\<rparr>"

lemma restrict_simps [simp]:
  "emind (restrict \<gamma> E) = emind E"
  "edims (restrict \<gamma> E) = map (restrict_entry \<gamma>) (edims E)"
  "esem (restrict \<gamma> E) data F = esem E data (frestrict (gsel \<gamma>) F)"
  "csem (restrict \<gamma> E) = csem E"
  by (simp_all add: restrict_def)

lemma group_frestrict:
  "group data a \<rho> (frestrict \<phi> F) k = {y \<in> group data a \<rho> F k. selects \<phi> y}"
  by (auto simp: group_def)

lemma content_frestrict:
  "content data e (frestrict (gsel \<gamma>) F) k = content data (restrict_entry \<gamma> e) F k"
  unfolding content_def cgraph_def efiber_def cpair_def by (auto simp: group_frestrict)

lemma cstrict_restrict: "cstrict E \<Longrightarrow> cstrict (restrict \<gamma> E)"
  unfolding cstrict_def by simp

theorem semilawful_restrict:
  assumes ES: "semilawful E"
  shows "semilawful (restrict \<gamma> E)"
proof (rule semilawfulI, simp_all only: restrict_simps)
  show "cstrict (restrict \<gamma> E)" by (rule cstrict_restrict[OF semilawful_cstrict[OF ES]])
  show "entry_wf e" if "e \<in> set (map (restrict_entry \<gamma>) (edims E))" for e
    using that semilawful_wf[OF ES] by (auto simp: restrict_entry_def entry_wf_def)
  show "emind E = fold (\<squnion>) (map elower (map (restrict_entry \<gamma>) (edims E))) \<bottom>"
    by (simp add: comp_def semilawful_mind_lub[OF ES])
  show "esem E data (frestrict (gsel \<gamma>) F) k = csem E\<cdot>(contents data (map (restrict_entry \<gamma>) (edims E)) F k)"
    if d: "conforms data" and k: "proj (emind E \<squnion> flod F)\<cdot>k = k" for data F k
  proof -
    have "proj (emind E \<squnion> flod (frestrict (gsel \<gamma>) F))\<cdot>k = k" using k by simp
    then show ?thesis by (simp add: semilawful_csem[OF ES d] content_frestrict comp_def)
  qed
qed

theorem lawful_restrict:
  assumes EL: "lawful E"
  shows "lawful (restrict \<gamma> E)"
proof (rule lawful_semiI[OF semilawful_restrict[OF lawful_semilawful[OF EL]]], simp_all only: restrict_simps)
  show "(eupper e \<sqinter> emind E) \<sqsubseteq> elower e" if "e \<in> set (map (restrict_entry \<gamma>) (edims E))" for e
    using that by (auto intro: lawful_saturated[OF EL])
  show "keyimg data F (emind E \<squnion> flod F) k" if d: "conforms data" and "esem E data (frestrict (gsel \<gamma>) F) k \<noteq> None" for data F k
  proof -
    have "keyimg data (frestrict (gsel \<gamma>) F) (emind E \<squnion> flod F) k"
      using lawful_key_law[OF EL that] by simp
    then show ?thesis by (rule keyimg_mono[rotated]) (simp add: frows_frestrict)
  qed
qed

subsection \<open>\<open>FOR\<close> and \<open>FIXED\<close>\<close>

text \<open>\<open>E FOR \<tau> G\<close>: the inner expression under the frame with LOD and slice truncated to \<open>\<tau>\<close>
  and \<open>G\<close> conjoined, at the truncated key.  Its upper parts meet \<open>\<tau>\<close>; each entry's guard is
  conjoined with \<open>G\<close> coarsened to the entry's upper part.  It is not gated: the result is
  broadcast over the dropped detail.  \<open>FIXED D\<close> is \<open>FOR D\<close> without a filter.\<close>

definition for_entry :: "'k semi_factor \<Rightarrow> 'f \<Rightarrow> ('k, 'r) entry \<Rightarrow> ('k, 'r) entry" where
  "for_entry \<tau> G e = e\<lparr>esel := sel (elower e) (eupper e \<sqinter> \<tau>), eguard := gand (guard_holds (coarsen (eupper e) G)) (eguard e)\<rparr>"

lemma for_entry_simps [simp]:
  "elower (for_entry \<tau> G e) = elower e" "eupper (for_entry \<tau> G e) = eupper e \<sqinter> \<tau>"
  "eguard (for_entry \<tau> G e) = gand (guard_holds (coarsen (eupper e) G)) (eguard e)"
  "eview (for_entry \<tau> G e) = eview e"
  by (simp_all add: for_entry_def)

definition filtfor :: "'k semi_factor \<Rightarrow> 'f \<Rightarrow> ('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "filtfor \<tau> G E = \<lparr>emind = emind E, edims = map (for_entry \<tau> G) (edims E),
     esem = \<lambda>data F k. esem E data (ffor \<tau> G F) (proj (emind E \<squnion> flod (ffor \<tau> G F))\<cdot>k), csem = csem E\<rparr>"

abbreviation fixed :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "fixed D \<equiv> filtfor D \<^bold>1"

lemma filtfor_simps [simp]:
  "emind (filtfor \<tau> G E) = emind E"
  "edims (filtfor \<tau> G E) = map (for_entry \<tau> G) (edims E)"
  "esem (filtfor \<tau> G E) data F k = esem E data (ffor \<tau> G F) (proj (emind E \<squnion> flod (ffor \<tau> G F))\<cdot>k)"
  "csem (filtfor \<tau> G E) = csem E"
  by (simp_all add: filtfor_def)

text \<open>Inside the truncated frame, at the truncated key, a group is the outer group through the
  composite mask, cut down by the filter coarsened to the inner upper part.\<close>

lemma group_ffor:
  assumes am: "a \<sqsubseteq> m"
  shows "group data a \<rho> (ffor \<tau> G F) (proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k)
       = {y \<in> group data a (\<rho> \<sqinter> \<tau>) F k. holds (coarsen \<rho> G) (rkey\<cdot>y)}"
proof -
  let ?X = "a \<squnion> ((\<rho> \<sqinter> \<tau>) \<sqinter> flod F)"
  have lod: "a \<squnion> (\<rho> \<sqinter> flod (ffor \<tau> G F)) = ?X" by (simp add: truncate_inf_comp)
  have le: "?X \<sqsubseteq> m \<squnion> flod (ffor \<tau> G F)"
    unfolding flod_ffor truncate_inf_comp by (rule lattice_join_mono[OF am truncate_below])
  have key: "proj ?X\<cdot>(proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k) = proj ?X\<cdot>k" by (rule proj_le[OF le])
  have sl: "holds (coarsen \<rho> (slice (ffor \<tau> G F))) k' \<longleftrightarrow>
      holds (coarsen (\<rho> \<sqinter> \<tau>) (slice F)) k' \<and> holds (coarsen \<rho> G) k'" for k'
    by (simp add: coarsen_conj coarsen_coarsen)
  show ?thesis unfolding group_def lod key sl by auto
qed

lemma content_ffor:
  assumes "elower e \<sqsubseteq> m"
  shows "content data e (ffor \<tau> G F) (proj (m \<squnion> flod (ffor \<tau> G F))\<cdot>k) = content data (for_entry \<tau> G e) F k"
  unfolding content_def cgraph_def efiber_def cpair_def group_ffor[OF assms] by auto

lemma content_const_top:
  assumes "proj (c \<squnion> flod F)\<cdot>k = k"
  shows "content data (mk_entry (sel c \<top>) gtrue \<bottom>) F k
       = (if keyimg data F (c \<squnion> flod F) k then [\<bottom> \<mapsto> \<bottom>] else Map.empty)"
proof -
  have "cgraph data (mk_entry (sel c \<top>) gtrue \<bottom>) F k = (\<lambda>_. (\<bottom>, \<bottom>)) ` group data c \<top> F k"
    unfolding cgraph_def efiber_def cpair_def by (simp add: proj_bot semi_factor_p_bot)
  moreover have "gmap {\<bottom> :: 'k \<times> 'r} = [\<bottom> \<mapsto> \<bottom>]" using gmap_singleton[of "\<bottom>::'k" "\<bottom>::'r"] by simp
  ultimately show ?thesis unfolding content_def by (simp add: image_constant_conv keyimg_group_top[OF assms])
qed

lemma cstrict_filtfor: "cstrict E \<Longrightarrow> cstrict (filtfor \<tau> G E)"
  unfolding cstrict_def by simp

theorem semilawful_filtfor: assumes "semilawful E" shows "semilawful (filtfor \<tau> G E)"
proof -
  have ES: "semilawful E" by (fact assms)
  let ?m = "emind E"
  have inner: "contents data (edims E) (ffor \<tau> G H) (proj (?m \<squnion> flod (ffor \<tau> G H))\<cdot>\<kappa>)
      = contents data (map (for_entry \<tau> G) (edims E)) H \<kappa>" for data H \<kappa>
    unfolding map_map comp_def by (rule map_cong[OF refl], rule content_ffor[OF lower_below_mind[OF ES]])
  show ?thesis
  proof (rule semilawfulI, simp_all only: filtfor_simps)
    show "cstrict (filtfor \<tau> G E)" by (rule cstrict_filtfor[OF semilawful_cstrict[OF ES]])
    show "entry_wf e" if "e \<in> set (map (for_entry \<tau> G) (edims E))" for e
      using that semilawful_wf[OF ES]
      by (auto simp: entry_wf_def)
    show "?m = fold (\<squnion>) (map elower (map (for_entry \<tau> G) (edims E))) \<bottom>"
      by (simp add: comp_def semilawful_mind_lub[OF ES])
    show "esem E data (ffor \<tau> G F) (proj (?m \<squnion> flod (ffor \<tau> G F))\<cdot>k)
        = csem E\<cdot>(contents data (map (for_entry \<tau> G) (edims E)) F k)"
      if d: "conforms data" for data F k
      by (simp only: semilawful_csem[OF ES d proj_idem] inner)
  qed
qed

subsection \<open>Including dimensions\<close>

text \<open>Evaluating under the frame raised by \<open>M\<close> is the same as raising each entry's lower part by
  its masked part of \<open>M\<close>: the entry-level form of \<open>finclude\<close>.\<close>

definition include_entry :: "'k semi_factor \<Rightarrow> ('k, 'r) entry \<Rightarrow> ('k, 'r) entry" where
  "include_entry M e = e\<lparr>esel := sel (sel_at (esel e) M) (eupper e)\<rparr>"

lemma include_entry_simps [simp]:
  "elower (include_entry M e) = sel_at (esel e) M" "eupper (include_entry M e) = eupper e"
  "eguard (include_entry M e) = eguard e" "eview (include_entry M e) = eview e"
  by (simp_all add: include_entry_def)

lemma content_include_entry: "content data (include_entry M e) F k = content data e (finclude M F) k"
proof -
  have lod: "(sel_at (esel e) M) \<squnion> (eupper e \<sqinter> flod F) = sel_at (esel e) (flod (finclude M F))"
    by (simp add: flod_finclude truncate_sup lattice_join_ac)
  have "group data (sel_at (esel e) M) (eupper e) F k = group data (elower e) (eupper e) (finclude M F) k"
    by (rule group_cong) (simp_all only: amb_finclude slice_finclude lod)
  then show ?thesis unfolding content_def cgraph_def efiber_def cpair_def by simp
qed

lemma entry_wf_include_entry: "entry_wf e \<Longrightarrow> entry_wf (include_entry M e)"
  unfolding entry_wf_def include_entry_simps .

subsection \<open>The gate\<close>

text \<open>The gate at \<open>M\<close> turns a semilawful expression into a lawful one: it evaluates under the
  frame including the minimal LOD and \<open>M\<close>, which saturates the entries (their lower parts take in
  the masked minimal LOD and \<open>M\<close>), and it is present exactly at the frame's data keys at that LOD,
  which a presence entry at the full key records.  \<open>gate \<bottom>\<close> is the plain gate; a larger \<open>M\<close>
  refines the expression's groups by further dimensions (requested ones, inside an aggregation).\<close>

definition gate_presence :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "gate_presence M E = \<lparr>emind = emind E \<squnion> M,
     edims = mk_entry (sel (emind E \<squnion> M) \<top>) gtrue \<bottom> # map (include_entry (emind E \<squnion> M)) (edims E),
     esem = \<lambda>data F k. if keyimg data F (emind E \<squnion> M \<squnion> flod F) k
       then esem E data (finclude (emind E \<squnion> M) F) k else None,
     csem = \<Lambda> Xs. if hd Xs = Map.empty then None else csem E\<cdot>(tl Xs)\<rparr>"

lemma gate_presence_simps [simp]:
  "emind (gate_presence M E) = emind E \<squnion> M"
  "edims (gate_presence M E) = mk_entry (sel (emind E \<squnion> M) \<top>) gtrue \<bottom> # map (include_entry (emind E \<squnion> M)) (edims E)"
  "esem (gate_presence M E) data F k = (if keyimg data F (emind E \<squnion> M \<squnion> flod F) k
       then esem E data (finclude (emind E \<squnion> M) F) k else None)"
  "csem (gate_presence M E)\<cdot>Xs = (if hd Xs = Map.empty then None else csem E\<cdot>(tl Xs))"
  by (simp_all add: gate_presence_def cont_if_rigid[OF rigid_hd_empty])

lemma cstrict_gate_presence:
  assumes E: "cstrict E"
  shows "cstrict (gate_presence M E)"
proof (rule cstrictI)
  fix Xs :: "('k \<Rightarrow> 'r option) list"
  assume l: "length Xs = length (edims (gate_presence M E))" and c: "csem (gate_presence M E)\<cdot>Xs \<noteq> None"
  then obtain X Xs' where Xs: "Xs = X # Xs'" and l': "length Xs' = length (edims E)"
    by (auto simp: length_Suc_conv)
  have "X \<noteq> Map.empty" and "csem E\<cdot>Xs' \<noteq> None" using c by (simp_all add: Xs split: if_splits)
  then show "Map.empty \<notin> set Xs" using cstrictD[OF E l'] by (auto simp: Xs)
qed

theorem lawful_gate_presence: assumes "semilawful E" shows "lawful (gate_presence M E)"
proof -
  have ES: "semilawful E" by (fact assms)
  let ?m = "emind E \<squnion> M"
  let ?h = "mk_entry (sel ?m \<top>) gtrue \<bottom> :: ('k, 'r) entry"
  have kdE: "emind E \<squnion> flod (finclude ?m F) = ?m \<squnion> flod F" for F
  proof -
    have "emind E \<sqsubseteq> flod F \<squnion> ?m" by (rule below_trans[OF lattice_join_ge1 lattice_join_ge2])
    then show ?thesis unfolding flod_finclude by (simp only: lattice_join_absorb2 lattice_join_commute)
  qed
  show ?thesis
  proof (rule lawfulI, simp_all only: gate_presence_simps)
    show "cstrict (gate_presence M E)" by (rule cstrict_gate_presence[OF semilawful_cstrict[OF ES]])
    show "entry_wf e" if "e \<in> set (?h # map (include_entry ?m) (edims E))" for e
      using that by (auto intro: entry_wf_view keyed_view_bot_view entry_wf_include_entry semilawful_wf[OF ES])
    show "(eupper e \<sqinter> ?m) \<sqsubseteq> elower e" if "e \<in> set (?h # map (include_entry ?m) (edims E))" for e
      using that by (auto simp: truncate_top intro: lattice_join_ge2)
    show "?m = fold (\<squnion>) (map elower (?h # map (include_entry ?m) (edims E))) \<bottom>"
    proof -
      have "fold (\<squnion>) (map elower (map (include_entry ?m) (edims E))) ?m = ?m"
        by (rule fold_join_absorb)
          (auto intro: lattice_join_least[OF below_trans[OF lower_below_mind[OF ES] lattice_join_ge1] truncate_below])
      then show ?thesis by simp
    qed
    show "keyimg data F (?m \<squnion> flod F) k"
      if "conforms data" and "(if keyimg data F (?m \<squnion> flod F) k then esem E data (finclude ?m F) k else None) \<noteq> None"
      for data F k
      using that by (simp split: if_splits)
    show "(if keyimg data F (?m \<squnion> flod F) k then esem E data (finclude ?m F) k else None)
        = (if hd (contents data (?h # map (include_entry ?m) (edims E)) F k) = Map.empty then None
           else csem E\<cdot>(tl (contents data (?h # map (include_entry ?m) (edims E)) F k)))"
      if d: "conforms data" and k: "proj (?m \<squnion> flod F)\<cdot>k = k" for data F k
    proof -
      have h: "hd (contents data (?h # map (include_entry ?m) (edims E)) F k) = Map.empty
          \<longleftrightarrow> \<not> keyimg data F (?m \<squnion> flod F) k"
        by (simp only: list.map list.sel content_const_top[OF k]) simp
      have t: "tl (contents data (?h # map (include_entry ?m) (edims E)) F k)
          = contents data (edims E) (finclude ?m F) k"
        by (simp add: comp_def content_include_entry)
      have "proj (emind E \<squnion> flod (finclude ?m F))\<cdot>k = k" by (simp only: kdE k)
      then show ?thesis by (simp only: h t semilawful_csem[OF ES d]) simp
    qed
  qed
qed

text \<open>An expression \<^emph>\<open>covers\<close> the key space when one of its entries has upper part \<open>\<top>\<close>: raised
  by the minimal LOD, that entry's group is all rows at the key, so by strictness its expression is
  absent wherever the key is not realised, whatever the entry's guard.  Then the gate needs no
  presence entry: it only raises the entries.\<close>

definition covering :: "('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> bool" where
  "covering E \<longleftrightarrow> (\<exists>e\<in>set (edims E). eupper e = \<top>)"

lemma content_include_top:
  assumes e: "eupper e = \<top>" and am: "elower e \<sqsubseteq> m" and k: "proj (m \<squnion> flod F)\<cdot>k = k"
    and nk: "\<not> keyimg data F (m \<squnion> flod F) k"
  shows "content data (include_entry m e) F k = Map.empty"
proof -
  have lo: "elower (include_entry m e) = m" using am by (simp add: e truncate_top lattice_join_absorb2)
  have g: "group data m \<top> F k = {}" using keyimg_group_top[OF k] nk by simp
  have "group data (elower (include_entry m e)) (eupper (include_entry m e)) F k = {}"
    by (simp only: lo include_entry_simps(2) e g)
  then show ?thesis by (simp add: content_def cgraph_def efiber_def)
qed

definition gate_raise :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "gate_raise M E = \<lparr>emind = emind E \<squnion> M,
     edims = map (include_entry (emind E \<squnion> M)) (edims E),
     esem = \<lambda>data F k. if keyimg data F (emind E \<squnion> M \<squnion> flod F) k
       then esem E data (finclude (emind E \<squnion> M) F) k else None,
     csem = csem E\<rparr>"

lemma gate_raise_simps [simp]:
  "emind (gate_raise M E) = emind E \<squnion> M"
  "edims (gate_raise M E) = map (include_entry (emind E \<squnion> M)) (edims E)"
  "esem (gate_raise M E) data F k = (if keyimg data F (emind E \<squnion> M \<squnion> flod F) k
       then esem E data (finclude (emind E \<squnion> M) F) k else None)"
  "csem (gate_raise M E) = csem E"
  by (simp_all add: gate_raise_def)

theorem lawful_gate_raise:
  assumes ES: "semilawful E" and cov: "covering E"
  shows "lawful (gate_raise M E)"
proof -
  let ?m = "emind E \<squnion> M"
  obtain t where t: "t \<in> set (edims E)" "eupper t = \<top>" using cov by (auto simp: covering_def)
  have tm: "elower t \<sqsubseteq> ?m" by (rule below_trans[OF lower_below_mind[OF ES t(1)] lattice_join_ge1])
  have kdE: "emind E \<squnion> flod (finclude ?m F) = ?m \<squnion> flod F" for F
  proof -
    have "emind E \<sqsubseteq> flod F \<squnion> ?m" by (rule below_trans[OF lattice_join_ge1 lattice_join_ge2])
    then show ?thesis unfolding flod_finclude by (simp only: lattice_join_absorb2 lattice_join_commute)
  qed
  show ?thesis
  proof (rule lawfulI, simp_all only: gate_raise_simps)
    show "cstrict (gate_raise M E)"
      using semilawful_cstrict[OF ES] by (simp add: cstrict_def)
    show "entry_wf e" if "e \<in> set (map (include_entry ?m) (edims E))" for e
      using that by (auto intro: entry_wf_include_entry semilawful_wf[OF ES])
    show "(eupper e \<sqinter> ?m) \<sqsubseteq> elower e" if "e \<in> set (map (include_entry ?m) (edims E))" for e
      using that by (auto intro: lattice_join_ge2)
    show "?m = fold (\<squnion>) (map elower (map (include_entry ?m) (edims E))) \<bottom>"
    proof (rule below_antisym)
      have lo: "elower (include_entry ?m t) = ?m" using tm by (simp add: t(2) truncate_top lattice_join_absorb2)
      have "elower (include_entry ?m t) \<in> set (map elower (map (include_entry ?m) (edims E)))"
        using t(1) by simp
      then show "?m \<sqsubseteq> fold (\<squnion>) (map elower (map (include_entry ?m) (edims E))) \<bottom>"
        unfolding lo by (rule fold_join_upper)
      show "fold (\<squnion>) (map elower (map (include_entry ?m) (edims E))) \<bottom> \<sqsubseteq> ?m"
        by (rule fold_join_least)
          (auto intro: lattice_join_least[OF below_trans[OF lower_below_mind[OF ES] lattice_join_ge1] truncate_below])
    qed
    show "keyimg data F (?m \<squnion> flod F) k"
      if "conforms data" and "(if keyimg data F (?m \<squnion> flod F) k then esem E data (finclude ?m F) k else None) \<noteq> None"
      for data F k
      using that by (simp split: if_splits)
    show "(if keyimg data F (?m \<squnion> flod F) k then esem E data (finclude ?m F) k else None)
        = csem E\<cdot>(contents data (map (include_entry ?m) (edims E)) F k)"
      if d: "conforms data" and k: "proj (?m \<squnion> flod F)\<cdot>k = k" for data F k
    proof -
      have c: "contents data (map (include_entry ?m) (edims E)) F k = contents data (edims E) (finclude ?m F) k"
        by (simp add: comp_def content_include_entry)
      have "proj (emind E \<squnion> flod (finclude ?m F))\<cdot>k = k" by (simp only: kdE k)
      then have v: "esem E data (finclude ?m F) k = csem E\<cdot>(contents data (map (include_entry ?m) (edims E)) F k)"
        by (simp only: c semilawful_csem[OF ES d])
      show ?thesis
      proof (cases "keyimg data F (?m \<squnion> flod F) k")
        case False
        have "Map.empty \<in> set (contents data (map (include_entry ?m) (edims E)) F k)"
          using content_include_top[OF t(2) tm k False] t(1) by force
        then have "csem E\<cdot>(contents data (map (include_entry ?m) (edims E)) F k) = None"
          by (rule cstrictD[OF semilawful_cstrict[OF ES], rotated]) simp
        then show ?thesis using False by simp
      qed (simp add: v)
    qed
  qed
qed

text \<open>The gate at \<open>M\<close>: raising alone for covering expressions, else with a presence entry.\<close>

definition gate :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "gate M E = (if covering E then gate_raise M E else gate_presence M E)"

lemma gate_simps [simp]:
  "emind (gate M E) = emind E \<squnion> M"
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
  by (simp add: include_entry_def lattice_join_absorb1)

lemma include_entry_idem: "include_entry m (include_entry m e) = include_entry m e"
  by (rule include_entry_saturated) (simp add: lattice_join_ge2)

lemma covering_gate: "covering (gate M E)"
proof (cases "covering E")
  case True
  then obtain t where "t \<in> set (edims E)" "eupper t = \<top>" by (auto simp: covering_def)
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
  have head: "include_entry ?m (mk_entry (sel ?m \<top>) gtrue \<bottom>) = mk_entry (sel ?m \<top>) gtrue \<bottom>"
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

lemma cont_collect_csem: "cont (\<lambda>Xs. those (map2 (\<lambda>E Ys. csem E\<cdot>Ys) Es (blocks ns Xs)))"
proof -
  have "cont (\<lambda>Xs. map2 (\<lambda>E Ys. csem E\<cdot>Ys) Es (blocks ns Xs))"
    by (rule cont_compose[OF cont_map2 cont_blocks]) simp
  then show ?thesis by (rule cont_compose[OF cont_those])
qed

definition collect :: "('k, 'f, 'r, 'a::cpo) expr list \<Rightarrow> ('k, 'f, 'r, 'a list) expr" where
  "collect Es = \<lparr>emind = fold (\<squnion>) (map emind Es) \<bottom>, edims = concat (map edims Es),
     esem = \<lambda>data F k. those (map (\<lambda>E. esem E data F (proj (kd E F)\<cdot>k)) Es),
     csem = \<Lambda> Xs. those (map2 (\<lambda>E Ys. csem E\<cdot>Ys) Es (blocks (map (\<lambda>E. length (edims E)) Es) Xs))\<rparr>"

lemma collect_simps [simp]:
  "emind (collect Es) = fold (\<squnion>) (map emind Es) \<bottom>"
  "edims (collect Es) = concat (map edims Es)"
  "esem (collect Es) data F k = those (map (\<lambda>E. esem E data F (proj (kd E F)\<cdot>k)) Es)"
  "csem (collect Es)\<cdot>Xs = those (map2 (\<lambda>E Ys. csem E\<cdot>Ys) Es (blocks (map (\<lambda>E. length (edims E)) Es) Xs))"
  by (simp_all add: collect_def cont_collect_csem)

text \<open>The contents of a semilawful expression only see the key at its own key LOD.\<close>

lemma contents_own_key:
  assumes E: "semilawful E"
  shows "contents data (edims E) F (proj (kd E F)\<cdot>k) = contents data (edims E) F k"
proof (rule map_cong[OF refl])
  fix e assume e: "e \<in> set (edims E)"
  have "proj (sel_at (esel e) (flod F))\<cdot>(proj (kd E F)\<cdot>k) = proj (sel_at (esel e) (flod F))\<cdot>k"
    by (rule proj_le[OF group_below_kd[OF E e]])
  then show "content data e F (proj (kd E F)\<cdot>k) = content data e F k"
    by (intro content_group_cong) (simp add: group_def)
qed

lemma collect_blocks_strict:
  assumes "\<And>E. E \<in> set Es \<Longrightarrow> cstrict E" and "length Xs = sum_list (map (\<lambda>E. length (edims E)) Es)"
    and "those (map2 (\<lambda>E Ys. csem E\<cdot>Ys) Es (blocks (map (\<lambda>E. length (edims E)) Es) Xs)) \<noteq> None"
  shows "Map.empty \<notin> set Xs"
  using assms
proof (induct Es arbitrary: Xs)
  case (Cons E Es)
  let ?n = "length (edims E)"
  have t: "csem E\<cdot>(take ?n Xs) \<noteq> None"
    and r: "those (map2 (\<lambda>E Ys. csem E\<cdot>Ys) Es (blocks (map (\<lambda>E. length (edims E)) Es) (drop ?n Xs))) \<noteq> None"
    using Cons.prems(3) by (auto split: option.splits)
  have "Map.empty \<notin> set (take ?n Xs)"
    using cstrictD[OF Cons.prems(1)[of E] _] t Cons.prems(2) by force
  moreover have "Map.empty \<notin> set (drop ?n Xs)"
    by (rule Cons.hyps) (use Cons.prems(1,2) r in auto)
  ultimately show ?case using set_append[of "take ?n Xs" "drop ?n Xs"] by auto
qed simp

lemma cstrict_collect: "(\<And>E. E \<in> set Es \<Longrightarrow> cstrict E) \<Longrightarrow> cstrict (collect Es)"
  by (rule cstrictI) (auto intro: collect_blocks_strict[THEN notE] simp: length_concat comp_def)

theorem semilawful_collect:
  assumes law: "\<And>E. E \<in> set Es \<Longrightarrow> semilawful E"
  shows "semilawful (collect Es)"
proof (rule semilawfulI, simp_all only: collect_simps)
  show "cstrict (collect Es)" by (rule cstrict_collect[OF semilawful_cstrict[OF law]])
  show "entry_wf e" if "e \<in> set (concat (map edims Es))" for e
    using that by (auto intro: semilawful_wf[OF law])
  show "fold (\<squnion>) (map emind Es) \<bottom> = fold (\<squnion>) (map elower (concat (map edims Es))) \<bottom>"
  proof (rule below_antisym)
    let ?R = "fold (\<squnion>) (map elower (concat (map edims Es))) \<bottom>"
    show "fold (\<squnion>) (map emind Es) \<bottom> \<sqsubseteq> ?R"
    proof (rule fold_join_least)
      fix x assume "x \<in> set (map emind Es)"
      then obtain E where E: "E \<in> set Es" and x: "x = emind E" by auto
      show "x \<sqsubseteq> ?R" unfolding x semilawful_mind_lub[OF law[OF E]]
      proof (rule fold_join_least)
        fix a assume "a \<in> set (map elower (edims E))"
        then show "a \<sqsubseteq> ?R" by (intro fold_join_upper) (use E in force)
      qed simp
    qed simp
    show "?R \<sqsubseteq> fold (\<squnion>) (map emind Es) \<bottom>"
    proof (rule fold_join_least)
      fix a assume "a \<in> set (map elower (concat (map edims Es)))"
      then obtain E e where E: "E \<in> set Es" and e: "e \<in> set (edims E)" and a: "a = elower e" by auto
      show "a \<sqsubseteq> fold (\<squnion>) (map emind Es) \<bottom>"
        unfolding a by (rule below_trans[OF lower_below_mind[OF law[OF E] e] fold_join_upper]) (simp add: E)
    qed simp
  qed
  show "those (map (\<lambda>E. esem E data F (proj (kd E F)\<cdot>k)) Es)
      = those (map (\<lambda>(E, Ys). csem E\<cdot>Ys)
          (zip Es (blocks (map (\<lambda>E. length (edims E)) Es) (contents data (concat (map edims Es)) F k))))"
    if d: "conforms data" for data F k
  proof -
    have c: "contents data (concat (map edims Es)) F k = concat (map (\<lambda>E. contents data (edims E) F k) Es)"
      by (simp add: map_concat comp_def)
    have b: "blocks (map (\<lambda>E. length (edims E)) Es) (contents data (concat (map edims Es)) F k)
        = map (\<lambda>E. contents data (edims E) F k) Es"
      using blocks_concat[of "\<lambda>E. contents data (edims E) F k" Es] by (simp only: c length_map)
    have z: "map (\<lambda>(E, Ys). csem E\<cdot>Ys) (zip Es (map (\<lambda>E. contents data (edims E) F k) Es))
        = map (\<lambda>E. csem E\<cdot>(contents data (edims E) F k)) Es"
      by (induct Es) simp_all
    have "esem E data F (proj (kd E F)\<cdot>k) = csem E\<cdot>(contents data (edims E) F k)" if E: "E \<in> set Es" for E
      by (simp only: semilawful_csem[OF law[OF E] d proj_idem] contents_own_key[OF law[OF E]])
    then show ?thesis by (simp only: b z cong: map_cong)
  qed
qed

end

end
