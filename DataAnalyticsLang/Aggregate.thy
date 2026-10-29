theory Aggregate
  imports Content_Law
begin

section \<open>Aggregation\<close>

text \<open>An aggregate folds the entries of an inner expression over each fiber of the frame's LOD
  with a commutative semigroup operation.  The fold adjoins a unit for the empty fiber, which
  gives no entry; it is not \<open>\<bottom>\<close>: a monotone operation with unit \<open>\<bottom>\<close> would be inflationary
  (\<open>x = x \<oplus> \<bottom> \<sqsubseteq> x \<oplus> y\<close>), which rules out sums on flat values.\<close>

definition agg_fold :: "('v::bifinite \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('a \<Rightarrow> 'v option_pd) \<Rightarrow> 'a set \<Rightarrow> 'v option_pd" where
  "agg_fold f v A = comm_monoid_set.F (\<lambda>x y. combine_option_pd f\<cdot>x\<cdot>y) Absent v A"

context
  fixes f :: "'v::bifinite \<rightarrow> 'v \<rightarrow> 'v"
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
begin

interpretation agg: comm_monoid_set "\<lambda>x y. combine_option_pd f\<cdot>x\<cdot>y" Absent
  unfolding comm_monoid_set_def by (rule comm_monoid_combine_option_pd[OF f])

lemma agg_fold_empty: "agg_fold f v {} = Absent"
  by (simp add: agg_fold_def)

lemma agg_fold_singleton: "agg_fold f v {a} = v a"
  by (simp add: agg_fold_def)

lemma agg_fold_nonempty: "agg_fold f v A \<noteq> Absent \<Longrightarrow> A \<noteq> {}"
  by (auto simp: agg_fold_empty)

lemma agg_fold_absent: "(\<And>a. a \<in> A \<Longrightarrow> v a = Absent) \<Longrightarrow> agg_fold f v A = Absent"
  unfolding agg_fold_def by (rule agg.neutral) simp

lemma agg_fold_cong: "A = B \<Longrightarrow> (\<And>a. a \<in> B \<Longrightarrow> v a = w a) \<Longrightarrow> agg_fold f v A = agg_fold f w B"
  unfolding agg_fold_def by (simp cong: agg.cong)

text \<open>Folding over two images of one set of rows, identified alike, with the same entries.\<close>

lemma agg_fold_image_cong:
  assumes "\<And>y z. y \<in> Z \<Longrightarrow> z \<in> Z \<Longrightarrow> g y = g z \<longleftrightarrow> g' y = g' z"
    and "\<And>y. y \<in> Z \<Longrightarrow> v (g y) = w (g' y)"
  shows "agg_fold f v (g ` Z) = agg_fold f w (g' ` Z)"
  unfolding agg_fold_def
proof (rule agg.reindex_bij_witness[where i = "\<lambda>b. g (SOME y. y \<in> Z \<and> g' y = b)"
      and j = "\<lambda>a. g' (SOME y. y \<in> Z \<and> g y = a)"])
  fix a assume "a \<in> g ` Z"
  then obtain y where y: "y \<in> Z" "g y = a" by blast
  let ?y = "SOME y. y \<in> Z \<and> g y = a"
  have y': "?y \<in> Z" "g ?y = a" using someI[of "\<lambda>y. y \<in> Z \<and> g y = a", OF conjI[OF y]] by simp_all
  let ?z = "SOME z. z \<in> Z \<and> g' z = g' ?y"
  have z: "?z \<in> Z" "g' ?z = g' ?y" using someI[of "\<lambda>z. z \<in> Z \<and> g' z = g' ?y" ?y] y'(1) by simp_all
  show "g ?z = a" using assms(1)[OF z(1) y'(1)] z(2) y'(2) by simp
  show "g' ?y \<in> g' ` Z" using y'(1) by blast
  show "w (g' ?y) = v a" using assms(2)[OF y'(1)] y'(2) by simp
next
  fix b assume "b \<in> g' ` Z"
  then obtain y where y: "y \<in> Z" "g' y = b" by blast
  let ?y = "SOME y. y \<in> Z \<and> g' y = b"
  have y': "?y \<in> Z" "g' ?y = b" using someI[of "\<lambda>y. y \<in> Z \<and> g' y = b", OF conjI[OF y]] by simp_all
  let ?z = "SOME z. z \<in> Z \<and> g z = g ?y"
  have z: "?z \<in> Z" "g ?z = g ?y" using someI[of "\<lambda>z. z \<in> Z \<and> g z = g ?y" ?y] y'(1) by simp_all
  show "g' ?z = b" using assms(1)[OF z(1) y'(1)] z(2) y'(2) by simp
  show "g ?y \<in> g ` Z" using y'(1) by blast
qed

text \<open>The fold is continuous in the folded values.\<close>


lemma cont_agg_fold:
  assumes v: "\<And>a. cont (\<lambda>x. v x a)"
  shows "cont (\<lambda>x. agg_fold f (v x) A)"
proof (cases "finite A")
  case True
  then show ?thesis
  proof (induct A rule: finite_induct)
    case (insert a A)
    have "agg.F (v x) (insert a A) = combine_option_pd f\<cdot>(v x a)\<cdot>(agg.F (v x) A)" for x
      by (rule agg.insert[OF insert(1,2)])
    then show ?case unfolding agg_fold_def
      by (simp only:) (rule cont2cont_APP[OF cont2cont_APP[OF cont_const v] insert(3)[unfolded agg_fold_def]])
  qed (simp add: agg_fold_def)
qed (simp add: agg_fold_def)

end

lemma agg_fold_bij:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and h: "bij_betw h A B"
  shows "agg_fold f (v \<circ> h) A = agg_fold f v B"
proof -
  interpret agg: comm_monoid_set "\<lambda>x y. combine_option_pd f\<cdot>x\<cdot>y" Absent
    unfolding comm_monoid_set_def by (rule comm_monoid_combine_option_pd[OF f])
  show ?thesis unfolding agg_fold_def comp_def by (rule agg.reindex_bij_betw[OF h])
qed

context dataspace
begin

text \<open>The rows of a frame in the fiber of a key at an LOD.\<close>

definition afiber :: "'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor \<Rightarrow> 'k \<Rightarrow> 'r set" where
  "afiber data F c k = {y \<in> lower_maximal data. frows F y \<and> rproj c y = k}"

text \<open>\<open>aggregate f E\<close> folds the inner values over the inner keys below each key of the frame:
  the realised ones, the keys at the inner key LOD of the frame's rows below the key.  Where the
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

text \<open>A released guard's content is read off likewise: the inner keys are the key parts of the
  keys in the slice; a set of keys needs no uniqueness.\<close>

definition agg_gpick :: "('k, 'p) entry \<Rightarrow> 'k \<Rightarrow> 'k set \<Rightarrow> 'k set" where
  "agg_gpick e p G = {q. \<exists>q0\<in>G. proj (elower e)\<cdot>q0 = proj (elower e)\<cdot>p \<and> proj (ekeys e)\<cdot>q0 = q}"

definition agg_inner :: "('k, 'r semi_factor) entry list \<Rightarrow> ('k \<Rightarrow> 'r option) list \<Rightarrow> 'k \<Rightarrow> ('k \<Rightarrow> 'r option) list" where
  "agg_inner es Xs p = map2 (\<lambda>e X. agg_pick e p X) es Xs"

definition agg_ginner :: "('k, 'r guard) entry list \<Rightarrow> 'k set list \<Rightarrow> 'k \<Rightarrow> 'k set list" where
  "agg_ginner gs Gs p = map2 (\<lambda>e G. agg_gpick e p G) gs Gs"

lemma cont_agg_inner: "cont (\<lambda>Xs. agg_inner es Xs p)"
  unfolding agg_inner_def by (rule cont_map2) (simp add: cont_agg_pick[unfolded eta_cfun])

text \<open>The content semantics folds the inner content semantics over the fold guard's keys, reading
  the inner contents at each off the outer ones.\<close>

definition agg_csem :: "('v::bifinite \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k, 'f, 'r, 'v) expr \<Rightarrow> 'k set list \<Rightarrow> ('k \<Rightarrow> 'r option) list \<Rightarrow> 'v option_pd" where
  "agg_csem f E Gs Xs = agg_fold f (\<lambda>p. csem E (agg_ginner (eguards E) (tl Gs) p)\<cdot>(agg_inner (evalues E) Xs p)) (hd Gs)"

text \<open>It is continuous in the value contents: the fold's index set is the fold guard's keys, and
  the fold is continuous in the values.\<close>

lemma cont_agg_csem:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
  shows "cont (agg_csem f E Gs)"
  unfolding agg_csem_def[abs_def]
  by (rule cont_agg_fold[OF f]) (simp add: cont_compose[OF _ cont_agg_inner])

lemma map2_map: "map2 g xs (map h xs) = map (\<lambda>x. g x (h x)) xs"
  by (induct xs) simp_all

definition aggregate :: "('v::bifinite \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k, 'f, 'r, 'v) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "aggregate f E = \<lparr>emind = \<bottom>,
     eguards = mk_guard (sel \<bottom> \<top>) gtrue (emind E) # map release (eguards E),
     evalues = map release (evalues E),
     esem = \<lambda>data F k. agg_fold f (esem E data F) (inner_keys E data F k),
     csem = \<lambda>Gs. \<Lambda> Xs. agg_csem f E Gs Xs\<rparr>"

lemma aggregate_simps [simp]:
  "emind (aggregate f E) = \<bottom>"
  "eguards (aggregate f E) = mk_guard (sel \<bottom> \<top>) gtrue (emind E) # map release (eguards E)"
  "evalues (aggregate f E) = map release (evalues E)"
  "esem (aggregate f E) data F k = agg_fold f (esem E data F) (inner_keys E data F k)"
  "csem (aggregate f E) Gs = (\<Lambda> Xs. agg_csem f E Gs Xs)"
  by (simp_all add: aggregate_def)

lemma aggregate_csem: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b) \<Longrightarrow> csem (aggregate f E) Gs\<cdot>Xs = agg_csem f E Gs Xs"
  by (simp add: cont_agg_csem)

subsection \<open>Lawfulness\<close>

text \<open>The fold guard reads the fiber.\<close>

lemma agg_fiber: "proj (flod F)\<cdot>k = k \<Longrightarrow> group data \<bottom> \<top> F k = afiber data F (flod F) k"
  by (simp add: group_top[of \<bottom>, simplified] afiber_def)

text \<open>An inner fiber is the outer fiber through the same upper part, cut down by the inner key's
  lower part; likewise an inner group.\<close>

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

lemma agg_group:
  assumes y: "rproj (flod F) y = k" and am: "a \<sqsubseteq> m"
  shows "group data a \<rho> F (rproj (m \<squnion> flod F) y) = {y' \<in> group data \<bottom> \<rho> F k. rproj a y' = rproj a y}"
  by (auto simp: group_fiber agg_fiber_group[OF y am])

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
  part of an inner entry is \<open>p\<close>'s, and the inner fibers and groups at \<open>\<kappa>\<close> are the released ones cut
  down there.  A released key's parts are its row's.\<close>

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
  unfolding gfiber_def \<kappa> agg_group[OF agg_inner_row(1)[OF yZ \<kappa> py am] am] agg_inner_row(2)[OF yZ \<kappa> py am]
  by auto

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
  unfolding agg_gpick_def gcontent_def agg_gfiber_inner[OF yZ \<kappa> py lower_below_mind_guard[OF ES e]]
  by (auto simp: release_key_parts)

text \<open>The aggregate is strict: an empty fold guard leaves nothing to fold, and an empty inner
  guard makes every inner content semantics absent.\<close>

lemma agg_pick_empty: "agg_pick e p Map.empty = Map.empty"
  by (simp add: fun_eq_iff agg_pick_def agg_src_def)

lemma agg_gpick_empty: "agg_gpick e p {} = {}"
  by (simp add: agg_gpick_def)

lemma agg_ginner_empty:
  "length Gs = length gs \<Longrightarrow> {} \<in> set Gs \<Longrightarrow> {} \<in> set (agg_ginner gs Gs p)"
  unfolding agg_ginner_def
proof (induct Gs gs rule: list_induct2)
  case (Cons G Gs e gs)
  then show ?case by (cases "G = {}") (auto simp: agg_gpick_empty)
qed simp

lemma cstrict_aggregate:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and E: "cstrict E"
  shows "cstrict (aggregate f E)"
proof (rule cstrictI)
  fix Gs :: "'k set list" and Xs :: "('k \<Rightarrow> 'r option) list"
  assume l: "length Gs = length (eguards (aggregate f E))" and lx: "length Xs = length (evalues (aggregate f E))"
    and c: "csem (aggregate f E) Gs\<cdot>Xs \<noteq> Absent"
  then obtain G Gs' where Gs: "Gs = G # Gs'" and l': "length Gs' = length (eguards E)"
    by (auto simp: length_Suc_conv)
  have lx': "length Xs = length (evalues E)" using lx by simp
  let ?\<Phi> = "\<lambda>p. csem E (agg_ginner (eguards E) Gs' p)\<cdot>(agg_inner (evalues E) Xs p)"
  have "agg_fold f ?\<Phi> G \<noteq> Absent" using c unfolding aggregate_csem[OF f] agg_csem_def Gs list.sel .
  then have ne: "\<exists>p\<in>G. ?\<Phi> p \<noteq> Absent" using agg_fold_absent[OF f, of G ?\<Phi>] by metis
  then have "G \<noteq> {}" by auto
  moreover have "{} \<notin> set Gs'"
  proof
    assume em: "{} \<in> set Gs'"
    have "csem E (agg_ginner (eguards E) Gs' p)\<cdot>(agg_inner (evalues E) Xs p) = Absent" for p
    proof (rule cstrictD[OF E])
      show "length (agg_ginner (eguards E) Gs' p) = length (eguards E)" by (simp add: agg_ginner_def l')
      show "length (agg_inner (evalues E) Xs p) = length (evalues E)" by (simp add: agg_inner_def lx')
      show "{} \<in> set (agg_ginner (eguards E) Gs' p)" by (rule agg_ginner_empty[OF l' em])
    qed
    then show False using ne by simp
  qed
  ultimately show "{} \<notin> set Gs" by (simp add: Gs)
qed

lemma fconf_release: "fconf (map release es) data F \<longleftrightarrow> fconf es data F"
  by (simp add: fconf_def entry_conf_def lattice_join_ac)

theorem lawful_aggregate:
  assumes ES: "semilawful E" and f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
  shows "lawful (aggregate f E)"
proof -
  let ?m = "emind E"
  let ?h = "mk_guard (sel \<bottom> \<top>) gtrue ?m :: ('k, 'r guard) entry"
  let ?gs = "?h # map release (eguards E)" and ?vs = "map release (evalues E)"
  note bij = agg_keys_bij[of ?m]
  show ?thesis
  proof (rule lawfulI, simp_all only: aggregate_simps)
    show "cstrict (aggregate f E)" by (rule cstrict_aggregate[OF f semilawful_cstrict[OF ES]])
    show "entry_wf e" if "e \<in> set ?vs" for e
      using that by (auto intro: entry_wf_release semilawful_wf[OF ES])
    show "(\<bottom>::'k semi_factor) = fold (\<squnion>) (map lower_part (map esel ?gs @ map esel ?vs)) \<bottom>"
    proof -
      have l: "map lower_part (map esel ?gs @ map esel ?vs) = map (\<lambda>_. \<bottom>) (map esel ?gs @ map esel ?vs)"
        by simp
      show ?thesis by (simp only: l fold_join_bots)
    qed
    show "keyimg data F (\<bottom> \<squnion> flod F) k"
      if d0: "fconf ?vs data F" and "agg_fold f (esem E data F) (inner_keys E data F k) \<noteq> Absent" for data F k
    proof -
      have d: "fconf (evalues E) data F" using d0 by (simp only: fconf_release)
      have "inner_keys E data F k \<noteq> {}" using agg_fold_nonempty[OF f that(2)] by auto
      then have "afiber data F (flod F) k \<noteq> {}" by (auto simp: inner_keys_def)
      then show ?thesis by (auto simp: afiber_def keyimg_def)
    qed
    show "agg_fold f (esem E data F) (inner_keys E data F k)
        = (\<Lambda> Xs. agg_csem f E (gcontents data ?gs F k) Xs)\<cdot>(contents data ?vs F k)"
      if d0: "fconf ?vs data F" and k: "proj (\<bottom> \<squnion> flod F)\<cdot>k = k" for data F k
    proof -
      have d: "fconf (evalues E) data F" using d0 by (simp only: fconf_release)
      have k1: "proj (flod F)\<cdot>k = k" using k by simp
      let ?Z = "afiber data F (flod F) k"
      let ?K = "rproj (?m \<squnion> flod F) ` ?Z"
      let ?P = "rproj ?m ` ?Z" and ?\<pi> = "Rep_cfun (proj ?m)"
      let ?v = "esem E data F"
      let ?G = "gcontents data (map release (eguards E)) F k"
      let ?X = "contents data ?vs F k"
      let ?\<Phi> = "\<lambda>p. csem E (agg_ginner (eguards E) ?G p)\<cdot>(agg_inner (evalues E) ?X p)"
      have hd: "hd (gcontents data ?gs F k) = ?P"
        by (simp add: gcontent_gtrue agg_fiber[OF k1])
      have tl: "tl (gcontents data ?gs F k) = ?G"
        by (simp only: list.map(2) list.sel(3))
      define \<psi> where "\<psi> = inv_into ?K ?\<pi>"
      have b: "bij_betw \<psi> ?P ?K" unfolding \<psi>_def by (rule bij_betw_inv_into[OF bij])
      have sP: "?\<pi> ` ?K = ?P" by (rule bij_betw_imp_surj_on[OF bij])
      have pt: "?\<Phi> p = ?v (\<psi> p)" if p: "p \<in> ?P" for p
      proof -
        have pK: "\<psi> p \<in> ?K" unfolding \<psi>_def by (rule inv_into_into) (simp only: sP p)
        obtain y where y: "y \<in> ?Z" "\<psi> p = rproj (?m \<squnion> flod F) y" using pK by blast
        have py: "proj ?m\<cdot>(\<psi> p) = p" unfolding \<psi>_def by (rule f_inv_into_f) (simp only: sP p)
        have "agg_ginner (eguards E) ?G p = map (\<lambda>e. agg_gpick e p (gcontent data (release e) F k)) (eguards E)"
          unfolding agg_ginner_def map_map map2_map by (simp add: comp_def)
        also have "\<dots> = gcontents data (eguards E) F (\<psi> p)"
          by (rule map_cong[OF refl], rule agg_gcontent_inner[OF ES _ y(1) y(2) py, symmetric])
        finally have g: "agg_ginner (eguards E) ?G p = gcontents data (eguards E) F (\<psi> p)" .
        have "agg_inner (evalues E) ?X p = map (\<lambda>e. agg_pick e p (content data (release e) F k)) (evalues E)"
          unfolding agg_inner_def map_map map2_map by (simp add: comp_def)
        also have "\<dots> = contents data (evalues E) F (\<psi> p)"
          by (rule map_cong[OF refl], rule agg_content_inner[OF ES _ d y(1) y(2) py, symmetric])
        finally have c: "agg_inner (evalues E) ?X p = contents data (evalues E) F (\<psi> p)" .
        have "proj (kd E F)\<cdot>(\<psi> p) = \<psi> p" by (simp only: y(2) proj_idem)
        then show ?thesis by (simp only: g c semilawful_csem_conf[OF ES d])
      qed
      have D: "inner_keys E data F k = ?K" by (simp only: inner_keys_def)
      have "agg_fold f ?v ?K = agg_fold f (?v \<circ> \<psi>) ?P"
        by (rule agg_fold_bij[OF f b, symmetric])
      also have "\<dots> = agg_fold f ?\<Phi> ?P"
      proof (rule agg_fold_cong[OF f refl])
        fix p assume "p \<in> ?P"
        then show "(?v \<circ> \<psi>) p = ?\<Phi> p" by (simp only: comp_apply pt)
      qed
      finally have "agg_fold f (esem E data F) (inner_keys E data F k)
          = agg_csem f E (gcontents data ?gs F k) ?X"
        unfolding agg_csem_def hd tl D .
      then show ?thesis by (simp only: beta_cfun[OF cont_agg_csem[OF f]])
    qed
  qed
qed

end

end
