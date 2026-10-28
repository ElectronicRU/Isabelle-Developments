theory Aggregate
  imports Content_Law
begin

section \<open>Aggregation\<close>

text \<open>An aggregate folds the entries of an inner expression over each fiber of the frame's LOD
  with a commutative semigroup operation.  The fold adjoins a unit for the empty fiber, which
  gives no entry; it is not \<open>\<bottom>\<close>: a monotone operation with unit \<open>\<bottom>\<close> would be inflationary
  (\<open>x = x \<oplus> \<bottom> \<sqsubseteq> x \<oplus> y\<close>), which rules out sums on flat values.\<close>

abbreviation opt_op :: "('v::pcpo \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> 'v option \<Rightarrow> 'v option \<Rightarrow> 'v option" where
  "opt_op f \<equiv> combine_options (\<lambda>a b. f\<cdot>a\<cdot>b)"

lemma comm_monoid_opt_op:
  assumes "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
  shows "comm_monoid (opt_op f) None"
proof -
  interpret abel_semigroup "\<lambda>a b. f\<cdot>a\<cdot>b" by (fact assms)
  show ?thesis by standard (auto simp: combine_options_def assoc commute left_commute split: option.splits)
qed

definition agg_fold :: "('v::pcpo \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('a \<rightharpoonup> 'v) \<Rightarrow> 'a set \<Rightarrow> 'v option" where
  "agg_fold f v A = comm_monoid_set.F (opt_op f) None v A"

context
  fixes f :: "'v::pcpo \<rightarrow> 'v \<rightarrow> 'v"
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
begin

interpretation agg: comm_monoid_set "opt_op f" None
  unfolding comm_monoid_set_def by (rule comm_monoid_opt_op[OF f])

lemma agg_fold_empty: "agg_fold f v {} = None"
  by (simp add: agg_fold_def)

lemma agg_fold_singleton: "agg_fold f v {a} = v a"
  by (simp add: agg_fold_def)

lemma agg_fold_nonempty: "agg_fold f v A \<noteq> None \<Longrightarrow> A \<noteq> {}"
  by (auto simp: agg_fold_empty)

lemma agg_fold_present: "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> v a \<noteq> None \<Longrightarrow> agg_fold f v A \<noteq> None"
  unfolding agg_fold_def by (subst agg.remove) (auto simp: combine_options_def split: option.splits)

lemma agg_fold_absent: "(\<And>a. a \<in> A \<Longrightarrow> v a = None) \<Longrightarrow> agg_fold f v A = None"
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

lemma cont_opt_op:
  assumes u: "cont u" and w: "cont w"
  shows "cont (\<lambda>x. opt_op f (u x) (w x))"
  unfolding combine_options_def
proof (rule cont2cont_case_option[OF u w])
  fix a show "cont (\<lambda>x. case w x of None \<Rightarrow> Some a | Some y \<Rightarrow> Some (f\<cdot>a\<cdot>y))"
    by (rule cont2cont_case_option[OF w]) simp_all
next
  fix x show "cont (\<lambda>a. case w x of None \<Rightarrow> Some a | Some y \<Rightarrow> Some (f\<cdot>a\<cdot>y))" by simp
qed

lemma cont_agg_fold:
  assumes v: "\<And>a. cont (\<lambda>x. v x a)"
  shows "cont (\<lambda>x. agg_fold f (v x) A)"
proof (cases "finite A")
  case True
  then show ?thesis
  proof (induct A rule: finite_induct)
    case (insert a A)
    have "agg.F (v x) (insert a A) = opt_op f (v x a) (agg.F (v x) A)" for x by (rule agg.insert[OF insert(1,2)])
    then show ?case unfolding agg_fold_def by (simp only:) (rule cont_opt_op[OF v insert(3)[unfolded agg_fold_def]])
  qed (simp add: agg_fold_def)
qed (simp add: agg_fold_def)

end

lemma agg_fold_bij:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and h: "bij_betw h A B"
  shows "agg_fold f (v \<circ> h) A = agg_fold f v B"
proof -
  interpret agg: comm_monoid_set "opt_op f" None
    unfolding comm_monoid_set_def by (rule comm_monoid_opt_op[OF f])
  show ?thesis unfolding agg_fold_def comp_def by (rule agg.reindex_bij_betw[OF h])
qed

context dataspace
begin

text \<open>The rows of a frame in the fiber of a key at an LOD.\<close>

definition afiber :: "'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor \<Rightarrow> 'k \<Rightarrow> 'r set" where
  "afiber data F c k = {y \<in> lower_maximal data. frows F y \<and> rproj c y = k}"

text \<open>\<open>aggregate f E\<close> folds the inner values over the inner keys below each key of the frame.
  The inner keys are those where the inner expression is present: its own domain, so for a lawful
  inner expression they are data keys.  Grouping finer than the frame is the inner expression's own
  (a gate at the requested dimensions).  The aggregate's keys are the frame's, so it decides no
  detail: its entries are the inner ones released (their lower parts move into their views' key
  parts), and the fold reads the fiber's classes at \<open>emind E\<close>.\<close>

definition inner_keys :: "('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> 'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'k set" where
  "inner_keys E data F k = {\<kappa>. proj (kd E F)\<cdot>\<kappa> = \<kappa> \<and> proj (flod F)\<cdot>\<kappa> = k \<and> esem E data F \<kappa> \<noteq> None}"

text \<open>For a lawful inner expression at a conforming dataset, its keys below \<open>k\<close> are the defined ones
  among the inner keys of the fiber of \<open>k\<close>.\<close>

lemma inner_keys_fiber:
  assumes EL: "lawful E" and d: "fconf (edims E) data F"
  shows "inner_keys E data F k = {\<kappa> \<in> rproj (kd E F) ` afiber data F (flod F) k. esem E data F \<kappa> \<noteq> None}"
proof -
  let ?X = "kd E F"
  have le: "flod F \<sqsubseteq> ?X" by (rule lattice_join_ge2)
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix \<kappa> assume "\<kappa> \<in> inner_keys E data F k"
    then have kfix: "proj ?X\<cdot>\<kappa> = \<kappa>" and below: "proj (flod F)\<cdot>\<kappa> = k" and kdef: "esem E data F \<kappa> \<noteq> None"
      by (simp_all add: inner_keys_def)
    obtain x where x: "x \<in> lower_maximal data" "frows F x" and kx: "\<kappa> = rproj ?X x"
      using lawful_key_law_conf[OF EL d kdef] by (auto simp: keyimg_def)
    have "rproj (flod F) x = k" using below unfolding kx by (simp only: proj_le[OF le])
    then show "\<kappa> \<in> {\<kappa> \<in> rproj ?X ` afiber data F (flod F) k. esem E data F \<kappa> \<noteq> None}"
      using x kx kdef by (auto simp: afiber_def)
  next
    fix \<kappa> assume "\<kappa> \<in> {\<kappa> \<in> rproj ?X ` afiber data F (flod F) k. esem E data F \<kappa> \<noteq> None}"
    then obtain x where x: "x \<in> afiber data F (flod F) k" and kx: "\<kappa> = rproj ?X x"
      and kdef: "esem E data F \<kappa> \<noteq> None" by blast
    have "rproj (flod F) x = k" using x by (simp add: afiber_def)
    then have "proj (flod F)\<cdot>\<kappa> = k" unfolding kx by (simp only: proj_le[OF le])
    then show "\<kappa> \<in> inner_keys E data F k" using kdef by (simp add: inner_keys_def kx)
  qed
qed

text \<open>An inner entry, seen from outside the aggregate, is \<^emph>\<open>released\<close>: its lower part, which the
  inner key fixes, moves into its view's key part, so the outer content is keyed by the inner keys
  as well.\<close>

definition release :: "('k, 'r) entry \<Rightarrow> ('k, 'r) entry" where
  "release e = e\<lparr>esel := sel \<bottom> (eupper e), eview := (ecols e, ekeys e \<squnion> elower e)\<rparr>"

lemma release_simps [simp]:
  "elower (release e) = \<bottom>" "eupper (release e) = eupper e"
  "eguard (release e) = eguard e" "eview (release e) = (ecols e, ekeys e \<squnion> elower e)"
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

context
  fixes e :: "('k, 'r) entry"
begin

text \<open>Let \<open>X\<close> be the content of the released entry \<open>e\<close>, keyed at \<open>ekeys e \<squnion> elower e\<close>, and \<open>p\<close> an
  inner key.  The inner fiber at \<open>p\<close> is the \<^emph>\<open>slice\<close> of the outer one where the lower part agrees
  with \<open>p\<close>; within it the lower part is constant, so an inner key \<open>q\<close> (at \<open>ekeys e\<close>) has as
  \<^emph>\<open>sources\<close> the outer keys in the slice whose \<open>ekeys e\<close>-part is \<open>q\<close>.  The inner content takes the
  value at the one source, and drops \<open>q\<close> when there is none or more than one.  Which keys collide is
  decided by the domain alone, so the read is continuous; on contents of data nothing collides.\<close>

definition agg_src :: "'k \<Rightarrow> ('k \<Rightarrow> 'r option) \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> bool" where
  "agg_src p X q q0 \<longleftrightarrow> q0 \<in> dom X \<and> proj (elower e)\<cdot>q0 = proj (elower e)\<cdot>p \<and> proj (ekeys e)\<cdot>q0 = q"

definition agg_pick :: "'k \<Rightarrow> ('k \<Rightarrow> 'r option) \<Rightarrow> 'k \<Rightarrow> 'r option" where
  "agg_pick p X q = (if \<exists>!q0. agg_src p X q q0 then X (THE q0. agg_src p X q q0) else None)"

lemma rigid_agg_src: "rigid (\<lambda>X. agg_src p X q)"
  by (rule rigidI) (simp add: fun_eq_iff agg_src_def map_below_dom)

lemma cont_agg_pick: "cont (agg_pick p)"
proof -
  have "cont (\<lambda>X. agg_pick p X q)" for q
    unfolding agg_pick_def
  proof (rule cont_if_rigid)
    have src: "agg_src p X q = agg_src p Y q" if "X \<sqsubseteq> Y" for X Y
      by (rule rigidD[OF rigid_agg_src that])
    show "rigid (\<lambda>X. \<exists>!q0. agg_src p X q q0)" by (rule rigidI) (simp only: src)
    have "rigid (\<lambda>X. THE q0. agg_src p X q q0)" by (rule rigidI) (simp only: src)
    then show "cont (\<lambda>X. X (THE q0. agg_src p X q q0))"
      by (rule cont_rigid_arg[where h = "\<lambda>X s. X s", rotated]) (simp add: cont2cont_fun)
  qed simp
  then have "cont (\<lambda>X. \<lambda>q. agg_pick p X q)" by (rule cont2cont_lambda)
  then show ?thesis by simp
qed

end

definition agg_inner :: "('k, 'r) entry list \<Rightarrow> ('k \<Rightarrow> 'r option) list \<Rightarrow> 'k \<Rightarrow> ('k \<Rightarrow> 'r option) list" where
  "agg_inner es Xs p = map2 (\<lambda>e X. agg_pick e p X) es Xs"

lemma cont_agg_inner: "cont (\<lambda>Xs. agg_inner es Xs p)"
  unfolding agg_inner_def by (rule cont_map2) (simp add: cont_agg_pick[unfolded eta_cfun])

text \<open>The content semantics folds the inner content semantics over the fold entry's keys, reading
  the inner contents at each off the outer ones.\<close>

definition agg_csem :: "('v::pcpo \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k, 'f, 'r, 'v) expr \<Rightarrow> ('k \<Rightarrow> 'r option) list \<Rightarrow> 'v option" where
  "agg_csem f E Xs = agg_fold f (\<lambda>p. csem E\<cdot>(agg_inner (edims E) (tl Xs) p))
     {p \<in> dom (hd Xs). csem E\<cdot>(agg_inner (edims E) (tl Xs) p) \<noteq> None}"

text \<open>It is continuous: the fold's index set is rigid (the fold entry's keys, and the inner keys
  present), and the fold is continuous in the values.\<close>

lemma cont_agg_csem:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
  shows "cont (agg_csem f E)"
proof -
  let ?\<Phi> = "\<lambda>Xs p. csem E\<cdot>(agg_inner (edims E) (tl Xs) p)"
  have \<Phi>: "cont (\<lambda>Xs. ?\<Phi> Xs p)" for p by (simp add: cont_compose[OF cont_agg_inner cont_tl])
  have S: "rigid (\<lambda>Xs. {p \<in> dom (hd Xs). ?\<Phi> Xs p \<noteq> None})"
  proof (rule rigidI)
    fix Xs Ys :: "('k \<Rightarrow> 'r option) list" assume b: "Xs \<sqsubseteq> Ys"
    have n: "?\<Phi> Xs p = None \<longleftrightarrow> ?\<Phi> Ys p = None" for p
      by (rule option_below_None[OF cont2monofunE[OF \<Phi> b]])
    have d: "dom (hd Xs) = dom (hd Ys)" by (rule map_below_dom[OF hd_mono[OF b]])
    show "{p \<in> dom (hd Xs). ?\<Phi> Xs p \<noteq> None} = {p \<in> dom (hd Ys). ?\<Phi> Ys p \<noteq> None}"
      by (simp only: d n)
  qed
  show ?thesis unfolding agg_csem_def
    by (rule cont_rigid_arg[OF _ S, where h = "\<lambda>Xs A. agg_fold f (?\<Phi> Xs) A"]) (rule cont_agg_fold[OF f \<Phi>])
qed

lemma map2_map: "map2 g xs (map h xs) = map (\<lambda>x. g x (h x)) xs"
  by (induct xs) simp_all

definition aggregate :: "('v::pcpo \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k, 'f, 'r, 'v) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "aggregate f E = \<lparr>emind = \<bottom>,
     edims = mk_entry (sel \<bottom> \<top>) gtrue (\<bottom>, emind E) # map release (edims E),
     esem = \<lambda>data F k. agg_fold f (esem E data F) (inner_keys E data F k),
     csem = \<Lambda> Xs. agg_csem f E Xs\<rparr>"

lemma aggregate_simps [simp]:
  "emind (aggregate f E) = \<bottom>"
  "edims (aggregate f E) = mk_entry (sel \<bottom> \<top>) gtrue (\<bottom>, emind E) # map release (edims E)"
  "esem (aggregate f E) data F k = agg_fold f (esem E data F) (inner_keys E data F k)"
  "csem (aggregate f E) = (\<Lambda> Xs. agg_csem f E Xs)"
  by (simp_all add: aggregate_def)

lemma aggregate_csem: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b) \<Longrightarrow> csem (aggregate f E)\<cdot>Xs = agg_csem f E Xs"
  by (simp add: cont_agg_csem)

subsection \<open>Lawfulness\<close>

text \<open>The fold entry reads the fiber.\<close>

lemma agg_fiber: "proj (flod F)\<cdot>k = k \<Longrightarrow> group data \<bottom> \<top> F k = afiber data F (flod F) k"
  by (simp add: group_top[of \<bottom>, simplified] afiber_def)

text \<open>An inner group is the outer group through the same upper part, cut down by the inner key's
  lower part.\<close>

lemma agg_group:
  assumes y: "rproj (flod F) y = k" and am: "a \<sqsubseteq> m"
  shows "group data a \<rho> F (rproj (m \<squnion> flod F) y) = {y' \<in> group data \<bottom> \<rho> F k. rproj a y' = rproj a y}"
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
  show ?thesis unfolding group_def proj_sup_eq kA kL by (auto simp: proj_bot)
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

text \<open>The content of an inner entry at an inner key is read off the released entry's content.\<close>

lemma agg_content_inner:
  assumes ES: "semilawful E" and e: "e \<in> set (edims E)" and d: "fconf (edims E) data G"
    and yZ: "y \<in> afiber data G (flod G) kG"
    and \<kappa>: "\<kappa> = rproj (emind E \<squnion> flod G) y" and py: "proj (emind E)\<cdot>\<kappa> = p"
  shows "content data e G \<kappa> = agg_pick e p (content data (release e) G kG)"
proof
  fix q
  let ?a = "elower e" and ?s = "ekeys e" and ?m = "emind E"
  let ?Y = "efiber data (release e) G kG" and ?X = "content data (release e) G kG"
  let ?P = "agg_src e p ?X q"
  have am: "?a \<sqsubseteq> ?m" by (rule lower_below_mind[OF ES e])
  have yA: "rproj ?a y = proj ?a\<cdot>p"
  proof -
    have "proj ?a\<cdot>p = proj ?a\<cdot>\<kappa>" unfolding py[symmetric] by (rule proj_le[OF am])
    also have "\<dots> = rproj ?a y" unfolding \<kappa> by (rule proj_le[OF below_trans[OF am lattice_join_ge1]])
    finally show ?thesis by simp
  qed
  have gy: "rproj (flod G) y = kG" using yZ by (simp add: afiber_def)
  have fib: "efiber data e G \<kappa> = {y' \<in> ?Y. rproj ?a y' = proj ?a\<cdot>p}"
    unfolding efiber_def \<kappa> agg_group[OF gy am] yA by auto
  have cpr: "cpair (release e) y' = (rproj (?s \<squnion> ?a) y', y' \<downharpoonright> ecols e)" for y' by (simp add: cpair_def)
  have dX: "dom ?X = (\<lambda>y'. rproj (?s \<squnion> ?a) y') ` ?Y" by (simp add: content_def cgraph_def cpr image_image)
  have pa: "proj ?a\<cdot>(rproj (?s \<squnion> ?a) y') = rproj ?a y'" for y' by (rule proj_le[OF lattice_join_ge2])
  have ps: "proj ?s\<cdot>(rproj (?s \<squnion> ?a) y') = rproj ?s y'" for y' by (rule proj_le[OF lattice_join_ge1])
  have wf: "entry_wf e" by (rule semilawful_wf[OF ES e])
  have ce: "entry_conf e data G" using d e by (simp add: fconf_def)
  then have ce': "entry_conf (release e) data G" by (simp add: entry_conf_def lattice_join_ac)
  have svR: "single_valued (cgraph data (release e) G kG)" by (rule cgraph_single_valued_conf[OF ce'])
  have svE: "single_valued (cgraph data e G \<kappa>)" by (rule cgraph_single_valued_conf[OF ce])
  show "content data e G \<kappa> q = agg_pick e p ?X q"
  proof (cases "\<exists>y'\<in>efiber data e G \<kappa>. rproj ?s y' = q")
    case True
    then obtain y' where y': "y' \<in> efiber data e G \<kappa>" "rproj ?s y' = q" by blast
    have yY: "y' \<in> ?Y" and ya: "rproj ?a y' = proj ?a\<cdot>p" using y'(1) fib by auto
    let ?q0 = "rproj (?s \<squnion> ?a) y'"
    have src: "?P ?q0" unfolding agg_src_def dX using yY ya y'(2) by (auto simp: pa ps)
    have uniq: "q1 = ?q0" if q1: "?P q1" for q1
    proof -
      obtain y1 where y1: "y1 \<in> ?Y" "q1 = rproj (?s \<squnion> ?a) y1" using q1 unfolding agg_src_def dX by blast
      have "rproj ?a y1 = rproj ?a y'" using q1 ya unfolding agg_src_def y1(2) pa by simp
      moreover have "rproj ?s y1 = rproj ?s y'" using q1 y'(2) unfolding agg_src_def y1(2) ps by simp
      ultimately show ?thesis unfolding y1(2) by (simp only: rproj_sup_eq)
    qed
    have ex1: "\<exists>!q0. ?P q0" using src uniq by blast
    have th: "(THE q0. ?P q0) = ?q0" using src uniq by blast
    have "(?q0, y' \<downharpoonright> ecols e) \<in> cgraph data (release e) G kG"
      unfolding cgraph_def using yY by (force simp: cpr)
    then have Xq0: "?X ?q0 = Some (y' \<downharpoonright> ecols e)" unfolding content_def by (rule gmap_apply[OF svR])
    have "(q, y' \<downharpoonright> ecols e) \<in> cgraph data e G \<kappa>"
      unfolding cgraph_def using y' by (force simp: cpair_def)
    then have Cq: "content data e G \<kappa> q = Some (y' \<downharpoonright> ecols e)" unfolding content_def by (rule gmap_apply[OF svE])
    show ?thesis unfolding agg_pick_def using ex1 th Xq0 Cq by simp
  next
    case False
    have Cq: "content data e G \<kappa> q = None"
      unfolding content_def gmap_def using False by (auto simp: cgraph_def cpair_def)
    have no: "\<not> (\<exists>q0. ?P q0)"
    proof
      assume "\<exists>q0. ?P q0"
      then obtain q0 y1 where y1: "y1 \<in> ?Y" "q0 = rproj (?s \<squnion> ?a) y1"
        and s: "proj ?a\<cdot>q0 = proj ?a\<cdot>p" "proj ?s\<cdot>q0 = q" unfolding agg_src_def dX by blast
      have "y1 \<in> efiber data e G \<kappa>" "rproj ?s y1 = q" using y1 s fib by (auto simp: pa ps)
      then show False using False by blast
    qed
    show ?thesis unfolding agg_pick_def using no Cq by auto
  qed
qed

text \<open>The aggregate is strict: an empty fold entry leaves nothing to fold, and an empty inner
  entry makes every inner content semantics absent.\<close>

lemma agg_pick_empty: "agg_pick e p Map.empty = Map.empty"
  by (simp add: fun_eq_iff agg_pick_def agg_src_def)

lemma agg_inner_empty:
  "length Xs = length es \<Longrightarrow> Map.empty \<in> set Xs \<Longrightarrow> Map.empty \<in> set (agg_inner es Xs p)"
  unfolding agg_inner_def
proof (induct Xs es rule: list_induct2)
  case (Cons X Xs e es)
  then show ?case by (cases "X = Map.empty") (auto simp: agg_pick_empty)
qed simp

lemma cstrict_aggregate:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and E: "cstrict E"
  shows "cstrict (aggregate f E)"
proof (rule cstrictI)
  fix Xs :: "('k \<Rightarrow> 'r option) list"
  assume l: "length Xs = length (edims (aggregate f E))" and c: "csem (aggregate f E)\<cdot>Xs \<noteq> None"
  then obtain X Xs' where Xs: "Xs = X # Xs'" and l': "length Xs' = length (edims E)"
    by (auto simp: length_Suc_conv)
  let ?S = "{p \<in> dom X. csem E\<cdot>(agg_inner (edims E) Xs' p) \<noteq> None}"
  have ne: "?S \<noteq> {}"
  proof
    assume S: "?S = {}"
    have "agg_csem f E Xs = None" unfolding agg_csem_def Xs list.sel by (simp only: S agg_fold_empty[OF f])
    then show False using c[unfolded aggregate_csem[OF f]] by simp
  qed
  then have "X \<noteq> Map.empty" by auto
  moreover have "Map.empty \<notin> set Xs'"
  proof
    assume em: "Map.empty \<in> set Xs'"
    have "csem E\<cdot>(agg_inner (edims E) Xs' p) = None" for p
    proof (rule cstrictD[OF E])
      show "length (agg_inner (edims E) Xs' p) = length (edims E)" by (simp add: agg_inner_def l')
      show "Map.empty \<in> set (agg_inner (edims E) Xs' p)" by (rule agg_inner_empty[OF l' em])
    qed
    then show False using ne by simp
  qed
  ultimately show "Map.empty \<notin> set Xs" by (simp add: Xs)
qed

lemma fconf_release: "fconf (mk_entry (sel \<bottom> \<top>) gtrue (\<bottom>, m) # map release es) data F \<longleftrightarrow> fconf es data F"
  by (simp add: fconf_def entry_conf_def lattice_join_ac vfd_refl below_prod_def)

theorem lawful_aggregate:
  assumes EL: "lawful E" and f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
  shows "lawful (aggregate f E)"
proof -
  have ES: "semilawful E" by (rule lawful_semilawful[OF EL])
  let ?m = "emind E"
  let ?h = "mk_entry (sel \<bottom> \<top>) gtrue (\<bottom>, ?m) :: ('k, 'r) entry"
  note bij = agg_keys_bij[of ?m]
  show ?thesis
  proof (rule lawfulI, simp_all only: aggregate_simps)
    show "cstrict (aggregate f E)" by (rule cstrict_aggregate[OF f semilawful_cstrict[OF ES]])
    show "entry_wf e" if "e \<in> set (?h # map release (edims E))" for e
      using that by (auto intro: entry_wf_view keyed_view_key entry_wf_release semilawful_wf[OF ES])
    show "(eupper e \<sqinter> \<bottom>) \<sqsubseteq> elower e" if "e \<in> set (?h # map release (edims E))" for e
      using that by (auto simp: lattice_meet_bot_right)
    show "(\<bottom>::'k semi_factor) = fold (\<squnion>) (map elower (?h # map release (edims E))) \<bottom>"
    proof -
      have l: "map elower (?h # map release (edims E)) = map (\<lambda>_. \<bottom>) (?h # map release (edims E))"
        by simp
      show ?thesis by (simp only: l fold_join_bots)
    qed
    show "keyimg data F (\<bottom> \<squnion> flod F) k"
      if d0: "fconf (?h # map release (edims E)) data F" and "agg_fold f (esem E data F) (inner_keys E data F k) \<noteq> None" for data F k
    proof -
      have d: "fconf (edims E) data F" using d0 by (simp add: fconf_release)
      have "inner_keys E data F k \<noteq> {}" using agg_fold_nonempty[OF f that(2)] by auto
      then have "afiber data F (flod F) k \<noteq> {}" by (auto simp: inner_keys_fiber[OF EL d])
      then show ?thesis by (auto simp: afiber_def keyimg_def)
    qed
    show "agg_fold f (esem E data F) (inner_keys E data F k)
        = (\<Lambda> Xs. agg_csem f E Xs)\<cdot>(contents data (?h # map release (edims E)) F k)"
      if d0: "fconf (?h # map release (edims E)) data F" and k: "proj (\<bottom> \<squnion> flod F)\<cdot>k = k" for data F k
    proof -
      have d: "fconf (edims E) data F" using d0 by (simp add: fconf_release)
      have k1: "proj (flod F)\<cdot>k = k" using k by simp
      let ?Z = "afiber data F (flod F) k"
      let ?K = "rproj (?m \<squnion> flod F) ` ?Z"
      let ?P = "rproj ?m ` ?Z" and ?\<pi> = "Rep_cfun (proj ?m)"
      let ?v = "esem E data F"
      let ?X = "contents data (map release (edims E)) F k"
      let ?\<Phi> = "\<lambda>p. csem E\<cdot>(agg_inner (edims E) ?X p)"
      have hd: "dom (hd (contents data (?h # map release (edims E)) F k)) = ?P"
        by (simp add: content_def cgraph_def cpair_def efiber_def agg_fiber[OF k1] image_image)
      have tl: "tl (contents data (?h # map release (edims E)) F k) = ?X"
        by (simp only: list.map(2) list.sel(3))
      define \<psi> where "\<psi> = inv_into ?K ?\<pi>"
      have b: "bij_betw \<psi> ?P ?K" unfolding \<psi>_def by (rule bij_betw_inv_into[OF bij])
      have sP: "?\<pi> ` ?K = ?P" by (rule bij_betw_imp_surj_on[OF bij])
      have pt: "?\<Phi> p = ?v (\<psi> p)" if p: "p \<in> ?P" for p
      proof -
        have pK: "\<psi> p \<in> ?K" unfolding \<psi>_def by (rule inv_into_into) (simp only: sP p)
        obtain y where y: "y \<in> ?Z" "\<psi> p = rproj (?m \<squnion> flod F) y" using pK by blast
        have py: "proj ?m\<cdot>(\<psi> p) = p" unfolding \<psi>_def by (rule f_inv_into_f) (simp only: sP p)
        have "agg_inner (edims E) ?X p = map (\<lambda>e. agg_pick e p (content data (release e) F k)) (edims E)"
          unfolding agg_inner_def map_map map2_map by (simp add: comp_def)
        also have "\<dots> = contents data (edims E) F (\<psi> p)"
          by (rule map_cong[OF refl], rule agg_content_inner[OF ES _ d y(1) y(2) py, symmetric])
        finally have c: "agg_inner (edims E) ?X p = contents data (edims E) F (\<psi> p)" .
        have "proj (kd E F)\<cdot>(\<psi> p) = \<psi> p" by (simp only: y(2) proj_idem)
        then show ?thesis by (simp only: c semilawful_csem_conf[OF ES d])
      qed
      let ?Q = "{p \<in> ?P. ?v (\<psi> p) \<noteq> None}"
      have D: "inner_keys E data F k = \<psi> ` ?Q"
        unfolding inner_keys_fiber[OF EL d] bij_betw_imp_surj_on[OF b, symmetric] by auto
      have T: "{p \<in> ?P. ?\<Phi> p \<noteq> None} = ?Q" using pt by auto
      have bQ: "bij_betw \<psi> ?Q (\<psi> ` ?Q)"
        by (rule inj_on_imp_bij_betw[OF inj_on_subset[OF bij_betw_imp_inj_on[OF b]]]) blast
      have "agg_fold f ?v (\<psi> ` ?Q) = agg_fold f (?v \<circ> \<psi>) ?Q"
        by (rule agg_fold_bij[OF f bQ, symmetric])
      also have "\<dots> = agg_fold f ?\<Phi> ?Q"
      proof (rule agg_fold_cong[OF f refl])
        fix p assume "p \<in> ?Q"
        then show "(?v \<circ> \<psi>) p = ?\<Phi> p" by (simp only: comp_apply pt mem_Collect_eq)
      qed
      finally have "agg_fold f (esem E data F) (inner_keys E data F k)
          = agg_csem f E (contents data (?h # map release (edims E)) F k)"
        unfolding agg_csem_def hd tl T D .
      then show ?thesis by (simp only: beta_cfun[OF cont_agg_csem[OF f]])
    qed
  qed
qed

end

end
