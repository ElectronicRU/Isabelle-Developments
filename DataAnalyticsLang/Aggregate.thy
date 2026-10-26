theory Aggregate
  imports Content_Law
begin

section \<open>Aggregation\<close>

text \<open>An aggregate folds the entries of an inner expression over each fiber of the frame's LOD
  with a commutative semigroup operation.  The fold adjoins a unit for the empty fiber, which
  gives no entry; it is not \<open>\<bottom>\<close>: a monotone operation with unit \<open>\<bottom>\<close> would be inflationary
  (\<open>x = x \<oplus> \<bottom> \<sqsubseteq> x \<oplus> y\<close>), which rules out sums on flat values.\<close>

definition opt_op :: "('v::pcpo \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> 'v option \<Rightarrow> 'v option \<Rightarrow> 'v option" where
  "opt_op f a b = (case a of None \<Rightarrow> b | Some x \<Rightarrow> Some (case b of None \<Rightarrow> x | Some y \<Rightarrow> f\<cdot>x\<cdot>y))"

lemma comm_monoid_opt_op:
  assumes "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
  shows "comm_monoid (opt_op f) None"
proof -
  interpret abel_semigroup "\<lambda>a b. f\<cdot>a\<cdot>b" by (fact assms)
  show ?thesis
    by standard (auto simp: opt_op_def assoc commute left_commute split: option.splits)
qed

definition agg_fold :: "('v::pcpo \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('a \<rightharpoonup> 'v) \<Rightarrow> 'a set \<Rightarrow> 'v option" where
  "agg_fold f v A = comm_monoid_set.F (opt_op f) None v A"

context
  fixes f :: "'v::pcpo \<rightarrow> 'v \<rightarrow> 'v"
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
begin

interpretation A: comm_monoid_set "opt_op f" None
  unfolding comm_monoid_set_def by (rule comm_monoid_opt_op[OF f])

lemma agg_fold_empty: "agg_fold f v {} = None"
  by (simp add: agg_fold_def)

lemma agg_fold_singleton: "agg_fold f v {a} = v a"
  by (simp add: agg_fold_def opt_op_def split: option.splits)

lemma agg_fold_nonempty: "agg_fold f v A \<noteq> None \<Longrightarrow> A \<noteq> {}"
  by (auto simp: agg_fold_empty)

lemma agg_fold_present: "finite A \<Longrightarrow> a \<in> A \<Longrightarrow> v a \<noteq> None \<Longrightarrow> agg_fold f v A \<noteq> None"
  unfolding agg_fold_def by (subst A.remove) (auto simp: opt_op_def)

lemma agg_fold_absent: "(\<And>a. a \<in> A \<Longrightarrow> v a = None) \<Longrightarrow> agg_fold f v A = None"
  unfolding agg_fold_def by (rule A.neutral) simp

lemma agg_fold_cong: "A = B \<Longrightarrow> (\<And>a. a \<in> B \<Longrightarrow> v a = w a) \<Longrightarrow> agg_fold f v A = agg_fold f w B"
  unfolding agg_fold_def by (simp cong: A.cong)

text \<open>Folding over two images of one set of rows, identified alike, with the same entries.\<close>

lemma agg_fold_image_cong:
  assumes "\<And>y z. y \<in> Z \<Longrightarrow> z \<in> Z \<Longrightarrow> g y = g z \<longleftrightarrow> g' y = g' z"
    and "\<And>y. y \<in> Z \<Longrightarrow> v (g y) = w (g' y)"
  shows "agg_fold f v (g ` Z) = agg_fold f w (g' ` Z)"
  unfolding agg_fold_def
proof (rule A.reindex_bij_witness[where i = "\<lambda>b. g (SOME y. y \<in> Z \<and> g' y = b)"
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
  unfolding opt_op_def
proof (rule cont2cont_case_option[OF u w])
  fix a
  have "cont (\<lambda>x. case w x of None \<Rightarrow> a | Some y \<Rightarrow> f\<cdot>a\<cdot>y)" by (rule cont2cont_case_option[OF w]) simp_all
  then show "cont (\<lambda>x. Some (case w x of None \<Rightarrow> a | Some y \<Rightarrow> f\<cdot>a\<cdot>y))" by (rule cont_compose[OF cont_Some])
next
  fix x show "cont (\<lambda>a. Some (case w x of None \<Rightarrow> a | Some y \<Rightarrow> f\<cdot>a\<cdot>y))" by simp
qed

lemma cont_agg_fold:
  assumes v: "\<And>a. cont (\<lambda>x. v x a)"
  shows "cont (\<lambda>x. agg_fold f (v x) A)"
proof (cases "finite A")
  case True
  then show ?thesis
  proof (induct A rule: finite_induct)
    case (insert a A)
    have "A.F (v x) (insert a A) = opt_op f (v x a) (A.F (v x) A)" for x by (rule A.insert[OF insert(1,2)])
    then show ?case unfolding agg_fold_def by (simp only:) (rule cont_opt_op[OF v insert(3)[unfolded agg_fold_def]])
  qed (simp add: agg_fold_def)
qed (simp add: agg_fold_def)

end

lemma agg_fold_bij:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)" and h: "bij_betw h A B"
  shows "agg_fold f (v \<circ> h) A = agg_fold f v B"
proof -
  interpret A: comm_monoid_set "opt_op f" None
    unfolding comm_monoid_set_def by (rule comm_monoid_opt_op[OF f])
  show ?thesis unfolding agg_fold_def comp_def by (rule A.reindex_bij_betw[OF h])
qed

context dataspace
begin

text \<open>The rows of a frame in the fiber of a key at an LOD.\<close>

definition afiber :: "'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor \<Rightarrow> 'k \<Rightarrow> 'r set" where
  "afiber data F c k = {y \<in> lower_maximal data. frows F y \<and> rproj c y = k}"

text \<open>\<open>aggregate R f E\<close> folds the inner values over the inner keys below each key of the frame,
  the inner expression being evaluated under the frame refined by the extra requested dimensions
  \<open>R\<close> (a grouping inside the aggregate).  The inner keys are those where the inner expression is
  present: its own domain, so for a lawful inner expression they are data keys.  Its keys are the
  frame's, so it decides no detail: the lower parts of the inner entries move into the
  views' key parts, and the fold reads the fiber's classes at \<open>emind E \<squnion> R\<close>.\<close>

definition inner_keys :: "'k semi_factor \<Rightarrow> ('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> 'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'k set" where
  "inner_keys R E data F k = {\<kappa>. proj (kd E (finclude R F))\<cdot>\<kappa> = \<kappa> \<and> proj (flod F)\<cdot>\<kappa> = k \<and>
     esem E data (finclude R F) \<kappa> \<noteq> None}"

text \<open>For a lawful inner expression at a conforming dataset, its keys below \<open>k\<close> are the defined ones
  among the inner keys of the fiber of \<open>k\<close>.\<close>

lemma inner_keys_fiber:
  assumes EL: "lawful E" and d: "conforms data"
  shows "inner_keys R E data F k = {\<kappa> \<in> rproj (kd E (finclude R F)) ` afiber data F (flod F) k.
      esem E data (finclude R F) \<kappa> \<noteq> None}"
proof -
  let ?X = "kd E (finclude R F)"
  have le: "flod F \<sqsubseteq> ?X" by (simp add: flod_finclude below_trans[OF lattice_join_ge1 lattice_join_ge2])
  show ?thesis
  proof (rule set_eqI, rule iffI)
    fix \<kappa> assume "\<kappa> \<in> inner_keys R E data F k"
    then have kfix: "proj ?X\<cdot>\<kappa> = \<kappa>" and below: "proj (flod F)\<cdot>\<kappa> = k" and kdef: "esem E data (finclude R F) \<kappa> \<noteq> None"
      by (simp_all add: inner_keys_def)
    obtain x where x: "x \<in> lower_maximal data" "frows F x" and kx: "\<kappa> = rproj ?X x"
      using lawful_key_law[OF EL d kdef] by (auto simp: keyimg_def)
    have "rproj (flod F) x = k" using below unfolding kx by (simp only: proj_le[OF le])
    then show "\<kappa> \<in> {\<kappa> \<in> rproj ?X ` afiber data F (flod F) k. esem E data (finclude R F) \<kappa> \<noteq> None}"
      using x kx kdef by (auto simp: afiber_def)
  next
    fix \<kappa> assume "\<kappa> \<in> {\<kappa> \<in> rproj ?X ` afiber data F (flod F) k. esem E data (finclude R F) \<kappa> \<noteq> None}"
    then obtain x where x: "x \<in> afiber data F (flod F) k" and kx: "\<kappa> = rproj ?X x"
      and kdef: "esem E data (finclude R F) \<kappa> \<noteq> None" by blast
    have "rproj (flod F) x = k" using x by (simp add: afiber_def)
    then have "proj (flod F)\<cdot>\<kappa> = k" unfolding kx by (simp only: proj_le[OF le])
    then show "\<kappa> \<in> inner_keys R E data F k" using kdef by (simp add: inner_keys_def kx)
  qed
qed

text \<open>An inner entry, seen from outside the aggregate: its lower part and its requested part move
  into its view's key part, so the outer content is keyed by the inner keys.\<close>

definition agg_entry :: "'k semi_factor \<Rightarrow> ('k, 'r) entry \<Rightarrow> ('k, 'r) entry" where
  "agg_entry R e = e\<lparr>esel := sel \<bottom> (eupper e), eview := (ecols e, ekeys e \<squnion> (elower e \<squnion> (eupper e \<sqinter> R)))\<rparr>"

lemma agg_entry_simps [simp]:
  "elower (agg_entry R e) = \<bottom>" "eupper (agg_entry R e) = eupper e"
  "eguard (agg_entry R e) = eguard e" "eview (agg_entry R e) = (ecols e, ekeys e \<squnion> (elower e \<squnion> (eupper e \<sqinter> R)))"
  by (simp_all add: agg_entry_def)

lemma keyed_view_raise: "keyed_view (c, a) \<Longrightarrow> keyed_view (c, a \<squnion> W)"
proof -
  assume "keyed_view (c, a)"
  then have "keyed_view ((c, a) \<squnion> (\<bottom>, W))" by (rule keyed_view_sup[OF _ keyed_view_key])
  then show ?thesis by (simp only: lattice_join_prod fst_conv snd_conv lattice_join_bot_right)
qed

lemma entry_wf_agg_entry: "entry_wf e \<Longrightarrow> entry_wf (agg_entry R e)"
  unfolding entry_wf_def agg_entry_simps using keyed_view_raise[of "ecols e" "ekeys e"] by simp

text \<open>The content semantics folds the inner content semantics over the fold entry's keys, reading
  each inner entry's content at a key off the outer content: the pairs whose key has the inner key's
  part at the entry's lower and requested parts, cut back to the inner key part.\<close>

definition agg_read :: "'k semi_factor \<Rightarrow> ('k, 'r) entry \<Rightarrow> 'k \<Rightarrow> ('k \<times> 'r) set \<Rightarrow> ('k \<times> 'r) set" where
  "agg_read R e p X = (\<lambda>x. (proj (ekeys e)\<cdot>(fst x), snd x)) `
     {x \<in> X. proj (elower e \<squnion> (eupper e \<sqinter> R))\<cdot>(fst x) = proj (elower e \<squnion> (eupper e \<sqinter> R))\<cdot>p}"

text \<open>On maps the read picks, at each inner key, the one outer key of the slice that projects to
  it, and drops the inner key when there is none or more than one.  Which keys collide is decided by
  the domain alone, so the read is monotone on all maps; on contents nothing collides.\<close>

definition agg_src :: "'k semi_factor \<Rightarrow> ('k, 'r) entry \<Rightarrow> 'k \<Rightarrow> ('k \<Rightarrow> 'r option) \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> bool" where
  "agg_src R e p X q q0 \<longleftrightarrow> q0 \<in> dom X \<and>
     proj (elower e \<squnion> (eupper e \<sqinter> R))\<cdot>q0 = proj (elower e \<squnion> (eupper e \<sqinter> R))\<cdot>p \<and> proj (ekeys e)\<cdot>q0 = q"

definition agg_pick :: "'k semi_factor \<Rightarrow> ('k, 'r) entry \<Rightarrow> 'k \<Rightarrow> ('k \<Rightarrow> 'r option) \<Rightarrow> 'k \<Rightarrow> 'r option" where
  "agg_pick R e p X q = (if \<exists>!q0. agg_src R e p X q q0 then X (THE q0. agg_src R e p X q q0) else None)"

definition agg_inner :: "'k semi_factor \<Rightarrow> ('k, 'r) entry list \<Rightarrow> ('k \<Rightarrow> 'r option) list \<Rightarrow> 'k \<Rightarrow> ('k \<Rightarrow> 'r option) list" where
  "agg_inner R es Xs p = map2 (\<lambda>e X. agg_pick R e p X) es Xs"

text \<open>A graph is \<^emph>\<open>shaped\<close> for an entry when it is single-valued with keys at the entry's key part.
  Outer keys at the outer key part are determined by their parts at the inner key part and at the
  lower and requested parts, so on shaped outer graphs the pick agrees with the graph read.\<close>

definition gshaped :: "('k, 'r) entry \<Rightarrow> ('k \<times> 'r) set \<Rightarrow> bool" where
  "gshaped e X \<longleftrightarrow> single_valued X \<and> (\<forall>x\<in>X. proj (ekeys e)\<cdot>(fst x) = fst x)"

lemma cgraph_gshaped: "entry_wf e \<Longrightarrow> conforms data \<Longrightarrow> gshaped e (cgraph data e F k)"
  unfolding gshaped_def using cgraph_single_valued[of e data F k] by (auto simp: cgraph_def cpair_def)

lemma agg_read_key_eq:
  assumes X: "gshaped (agg_entry R e) X" and Y: "gshaped (agg_entry R e) Y"
    and q: "(q, v) \<in> X" and q': "(q', w) \<in> Y"
    and A: "proj (elower e \<squnion> (eupper e \<sqinter> R))\<cdot>q = proj (elower e \<squnion> (eupper e \<sqinter> R))\<cdot>q'"
    and s: "proj (ekeys e)\<cdot>q = proj (ekeys e)\<cdot>q'"
  shows "q = q'"
proof -
  let ?S = "ekeys e \<squnion> (elower e \<squnion> (eupper e \<sqinter> R))"
  have "q = proj ?S\<cdot>q" "q' = proj ?S\<cdot>q'" using X Y q q' by (force simp: gshaped_def)+
  moreover have "proj ?S\<cdot>q = proj ?S\<cdot>q'" using A s by (simp only: proj_sup_eq)
  ultimately show ?thesis by simp
qed

lemma agg_read_single_valued:
  assumes X: "gshaped (agg_entry R e) X"
  shows "single_valued (agg_read R e p X)"
proof (rule single_valuedI)
  fix q u u' assume u: "(q, u) \<in> agg_read R e p X" and u': "(q, u') \<in> agg_read R e p X"
  obtain q1 where 1: "(q1, u) \<in> X" "q = proj (ekeys e)\<cdot>q1"
    "proj (elower e \<squnion> (eupper e \<sqinter> R))\<cdot>q1 = proj (elower e \<squnion> (eupper e \<sqinter> R))\<cdot>p"
    using u unfolding agg_read_def by force
  obtain q2 where 2: "(q2, u') \<in> X" "q = proj (ekeys e)\<cdot>q2"
    "proj (elower e \<squnion> (eupper e \<sqinter> R))\<cdot>q2 = proj (elower e \<squnion> (eupper e \<sqinter> R))\<cdot>p"
    using u' unfolding agg_read_def by force
  have "q1 = q2" by (rule agg_read_key_eq[OF X X 1(1) 2(1)]) (use 1(2,3) 2(2,3) in simp_all)
  then show "u = u'" using single_valuedD[of X] X 1(1) 2(1) by (simp add: gshaped_def)
qed

lemma agg_pick_graph:
  assumes X: "gshaped (agg_entry R e) (graph X)"
  shows "agg_pick R e p X q = gmap (agg_read R e p (graph X)) q"
proof -
  let ?A = "elower e \<squnion> (eupper e \<sqinter> R)" and ?P = "agg_src R e p X q"
  have uniq: "q1 = q2" if 1: "?P q1" and 2: "?P q2" for q1 q2
  proof -
    obtain v w where v: "X q1 = Some v" and w: "X q2 = Some w" using 1 2 by (auto simp: agg_src_def)
    show ?thesis
      by (rule agg_read_key_eq[OF X X, of q1 v q2 w]) (use 1 2 v w in \<open>simp_all add: graph_def agg_src_def\<close>)
  qed
  show ?thesis
  proof (cases "\<exists>q0. ?P q0")
    case True
    then obtain q0 where q0: "?P q0" by blast
    then obtain v where v: "X q0 = Some v" by (auto simp: agg_src_def)
    have ex1: "\<exists>!q0. ?P q0" using q0 uniq by blast
    have th: "(THE q0. ?P q0) = q0" using q0 uniq by blast
    have "(q, v) \<in> agg_read R e p (graph X)"
      unfolding agg_read_def using q0 v by (force simp: graph_def agg_src_def intro: rev_image_eqI)
    then have "gmap (agg_read R e p (graph X)) q = Some v" by (rule gmap_apply[OF agg_read_single_valued[OF X]])
    then show ?thesis unfolding agg_pick_def using ex1 th v by simp
  next
    case False
    then have "q \<notin> fst ` agg_read R e p (graph X)" unfolding agg_read_def by (force simp: graph_def agg_src_def)
    then show ?thesis unfolding agg_pick_def gmap_def using False by auto
  qed
qed

definition agg_csem :: "'k semi_factor \<Rightarrow> ('v::pcpo \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k, 'f, 'r, 'v) expr \<Rightarrow> ('k \<Rightarrow> 'r option) list \<Rightarrow> 'v option" where
  "agg_csem R f E Xs = agg_fold f (\<lambda>p. csem E\<cdot>(agg_inner R (edims E) (tl Xs) p))
     {p \<in> dom (hd Xs). csem E\<cdot>(agg_inner R (edims E) (tl Xs) p) \<noteq> None}"

lemma map2_map: "map2 g xs (map h xs) = map (\<lambda>x. g x (h x)) xs"
  by (induct xs) simp_all

definition aggregate :: "'k semi_factor \<Rightarrow> ('v::pcpo \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k, 'f, 'r, 'v) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "aggregate R f E = \<lparr>emind = \<bottom>,
     edims = mk_entry (sel \<bottom> lattice_top) gtrue (\<bottom>, emind E \<squnion> R) # map (agg_entry R) (edims E),
     esem = \<lambda>data F k. agg_fold f (esem E data (finclude R F)) (inner_keys R E data F k),
     csem = \<Lambda> Xs. agg_csem R f E Xs\<rparr>"

lemma aggregate_simps [simp]:
  "emind (aggregate R f E) = \<bottom>"
  "edims (aggregate R f E) = mk_entry (sel \<bottom> lattice_top) gtrue (\<bottom>, emind E \<squnion> R) # map (agg_entry R) (edims E)"
  "esem (aggregate R f E) data F k = agg_fold f (esem E data (finclude R F)) (inner_keys R E data F k)"
  "csem (aggregate R f E) = (\<Lambda> Xs. agg_csem R f E Xs)"
  by (simp_all add: aggregate_def)

text \<open>The content semantics is continuous: the pick only chooses the outer key by the domain, the
  fold's index set is rigid (the fold entry's keys, and the inner keys present), and the fold is
  continuous in the values.\<close>

lemma rigid_agg_src: "rigid (\<lambda>X. agg_src R e p X q)"
  by (rule rigidI) (simp add: fun_eq_iff agg_src_def map_below_dom)

lemma cont_agg_pick: "cont (agg_pick R e p)"
proof -
  have "cont (\<lambda>X. agg_pick R e p X q)" for q
    unfolding agg_pick_def
  proof (rule cont_if_rigid)
    have src: "agg_src R e p X q = agg_src R e p Y q" if "X \<sqsubseteq> Y" for X Y
      by (rule rigidD[OF rigid_agg_src that])
    show "rigid (\<lambda>X. \<exists>!q0. agg_src R e p X q q0)" by (rule rigidI) (simp only: src)
    have "rigid (\<lambda>X. THE q0. agg_src R e p X q q0)" by (rule rigidI) (simp only: src)
    then show "cont (\<lambda>X. X (THE q0. agg_src R e p X q q0))"
      by (rule cont_rigid_arg[where h = "\<lambda>X s. X s", rotated]) (simp add: cont2cont_fun)
  qed simp
  then have "cont (\<lambda>X. \<lambda>q. agg_pick R e p X q)" by (rule cont2cont_lambda)
  then show ?thesis by simp
qed

lemma cont_agg_inner: "cont (\<lambda>Xs. agg_inner R es Xs p)"
  unfolding agg_inner_def by (rule cont_map2) (simp add: cont_agg_pick[unfolded eta_cfun])

lemma cont_agg_csem:
  assumes f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
  shows "cont (agg_csem R f E)"
proof -
  let ?\<Phi> = "\<lambda>Xs p. csem E\<cdot>(agg_inner R (edims E) (tl Xs) p)"
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

lemma aggregate_csem: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b) \<Longrightarrow> csem (aggregate R f E)\<cdot>Xs = agg_csem R f E Xs"
  by (simp add: cont_agg_csem)

text \<open>The fold entry reads the fiber.\<close>

lemma agg_fiber: "proj (flod F)\<cdot>k = k \<Longrightarrow> group data \<bottom> lattice_top F k = afiber data F (flod F) k"
  by (simp add: group_top[of \<bottom>, simplified lattice_join_bot_left] afiber_def lattice_join_bot_left)

text \<open>An inner group is the outer group through the same upper part, cut down by the inner key's
  lower part and requested part.\<close>

lemma agg_group:
  assumes y: "rproj (flod F) y = k" and am: "a \<sqsubseteq> m"
  shows "group data a \<rho> (finclude R F) (rproj (m \<squnion> flod (finclude R F)) y)
      = {y' \<in> group data \<bottom> \<rho> F k. rproj (a \<squnion> (\<rho> \<sqinter> R)) y' = rproj (a \<squnion> (\<rho> \<sqinter> R)) y}"
proof -
  let ?X = "m \<squnion> flod (finclude R F)" and ?A = "a \<squnion> (\<rho> \<sqinter> R)" and ?L = "(\<rho> \<sqinter> flod F)"
  have lod: "a \<squnion> (\<rho> \<sqinter> flod (finclude R F)) = ?A \<squnion> ?L" by (simp add: flod_finclude truncate_sup lattice_join_ac)
  have mR: "m \<squnion> R \<sqsubseteq> ?X" by (simp add: flod_finclude lattice_join_mono lattice_join_ge2)
  have AX: "?A \<sqsubseteq> ?X" by (rule below_trans[OF lattice_join_mono[OF am truncate_below] mR])
  have LX: "?L \<sqsubseteq> ?X"
    by (rule below_trans[OF truncate_below]) (simp add: flod_finclude below_trans[OF lattice_join_ge1 lattice_join_ge2])
  have kA: "proj ?A\<cdot>(rproj ?X y) = rproj ?A y" by (rule proj_le[OF AX])
  have kL: "proj ?L\<cdot>(rproj ?X y) = proj ?L\<cdot>k"
  proof -
    have "proj ?L\<cdot>(rproj ?X y) = rproj ?L y" by (rule proj_le[OF LX])
    also have "\<dots> = proj ?L\<cdot>(rproj (flod F) y)" by (rule proj_le[OF truncate_below, symmetric])
    finally show ?thesis by (simp only: y)
  qed
  show ?thesis unfolding group_def lod proj_sup_eq kA kL by (auto simp: lattice_join_bot_left proj_bot)
qed

text \<open>Inner keys of a fiber correspond to their parts at \<open>m \<squnion> R\<close>.\<close>

lemma agg_keys_bij:
  "bij_betw (Rep_cfun (proj (m \<squnion> R))) (rproj (m \<squnion> flod (finclude R F)) ` afiber data F (flod F) k)
      (rproj (m \<squnion> R) ` afiber data F (flod F) k)"
proof -
  let ?X = "m \<squnion> flod (finclude R F)" and ?Z = "afiber data F (flod F) k"
  have le: "m \<squnion> R \<sqsubseteq> ?X" by (simp add: flod_finclude lattice_join_mono lattice_join_ge2)
  have pr: "proj (m \<squnion> R)\<cdot>(rproj ?X y) = rproj (m \<squnion> R) y" for y by (rule proj_le[OF le])
  show ?thesis
  proof (rule bij_betw_imageI)
    show "inj_on (Rep_cfun (proj (m \<squnion> R))) (rproj ?X ` ?Z)"
    proof (rule inj_onI)
      fix \<kappa>1 \<kappa>2 assume k1: "\<kappa>1 \<in> rproj ?X ` ?Z" and k2: "\<kappa>2 \<in> rproj ?X ` ?Z"
        and e: "proj (m \<squnion> R)\<cdot>\<kappa>1 = proj (m \<squnion> R)\<cdot>\<kappa>2"
      obtain y1 where y1: "y1 \<in> ?Z" "\<kappa>1 = rproj ?X y1" using k1 by blast
      obtain y2 where y2: "y2 \<in> ?Z" "\<kappa>2 = rproj ?X y2" using k2 by blast
      have "rproj (m \<squnion> R) y1 = rproj (m \<squnion> R) y2" using e unfolding y1(2) y2(2) pr .
      moreover have "rproj (flod F) y1 = rproj (flod F) y2" using y1(1) y2(1) by (simp add: afiber_def)
      ultimately have "rproj ((m \<squnion> R) \<squnion> flod F) y1 = rproj ((m \<squnion> R) \<squnion> flod F) y2"
        by (simp only: rproj_sup_eq)
      moreover have "(m \<squnion> R) \<squnion> flod F = ?X" by (simp add: flod_finclude lattice_join_ac)
      ultimately show "\<kappa>1 = \<kappa>2" by (simp add: y1(2) y2(2))
    qed
    show "Rep_cfun (proj (m \<squnion> R)) ` rproj ?X ` ?Z = rproj (m \<squnion> R) ` ?Z"
      by (simp only: image_image pr)
  qed
qed

text \<open>The content graph of an inner entry at an inner key is read off the outer entry's: the
  pairs whose key has the inner key's part at the entry's lower and requested parts.\<close>

lemma agg_content_inner:
  assumes ES: "semilawful E" and e: "e \<in> set (edims E)" and yZ: "y \<in> afiber data G (flod G) kG"
    and \<kappa>: "\<kappa> = rproj (emind E \<squnion> flod (finclude R G)) y" and py: "proj (emind E \<squnion> R)\<cdot>\<kappa> = p"
  shows "cgraph data e (finclude R G) \<kappa> = agg_read R e p (cgraph data (agg_entry R e) G kG)"
proof -
  let ?m = "emind E" and ?a = "elower e" and ?\<rho> = "eupper e" and ?s = "ekeys e"
  have am: "?a \<sqsubseteq> ?m" by (rule lower_below_mind[OF ES e])
  let ?A = "?a \<squnion> (?\<rho> \<sqinter> R)"
  have AmR: "?A \<sqsubseteq> ?m \<squnion> R" by (rule lattice_join_mono[OF am truncate_below])
  have mR: "?m \<squnion> R \<sqsubseteq> ?m \<squnion> flod (finclude R G)" by (simp add: flod_finclude lattice_join_mono lattice_join_ge2)
  have yA: "rproj ?A y = proj ?A\<cdot>p"
  proof -
    have "proj ?A\<cdot>p = proj ?A\<cdot>\<kappa>" unfolding py[symmetric] by (rule proj_le[OF AmR])
    also have "\<dots> = rproj ?A y" unfolding \<kappa> by (rule proj_le[OF below_trans[OF AmR mR]])
    finally show ?thesis by simp
  qed
  have gy: "rproj (flod G) y = kG" using yZ by (simp add: afiber_def)
  have grp: "group data ?a ?\<rho> (finclude R G) \<kappa> = {y' \<in> group data \<bottom> ?\<rho> G kG. rproj ?A y' = proj ?A\<cdot>p}"
    unfolding \<kappa> agg_group[OF gy am] yA ..
  have pA: "proj ?A\<cdot>(rproj (?s \<squnion> ?A) y') = rproj ?A y'" for y' by (rule proj_le[OF lattice_join_ge2])
  have ps: "proj ?s\<cdot>(rproj (?s \<squnion> ?A) y') = rproj ?s y'" for y' by (rule proj_le[OF lattice_join_ge1])
  let ?h = "\<lambda>y'. (rproj (?s \<squnion> ?A) y', y' \<downharpoonright> ecols e)"
  let ?Y = "efiber data (agg_entry R e) G kG"
  have "{x \<in> ?h ` ?Y. proj ?A\<cdot>(fst x) = proj ?A\<cdot>p} = ?h ` {y' \<in> ?Y. rproj ?A y' = proj ?A\<cdot>p}"
    by (auto simp: pA)
  then have "agg_read R e p (cgraph data (agg_entry R e) G kG)
      = cpair e ` {y' \<in> ?Y. rproj ?A y' = proj ?A\<cdot>p}"
    unfolding agg_read_def cgraph_def cpair_def agg_entry_simps fst_conv snd_conv by (simp add: image_image ps)
  moreover have "{y' \<in> ?Y. rproj ?A y' = proj ?A\<cdot>p} = efiber data e (finclude R G) \<kappa>"
    unfolding efiber_def grp by auto
  ultimately show ?thesis unfolding cgraph_def by simp
qed

theorem lawful_aggregate:
  assumes EL: "lawful E" and f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
  shows "lawful (aggregate R f E)"
proof -
  have ES: "semilawful E" by (rule lawful_semilawful[OF EL])
  let ?m = "emind E"
  let ?h = "mk_entry (sel \<bottom> lattice_top) gtrue (\<bottom>, ?m \<squnion> R) :: ('k, 'r) entry"
  have bj: "\<bottom> \<squnion> X = X" for X :: "'k semi_factor" by (rule lattice_join_bot_left)
  note fiber = agg_fiber
  note bij = agg_keys_bij[of ?m R]
  show ?thesis
  proof (rule lawfulI, simp_all only: aggregate_simps)
    show "entry_wf e" if "e \<in> set (?h # map (agg_entry R) (edims E))" for e
      using that by (auto intro: entry_wf_view keyed_view_key supported_gtrue entry_wf_agg_entry semilawful_wf[OF ES])
    show "(eupper e \<sqinter> \<bottom>) \<sqsubseteq> elower e" if "e \<in> set (?h # map (agg_entry R) (edims E))" for e
      using that by (auto simp: lattice_meet_bot_right)
    show "(\<bottom>::'k semi_factor) = fold (\<squnion>) (map elower (?h # map (agg_entry R) (edims E))) \<bottom>"
    proof -
      have l: "map elower (?h # map (agg_entry R) (edims E)) = map (\<lambda>_. \<bottom>) (?h # map (agg_entry R) (edims E))"
        by simp
      show ?thesis by (simp only: l fold_join_bots)
    qed
    show "keyimg data F (\<bottom> \<squnion> flod F) k"
      if d: "conforms data" and "agg_fold f (esem E data (finclude R F)) (inner_keys R E data F k) \<noteq> None"
      for data F k
    proof -
      have "inner_keys R E data F k \<noteq> {}" using agg_fold_nonempty[OF f that(2)] by auto
      then have "afiber data F (flod F) k \<noteq> {}" by (auto simp: inner_keys_fiber[OF EL d])
      then show ?thesis by (auto simp: afiber_def keyimg_def bj)
    qed
    show "agg_fold f (esem E data (finclude R F)) (inner_keys R E data F k)
        = (\<Lambda> Xs. agg_csem R f E Xs)\<cdot>(contents data (?h # map (agg_entry R) (edims E)) F k)"
      if d: "conforms data" and k: "proj (\<bottom> \<squnion> flod F)\<cdot>k = k" for data F k
    proof -
      have k1: "proj (flod F)\<cdot>k = k" using k by (simp only: bj)
      let ?Z = "afiber data F (flod F) k"
      let ?K = "rproj (?m \<squnion> flod (finclude R F)) ` ?Z"
      let ?P = "rproj (?m \<squnion> R) ` ?Z" and ?\<pi> = "Rep_cfun (proj (?m \<squnion> R))"
      let ?v = "esem E data (finclude R F)"
      let ?X = "contents data (map (agg_entry R) (edims E)) F k"
      let ?\<Phi> = "\<lambda>p. csem E\<cdot>(agg_inner R (edims E) ?X p)"
      have hd: "dom (hd (contents data (?h # map (agg_entry R) (edims E)) F k)) = ?P"
        by (simp add: content_def cgraph_def cpair_def efiber_def fiber[OF k1] image_image)
      have tl: "tl (contents data (?h # map (agg_entry R) (edims E)) F k) = ?X"
        by (simp only: list.map(2) list.sel(3))
      define \<psi> where "\<psi> = inv_into ?K ?\<pi>"
      have b: "bij_betw \<psi> ?P ?K" unfolding \<psi>_def by (rule bij_betw_inv_into[OF bij])
      have sP: "?\<pi> ` ?K = ?P" by (rule bij_betw_imp_surj_on[OF bij])
      have pt: "?\<Phi> p = ?v (\<psi> p)" if p: "p \<in> ?P" for p
      proof -
        have pK: "\<psi> p \<in> ?K" unfolding \<psi>_def by (rule inv_into_into) (simp only: sP p)
        obtain y where y: "y \<in> ?Z" "\<psi> p = rproj (?m \<squnion> flod (finclude R F)) y" using pK by blast
        have py: "proj (?m \<squnion> R)\<cdot>(\<psi> p) = p" unfolding \<psi>_def by (rule f_inv_into_f) (simp only: sP p)
        have "agg_inner R (edims E) ?X p = map (\<lambda>e. agg_pick R e p (content data (agg_entry R e) F k)) (edims E)"
          unfolding agg_inner_def map_map map2_map by (simp add: comp_def)
        also have "\<dots> = contents data (edims E) (finclude R F) (\<psi> p)"
        proof (rule map_cong[OF refl])
          fix e assume e: "e \<in> set (edims E)"
          have wf: "entry_wf (agg_entry R e)" by (rule entry_wf_agg_entry[OF semilawful_wf[OF ES e]])
          have g: "graph (content data (agg_entry R e) F k) = cgraph data (agg_entry R e) F k"
            by (rule graph_content[OF wf d])
          have sh: "gshaped (agg_entry R e) (graph (content data (agg_entry R e) F k))"
            unfolding g by (rule cgraph_gshaped[OF wf d])
          show "agg_pick R e p (content data (agg_entry R e) F k) = content data e (finclude R F) (\<psi> p)"
          proof
            fix q
            have "agg_pick R e p (content data (agg_entry R e) F k) q = gmap (agg_read R e p (cgraph data (agg_entry R e) F k)) q"
              by (simp only: agg_pick_graph[OF sh] g)
            then show "agg_pick R e p (content data (agg_entry R e) F k) q = content data e (finclude R F) (\<psi> p) q"
              by (simp only: content_def agg_content_inner[OF ES e y(1) y(2) py])
          qed
        qed
        finally have c: "agg_inner R (edims E) ?X p = contents data (edims E) (finclude R F) (\<psi> p)" .
        have "proj (kd E (finclude R F))\<cdot>(\<psi> p) = \<psi> p" by (simp only: y(2) proj_idem)
        then show ?thesis by (simp only: c semilawful_csem[OF ES d])
      qed
      let ?Q = "{p \<in> ?P. ?v (\<psi> p) \<noteq> None}"
      have D: "inner_keys R E data F k = \<psi> ` ?Q"
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
      finally have "agg_fold f (esem E data (finclude R F)) (inner_keys R E data F k)
          = agg_csem R f E (contents data (?h # map (agg_entry R) (edims E)) F k)"
        unfolding agg_csem_def hd tl T D .
      then show ?thesis by (simp only: beta_cfun[OF cont_agg_csem[OF f]])
    qed
  qed
qed

end

end
