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

definition afiber :: "('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor \<Rightarrow> 'k \<Rightarrow> 'r set" where
  "afiber F c k = {y \<in> pts S. frows F y \<and> rproj c y = k}"

text \<open>\<open>aggregate R f E\<close> folds the inner entries over each fiber of the frame LOD, the inner
  expression being evaluated under the frame refined by the extra requested dimensions \<open>R\<close> (a
  grouping inside the aggregate).  Its keys are the frame's, so it decides no detail: the lower
  parts of the inner entries move into the observations, and the fold reads the fiber's classes
  at \<open>emind E \<squnion> R\<close>.\<close>

definition aggregate :: "'k semi_factor \<Rightarrow> ('v::pcpo \<rightarrow> 'v \<rightarrow> 'v) \<Rightarrow> ('k, 'f, 'r, 'v) expr \<Rightarrow> ('k, 'f, 'r, 'v) expr" where
  "aggregate R f E = \<lparr>emind = \<bottom>,
     edims = (\<bottom>, lattice_top, obs_key (emind E \<squnion> R)) #
       map (\<lambda>(a, \<rho>, g). (\<bottom>, \<rho>, obs_pair g (obs_key (a \<squnion> truncate \<rho> R)))) (edims E),
     esem = \<lambda>F k. agg_fold f (esem E (finclude R F))
       (rproj (emind E \<squnion> flod (finclude R F)) ` afiber F (flod F) k)\<rparr>"

lemma aggregate_simps [simp]:
  "emind (aggregate R f E) = \<bottom>"
  "edims (aggregate R f E) = (\<bottom>, lattice_top, obs_key (emind E \<squnion> R)) #
       map (\<lambda>(a, \<rho>, g). (\<bottom>, \<rho>, obs_pair g (obs_key (a \<squnion> truncate \<rho> R)))) (edims E)"
  "esem (aggregate R f E) F k = agg_fold f (esem E (finclude R F))
       (rproj (emind E \<squnion> flod (finclude R F)) ` afiber F (flod F) k)"
  by (simp_all add: aggregate_def)

theorem lawful_aggregate:
  assumes E: "lawfulE E" and f: "abel_semigroup (\<lambda>a b. f\<cdot>a\<cdot>b)"
  shows "lawfulE (aggregate R f E)"
proof -
  interpret E: expr_sem conj sunit slod sopen coarsen spin rkey S "emind E" "edims E" "esem E"
    by (fact E)
  let ?m = "emind E"
  let ?t = "\<lambda>(a, \<rho>, g). (\<bottom>::'k semi_factor, \<rho>, obs_pair g (obs_key (a \<squnion> truncate \<rho> R)))"
  have bj: "\<bottom> \<squnion> X = X" for X :: "'k semi_factor" by (rule lattice_join_bot_left)
  have ok: "Rep_cfun (obs_key c) = (\<lambda>y. emb\<cdot>(rproj c y))" for c by (rule ext) (rule obs_key_apply)
  text \<open>The fold entry reads the fiber.\<close>
  have fiber: "group \<bottom> lattice_top F k = afiber F (flod F) k" if "proj (flod F)\<cdot>k = k" for F k
  proof -
    have "proj (\<bottom> \<squnion> flod F)\<cdot>k = k" using that by (simp only: bj)
    then show ?thesis by (simp add: group_top afiber_def bj)
  qed
  text \<open>An inner group is the outer group through the same upper part, cut down by the inner
    key's lower part and requested part.\<close>
  have ig: "group a \<rho> (finclude R F) (rproj (?m \<squnion> flod (finclude R F)) y)
      = {y' \<in> group \<bottom> \<rho> F k. rproj (a \<squnion> truncate \<rho> R) y' = rproj (a \<squnion> truncate \<rho> R) y}"
    if y: "rproj (flod F) y = k" and am: "a \<sqsubseteq> ?m" for a \<rho> F k y
  proof -
    let ?X = "?m \<squnion> flod (finclude R F)" and ?A = "a \<squnion> truncate \<rho> R" and ?L = "truncate \<rho> (flod F)"
    have lod: "a \<squnion> truncate \<rho> (flod (finclude R F)) = ?A \<squnion> ?L" by (simp add: truncate_sup lattice_join_ac)
    have mR: "?m \<squnion> R \<sqsubseteq> ?X" by (simp add: lattice_join_mono lattice_join_ge2)
    have AX: "?A \<sqsubseteq> ?X" by (rule below_trans[OF lattice_join_mono[OF am truncate_below] mR])
    have LX: "?L \<sqsubseteq> ?X"
      by (rule below_trans[OF truncate_below]) (simp add: below_trans[OF lattice_join_ge1 lattice_join_ge2])
    have kA: "proj ?A\<cdot>(rproj ?X y) = rproj ?A y" by (rule proj_le[OF AX])
    have kL: "proj ?L\<cdot>(rproj ?X y) = proj ?L\<cdot>k"
    proof -
      have "proj ?L\<cdot>(rproj ?X y) = rproj ?L y" by (rule proj_le[OF LX])
      also have "\<dots> = proj ?L\<cdot>(rproj (flod F) y)" by (rule proj_le[OF truncate_below, symmetric])
      finally show ?thesis by (simp only: y)
    qed
    show ?thesis unfolding group_def lod proj_sup_eq kA kL by (auto simp: bj proj_bot)
  qed
  text \<open>Inner keys of a fiber correspond to their parts at \<open>emind E \<squnion> R\<close>.\<close>
  have bij: "bij_betw (Rep_cfun (proj (?m \<squnion> R))) (rproj (?m \<squnion> flod (finclude R F)) ` afiber F (flod F) k)
      (rproj (?m \<squnion> R) ` afiber F (flod F) k)" for F k
  proof -
    let ?X = "?m \<squnion> flod (finclude R F)" and ?Z = "afiber F (flod F) k"
    have le: "?m \<squnion> R \<sqsubseteq> ?X" by (simp add: lattice_join_mono lattice_join_ge2)
    have pr: "proj (?m \<squnion> R)\<cdot>(rproj ?X y) = rproj (?m \<squnion> R) y" for y by (rule proj_le[OF le])
    show ?thesis
    proof (rule bij_betw_imageI)
      show "inj_on (Rep_cfun (proj (?m \<squnion> R))) (rproj ?X ` ?Z)"
      proof (rule inj_onI)
        fix \<kappa>1 \<kappa>2 assume k1: "\<kappa>1 \<in> rproj ?X ` ?Z" and k2: "\<kappa>2 \<in> rproj ?X ` ?Z"
          and e: "proj (?m \<squnion> R)\<cdot>\<kappa>1 = proj (?m \<squnion> R)\<cdot>\<kappa>2"
        obtain y1 where y1: "y1 \<in> ?Z" "\<kappa>1 = rproj ?X y1" using k1 by blast
        obtain y2 where y2: "y2 \<in> ?Z" "\<kappa>2 = rproj ?X y2" using k2 by blast
        have "rproj (?m \<squnion> R) y1 = rproj (?m \<squnion> R) y2" using e unfolding y1(2) y2(2) pr .
        moreover have "rproj (flod F) y1 = rproj (flod F) y2" using y1(1) y2(1) by (simp add: afiber_def)
        ultimately have "rproj ((?m \<squnion> R) \<squnion> flod F) y1 = rproj ((?m \<squnion> R) \<squnion> flod F) y2"
          by (simp only: rproj_sup_eq)
        moreover have "(?m \<squnion> R) \<squnion> flod F = ?X" by (simp add: lattice_join_ac)
        ultimately show "\<kappa>1 = \<kappa>2" by (simp add: y1(2) y2(2))
      qed
      show "Rep_cfun (proj (?m \<squnion> R)) ` rproj ?X ` ?Z = rproj (?m \<squnion> R) ` ?Z"
        by (simp only: image_image pr)
    qed
  qed
  text \<open>The content of an inner entry at an inner key is read off the outer entry's content.\<close>
  have inner: "content e (finclude R G) \<kappa>
      = sel_snd (emb\<cdot>(proj (fst e \<squnion> truncate (fst (snd e)) R)\<cdot>p)) (content (?t e) G kG)"
    if e: "e \<in> set (edims E)" and yZ: "y \<in> afiber G (flod G) kG"
      and \<kappa>: "\<kappa> = rproj (?m \<squnion> flod (finclude R G)) y" and py: "proj (?m \<squnion> R)\<cdot>\<kappa> = p" for e G kG \<kappa> y p
  proof -
    obtain a \<rho> g where ae: "e = (a, \<rho>, g)" by (cases e) auto
    have am: "a \<sqsubseteq> ?m" by (rule E.lower_below_mind[OF e[unfolded ae]])
    let ?A = "a \<squnion> truncate \<rho> R"
    have AmR: "?A \<sqsubseteq> ?m \<squnion> R" by (rule lattice_join_mono[OF am truncate_below])
    have mR: "?m \<squnion> R \<sqsubseteq> ?m \<squnion> flod (finclude R G)" by (simp add: lattice_join_mono lattice_join_ge2)
    have yA: "rproj ?A y = proj ?A\<cdot>p"
    proof -
      have "proj ?A\<cdot>p = proj ?A\<cdot>\<kappa>" unfolding py[symmetric] by (rule proj_le[OF AmR])
      also have "\<dots> = rproj ?A y" unfolding \<kappa> by (rule proj_le[OF below_trans[OF AmR mR]])
      finally show ?thesis by simp
    qed
    have gy: "rproj (flod G) y = kG" using yZ by (simp add: afiber_def)
    have grp: "group a \<rho> (finclude R G) \<kappa> = {y' \<in> group \<bottom> \<rho> G kG. rproj ?A y' = proj ?A\<cdot>p}"
      unfolding \<kappa> ig[OF gy am] yA ..
    show ?thesis unfolding ae by (simp add: grp sel_snd_obs_pair obs_key_apply emb_eq_iff)
  qed
  show ?thesis
  proof (rule lawfulI, simp_all only: aggregate_simps)
    show "truncate \<rho> \<bottom> \<sqsubseteq> a"
      if "(a, \<rho>, g) \<in> set ((\<bottom>, lattice_top, obs_key (?m \<squnion> R)) # map ?t (edims E))" for a \<rho> g
      using that by (auto simp: lattice_meet_bot_right)
    show "(\<bottom>::'k semi_factor) = fold (\<squnion>) (map fst ((\<bottom>, lattice_top, obs_key (?m \<squnion> R)) # map ?t (edims E))) \<bottom>"
    proof -
      let ?es = "(\<bottom>::'k semi_factor, lattice_top, obs_key (?m \<squnion> R)) # map ?t (edims E)"
      text \<open>Every lower part is \<open>\<bottom>\<close>, and joining \<open>\<bottom>\<close>s onto \<open>\<bottom>\<close> gives \<open>\<bottom>\<close>.\<close>
      have l: "map fst ?es = map (\<lambda>_. \<bottom>) ?es"
        by (simp only: list.map(2) fst_conv) (simp add: map_map comp_def split_def)
      show ?thesis by (simp only: l fold_join_bots)
    qed
    show "keyimg S F (\<bottom> \<squnion> flod F) k"
      if "agg_fold f (esem E (finclude R F)) (rproj (?m \<squnion> flod (finclude R F)) ` afiber F (flod F) k) \<noteq> None"
      for F k
    proof -
      have "afiber F (flod F) k \<noteq> {}" using agg_fold_nonempty[OF f that] by auto
      then show ?thesis by (auto simp: afiber_def keyimg_def bj)
    qed
    show "agg_fold f (esem E (finclude R F)) (rproj (?m \<squnion> flod (finclude R F)) ` afiber F (flod F) k)
        = agg_fold f (esem E (finclude R F')) (rproj (?m \<squnion> flod (finclude R F')) ` afiber F' (flod F') k')"
      if k: "proj (\<bottom> \<squnion> flod F)\<cdot>k = k" "proj (\<bottom> \<squnion> flod F')\<cdot>k' = k'"
        and e: "contents ((\<bottom>, lattice_top, obs_key (?m \<squnion> R)) # map ?t (edims E)) F k
              = contents ((\<bottom>, lattice_top, obs_key (?m \<squnion> R)) # map ?t (edims E)) F' k'" for F F' k k'
    proof -
      have k1: "proj (flod F)\<cdot>k = k" and k2: "proj (flod F')\<cdot>k' = k'" using k by (simp_all only: bj)
      have eh: "content (\<bottom>, lattice_top, obs_key (?m \<squnion> R)) F k = content (\<bottom>, lattice_top, obs_key (?m \<squnion> R)) F' k'"
        and et: "contents (map ?t (edims E)) F k = contents (map ?t (edims E)) F' k'"
        using e by (simp_all only: list.map list.inject)
      have ptw: "content (?t e) F k = content (?t e) F' k'" if "e \<in> set (edims E)" for e
        using et that by (simp add: map_eq_conv)
      let ?Z = "afiber F (flod F) k" and ?Z' = "afiber F' (flod F') k'"
      let ?K = "rproj (?m \<squnion> flod (finclude R F)) ` ?Z" and ?K' = "rproj (?m \<squnion> flod (finclude R F')) ` ?Z'"
      let ?P = "rproj (?m \<squnion> R) ` ?Z" and ?\<pi> = "Rep_cfun (proj (?m \<squnion> R))"
      have P: "rproj (?m \<squnion> R) ` ?Z' = ?P"
      proof (rule emb_image_eq)
        show "Rep_cfun emb ` rproj (?m \<squnion> R) ` ?Z' = Rep_cfun emb ` ?P"
          using eh by (simp add: fiber[OF k1] fiber[OF k2] image_image ok)
      qed
      define \<psi> where "\<psi> = inv_into ?K ?\<pi>"
      define \<psi>' where "\<psi>' = inv_into ?K' ?\<pi>"
      have b: "bij_betw \<psi> ?P ?K" unfolding \<psi>_def by (rule bij_betw_inv_into[OF bij])
      have b': "bij_betw \<psi>' ?P ?K'" unfolding \<psi>'_def using bij_betw_inv_into[OF bij[of F' k']] by (simp only: P)
      have sP: "?\<pi> ` ?K = ?P" by (rule bij_betw_imp_surj_on[OF bij])
      have sP': "?\<pi> ` ?K' = ?P" using bij_betw_imp_surj_on[OF bij[of F' k']] by (simp only: P)
      have pt: "esem E (finclude R F) (\<psi> p) = esem E (finclude R F') (\<psi>' p)" if p: "p \<in> ?P" for p
      proof -
        have pK: "\<psi> p \<in> ?K" unfolding \<psi>_def by (rule inv_into_into) (simp only: sP p)
        have pK': "\<psi>' p \<in> ?K'" unfolding \<psi>'_def by (rule inv_into_into) (simp only: sP' p)
        obtain y where y: "y \<in> ?Z" "\<psi> p = rproj (?m \<squnion> flod (finclude R F)) y" using pK by blast
        obtain y' where y': "y' \<in> ?Z'" "\<psi>' p = rproj (?m \<squnion> flod (finclude R F')) y'" using pK' by blast
        have py: "proj (?m \<squnion> R)\<cdot>(\<psi> p) = p" unfolding \<psi>_def by (rule f_inv_into_f) (simp only: sP p)
        have py': "proj (?m \<squnion> R)\<cdot>(\<psi>' p) = p" unfolding \<psi>'_def by (rule f_inv_into_f) (simp only: sP' p)
        show ?thesis
        proof (rule E.content_law)
          show "proj (?m \<squnion> flod (finclude R F))\<cdot>(\<psi> p) = \<psi> p" by (simp only: y(2) proj_idem)
          show "proj (?m \<squnion> flod (finclude R F'))\<cdot>(\<psi>' p) = \<psi>' p" by (simp only: y'(2) proj_idem)
          show "contents (edims E) (finclude R F) (\<psi> p) = contents (edims E) (finclude R F') (\<psi>' p)"
          proof (rule map_cong[OF refl])
            fix e assume e: "e \<in> set (edims E)"
            show "content e (finclude R F) (\<psi> p) = content e (finclude R F') (\<psi>' p)"
              by (simp only: inner[OF e y(1) y(2) py] inner[OF e y'(1) y'(2) py'] ptw[OF e])
          qed
        qed
      qed
      have "agg_fold f (esem E (finclude R F)) ?K = agg_fold f (esem E (finclude R F) \<circ> \<psi>) ?P"
        by (rule agg_fold_bij[OF f b, symmetric])
      also have "\<dots> = agg_fold f (esem E (finclude R F') \<circ> \<psi>') ?P"
        by (rule agg_fold_cong[OF f refl]) (simp add: pt)
      also have "\<dots> = agg_fold f (esem E (finclude R F')) ?K'"
        by (rule agg_fold_bij[OF f b'])
      finally show ?thesis .
    qed
  qed
qed

end

end
