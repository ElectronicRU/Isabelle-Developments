theory Content_Law
  imports Frame "HOLCF-Library.List_Cpo" "HOLCF-Library.Option_Cpo"
begin

default_sort type

section \<open>The content law\<close>

text \<open>An expression reads its data through a finite list of \<^emph>\<open>generalized tables\<close>.  An entry's
  \<^emph>\<open>selector\<close> \<open>(a, \<rho>)\<close> picks the fiber: the rows of the frame whose key agrees with the key at hand
  at \<open>a \<squnion> \<rho> \<sqinter> L\<close>, for the frame LOD \<open>L\<close>, among the rows passing the ambient filter and the slice
  coarsened to \<open>\<rho>\<close>.  Its guard cuts the fiber down, and its \<^emph>\<open>view\<close> \<open>(c, \<kappa>)\<close> reads the rest: the
  content maps each row's key at \<open>\<kappa>\<close> to its section at \<open>c\<close>, which the key determines.  The
  \<^emph>\<open>content law\<close> says that the semantics at a key is a function of these contents.\<close>

subsection \<open>Observations\<close>

text \<open>Observations are continuous maps from rows into observed values.  A selection reads as a
  continuous truth value; selections pull back along continuous maps.\<close>

definition sel_chi :: "'r::pcpo sel \<Rightarrow> 'r \<rightarrow> tr" where
  "sel_chi P = (\<Lambda> x. if selects P x then TT else \<bottom>)"

lemma cont_sel_chi: "cont (\<lambda>x. if selects P x then TT else (\<bottom>::tr))"
proof (rule contI2)
  show m: "monofun (\<lambda>x. if selects P x then TT else (\<bottom>::tr))"
    by (rule monofunI) (auto dest: selects_up)
  fix Y :: "nat \<Rightarrow> 'a" assume Y: "chain Y"
  have ch: "chain (\<lambda>i. if selects P (Y i) then TT else (\<bottom>::tr))"
    by (rule ch2ch_monofun[OF m Y])
  show "(if selects P (\<Squnion>i. Y i) then TT else \<bottom>) \<sqsubseteq> (\<Squnion>i. if selects P (Y i) then TT else (\<bottom>::tr))"
  proof (cases "\<exists>i. selects P (Y i)")
    case True
    then obtain i where i: "selects P (Y i)" by blast
    have "(if selects P (Y i) then TT else (\<bottom>::tr)) \<sqsubseteq> (\<Squnion>i. if selects P (Y i) then TT else (\<bottom>::tr))"
      by (rule is_ub_thelub[OF ch])
    then show ?thesis using i by simp
  next
    case False
    then have "\<not> selects P (\<Squnion>i. Y i)" by (intro admD[OF selects_open Y]) blast
    then show ?thesis by simp
  qed
qed

lemma sel_chi_apply: "sel_chi P\<cdot>x = (if selects P x then TT else \<bottom>)"
  unfolding sel_chi_def by (rule beta_cfun[OF cont_sel_chi])

lift_definition sel_vimage :: "('a::pcpo \<rightarrow> 'b::pcpo) \<Rightarrow> 'b sel \<Rightarrow> 'a sel" is "\<lambda>g P x. P (g\<cdot>x)"
proof (intro conjI allI impI)
  fix g :: "'a \<rightarrow> 'b" and P :: "'b \<Rightarrow> bool" and x y :: 'a
  assume P: "(\<forall>x y. P x \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> P y) \<and> adm (\<lambda>x. \<not> P x)"
  show "P (g\<cdot>y)" if "P (g\<cdot>x)" "x \<sqsubseteq> y" using P that monofun_cfun_arg by blast
next
  fix g :: "'a \<rightarrow> 'b" and P :: "'b \<Rightarrow> bool"
  assume P: "(\<forall>x y. P x \<longrightarrow> x \<sqsubseteq> y \<longrightarrow> P y) \<and> adm (\<lambda>x. \<not> P x)"
  show "adm (\<lambda>x. \<not> P (g\<cdot>x))" by (rule adm_subst[OF cont_Rep_cfun2]) (use P in blast)
qed

lemma selects_sel_vimage [simp]: "selects (sel_vimage g P) x \<longleftrightarrow> selects P (g\<cdot>x)"
  by (simp add: sel_vimage.rep_eq)

text \<open>The truth value \<open>TT\<close> is maximal and compact, so being \<open>TT\<close> is a selection.\<close>

lift_definition sel_TT :: "tr sel" is "\<lambda>t. t = TT"
proof (intro conjI allI impI)
  show "y = TT" if "x = TT" "x \<sqsubseteq> y" for x y :: tr using that by simp
  show "adm (\<lambda>t. t \<noteq> TT)" by (simp add: compact_TT eq_commute[of _ TT])
qed

lemma selects_sel_TT [simp]: "selects sel_TT t \<longleftrightarrow> t = TT"
  by (simp add: sel_TT.rep_eq)

text \<open>Guards are continuous truth-valued functions of the parts of a declared view: the section
  of the row and the part of its key that they read.  On rows they are read through their view, so
  they read nothing else.\<close>

record ('r::"{domain, distributive_cpo}", 'k::"{domain, distributive_cpo}", 'b::cpo) vfn =
  vfun :: "'r \<times> 'k \<rightarrow> 'b"
  oview :: "('r, 'k) view"

hide_const (open) vfn.truncate

type_synonym ('r, 'k) guard = "('r, 'k, tr) vfn"

abbreviation ocols :: "('r::{domain, distributive_cpo}, 'k::{domain, distributive_cpo}, 'b::cpo) vfn \<Rightarrow> 'r semi_factor" where
  "ocols f \<equiv> fst (oview f)"

abbreviation okeys :: "('r::{domain, distributive_cpo}, 'k::{domain, distributive_cpo}, 'b::cpo) vfn \<Rightarrow> 'k semi_factor" where
  "okeys f \<equiv> snd (oview f)"

text \<open>Reading the section at a view.\<close>

definition vsection :: "('r::{domain, distributive_cpo}, 'k::{domain, distributive_cpo}) view \<Rightarrow> ('r, 'k, 'r) vfn" where
  "vsection v = \<lparr>vfun = cfst, oview = v\<rparr>"

lemma oview_vsection [simp]: "oview (vsection v) = v"
  by (simp add: vsection_def)

text \<open>The guard every row passes, and the conjunction of guards, on the joined view.\<close>

definition gtrue :: "('r::{domain, distributive_cpo}, 'k::{domain, distributive_cpo}) guard" where
  "gtrue = \<lparr>vfun = \<Lambda> _. TT, oview = \<bottom>\<rparr>"

lemma oview_gtrue [simp]: "oview gtrue = \<bottom>"
  by (simp add: gtrue_def)

definition gand :: "('r::{domain, distributive_cpo}, 'k::{domain, distributive_cpo}) guard \<Rightarrow> ('r, 'k) guard \<Rightarrow> ('r, 'k) guard" where
  "gand \<gamma> \<delta> = \<lparr>vfun = \<Lambda> p. (vfun \<gamma>\<cdot>(pproj (oview \<gamma>)\<cdot>p)) andalso (vfun \<delta>\<cdot>(pproj (oview \<delta>)\<cdot>p)),
     oview = oview \<gamma> \<squnion> oview \<delta>\<rparr>"

lemma gand_view [simp]: "oview (gand \<gamma> \<delta>) = oview \<gamma> \<squnion> oview \<delta>"
  by (simp add: gand_def)

text \<open>An entry: a selector, picking the fiber; a guard, cutting it down; and a view, whose key
  part keys the content and whose section is recorded at each key.\<close>

record 'k selector =
  lower_part :: "'k semi_factor"
  upper_part :: "'k semi_factor"

hide_const (open) selector.truncate

abbreviation sel :: "'k semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> 'k selector" where
  "sel a \<rho> \<equiv> \<lparr>lower_part = a, upper_part = \<rho>\<rparr>"

text \<open>A selector is the affine LOD map \<open>L \<mapsto> a \<squnion> \<rho> \<sqinter> L\<close>: at the frame LOD it gives the group LOD.\<close>

abbreviation sel_at :: "('k::{bifinite, distributive_cpo}) selector \<Rightarrow> 'k semi_factor \<Rightarrow> 'k semi_factor" where
  "sel_at S L \<equiv> lower_part S \<squnion> (upper_part S \<sqinter> L)"

record ('k::"{domain, distributive_cpo}", 'r::"{domain, distributive_cpo}") entry =
  esel :: "'k selector"
  eguard :: "('r, 'k) guard"
  eview :: "('r, 'k) view"

hide_const (open) entry.truncate

abbreviation elower :: "('k::{domain, distributive_cpo}, 'r::{domain, distributive_cpo}) entry \<Rightarrow> 'k semi_factor" where
  "elower e \<equiv> lower_part (esel e)"

abbreviation eupper :: "('k::{domain, distributive_cpo}, 'r::{domain, distributive_cpo}) entry \<Rightarrow> 'k semi_factor" where
  "eupper e \<equiv> upper_part (esel e)"

abbreviation ekeys :: "('k::{domain, distributive_cpo}, 'r::{domain, distributive_cpo}) entry \<Rightarrow> 'k semi_factor" where
  "ekeys e \<equiv> snd (eview e)"

abbreviation ecols :: "('k::{domain, distributive_cpo}, 'r::{domain, distributive_cpo}) entry \<Rightarrow> 'r semi_factor" where
  "ecols e \<equiv> fst (eview e)"

abbreviation mk_entry ::
  "'k selector \<Rightarrow> ('r, 'k) guard \<Rightarrow> ('r, 'k) view \<Rightarrow> ('k::{domain, distributive_cpo}, 'r::{domain, distributive_cpo}) entry" where
  "mk_entry S \<gamma> v \<equiv> \<lparr>esel = S, eguard = \<gamma>, eview = v\<rparr>"

record ('k::"domain", 'f::type, 'r::"{bifinite, distributive_cpo}", 'v::cpo) expr =
  emind :: "'k semi_factor"
  edims :: "('k, 'r) entry list"
  esem :: "'r lower_pd \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<rightharpoonup> 'v"
  csem :: "('k \<Rightarrow> 'r option) list \<rightarrow> 'v option"

hide_const (open) expr.truncate

text \<open>Contents are maps from keys to sections.  A graph, a single-valued set of pairs, gives one;
  the value it records at a key is \<open>cval\<close>.\<close>

definition cval :: "('k \<times> 'b) set \<Rightarrow> 'k \<Rightarrow> 'b" where
  "cval X q = (THE v. (q, v) \<in> X)"

lemma cval_singleton [simp]: "cval {(q, v)} q = v"
  by (simp add: cval_def)

lemma cval_eq: "single_valued X \<Longrightarrow> (q, v) \<in> X \<Longrightarrow> cval X q = v"
  unfolding cval_def by (rule the_equality) (auto dest: single_valuedD)

definition gmap :: "('k \<times> 'b) set \<Rightarrow> 'k \<Rightarrow> 'b option" where
  "gmap X q = (if q \<in> fst ` X then Some (cval X q) else None)"

definition graph :: "('k \<Rightarrow> 'b option) \<Rightarrow> ('k \<times> 'b) set" where
  "graph m = {(q, s). m q = Some s}"

lemma dom_gmap [simp]: "dom (gmap X) = fst ` X"
  by (auto simp: gmap_def dom_def)

lemma gmap_empty_iff [simp]: "gmap X = Map.empty \<longleftrightarrow> X = {}"
  unfolding dom_eq_empty_conv[symmetric] dom_gmap by simp

lemma gmap_apply: "single_valued X \<Longrightarrow> (q, s) \<in> X \<Longrightarrow> gmap X q = Some s"
  unfolding gmap_def by (simp add: cval_eq rev_image_eqI)

lemma gmap_singleton [simp]: "gmap {(q, s)} = [q \<mapsto> s]"
  by (auto simp: gmap_def fun_eq_iff)

lemma single_valued_graph: "single_valued (graph m)"
  by (auto simp: single_valued_def graph_def)

lemma graph_gmap:
  assumes X: "single_valued X"
  shows "graph (gmap X) = X"
proof (rule set_eqI, rule iffI)
  fix x assume "x \<in> graph (gmap X)"
  then obtain q s where x: "x = (q, s)" and q: "gmap X q = Some s" by (auto simp: graph_def)
  then obtain s' where s': "(q, s') \<in> X" by (force simp: gmap_def split: if_splits)
  then show "x \<in> X" using q gmap_apply[OF X s'] by (simp add: x)
next
  fix x assume "x \<in> X"
  then show "x \<in> graph (gmap X)" using gmap_apply[OF X] by (cases x) (simp add: graph_def)
qed

lemma gmap_graph [simp]: "gmap (graph m) = m"
proof
  fix q show "gmap (graph m) q = m q"
  proof (cases "m q")
    case None
    then have "q \<notin> fst ` graph m" by (force simp: graph_def)
    then show ?thesis using None by (simp add: gmap_def)
  next
    case (Some s)
    then have "(q, s) \<in> graph m" by (simp add: graph_def)
    from gmap_apply[OF single_valued_graph this] Some show ?thesis by simp
  qed
qed

subsection \<open>Continuity on contents\<close>

text \<open>Contents are ordered pointwise with missing keys incomparable to present ones, so refining
  a content keeps its keys; results are ordered likewise, and lists componentwise.  The content
  semantics is a continuous function.  Along a chain the keys stay fixed, so a function of a
  \<^emph>\<open>rigid\<close> part of the argument (one that is the same on related arguments) is continuous, and a
  rigid argument may be held fixed.\<close>

definition rigid :: "('a::cpo \<Rightarrow> 'b) \<Rightarrow> bool" where
  "rigid q \<longleftrightarrow> (\<forall>x y. x \<sqsubseteq> y \<longrightarrow> q x = q y)"

lemma rigidI: "(\<And>x y. x \<sqsubseteq> y \<Longrightarrow> q x = q y) \<Longrightarrow> rigid q"
  unfolding rigid_def by blast

lemma rigidD: "rigid q \<Longrightarrow> x \<sqsubseteq> y \<Longrightarrow> q x = q y"
  unfolding rigid_def by blast

lemma rigid_chain: "rigid q \<Longrightarrow> chain Y \<Longrightarrow> q (Y i) = q (\<Squnion>j. Y j)"
  by (erule rigidD) (erule is_ub_thelub)

lemma rigid_comp: "rigid q \<Longrightarrow> monofun g \<Longrightarrow> rigid (\<lambda>x. q (g x))"
  unfolding rigid_def by (blast dest: monofunE)

lemma cont_rigid_arg:
  fixes h :: "'a::cpo \<Rightarrow> 's \<Rightarrow> 'b::cpo"
  assumes h: "\<And>s. cont (\<lambda>x. h x s)" and q: "rigid q"
  shows "cont (\<lambda>x. h x (q x))"
proof (rule contI2)
  show "monofun (\<lambda>x. h x (q x))"
  proof (rule monofunI)
    fix x y :: 'a assume xy: "x \<sqsubseteq> y"
    have "q y = q x" using rigidD[OF q xy] by simp
    then show "h x (q x) \<sqsubseteq> h y (q y)" by (simp only: cont2monofunE[OF h xy])
  qed
next
  fix Y :: "nat \<Rightarrow> 'a" assume Y: "chain Y"
  have "h (\<Squnion>i. Y i) (q (\<Squnion>i. Y i)) = (\<Squnion>i. h (Y i) (q (\<Squnion>i. Y i)))" by (rule cont2contlubE[OF h Y])
  also have "\<dots> = (\<Squnion>i. h (Y i) (q (Y i)))" by (simp only: rigid_chain[OF q Y])
  finally show "h (\<Squnion>i. Y i) (q (\<Squnion>i. Y i)) \<sqsubseteq> (\<Squnion>i. h (Y i) (q (Y i)))" by simp
qed

lemma cont_rigid: "rigid f \<Longrightarrow> cont f"
  using cont_rigid_arg[of "\<lambda>x s. s" f] by simp

lemma cont_if_rigid:
  assumes "rigid P" and "cont f" and "cont g"
  shows "cont (\<lambda>x. if P x then f x else g x)"
proof -
  have "cont (\<lambda>x. if b then f x else g x)" for b by (cases b) (simp_all add: assms)
  then show ?thesis by (rule cont_rigid_arg[OF _ assms(1)])
qed

lemma map_below_dom: "(X :: 'k \<Rightarrow> 'r::below option) \<sqsubseteq> Y \<Longrightarrow> dom X = dom Y"
proof -
  assume b: "X \<sqsubseteq> Y"
  have "X q = None \<longleftrightarrow> Y q = None" for q
    using fun_belowD[OF b, of q] by (cases "X q"; cases "Y q") simp_all
  then show ?thesis unfolding dom_def by auto
qed

lemma option_below_None: "(u :: 'v::below option) \<sqsubseteq> w \<Longrightarrow> u = None \<longleftrightarrow> w = None"
  by (cases u; cases w) simp_all

lemma rigid_dom: "rigid (\<lambda>X :: 'k \<Rightarrow> 'r::cpo option. dom X)"
  by (rule rigidI) (rule map_below_dom)

lemma rigid_None: "monofun f \<Longrightarrow> rigid (\<lambda>x. f x = (None :: 'v::cpo option))"
  by (rule rigidI) (rule option_below_None, erule monofunE)

lemma cont_hd: "cont (hd :: 'a::cpo list \<Rightarrow> 'a)"
  by (rule list_contI[where g = "\<lambda>x xs y. x"]) simp_all

lemma cont_tl: "cont (tl :: 'a::cpo list \<Rightarrow> 'a list)"
  by (rule list_contI[where g = "\<lambda>x xs y. xs"]) simp_all

lemmas cont2cont_hd [simp, cont2cont] = cont_compose[OF cont_hd]
lemmas cont2cont_tl [simp, cont2cont] = cont_compose[OF cont_tl]

lemma cont_take: "cont (take n :: 'a::cpo list \<Rightarrow> 'a list)"
proof (induct n)
  case (Suc n)
  show ?case by (rule list_contI[where g = "\<lambda>x xs y. x # take n xs"]) (simp_all add: Suc cont_compose)
qed simp

lemma cont_drop: "cont (drop n :: 'a::cpo list \<Rightarrow> 'a list)"
proof (induct n)
  case (Suc n)
  show ?case by (rule list_contI[where g = "\<lambda>x xs y. drop n xs"]) (simp_all add: Suc)
qed (simp add: cont_id)

lemma cont_the: "cont (the :: 'a::cpo option \<Rightarrow> 'a)"
proof (rule contI2[OF monofun_the])
  fix Y :: "nat \<Rightarrow> 'a option" assume Y: "chain Y"
  then show "the (\<Squnion>i. Y i) \<sqsubseteq> (\<Squnion>i. the (Y i))"
  proof (cases rule: option_chain_cases)
    case (2 A)
    then show ?thesis by (simp add: lub_Some)
  qed simp
qed

lemma cont_map2: "(\<And>a. cont (h a)) \<Longrightarrow> cont (\<lambda>xs. map2 h as xs)"
proof (induct as)
  case (Cons a as)
  show ?case
    by (rule list_contI[where g = "\<lambda>y ys z. h a y # map2 h as ys"]) (simp_all add: Cons)
qed simp

lemma cont_those: "cont (those :: 'a::cpo option list \<Rightarrow> 'a list option)"
  by (rule list_contI[where g = "\<lambda>x xs y. case x of None \<Rightarrow> None | Some a \<Rightarrow> map_option (Cons a) y"])
    (simp_all split: option.split)

subsection \<open>Groups and contents\<close>

context dataspace
begin

text \<open>Reading a guard or a section on rows.\<close>

definition ofun :: "('r, 'k, 'b::cpo) vfn \<Rightarrow> 'r \<rightarrow> 'b" where
  "ofun f = vfun f oo vproj (oview f)"

lemma ofun_apply: "ofun f\<cdot>y = vfun f\<cdot>(vpart (oview f) y)"
  by (simp add: ofun_def)

lemma ofun_vsection [simp]: "ofun (vsection v)\<cdot>y = y \<downharpoonright> fst v"
  by (simp add: ofun_apply vsection_def vpart_def)

lemma ofun_gtrue [simp]: "ofun gtrue\<cdot>y = TT"
  by (simp add: ofun_apply gtrue_def)

lemma gand_apply: "ofun (gand \<gamma> \<delta>)\<cdot>y = (ofun \<gamma>\<cdot>y andalso ofun \<delta>\<cdot>y)"
  by (simp add: ofun_apply gand_def vpart_pproj lattice_join_ge1 lattice_join_ge2)

lemma gand_TT [simp]: "ofun (gand \<gamma> \<delta>)\<cdot>y = TT \<longleftrightarrow> ofun \<gamma>\<cdot>y = TT \<and> ofun \<delta>\<cdot>y = TT"
  unfolding gand_apply by (cases "ofun \<gamma>\<cdot>y" rule: trE) simp_all

text \<open>The rows a test passes are a selection.\<close>

definition gsel :: "('r, 'k) guard \<Rightarrow> 'r sel" where
  "gsel \<gamma> = sel_vimage (ofun \<gamma>) sel_TT"

lemma selects_gsel [simp]: "selects (gsel \<gamma>) y \<longleftrightarrow> ofun \<gamma>\<cdot>y = TT"
  by (simp add: gsel_def)

text \<open>Whether a row passes a slice, as a guard.\<close>

definition guard_holds :: "'f \<Rightarrow> ('r, 'k) guard" where
  "guard_holds X = \<lparr>vfun = sel_chi (sopen X) oo csnd, oview = (\<bottom>, slod X)\<rparr>"

lemma guard_holds_apply: "ofun (guard_holds X)\<cdot>y = (if holds X (rkey\<cdot>y) then TT else \<bottom>)"
  by (simp add: ofun_apply guard_holds_def sel_chi_apply holds_def sopen_lod)

lemma guard_holds_view [simp]: "oview (guard_holds X) = (\<bottom>, slod X)"
  by (simp add: guard_holds_def)

lemma guard_holds_TT [simp]: "ofun (guard_holds X)\<cdot>y = TT \<longleftrightarrow> holds X (rkey\<cdot>y)"
  by (simp add: guard_holds_apply)

subsection \<open>Supports of guards\<close>

text \<open>A guard or section is \<^emph>\<open>supported\<close> when its view is keyed: within every
  conforming dataset its key part determines it on rows.\<close>

definition supported :: "('r, 'k, 'b::cpo) vfn \<Rightarrow> bool" where
  "supported f \<longleftrightarrow> keyed_view (oview f)"

lemma supported_fun_support: "supported f \<Longrightarrow> fun_support (oview f) (ofun f)"
proof -
  assume f: "supported f"
  have "determines UNIV (oview f) (vfun f oo vproj (oview f))"
    by (rule determines_comp) (rule vfd_refl[OF below_refl])
  moreover have "universally (\<lambda>P. determines P (vkey (oview f)) (vfun f oo vproj (oview f)))"
    unfolding universally_def using keyed_view_determines f[unfolded supported_def] by blast
  ultimately show ?thesis unfolding fun_support_def ofun_def by blast
qed

lemma supported_determines:
  "supported f \<Longrightarrow> conforms X \<Longrightarrow> determines (lower_maximal X) (vkey (oview f)) (ofun f)"
  unfolding supported_def ofun_def by (rule keyed_view_determines)

text \<open>Rows agreeing on a key part covering a supported function's key part agree on it.\<close>

lemma supported_agree:
  assumes h: "supported h" and d: "conforms data" and x: "x \<in> lower_maximal data" and y: "y \<in> lower_maximal data"
    and le: "okeys h \<sqsubseteq> G" and e: "rproj G y = rproj G x"
  shows "ofun h\<cdot>y = ofun h\<cdot>x"
proof (rule determinesD[OF supported_determines[OF h d] y x])
  have "rproj (okeys h) y = rproj (okeys h) x"
    using arg_cong[OF e, of "Rep_cfun (proj (okeys h))"] by (simp add: proj_le[OF le])
  then show "vpart (vkey (oview h)) y = vpart (vkey (oview h)) x" by (simp add: vkey_def proj_bot)
qed

text \<open>Rows agreeing on a key part covering a keyed view's key part agree on its section.\<close>

lemma view_agree:
  assumes v: "keyed_view v" and d: "conforms data" and x: "x \<in> lower_maximal data" and y: "y \<in> lower_maximal data"
    and le: "snd v \<sqsubseteq> G" and e: "rproj G y = rproj G x"
  shows "y \<downharpoonright> fst v = x \<downharpoonright> fst v"
proof -
  have "supported (vsection v)" using v by (simp add: supported_def)
  from supported_agree[OF this d x y _ e] le show ?thesis by simp
qed

lemma keyed_view_bot_view: "keyed_view (\<bottom> :: ('r, 'k) view)"
  unfolding inst_prod_pcpo by (rule keyed_view_key)

text \<open>A guard is \<^emph>\<open>key-pure\<close> when its view is its key part: then it is determined by its key
  part on all rows, independently of any dataset.  Slice tests are key-pure.\<close>

definition key_pure :: "('r, 'k, 'b::cpo) vfn \<Rightarrow> bool" where
  "key_pure f \<longleftrightarrow> vkey (oview f) = oview f"

lemma key_pure_determines: "key_pure f \<Longrightarrow> determines UNIV (oview f) (ofun f)"
  unfolding ofun_def by (rule determines_comp) (rule vfd_refl[OF below_refl])

lemma key_pure_guard_holds: "key_pure (guard_holds X)"
  by (simp add: key_pure_def vkey_def)

lemma supported_guard_holds: "supported (guard_holds X)"
  by (simp add: supported_def keyed_view_key)

lemma supported_gtrue: "supported gtrue"
  unfolding supported_def oview_gtrue inst_prod_pcpo by (rule keyed_view_key)

lemma supported_gand: "supported \<gamma> \<Longrightarrow> supported \<delta> \<Longrightarrow> supported (gand \<gamma> \<delta>)"
  by (simp add: supported_def keyed_view_sup)

text \<open>An entry is \<^emph>\<open>well-formed\<close> when its view is keyed and its guard supported.  Then the
  view's key part determines its section on the rows of a conforming dataset: contents are graphs.
  This is a property of the expression, independent of the frame.\<close>

definition entry_wf :: "('k, 'r) entry \<Rightarrow> bool" where
  "entry_wf e \<longleftrightarrow> keyed_view (eview e) \<and> supported (eguard e)"

lemma okeys_gtrue [simp]: "okeys gtrue = \<bottom>"
  unfolding oview_gtrue inst_prod_pcpo by (rule snd_conv)

lemma entry_wf_view: "keyed_view v \<Longrightarrow> supported \<gamma> \<Longrightarrow> entry_wf (mk_entry S \<gamma> v)"
  by (simp add: entry_wf_def)

lemma entry_wf_guard: "entry_wf e \<Longrightarrow> supported \<gamma> \<Longrightarrow> entry_wf (e\<lparr>eguard := gand \<gamma> (eguard e)\<rparr>)"
  by (simp add: entry_wf_def supported_gand)

definition group :: "'r lower_pd \<Rightarrow> 'k semi_factor \<Rightarrow> 'k semi_factor \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'r set" where
  "group data a \<rho> F k = {y \<in> lower_maximal data. selects (amb F) y \<and> holds (coarsen \<rho> (slice F)) (rkey\<cdot>y) \<and>
     rproj (a \<squnion> (\<rho> \<sqinter> flod F)) y = proj (a \<squnion> (\<rho> \<sqinter> flod F))\<cdot>k}"

text \<open>The fiber of an entry: the rows of its group passing its guard.  Its content graph pairs
  each row's key at the view's key part with its section at the view's columns; the content is
  that graph as a map.\<close>

definition efiber :: "'r lower_pd \<Rightarrow> ('k, 'r) entry \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'r set" where
  "efiber data e F k = {y \<in> group data (elower e) (eupper e) F k. ofun (eguard e)\<cdot>y = TT}"

definition cpair :: "('k, 'r) entry \<Rightarrow> 'r \<Rightarrow> 'k \<times> 'r" where
  "cpair e y = (rproj (ekeys e) y, y \<downharpoonright> ecols e)"

lemma cpair_vpart: "cpair e y = (snd (vpart (eview e) y), fst (vpart (eview e) y))"
  by (simp add: cpair_def vpart_def)

definition cgraph :: "'r lower_pd \<Rightarrow> ('k, 'r) entry \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> ('k \<times> 'r) set" where
  "cgraph data e F k = cpair e ` efiber data e F k"

definition content :: "'r lower_pd \<Rightarrow> ('k, 'r) entry \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> 'k \<Rightarrow> 'r option" where
  "content data e F k = gmap (cgraph data e F k)"

abbreviation contents :: "'r lower_pd \<Rightarrow> ('k, 'r) entry list \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k \<Rightarrow> ('k \<Rightarrow> 'r option) list" where
  "contents data es F k \<equiv> map (\<lambda>e. content data e F k) es"

text \<open>The \<^emph>\<open>point family\<close> at a row and a key: each entry's content as if its fiber were that one
  row with that key.  A fiber of one row gives the point content.\<close>

definition point :: "('k, 'r) entry list \<Rightarrow> 'r \<times> 'k \<Rightarrow> ('k \<Rightarrow> 'r option) list" where
  "point es p = map (\<lambda>e. [proj (ekeys e)\<cdot>(snd p) \<mapsto> fst p \<downharpoonright> ecols e]) es"

lemma point_simps [simp]:
  "point [] p = []" "point (e # es) p = [proj (ekeys e)\<cdot>(snd p) \<mapsto> fst p \<downharpoonright> ecols e] # point es p"
  "point (es @ es') p = point es p @ point es' p" "length (point es p) = length es"
  by (simp_all add: point_def)

lemma point_concat: "point (concat ess) p = concat (map (\<lambda>es. point es p) ess)"
  by (induct ess) simp_all

lemma content_single_fiber: "efiber data e F k = {y} \<Longrightarrow> content data e F k = hd (point [e] (y, rkey\<cdot>y))"
  by (simp add: content_def cgraph_def cpair_def)

text \<open>A \<^emph>\<open>row entry\<close> keys its view and guard within its lower part: rows of a fiber, which agree
  there, agree on the whole content pair, so its content has at most one key.\<close>

definition row_entry :: "('k, 'r) entry \<Rightarrow> bool" where
  "row_entry e \<longleftrightarrow> ekeys e \<sqsubseteq> elower e \<and> okeys (eguard e) \<sqsubseteq> elower e"

lemma rproj_agree: "s \<sqsubseteq> G \<Longrightarrow> rproj G y = rproj G x \<Longrightarrow> rproj s y = rproj s x"
  by (metis proj_le)

lemma row_entry_image:
  assumes e: "entry_wf e" and r: "row_entry e" and d: "conforms data" and Y: "Y \<subseteq> lower_maximal data"
    and x: "x \<in> Y" and aG: "elower e \<sqsubseteq> G" and agree: "\<And>y. y \<in> Y \<Longrightarrow> rproj G y = rproj G x"
  shows "cpair e ` {y \<in> Y. ofun (eguard e)\<cdot>y = TT} = (if ofun (eguard e)\<cdot>x = TT then {cpair e x} else {})"
proof -
  have sG: "ekeys e \<sqsubseteq> G" and gG: "okeys (eguard e) \<sqsubseteq> G"
    using r aG unfolding row_entry_def by (blast intro: below_trans)+
  have xm: "x \<in> lower_maximal data" using x Y by blast
  have kv: "keyed_view (eview e)" and sup: "supported (eguard e)" using e by (simp_all add: entry_wf_def)
  let ?g = "\<lambda>y. ofun (eguard e)\<cdot>y"
  have g: "?g y = ?g x" if y: "y \<in> Y" for y
    using supported_agree[OF sup d xm _ gG agree[OF y]] y Y by blast
  have h: "cpair e y = cpair e x" if y: "y \<in> Y" for y
    using rproj_agree[OF sG agree[OF y]] view_agree[OF kv d xm _ sG agree[OF y]] y Y
    unfolding cpair_def by blast
  show ?thesis
  proof (cases "?g x = TT")
    case True
    have "{y \<in> Y. ?g y = TT} = Y"
    proof (rule set_eqI, rule iffI)
      fix y assume "y \<in> Y"
      then show "y \<in> {y \<in> Y. ?g y = TT}" using True by (simp add: g)
    qed simp
    moreover have "cpair e ` Y = (\<lambda>_. cpair e x) ` Y" by (rule image_cong[OF refl h])
    moreover have "Y \<noteq> {}" using x by blast
    ultimately show ?thesis using True by (simp only: image_constant_conv if_False) simp
  next
    case False
    have "{y \<in> Y. ?g y = TT} = {}"
    proof (rule equals0I)
      fix y assume "y \<in> {y \<in> Y. ?g y = TT}"
      then have y: "y \<in> Y" "?g y = TT" by simp_all
      then have "?g x = TT" by (simp only: g[OF y(1)])
      then show False using False by simp
    qed
    then show ?thesis using False by simp
  qed
qed

text \<open>Content graphs of well-formed entries are single-valued.\<close>

lemma cgraph_single_valued:
  assumes e: "entry_wf e" and d: "conforms data"
  shows "single_valued (cgraph data e F k)"
proof (rule single_valuedI)
  fix q u u' assume u: "(q, u) \<in> cgraph data e F k" and u': "(q, u') \<in> cgraph data e F k"
  obtain y where y: "y \<in> efiber data e F k" "q = rproj (ekeys e) y" "u = y \<downharpoonright> ecols e"
    using u unfolding cgraph_def cpair_def by blast
  obtain y' where y': "y' \<in> efiber data e F k" "q = rproj (ekeys e) y'" "u' = y' \<downharpoonright> ecols e"
    using u' unfolding cgraph_def cpair_def by blast
  have m: "y \<in> lower_maximal data" "y' \<in> lower_maximal data"
    using y(1) y'(1) by (auto simp: efiber_def group_def)
  have kv: "keyed_view (eview e)" using e by (simp add: entry_wf_def)
  have "y' \<downharpoonright> ecols e = y \<downharpoonright> ecols e"
    by (rule view_agree[OF kv d m(1) m(2) below_refl]) (use y(2) y'(2) in simp)
  then show "u = u'" using y(3) y'(3) by simp
qed

lemma graph_content: "entry_wf e \<Longrightarrow> conforms data \<Longrightarrow> graph (content data e F k) = cgraph data e F k"
  unfolding content_def by (rule graph_gmap[OF cgraph_single_valued])

subsection \<open>Column supports of frames and sections of datasets\<close>

text \<open>A selection \<^emph>\<open>reads\<close> a section of the row when it is decided there.  A frame reads a
  section covering its ambient filter and the column support of its slice's LOD.  The
  \<^emph>\<open>point section\<close> of a dataset at a section is the set of its data points cut down to it; it is
  a plain set, not down-closed: contents are sets of values over data points.\<close>

definition sel_reads :: "'r semi_factor \<Rightarrow> 'r sel \<Rightarrow> bool" where
  "sel_reads c P \<longleftrightarrow> (\<forall>y. selects P (y \<downharpoonright> c) \<longleftrightarrow> selects P y)"

definition frame_reads :: "'r semi_factor \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> bool" where
  "frame_reads c F \<longleftrightarrow> sel_reads c (amb F) \<and> csupp (slod (slice F)) \<sqsubseteq> c"

definition pts_section :: "'r semi_factor \<Rightarrow> 'r lower_pd \<Rightarrow> 'r set" where
  "pts_section c data = (\<lambda>y. y \<downharpoonright> c) ` lower_maximal data"

lemma image_filter_factor:
  assumes "\<And>y. Q (g y) = Q y" and "\<And>y. h (g y) = h y"
  shows "h ` {y \<in> M. Q y} = h ` {z \<in> g ` M. Q z}"
proof -
  have "{z \<in> g ` M. Q z} = g ` {y \<in> M. Q y}" using assms(1) by auto
  then show ?thesis by (simp add: image_image assms(2))
qed

lemma holds_section: "csupp (slod X) \<sqsubseteq> c \<Longrightarrow> holds X (rkey\<cdot>(y \<downharpoonright> c)) \<longleftrightarrow> holds X (rkey\<cdot>y)"
  by (metis holds_lod rproj_section)

text \<open>A view's parts are read off any section covering its columns and its key part's support.\<close>

lemma vpart_section: "fst (vsec v) \<sqsubseteq> c \<Longrightarrow> vpart v (y \<downharpoonright> c) = vpart v y"
  unfolding vsec_def fst_conv
  by (simp add: vpart_def proj_le[OF below_trans[OF lattice_join_ge1]]
      rproj_section[OF below_trans[OF lattice_join_ge2]])

lemma ofun_section: "fst (vsec (oview f)) \<sqsubseteq> c \<Longrightarrow> ofun f\<cdot>(y \<downharpoonright> c) = ofun f\<cdot>y"
  by (simp add: ofun_apply vpart_section)

text \<open>The content of an entry is computed from the point section at any section covering the
  group LOD's support, the frame, and the views of the guard and the entry.\<close>

lemma content_section:
  assumes F: "frame_reads c F" and G: "csupp (sel_at (esel e) (flod F)) \<sqsubseteq> c"
    and fc: "fst (vsec (eview e)) \<sqsubseteq> c" and gc: "fst (vsec (oview (eguard e))) \<sqsubseteq> c"
  shows "content data e F k = gmap (cpair e ` {z \<in> pts_section c data.
    selects (amb F) z \<and> holds (coarsen (eupper e) (slice F)) (rkey\<cdot>z) \<and>
    rproj (sel_at (esel e) (flod F)) z = proj (sel_at (esel e) (flod F))\<cdot>k \<and>
    ofun (eguard e)\<cdot>z = TT})"
proof -
  let ?G = "sel_at (esel e) (flod F)"
  let ?P = "\<lambda>z. selects (amb F) z \<and> holds (coarsen (eupper e) (slice F)) (rkey\<cdot>z) \<and> rproj ?G z = proj ?G\<cdot>k \<and>
    ofun (eguard e)\<cdot>z = TT"
  let ?h = "cpair e"
  have sl: "csupp (slod (coarsen (eupper e) (slice F))) \<sqsubseteq> c"
    using F csupp_mono[OF below_trans[OF slod_coarsen lattice_meet_le1]] unfolding frame_reads_def
    by (blast intro: below_trans)
  have P: "?P (y \<downharpoonright> c) \<longleftrightarrow> ?P y" for y
    using F unfolding frame_reads_def sel_reads_def
    by (simp add: holds_section[OF sl] rproj_section[OF G] ofun_section[OF gc])
  have h: "?h (y \<downharpoonright> c) = ?h y" for y by (simp only: cpair_vpart vpart_section[OF fc])
  have "efiber data e F k = {y \<in> lower_maximal data. ?P y}" by (auto simp: efiber_def group_def)
  moreover have "?h ` {y \<in> lower_maximal data. ?P y} = ?h ` {z \<in> pts_section c data. ?P z}"
    unfolding pts_section_def by (rule image_filter_factor) (fact P h)+
  ultimately show ?thesis unfolding content_def cgraph_def by simp
qed

text \<open>Groups with the same parameters and rows coincide.\<close>

lemma group_cong:
  assumes "amb F = amb F'" "slice F = slice F'"
    and "a \<squnion> (\<rho> \<sqinter> flod F) = a' \<squnion> (\<rho> \<sqinter> flod F')"
    and "proj (a \<squnion> (\<rho> \<sqinter> flod F))\<cdot>k = proj (a' \<squnion> (\<rho> \<sqinter> flod F'))\<cdot>k'"
  shows "group data a \<rho> F k = group data a' \<rho> F' k'"
  using assms unfolding group_def by simp

text \<open>A lower part covering the masked part of the minimal LOD absorbs it.\<close>

lemma sat_absorb:
  fixes a \<rho> m L :: "'k semi_factor"
  assumes "(\<rho> \<sqinter> m) \<sqsubseteq> a"
  shows "a \<squnion> (\<rho> \<sqinter> (m \<squnion> L)) = a \<squnion> (\<rho> \<sqinter> L)"
proof -
  have "a \<squnion> (\<rho> \<sqinter> (m \<squnion> L)) = (a \<squnion> (\<rho> \<sqinter> m)) \<squnion> (\<rho> \<sqinter> L)"
    by (simp only: truncate_sup lattice_join_assoc)
  also have "a \<squnion> (\<rho> \<sqinter> m) = a" by (rule lattice_join_absorb1[OF assms])
  finally show ?thesis .
qed

end

text \<open>Projecting to a finer LOD after a coarser one changes nothing.\<close>

lemma proj_absorb: "a \<sqsubseteq> b \<Longrightarrow> proj b\<cdot>(proj a\<cdot>k) = proj a\<cdot>k"
  by (metis proj_inf lattice_meet_absorb2)

text \<open>Joins of lists in complete lattices.\<close>

lemma fold_join_absorb: "(\<And>x. x \<in> set xs \<Longrightarrow> x \<sqsubseteq> b) \<Longrightarrow> fold (\<squnion>) xs b = (b::'a::lattice_complete)"
  by (induct xs) (simp_all add: lattice_join_absorb2)

lemma fold_join_bots: "fold (\<squnion>) (map (\<lambda>_. \<bottom>) xs) (\<bottom>::'a::lattice_complete) = \<bottom>"
  by (induct xs) (simp_all add: lattice_join_bot_left)

lemma fold_join_least:
  "(\<And>x. x \<in> set xs \<Longrightarrow> x \<sqsubseteq> y) \<Longrightarrow> b \<sqsubseteq> y \<Longrightarrow> fold (\<squnion>) xs b \<sqsubseteq> (y::'a::lattice_complete)"
  by (induct xs arbitrary: b) (simp_all add: lattice_join_least)

lemma fold_join_base: "b \<sqsubseteq> fold (\<squnion>) xs (b::'a::lattice_complete)"
proof (induct xs arbitrary: b)
  case (Cons x xs)
  have "b \<sqsubseteq> x \<squnion> b" by (rule lattice_join_ge2)
  also have "\<dots> \<sqsubseteq> fold (\<squnion>) xs (x \<squnion> b)" by (rule Cons)
  finally show ?case by simp
qed simp

subsection \<open>The laws\<close>

text \<open>A \<^emph>\<open>semilawful\<close> expression has supported entries, its minimal LOD is the join of their lower
  parts, and its presence and values are its content semantics of its contents, at every key of
  its key LOD and every conforming dataset (the content law).  A \<^emph>\<open>lawful\<close> one is moreover
  \<^emph>\<open>saturated\<close> (each lower part covers the part of the minimal LOD its upper part keeps, so groups
  depend on the frame LOD only through the key LOD) and has entries only at the frame's data keys
  (the key law).\<close>

context dataspace
begin

abbreviation kd :: "('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor" where
  "kd E F \<equiv> emind E \<squnion> flod F"

definition semilawful :: "('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> bool" where
  "semilawful E \<longleftrightarrow> emind E = fold (\<squnion>) (map elower (edims E)) \<bottom> \<and> (\<forall>e\<in>set (edims E). entry_wf e) \<and>
     (\<forall>data F k. conforms data \<longrightarrow> proj (kd E F)\<cdot>k = k \<longrightarrow> esem E data F k = csem E\<cdot>(contents data (edims E) F k))"

definition lawful :: "('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> bool" where
  "lawful E \<longleftrightarrow> semilawful E \<and> (\<forall>e\<in>set (edims E). (eupper e \<sqinter> emind E) \<sqsubseteq> elower e) \<and>
     (\<forall>data F k. conforms data \<longrightarrow> esem E data F k \<noteq> None \<longrightarrow> keyimg data F (kd E F) k)"

lemma semilawfulI:
  assumes "emind E = fold (\<squnion>) (map elower (edims E)) \<bottom>"
    and "\<And>e. e \<in> set (edims E) \<Longrightarrow> entry_wf e"
    and "\<And>data F k. \<lbrakk>conforms data; proj (emind E \<squnion> flod F)\<cdot>k = k\<rbrakk> \<Longrightarrow>
           esem E data F k = csem E\<cdot>(contents data (edims E) F k)"
  shows "semilawful E"
  unfolding semilawful_def using assms by blast

lemma semilawful_mind_lub: "semilawful E \<Longrightarrow> emind E = fold (\<squnion>) (map elower (edims E)) \<bottom>"
  unfolding semilawful_def by blast

lemma semilawful_wf: "semilawful E \<Longrightarrow> e \<in> set (edims E) \<Longrightarrow> entry_wf e"
  unfolding semilawful_def by blast

lemma semilawful_keyed: "semilawful E \<Longrightarrow> e \<in> set (edims E) \<Longrightarrow> keyed_view (eview e)"
  and semilawful_guard_supported: "semilawful E \<Longrightarrow> e \<in> set (edims E) \<Longrightarrow> supported (eguard e)"
  using semilawful_wf unfolding entry_wf_def by blast+

lemma semilawful_csem:
  "\<lbrakk>semilawful E; conforms data; proj (kd E F)\<cdot>k = k\<rbrakk> \<Longrightarrow> esem E data F k = csem E\<cdot>(contents data (edims E) F k)"
  unfolding semilawful_def by blast

text \<open>Equal contents give equal values, across datasets and frames.\<close>

lemma semilawful_content_law:
  "\<lbrakk>semilawful E; conforms data; conforms data'; proj (kd E F)\<cdot>k = k; proj (kd E F')\<cdot>k' = k';
    contents data (edims E) F k = contents data' (edims E) F' k'\<rbrakk> \<Longrightarrow> esem E data F k = esem E data' F' k'"
  by (simp only: semilawful_csem)

text \<open>Refined contents give refined values, across datasets and frames: the content semantics is
  continuous.\<close>

lemma semilawful_mono:
  "\<lbrakk>semilawful E; conforms data; conforms data'; proj (kd E F)\<cdot>k = k; proj (kd E F')\<cdot>k' = k';
    contents data (edims E) F k \<sqsubseteq> contents data' (edims E) F' k'\<rbrakk> \<Longrightarrow> esem E data F k \<sqsubseteq> esem E data' F' k'"
  by (simp only: semilawful_csem monofun_cfun_arg)

lemma lawful_semiI:
  assumes "semilawful E"
    and "\<And>e. e \<in> set (edims E) \<Longrightarrow> (eupper e \<sqinter> emind E) \<sqsubseteq> elower e"
    and "\<And>data F k. conforms data \<Longrightarrow> esem E data F k \<noteq> None \<Longrightarrow> keyimg data F (emind E \<squnion> flod F) k"
  shows "lawful E"
  unfolding lawful_def using assms by blast

lemma lawfulI:
  assumes "\<And>e. e \<in> set (edims E) \<Longrightarrow> (eupper e \<sqinter> emind E) \<sqsubseteq> elower e"
    and "emind E = fold (\<squnion>) (map elower (edims E)) \<bottom>"
    and "\<And>e. e \<in> set (edims E) \<Longrightarrow> entry_wf e"
    and "\<And>data F k. \<lbrakk>conforms data; proj (emind E \<squnion> flod F)\<cdot>k = k\<rbrakk> \<Longrightarrow>
           esem E data F k = csem E\<cdot>(contents data (edims E) F k)"
    and "\<And>data F k. conforms data \<Longrightarrow> esem E data F k \<noteq> None \<Longrightarrow> keyimg data F (emind E \<squnion> flod F) k"
  shows "lawful E"
  by (rule lawful_semiI[OF semilawfulI[OF assms(2-4)] assms(1,5)])

lemma lawful_semilawful: "lawful E \<Longrightarrow> semilawful E"
  unfolding lawful_def by blast

lemma lawful_saturated: "lawful E \<Longrightarrow> e \<in> set (edims E) \<Longrightarrow> (eupper e \<sqinter> emind E) \<sqsubseteq> elower e"
  unfolding lawful_def by blast

lemma lawful_key_law: "lawful E \<Longrightarrow> conforms data \<Longrightarrow> esem E data F k \<noteq> None \<Longrightarrow> keyimg data F (kd E F) k"
  unfolding lawful_def by blast

lemma lawful_keyed: "lawful E \<Longrightarrow> e \<in> set (edims E) \<Longrightarrow> keyed_view (eview e)"
  by (rule semilawful_keyed[OF lawful_semilawful])

lemma lower_below_mind:
  assumes E: "semilawful E" and e: "e \<in> set (edims E)"
  shows "elower e \<sqsubseteq> emind E"
proof -
  have "elower e \<in> set (map elower (edims E))" using e by force
  then show ?thesis unfolding semilawful_mind_lub[OF E] by (rule fold_join_upper)
qed

lemma group_below_kd:
  "semilawful E \<Longrightarrow> e \<in> set (edims E) \<Longrightarrow> sel_at (esel e) (flod F) \<sqsubseteq> kd E F"
  by (rule join_belowI[OF below_trans[OF lower_below_mind lattice_join_ge1]
        below_trans[OF truncate_below lattice_join_ge2]])

text \<open>Contents agree when the groups do.\<close>

lemma content_group_cong:
  "group data (elower e) (eupper e) F k = group data' (elower e) (eupper e) F' k' \<Longrightarrow>
    content data e F k = content data' e F' k'"
  by (simp add: content_def cgraph_def efiber_def)

text \<open>Contents only depend on the point section at a section covering the frame, the key LOD and
  the sections of the entries' views.\<close>

definition entry_reads :: "'r semi_factor \<Rightarrow> ('k, 'r) entry \<Rightarrow> bool" where
  "entry_reads c e \<longleftrightarrow> fst (vsec (eview e)) \<sqsubseteq> c \<and> fst (vsec (oview (eguard e))) \<sqsubseteq> c"

lemma contents_section:
  assumes E: "semilawful E" and F: "frame_reads c F" and K: "csupp (kd E F) \<sqsubseteq> c"
    and cols: "\<And>e. e \<in> set (edims E) \<Longrightarrow> entry_reads c e"
    and sec: "pts_section c data = pts_section c data'"
  shows "contents data (edims E) F k = contents data' (edims E) F k"
proof (rule map_cong[OF refl])
  fix e assume e: "e \<in> set (edims E)"
  have G: "csupp (sel_at (esel e) (flod F)) \<sqsubseteq> c"
    by (rule below_trans[OF csupp_mono[OF group_below_kd[OF E e]] K])
  have r: "fst (vsec (eview e)) \<sqsubseteq> c" "fst (vsec (oview (eguard e))) \<sqsubseteq> c"
    using cols[OF e] by (simp_all add: entry_reads_def)
  show "content data e F k = content data' e F k"
    unfolding content_section[OF F G r] sec ..
qed

text \<open>The \<^emph>\<open>grain\<close> of an expression at a frame joins the group LODs of its entries.  Contents, and
  so values, depend on the key only through its part at the grain: an expression emits at its
  grain, and its values at finer keys are broadcast.\<close>

definition grain :: "('k, 'f, 'r, 'v::cpo) expr \<Rightarrow> ('k semi_factor, 'f, 'r) frame \<Rightarrow> 'k semi_factor" where
  "grain E F = fold (\<squnion>) (map (\<lambda>e. sel_at (esel e) (flod F)) (edims E)) \<bottom>"

lemma group_below_grain: "e \<in> set (edims E) \<Longrightarrow> sel_at (esel e) (flod F) \<sqsubseteq> grain E F"
  unfolding grain_def by (rule fold_join_upper) force

lemma grain_below_kd: "semilawful E \<Longrightarrow> grain E F \<sqsubseteq> kd E F"
  unfolding grain_def by (rule fold_join_least) (auto intro: group_below_kd)

theorem sem_grain:
  assumes E: "semilawful E" and d: "conforms data" and k: "proj (kd E F)\<cdot>k = k"
  shows "esem E data F k = esem E data F (proj (grain E F)\<cdot>k)"
proof (rule semilawful_content_law[OF E d d k])
  show "proj (kd E F)\<cdot>(proj (grain E F)\<cdot>k) = proj (grain E F)\<cdot>k"
    by (rule proj_absorb[OF grain_below_kd[OF E]])
  show "contents data (edims E) F k = contents data (edims E) F (proj (grain E F)\<cdot>k)"
  proof (rule map_cong[OF refl])
    fix e assume e: "e \<in> set (edims E)"
    have "proj (sel_at (esel e) (flod F))\<cdot>(proj (grain E F)\<cdot>k) = proj (sel_at (esel e) (flod F))\<cdot>k"
      by (rule proj_le[OF group_below_grain[OF e]])
    then show "content data e F k = content data e F (proj (grain E F)\<cdot>k)"
      by (intro content_group_cong) (simp add: group_def)
  qed
qed

text \<open>For lawful expressions the frame LOD inside the minimal LOD does not matter: groups only see
  the key LOD.\<close>

lemma group_kd:
  "lawful E \<Longrightarrow> e \<in> set (edims E) \<Longrightarrow> sel_at (esel e) (flod F) = sel_at (esel e) (kd E F)"
  by (rule sat_absorb[symmetric, OF lawful_saturated])

lemma contents_kd:
  assumes E: "lawful E" and F: "amb F = amb F'" "slice F = slice F'" "kd E F = kd E F'"
  shows "contents data (edims E) F k = contents data (edims E) F' k"
proof (rule map_cong[OF refl])
  fix e assume e: "e \<in> set (edims E)"
  have "group data (elower e) (eupper e) F k = group data (elower e) (eupper e) F' k"
    by (rule group_cong[OF F(1,2)]) (simp_all only: group_kd[OF E e] F(3))
  then show "content data e F k = content data e F' k" by (rule content_group_cong)
qed

text \<open>Pegging the frame to a key does not change that key's contents: the pin's demand within
  a mask is part of the group already, by saturation.\<close>

lemma peg_group:
  assumes E: "lawful E" and e: "e \<in> set (edims E)" and cK: "compact K" and K: "proj (kd E F)\<cdot>K = K"
  shows "group data (elower e) (eupper e) (peg K F) K = group data (elower e) (eupper e) F K"
proof -
  let ?G = "sel_at (esel e) (flod F)" and ?T = "(eupper e \<sqinter> kd E F)"
  have le: "?T \<sqsubseteq> ?G" unfolding group_kd[OF E e] by (rule lattice_join_ge2)
  have pin: "holds (coarsen (eupper e) (spin K)) (rkey\<cdot>y)" if y: "rproj ?G y = proj ?G\<cdot>K" for y
  proof -
    have "proj (eupper e)\<cdot>K = proj ?T\<cdot>K" by (simp only: proj_inf K)
    also have "\<dots> = proj ?T\<cdot>(proj ?G\<cdot>K)" by (rule proj_le[OF le, symmetric])
    also have "\<dots> = proj ?T\<cdot>(rproj ?G y)" by (simp only: y)
    also have "\<dots> = rproj ?T y" by (rule proj_le[OF le])
    finally have "proj (eupper e)\<cdot>K \<sqsubseteq> rkey\<cdot>y" using proj_below[of ?T "rkey\<cdot>y"] by simp
    then show ?thesis by (rule holds_coarsen_spin[OF cK])
  qed
  show ?thesis unfolding group_def using pin by (auto simp: coarsen_conj)
qed

lemma peg_contents:
  assumes E: "lawful E" and cK: "compact K" and K: "proj (kd E F)\<cdot>K = K"
  shows "contents data (edims E) (peg K F) K = contents data (edims E) F K"
proof (rule map_cong[OF refl])
  fix e assume e: "e \<in> set (edims E)"
  show "content data e (peg K F) K = content data e F K"
    by (rule content_group_cong[OF peg_group[OF E e cK K]])
qed

lemma key_lives: "lawful E \<Longrightarrow> conforms data \<Longrightarrow> esem E data F k \<noteq> None \<Longrightarrow> proj (kd E F)\<cdot>k = k"
  by (auto dest!: lawful_key_law simp: keyimg_def)

text \<open>The effective-LOD law: the frame LOD matters only through the key LOD.\<close>

theorem eff_law:
  assumes E: "lawful E" and d: "conforms data" and F: "amb F = amb F'" "slice F = slice F'" "kd E F = kd E F'"
  shows "esem E data F = esem E data F'"
proof
  fix k
  show "esem E data F k = esem E data F' k"
  proof (cases "proj (kd E F)\<cdot>k = k")
    case True
    then have "proj (kd E F')\<cdot>k = k" by (simp add: F(3))
    then show ?thesis
      by (rule semilawful_content_law[OF lawful_semilawful[OF E] d d True _ contents_kd[OF E F]])
  next
    case False
    then have "proj (kd E F')\<cdot>k \<noteq> k" by (simp add: F(3))
    then have "esem E data F' k = None" using key_lives[OF E d, of F' k] by blast
    moreover have "esem E data F k = None" using False key_lives[OF E d, of F k] by blast
    ultimately show ?thesis by simp
  qed
qed

text \<open>The peg law: pegging the frame to a key does not change the value there.\<close>

theorem peg_law:
  assumes E: "lawful E" and d: "conforms data" and cK: "compact K"
  shows "esem E data (peg K F) K = esem E data F K"
proof (cases "proj (kd E F)\<cdot>K = K")
  case True
  have "proj (kd E (peg K F))\<cdot>K = K" using True by simp
  then show ?thesis
    by (rule semilawful_content_law[OF lawful_semilawful[OF E] d d _ True peg_contents[OF E cK True]])
next
  case False
  then have "proj (kd E (peg K F))\<cdot>K \<noteq> K" by simp
  then have "esem E data (peg K F) K = None" using key_lives[OF E d, of "peg K F" K] by blast
  moreover have "esem E data F K = None" using False key_lives[OF E d, of F K] by blast
  ultimately show ?thesis by simp
qed

text \<open>Locality: the semantics at a frame depends on the dataset only through its point section at
  a section covering the frame, the key LOD and the entries' columns.\<close>

theorem sem_section:
  assumes E: "lawful E" and d: "conforms data" and d': "conforms data'"
    and F: "frame_reads c F" and K: "csupp (kd E F) \<sqsubseteq> c"
    and cols: "\<And>e. e \<in> set (edims E) \<Longrightarrow> entry_reads c e"
    and sec: "pts_section c data = pts_section c data'"
  shows "esem E data F k = esem E data' F k"
proof (cases "proj (kd E F)\<cdot>k = k")
  case True
  show ?thesis
    by (rule semilawful_content_law[OF lawful_semilawful[OF E] d d' True True
          contents_section[OF lawful_semilawful[OF E] F K cols sec]])
next
  case False
  then have "esem E data F k = None" "esem E data' F k = None"
    using key_lives[OF E d] key_lives[OF E d'] by blast+
  then show ?thesis by simp
qed

end

subsection \<open>Lemmas for the combinators\<close>

lemma concat_map_blocks:
  assumes "concat (map f xs) = concat (map g xs)" and "\<And>x. x \<in> set xs \<Longrightarrow> length (f x) = length (g x)"
    and "x \<in> set xs"
  shows "f x = g x"
  using assms
proof (induct xs)
  case (Cons y ys)
  have l: "length (f y) = length (g y)" by (rule Cons.prems(2)) simp
  have "f y = g y \<and> concat (map f ys) = concat (map g ys)"
    using Cons.prems(1) by (simp add: append_eq_append_conv[OF disjI1[OF l]])
  then show ?case using Cons by auto
qed simp

lemma proj_sup_eq:
  "proj (a \<squnion> b)\<cdot>x = proj (a \<squnion> b)\<cdot>z \<longleftrightarrow> proj a\<cdot>x = proj a\<cdot>z \<and> proj b\<cdot>x = proj b\<cdot>z"
proof
  assume e: "proj (a \<squnion> b)\<cdot>x = proj (a \<squnion> b)\<cdot>z"
  show "proj a\<cdot>x = proj a\<cdot>z \<and> proj b\<cdot>x = proj b\<cdot>z"
    using arg_cong[OF e, of "Rep_cfun (proj a)"] arg_cong[OF e, of "Rep_cfun (proj b)"]
    by (simp add: proj_le lattice_join_ge1 lattice_join_ge2)
qed (simp add: proj_sup)


context dataspace
begin

text \<open>The group of the full mask on top of an LOD is the key's own group.\<close>

lemma group_top:
  assumes "proj (c \<squnion> flod F)\<cdot>k = k"
  shows "group data c lattice_top F k = {y \<in> lower_maximal data. frows F y \<and> rproj (c \<squnion> flod F) y = k}"
  using assms by (auto simp: group_def truncate_top frows_def)

lemma keyimg_group_top:
  assumes "proj (c \<squnion> flod F)\<cdot>k = k"
  shows "keyimg data F (c \<squnion> flod F) k \<longleftrightarrow> group data c lattice_top F k \<noteq> {}"
  by (auto simp: group_top[OF assms] keyimg_def)

end

end
