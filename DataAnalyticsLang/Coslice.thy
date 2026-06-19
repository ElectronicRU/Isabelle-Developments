theory Coslice
  imports HOLCF
begin

section \<open>Coslices of a domain (a.k.a.\ levels of detail)\<close>

text \<open>
  A \<^emph>\<open>coslice\<close> of a domain \<^typ>\<open>'a\<close> is a continuous function \<^term>\<open>a :: 'a \<rightarrow> udom\<close>
  considered up to \<^emph>\<open>information content\<close>: \<^term>\<open>a\<close> and \<^term>\<open>b\<close> carry the same
  information exactly when each factors through the other by a continuous self-map of
  \<^typ>\<open>udom\<close>.

  Categorically this is the preorder reflection of the coslice (under-)category
  \<open>'a \<down> Domain\<close>: objects are the maps out of \<^typ>\<open>'a\<close>, and we keep only the
  \<^emph>\<open>existence\<close> of a connecting morphism.  In the data-analytics language this models a
  \<^emph>\<open>level of detail\<close> (LOD) over a row domain \<^typ>\<open>'a\<close>: a read-only quotient/abstraction
  of rows.  The order is \<^emph>\<open>finer = higher\<close>: the top coslice is \<^typ>\<open>'a\<close> itself, the
  bottom is the constant map (no information).

  This is \<^emph>\<open>not\<close> the deflation/retract world of \<^file>\<open>Subdomain.thy\<close>: coslices are genuine
  quotients, strictly more general than retracts (a continuous bijection of domains need
  not be an iso, so the factoring preorder is strictly finer than kernel-equality and
  remembers the induced order on the quotient, not just the partition).
\<close>

subsection \<open>The factoring preorder on \<^typ>\<open>'a \<rightarrow> udom\<close>\<close>

definition cofactor :: "('a::domain \<rightarrow> udom) \<Rightarrow> ('a \<rightarrow> udom) \<Rightarrow> bool"  (infix "\<preceq>" 50)
  where "a \<preceq> b \<longleftrightarrow> (\<exists>f::udom \<rightarrow> udom. a = f oo b)"

lemma cofactorI: "a = f oo b \<Longrightarrow> a \<preceq> b"
  by (auto simp add: cofactor_def)

definition cosim :: "('a::domain \<rightarrow> udom) \<Rightarrow> ('a \<rightarrow> udom) \<Rightarrow> bool"
  where "cosim a b \<longleftrightarrow> a \<preceq> b \<and> b \<preceq> a"

lemma cofactor_refl [simp]: "a \<preceq> a"
  unfolding cofactor_def by (rule exI[of _ ID]) simp

lemma cofactor_trans:
  assumes "a \<preceq> b" and "b \<preceq> c" shows "a \<preceq> c"
proof -
  from assms obtain f g where "a = f oo b" "b = g oo c"
    unfolding cofactor_def by blast
  hence "a = (f oo g) oo c" by (metis assoc_oo)
  thus ?thesis unfolding cofactor_def by blast
qed

lemma cosim_equivp: "equivp cosim"
proof (rule equivpI)
  show "reflp cosim" by (simp add: reflp_def cosim_def)
  show "symp cosim" by (auto simp: symp_def cosim_def)
  show "transp cosim" by (auto simp: transp_def cosim_def intro: cofactor_trans)
qed

subsection \<open>The quotient type of coslices\<close>

quotient_type 'a coslice = "'a::domain \<rightarrow> udom" / cosim
  morphisms rep_coslice abs_coslice
  by (rule cosim_equivp)

subsection \<open>Pairing into \<^typ>\<open>udom\<close> (used for joins)\<close>

lemma emb_pair_recover [simp]: "prj\<cdot>(emb\<cdot>(u, v)) = ((u, v) :: udom \<times> udom)"
  by (rule emb_inverse)

thm fst_conv

text \<open>The join of two coslices: pair the two outputs into \<^typ>\<open>udom\<close> (cartesian, so
  \<^term>\<open>(\<bottom>, v)\<close> and \<^term>\<open>(u, \<bottom>)\<close> stay distinct).  This is the product in the coslice.\<close>

definition cojoin :: "('a::domain \<rightarrow> udom) \<Rightarrow> ('a \<rightarrow> udom) \<Rightarrow> ('a \<rightarrow> udom)"
  where "cojoin a b = (\<Lambda> x. emb\<cdot>(a\<cdot>x, b\<cdot>x))"

subsection \<open>Top, bottom, and join at representative level\<close>

lemma cofactor_top: "a \<preceq> emb"
  unfolding cofactor_def
  by (rule exI[of _ "a oo prj"])
     (rule cfun_eqI, simp add: ep_pair.e_inverse[OF ep_pair_emb_prj])

lemma cofactor_const: "(\<Lambda> _. c) \<preceq> a"
  unfolding cofactor_def by (rule exI[of _ "(\<Lambda> _. c)"]) (rule cfun_eqI, simp)

corollary cofactor_bot: "\<bottom> \<preceq> a"
  using cofactor_const[of "\<bottom>"] by auto

lemma cofactor_join1: "a \<preceq> cojoin a b"
  unfolding cofactor_def cojoin_def
  by (rule exI[of _ "\<Lambda> w. fst (prj\<cdot>w :: udom \<times> udom)"]) (rule cfun_eqI, simp)

lemma cofactor_join2: "b \<preceq> cojoin a b"
  unfolding cofactor_def cojoin_def
  by (rule exI[of _ "\<Lambda> w. snd (prj\<cdot>w :: udom \<times> udom)"]) (rule cfun_eqI, simp)

lemma cofactor_join_lub:
  assumes "a \<preceq> c" and "b \<preceq> c" shows "cojoin a b \<preceq> c"
proof -
  from assms obtain f g where fg: "a = f oo c" "b = g oo c"
    unfolding cofactor_def by blast
  hence "cojoin a b = (\<Lambda> u. emb\<cdot>(f\<cdot>u, g\<cdot>u)) oo c"
    unfolding cojoin_def by (intro cfun_eqI) simp
  thus ?thesis unfolding cofactor_def by blast
qed

subsection \<open>The partial order of coslices (finer = higher)\<close>

instantiation coslice :: ("domain") order
begin

lift_definition less_eq_coslice :: "'a coslice \<Rightarrow> 'a coslice \<Rightarrow> bool" is cofactor
  by (unfold cosim_def, metis cofactor_trans)

definition less_coslice :: "'a coslice \<Rightarrow> 'a coslice \<Rightarrow> bool"
  where "less_coslice x y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"

instance proof
  fix x y z :: "'a coslice"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by (rule less_coslice_def)
  show "x \<le> x" by transfer simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by transfer (rule cofactor_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by transfer (simp add: cosim_def)
qed
end

subsection \<open>Bottom (no information) and top (\<^typ>\<open>'a\<close> itself)\<close>

instantiation coslice :: ("domain") order_bot
begin
lift_definition bot_coslice :: "'a coslice" is "\<bottom> :: 'a \<rightarrow> udom" .
instance by (intro_classes, transfer) (rule cofactor_bot)
end

instantiation coslice :: ("domain") order_top
begin
lift_definition top_coslice :: "'a coslice" is "emb :: 'a \<rightarrow> udom" .
instance by (intro_classes, transfer) (rule cofactor_top)
end

subsection \<open>Join: coslices form a sup-semilattice with bottom\<close>

instantiation coslice :: ("domain") semilattice_sup
begin
lift_definition sup_coslice :: "'a coslice \<Rightarrow> 'a coslice \<Rightarrow> 'a coslice" is cojoin
  unfolding cosim_def
  by (metis cofactor_join1 cofactor_join2 cofactor_join_lub cofactor_trans)
instance proof
  fix x y z :: "'a coslice"
  show "x \<le> sup x y" by transfer (rule cofactor_join1)
  show "y \<le> sup x y" by transfer (rule cofactor_join2)
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> sup y z \<le> x" by transfer (rule cofactor_join_lub)
qed
end

instance coslice :: ("domain") bounded_semilattice_sup_bot ..

subsection \<open>The canonical morphism \<^typ>\<open>('a \<rightarrow> 'b) \<Rightarrow> 'a coslice\<close>\<close>

lift_definition lod_of :: "('a::domain \<rightarrow> 'b::domain) \<Rightarrow> 'a coslice" is "\<lambda>g. emb oo g" .

text \<open>Every continuous function out of \<^typ>\<open>'a\<close> defines a level of detail; taking
  \<^typ>\<open>'b\<close> = \<^typ>\<open>udom\<close> shows \<^const>\<open>lod_of\<close> is onto, so coslices are exactly these.\<close>

lemma lod_of_ID: "lod_of ID = top"
  by transfer (simp add: cosim_def)

lemma emb_comp_const: "emb oo (\<Lambda> _. c) = (\<Lambda> _. emb\<cdot>c)"
  by (rule cfun_eqI) simp

lemma emb_comp_bot: "emb oo \<bottom> = \<bottom>"
  by (rule cfun_eqI) simp

lemma lod_of_const: "lod_of (\<Lambda> _. c) = bot"
  by transfer (simp add: emb_comp_const cofactor_const cofactor_bot cosim_def)

lemma lod_of_bot: "lod_of \<bottom> = bot"
  by transfer (simp add: emb_comp_bot cosim_def cofactor_bot)

lemma lod_of_oo_le: "lod_of (h oo g) \<le> lod_of g"
proof (transfer fixing: g h, intro cofactorI)
  show "emb oo h oo g = (emb oo h oo prj) oo emb oo g"
    by (rule cfun_eqI) simp
qed


text \<open>Post-composition with an \<^typ>\<open>udom\<close>-self-map leaves the coslice unchanged on the
  nose modulo \<^const>\<open>cosim\<close>, witnessing surjectivity of \<^const>\<open>lod_of\<close> at \<^typ>\<open>'b\<close> = \<^typ>\<open>udom\<close>.\<close>

lemma emb_eq: fixes a :: "'a \<rightarrow> udom" shows "emb oo a = a" by simp

lemma lod_of_abs: "lod_of = abs_coslice"
  by (rule ext) (transfer, simp add: emb_eq cosim_equivp equivp_reflp equivp_symp)

lemma lod_of_rep: "lod_of (rep_coslice c) = c"
  using Quotient3_coslice[THEN Quotient3_abs_rep] lod_of_abs by metis

subsection \<open>Binary meets: structure and the open question\<close>

text \<open>A binary meet of \<^term>\<open>x\<close> and \<^term>\<open>y\<close> is a greatest common lower bound.  We do
  \<^emph>\<open>not\<close> instantiate \<^class>\<open>lattice\<close>, because meets are subtle.  The set of common lower
  bounds is downward closed and closed under \<^const>\<open>sup\<close> (lemma \<open>common_lb_sup\<close> below), i.e.\
  a directed ideal, and a meet is exactly its \<^emph>\<open>directed supremum\<close>.  Since coslices are not
  a dcpo, that supremum -- hence the meet -- need not exist.\<close>

definition has_inf :: "'a::domain coslice \<Rightarrow> 'a coslice \<Rightarrow> bool"
  where "has_inf x y \<longleftrightarrow> (\<exists>m. m \<le> x \<and> m \<le> y \<and> (\<forall>c. c \<le> x \<longrightarrow> c \<le> y \<longrightarrow> c \<le> m))"

text \<open>The common-lower-bound set is closed under joins, hence directed.\<close>

lemma common_lb_sup:
  assumes "c \<le> x" "c \<le> y" and "d \<le> x" "d \<le> y" shows "sup c d \<le> x \<and> sup c d \<le> y"
  using assms by (simp add: sup_least)

text \<open>Comparable elements always have a meet (the smaller one); in particular every element
  has a meet with \<^const>\<open>bot\<close> and with \<^const>\<open>top\<close>.  So the only open case is genuinely
  incomparable \<^term>\<open>x\<close>, \<^term>\<open>y\<close>.\<close>

lemma has_inf_comparable: "x \<le> y \<Longrightarrow> has_inf x y"
  unfolding has_inf_def by (metis order_refl)

lemma has_inf_bot [simp]: "has_inf x bot"
  unfolding has_inf_def by (metis bot_least order_refl)

lemma has_inf_top [simp]: "has_inf x top"
  unfolding has_inf_def by (metis top_greatest order_refl)

text \<open>Whether \<^term>\<open>has_inf x y\<close> holds for \<^emph>\<open>all\<close> pairs is the question of whether the
  common-coarsening ideal is always principal.  It holds for finite \<^typ>\<open>'a\<close> (a finite
  bounded sup-semilattice is a lattice) but is expected to fail in general -- the same
  profinite incompleteness that stops coslices being a dcpo.  A decisive negative answer
  needs an infinite-\<^typ>\<open>'a\<close> counterexample (a pair whose common lower bounds form a
  strictly ascending chain with no representable supremum).\<close>

end
