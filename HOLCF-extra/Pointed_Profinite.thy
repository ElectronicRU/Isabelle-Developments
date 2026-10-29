theory Pointed_Profinite
  imports HOLCF
begin

section \<open>Pointed profinite domains are bifinite\<close>

text \<open>A profinite cpo has an approximation chain on its lifting.  If it is pointed, lowering back
  through \<open>fup\<cdot>ID\<close> gives one on the cpo itself: \<open>up\<close> followed by \<open>fup\<cdot>ID\<close> is the identity, and \<open>fup\<cdot>ID\<close>
  followed by \<open>up\<close> is above it, so the lowered finite deflations stay idempotent.\<close>

lemma up_fup_ID_above: "y \<sqsubseteq> up\<cdot>(fup\<cdot>ID\<cdot>y)"
  by (cases y) simp_all

lemma approx_chain_lower:
  assumes d: "approx_chain (d :: nat \<Rightarrow> 'a::pcpo u \<rightarrow> 'a u)"
  shows "approx_chain (\<lambda>i. fup\<cdot>ID oo d i oo up)"
proof (rule approx_chain.intro)
  interpret approx_chain d by (fact d)
  show "chain (\<lambda>i. fup\<cdot>ID oo d i oo up)"
    by (rule chainI, rule cfun_belowI) (simp add: monofun_cfun_arg monofun_cfun_fun[OF chainE[OF chain_approx]])
  then show "(\<Squnion>i. fup\<cdot>ID oo d i oo up) = ID"
  proof (intro cfun_eqI)
    fix x assume c: "chain (\<lambda>i. fup\<cdot>ID oo d i oo up)"
    have "(\<Squnion>i. fup\<cdot>ID\<cdot>(d i\<cdot>(up\<cdot>x))) = fup\<cdot>ID\<cdot>(\<Squnion>i. d i\<cdot>(up\<cdot>x))"
      by (rule cont2contlubE[OF cont_Rep_cfun2 ch2ch_Rep_cfunL[OF chain_approx], symmetric])
    then show "(\<Squnion>i. fup\<cdot>ID oo d i oo up)\<cdot>x = ID\<cdot>x"
      by (simp add: contlub_cfun_fun[OF c] contlub_cfun_fun[OF chain_approx, symmetric])
  qed
  show "finite_deflation (fup\<cdot>ID oo d i oo up)" for i
  proof -
    interpret d: finite_deflation "d i" by simp
    let ?c = "fup\<cdot>ID oo d i oo up"
    have below: "?c\<cdot>x \<sqsubseteq> x" for x
    proof -
      have "fup\<cdot>ID\<cdot>(d i\<cdot>(up\<cdot>x)) \<sqsubseteq> fup\<cdot>ID\<cdot>(up\<cdot>x)" by (rule monofun_cfun_arg[OF d.below])
      then show ?thesis by simp
    qed
    have idem: "?c\<cdot>(?c\<cdot>x) = ?c\<cdot>x" for x
    proof (rule below_antisym[OF below])
      have "d i\<cdot>(up\<cdot>x) \<sqsubseteq> up\<cdot>(fup\<cdot>ID\<cdot>(d i\<cdot>(up\<cdot>x)))" by (rule up_fup_ID_above)
      then have "d i\<cdot>(d i\<cdot>(up\<cdot>x)) \<sqsubseteq> d i\<cdot>(up\<cdot>(fup\<cdot>ID\<cdot>(d i\<cdot>(up\<cdot>x))))" by (rule monofun_cfun_arg)
      then show "?c\<cdot>x \<sqsubseteq> ?c\<cdot>(?c\<cdot>x)" by (simp add: d.idem monofun_cfun_arg)
    qed
    have fin: "finite {x. ?c\<cdot>x = x}"
    proof (rule finite_subset)
      show "{x. ?c\<cdot>x = x} \<subseteq> (\<lambda>y. fup\<cdot>ID\<cdot>y) ` {y. d i\<cdot>y = y}"
      proof
        fix x assume "x \<in> {x. ?c\<cdot>x = x}"
        then have "x = fup\<cdot>ID\<cdot>(d i\<cdot>(up\<cdot>x))" by simp
        moreover have "d i\<cdot>(d i\<cdot>(up\<cdot>x)) = d i\<cdot>(up\<cdot>x)" by (rule d.idem)
        ultimately show "x \<in> (\<lambda>y. fup\<cdot>ID\<cdot>y) ` {y. d i\<cdot>y = y}" by blast
      qed
      show "finite ((\<lambda>y. fup\<cdot>ID\<cdot>y) ` {y. d i\<cdot>y = y})" using d.finite_fixes by simp
    qed
    show ?thesis unfolding finite_deflation_def finite_deflation_axioms_def deflation_def
      using below idem fin by blast
  qed
qed

lemma bifinite_profinite_pointed: "OFCLASS('a::{profinite, pcpo}, bifinite_class)"
proof
  obtain d :: "nat \<Rightarrow> 'a u \<rightarrow> 'a u" where "approx_chain d" using profinite by blast
  then show "\<exists>a :: nat \<Rightarrow> 'a \<rightarrow> 'a. approx_chain a" by (blast intro: approx_chain_lower)
qed

end
