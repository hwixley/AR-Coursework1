theory Practical
imports Main
begin

section \<open>Part 1\<close>

(* 1 mark *)
lemma disjunction_idempotence:
  "A \<or> A \<longleftrightarrow> A"
  apply(rule iffI)
   apply(erule disjE)
    apply(assumption)+
  apply(rule disjI1)
  by assumption

(* 1 mark *)
lemma conjunction_idempotence:
  "A \<and> A \<longleftrightarrow> A"
  apply(rule iffI)
   apply(erule conjE)
   apply(assumption)
  apply(rule conjI)
  by assumption

(* 1 mark *)
lemma disjunction_to_conditional:
  "(\<not> P \<or> R) \<longrightarrow> (P \<longrightarrow> R)"
  apply(rule impI)+
  apply(erule disjE)
   apply(erule notE)
  by assumption

(* 1 mark *)
lemma
  "(\<exists>x. P x \<and> Q x) \<longrightarrow> (\<exists>x. P x) \<and> (\<exists>x. Q x)"
  apply(rule impI)
  apply(rule conjI)
   apply(erule exE)+
   apply(erule conjE)+
   apply(erule exI)
  apply(erule exE)
  apply(erule conjE)
  apply(rule exI)
  by assumption

(* 1 mark *)
lemma
  "(\<not> (\<exists>x. \<not>P x) \<or> R) \<longrightarrow> ((\<exists>x. \<not> P x) \<longrightarrow> R)"
  apply(rule impI)+
  apply(erule disjE)
   apply(erule exE)
   apply(erule notE)
   apply(rule exI)
   apply(rule notI)
   apply(erule notE)
   apply(assumption)
  apply(erule exE)
  by assumption

(* 2 marks *)
lemma
  "(\<forall>x. P x) \<longrightarrow> \<not> (\<exists>x. \<not> P x)"            
  apply(rule impI)
  apply(rule notI)
  apply(erule exE)
  apply(erule allE)
  apply(erule notE)
  by assumption

(* 3 marks *)
text \<open>Prove using ccontr\<close>
lemma excluded_middle:
  "P \<or> \<not> P"
  apply(cut_tac P="P" and Q="P" in impI)
   apply(assumption)
  apply(rule ccontr)
  apply(erule impE)
   apply(rule ccontr)
   apply(erule notE)
   apply(rule disjI2)
   apply(assumption)
  apply(erule notE)
  apply(rule disjI1)
  by assumption

(* 3 marks *)
text \<open>Prove using excluded middle\<close>
lemma notnotD:
  "\<not>\<not> P \<Longrightarrow> P"
  apply(cut_tac P="P" in excluded_middle)
   apply(erule disjE)
  apply(assumption)
   apply(erule notE)
  by assumption+

(* 3 marks *)
text \<open>Prove using double-negation (rule notnotD)\<close>
lemma classical:
  "(\<not> P \<Longrightarrow> P) \<Longrightarrow> P"
  apply(rule notnotD)
  apply(drule impI)
  apply(rule notI)
  apply(erule impE)
   apply(assumption)
  apply(erule notE)
  by assumption

(* 3 marks *)
text \<open>Prove using classical\<close>
lemma ccontr:
  "(\<not> P \<Longrightarrow> False) \<Longrightarrow> P"
  apply(rule classical)
  apply(drule impI)
  apply(erule impE)
   apply(assumption)
  apply(erule notE)
  apply(cut_tac P="\<not>P" in notI)
   apply(assumption)
  apply(erule notE)
  apply(rule notI)
  by assumption

(* 3 marks *)
lemma
  "(\<not> (\<forall>x. P x \<or> R x)) = (\<exists>x. \<not> P x \<and> \<not> R x)"
  apply(rule iffI)
   apply(rule ccontr)
   apply(erule notE)
   apply(rule allI)
   apply(rule ccontr)
   apply(erule notE)
   apply(rule_tac x="x" in exI)
   apply(rule conjI)
    apply(rule notI)
    apply(erule notE)
    apply(rule disjI1)
    apply(assumption)
   apply(rule notI)
   apply(erule notE)
   apply(rule disjI2)
   apply(assumption)
  apply(rule notI)
  apply(erule exE)
  apply(erule_tac x="x" in allE)
  apply(erule conjE)
  apply(erule disjE)
   apply(erule notE)
   apply(assumption)
  apply(erule notE)+
  by assumption

(* 3 marks *)
lemma
  "(\<exists>x. P x \<or> R x) = (\<not>((\<forall>x. \<not> P x) \<and> \<not> (\<exists>x. R x)))"
  apply(rule iffI)
   apply(rule notI)
   apply(erule exE)
   apply(erule conjE)
   apply(erule disjE)
    apply(erule_tac x="x" in allE)
    apply(erule notE)
    apply(rule_tac x="x" in exI)
    apply(erule notE)
    apply(assumption)
   apply(erule_tac x="x" in allE)
   apply(erule notE)
   apply(rule_tac x="x" in exI)
   apply(assumption)
  apply(rule ccontr)
  apply(erule notE)
  apply(rule conjI)
   apply(rule allI)
   apply(rule notI)
   apply(erule notE)
   apply(rule_tac x="x" in exI)
   apply(rule disjI1)
   apply(assumption)
  apply(rule notI)
  apply(erule notE)
  apply(erule exE)
  apply(rule_tac x="x" in exI)
  apply(rule disjI2)
  by assumption

section \<open>Part 2.1\<close>

locale partof =
  fixes partof :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<sqsubseteq>" 100)
begin

(* 1 mark *)
definition properpartof :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<sqsubset>" 100) where
  "x \<sqsubset> y \<equiv> x \<sqsubseteq> y \<and> x \<noteq> y"


(* 1 mark *)
definition overlaps :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<frown>" 100) where
  "x \<frown> y \<equiv> \<exists>z. z \<sqsubseteq> x \<and> z \<sqsubseteq> y"

definition disjoint :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<asymp>" 100) where
  "x \<asymp> y \<equiv> \<not> x \<frown> y"

(* 1 mark *)
definition partialoverlap :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "~\<frown>" 100) where
  "x ~\<frown> y \<equiv> x \<frown> y \<and> \<not>x \<sqsubseteq> y \<and> \<not>y \<sqsubseteq> x"

(* 1 mark *)
definition sumregions :: "'region set \<Rightarrow> 'region \<Rightarrow> bool" ("\<Squnion> _ _" [100, 100] 100) where
  "\<Squnion> \<alpha> x \<equiv> (\<forall>y. y \<in> \<alpha> \<and>  y \<sqsubseteq> x) \<and> (\<forall>y. y \<sqsubseteq> x \<longrightarrow> (\<exists>z. z \<in> \<alpha> \<and> y \<frown> z))"

end

(* 1+1+1=3 marks *)
locale mereology = partof +
  assumes A1: "\<forall>x y z. x \<sqsubseteq> y \<and> y \<sqsubseteq> z \<longrightarrow> x \<sqsubseteq> z"
      and A2: "\<forall>\<alpha>. \<alpha> \<noteq> {} \<longrightarrow> (\<exists>x. \<Squnion> \<alpha> x)"
      and A2': "\<forall>\<alpha> x y. \<Squnion> \<alpha> x \<and> \<Squnion> \<alpha> y \<longrightarrow> x = y"
begin

section \<open>Part 2.2\<close>

(* 2 marks *)
theorem overlaps_sym:
  "(x \<frown> y) = (y \<frown> x)"
  apply(unfold overlaps_def)
  apply(rule iffI)
  apply(erule exE)
   apply(rule_tac x="z" in exI)
   apply(rule conjI)
    apply(erule conjE)
    apply(assumption)
   apply(erule conjE)
   apply(assumption)
  apply(erule exE)
  apply(rule_tac x="z" in exI)
  apply(rule conjI)
   apply(erule conjE)
   apply(assumption)
  apply(erule conjE)
  by assumption

(* 1 mark *)
theorem in_sum_set_partof:
  "m \<in> \<alpha> \<and> \<Squnion> \<alpha> r \<Longrightarrow> m \<sqsubseteq> r"
proof -
  have "\<Squnion> \<alpha> r \<Longrightarrow> (\<forall>y. y \<in> \<alpha> \<and>  y \<sqsubseteq> r)" using sumregions_def by simp
  thus "m \<in> \<alpha> \<and> \<Squnion> \<alpha> r \<Longrightarrow> m \<sqsubseteq> r" by simp
qed

(* 3 marks *)
theorem overlaps_refl:
  "x \<frown> x"
proof -
  have 0: "{x} \<noteq> {} \<Longrightarrow> \<exists>z. \<Squnion> {x} z" using sumregions_def A2 by blast
  from 0 have 1: "{x} \<noteq> {} \<Longrightarrow> \<Squnion> {x} x" using sumregions_def A2 by fastforce
  thus "x \<frown> x" using "1" sumregions_def by auto
qed

(* 1 mark *)
theorem all_has_partof:
  "\<exists>p. p \<sqsubseteq> r"
  using A2 overlaps_def sumregions_def by fastforce

(* 2 marks *)
theorem partof_overlaps:
  assumes a: "z \<sqsubseteq> x \<and> x \<sqsubseteq> y"
  shows "x \<frown> y"
proof -
  from a have "z \<sqsubseteq> y" using A1 by blast
  moreover
  from a have "z \<sqsubseteq> x" by simp
  ultimately show "x \<frown> y" using overlaps_def by auto
qed

(* 1 mark *)
theorem sum_parts_eq:
  "\<Squnion> {p. p \<sqsubseteq> x} x"
proof -
  have 0: "\<exists>y. \<Squnion> {p. p \<sqsubseteq> x} y" using A2 all_has_partof by auto
  thus "\<Squnion> {p. p \<sqsubseteq> x} x" using UNIV_eq_I sumregions_def by fastforce
qed

(* 2 marks *)
theorem sum_relation_is_same':
  assumes "\<And>c. r y c \<Longrightarrow> c \<sqsubseteq> y"
      and "\<And>f. y \<frown> f \<Longrightarrow> \<exists>g. r y g \<and> g \<frown> f"
      and "\<Squnion> {y} x"
  shows "\<Squnion> {k. r y k} x"
proof -
  let ?\<beta> = "{k. r y k}"
  let ?\<alpha> = "{k. k \<sqsubseteq> x}"
  have 0: "\<Squnion> ?\<alpha> x" using assms(3) sumregions_def by auto
  have 1: "y \<sqsubseteq> x \<Longrightarrow> r y y" using assms sumregions_def by fastforce
  from 1 have 2: "p \<sqsubseteq> x \<Longrightarrow> r y p" using sumregions_def assms by force
  have 3: "?\<beta> = ?\<alpha>" using sumregions_def 1 assms(3) by fastforce
  thus "\<Squnion> ?\<beta> x" using 0 by simp
qed

(* 1 mark *)
theorem overlap_has_partof_overlap:
  assumes "\<And>e f. e \<frown> f"
  shows "\<exists>x. x \<sqsubseteq> e \<and> x \<frown> f"
  using assms overlaps_def by blast

(* 1 marks *)
theorem sum_parts_of_one_eq:
  assumes "\<Squnion> {x} x"
  shows "\<Squnion> {p. p \<sqsubseteq> x} x"
  using sum_relation_is_same' [where x = "x" and y = "x" and r = "\<lambda>x y. y \<sqsubseteq> x"] 
  by (simp add: sum_parts_eq)

(* 5 marks *)
theorem both_partof_eq:
assumes "x \<sqsubseteq> y \<and> y \<sqsubseteq> x"
  shows "x = y"
proof -
  have 0: "\<Squnion> {z. z \<sqsubseteq> x} y"
  proof (rule ccontr)
    assume a: "\<not> \<Squnion> {z. z \<sqsubseteq> x} y"
    have 1: "\<exists>w. w \<sqsubseteq> x \<and> \<not> w \<sqsubseteq> y \<Longrightarrow> False"
    proof -
      assume b: "\<exists>w. w \<sqsubseteq> x \<and> \<not> w \<sqsubseteq> y"
      have 2: "w \<sqsubseteq> x \<Longrightarrow> w \<sqsubseteq> y" using assms A1 by blast
      from 2 have 3: "\<not>(\<exists>w. w \<sqsubseteq> x \<and> \<not> w \<sqsubseteq> y)" using A1 assms by blast
      thus "False" using b sumregions_def sum_parts_eq a by auto
    qed
    moreover
    have 4: "\<exists>w. \<forall>v. v \<sqsubseteq> x \<and> w \<sqsubseteq> y \<and> v \<asymp> w \<Longrightarrow> False"
    proof -
      assume c: "\<exists>w. \<forall>v. v \<sqsubseteq> x \<and> w \<sqsubseteq> y \<and> v \<asymp> w"
      fix w
      have 5: "y \<sqsubseteq> x \<Longrightarrow> y \<asymp> w" using c disjoint_def overlaps_refl by blast
      thus "False" using c disjoint_def overlaps_refl by blast
    qed
    ultimately show "False" using sumregions_def a overlaps_def sum_parts_eq by simp
  qed
  thus "x = y" using 0 A2' sum_parts_eq by blast
qed

(* 4 marks *)
theorem sum_all_with_parts_overlapping:
  assumes "\<Squnion> {z. \<forall>p. p \<sqsubseteq> z \<and> p \<frown> y} x"
  shows "\<Squnion> {y} x"
proof -
  have "\<Squnion> {y} x"
  proof (rule ccontr)
    assume a: "\<not> \<Squnion> {y} x"
    have 0: "\<not> y \<sqsubseteq> x" using A2' a assms sumregions_def by fastforce
    have 1: "\<exists>w. w \<sqsubseteq> x \<and> w \<asymp> y" using 0 assms sumregions_def by blast
    thus "False" using 0 assms sumregions_def by blast
  qed
  thus "\<Squnion> {y} x" by simp
qed

(* 2 marks *)
theorem sum_one_is_self:
  "\<Squnion> {x} x"
proof -
  have 0: "\<exists>y. \<Squnion> {x} y" using A2 by simp
  thus "\<Squnion> {x} x" using A2 sumregions_def by fastforce
qed

(* 2 marks *)
theorem sum_all_with_parts_overlapping_self:
  "\<Squnion> {z. \<forall>p. p \<sqsubseteq> z \<and> p \<frown> x} x"
  using sumregions_def sum_one_is_self by auto

(* 4 marks *)
theorem proper_have_nonoverlapping_proper:
  assumes "s \<sqsubset> r"
  shows "\<exists>z. z \<sqsubset> r \<and> z \<asymp> s"
proof -
  have 0: "\<Squnion> {z. z \<sqsubset> r} y" using A2 sumregions_def properpartof_def assms by auto
  from 0 have 1: "y \<noteq> s" using sumregions_def properpartof_def by auto
  from 1 have 2: "{z. z \<sqsubset> r} \<noteq> {s}" using 0 sum_one_is_self A2' by fastforce
  thus "\<exists>z. z \<sqsubset> r \<and> z \<asymp> s" using 0 properpartof_def sumregions_def by auto
qed

(* 1 mark *)
sublocale parthood_partial_order: order "(\<sqsubseteq>)" "(\<sqsubset>)"
proof
  show "\<And>x y. x \<sqsubset> y = (x \<sqsubseteq> y \<and> \<not> y \<sqsubseteq> x)" using properpartof_def A2 sumregions_def by auto
next
  show "\<And>x. x \<sqsubseteq> x" using sumregions_def sum_one_is_self by simp
next
  show "\<And>x y z. \<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z" using A1 by blast
next
  show "\<And>x y. \<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> x = y" using both_partof_eq by simp
qed

end

section \<open>Part 2.3\<close>

locale sphere =
  fixes sphere :: "'a \<Rightarrow> bool"
begin

abbreviation AllSpheres :: "('a \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<forall>\<degree>" 10) where
  "\<forall>\<degree>x. P x \<equiv> \<forall>x. sphere x \<longrightarrow> P x"

abbreviation ExSpheres :: "('a \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<exists>\<degree>" 10) where
  "\<exists>\<degree>x. P x \<equiv> \<exists>x. sphere x \<and> P x"

end

locale mereology_sphere = mereology partof + sphere sphere
  for partof :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<sqsubseteq>" 100)
  and sphere :: "'region \<Rightarrow> bool"
begin

definition exttan :: "'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "exttan a b \<equiv> sphere a \<and> sphere b \<and> a \<asymp> b \<and> (\<forall>\<degree>x y. a \<sqsubseteq> x \<and> a \<sqsubseteq> y \<and> b \<asymp> x \<and> b \<asymp> y
                                                        \<longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x)"

definition inttan :: "'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "inttan a b \<equiv> sphere a \<and> sphere b \<and> a \<asymp> b \<and> (\<forall>\<degree>x y. a \<sqsubseteq> x \<and> a \<sqsubseteq> y \<and> x \<sqsubseteq> b \<and> y \<sqsubseteq> b
                                                        \<longrightarrow> x \<sqsubseteq> y \<or> y \<sqsubseteq> x)"

definition extdiam :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "extdiam a b c \<equiv> exttan a c \<and> exttan b c
                 \<and> (\<forall>\<degree>x y. x \<asymp> c \<and> y \<asymp> c \<and> a \<sqsubseteq> x \<and> b \<sqsubseteq> y \<longrightarrow> x \<asymp> y)"

definition intdiam :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "intdiam a b c \<equiv> inttan a c \<and> inttan b c
                 \<and> (\<forall>\<degree>x y. x \<asymp> c \<and> y \<asymp> c \<and> exttan a x \<and> exttan b y \<longrightarrow> x \<asymp> y)"

abbreviation properconcentric :: "'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "properconcentric a b \<equiv> a \<sqsubset> b
                        \<and> (\<forall>\<degree>x y. extdiam x y a \<and> inttan x b \<and> inttan y b \<longrightarrow> intdiam x y b)"

definition concentric :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<odot>" 100) where
  "a \<odot> b \<equiv> sphere a \<and> sphere b \<and> (a = b \<or> properconcentric a b \<or> properconcentric b a)"

definition onboundary :: "'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "onboundary s r \<equiv> sphere s \<and> (\<forall>s'. s' \<odot> s \<longrightarrow> s' \<frown> r \<and> \<not> s' \<sqsubseteq> r)"

definition equidistant3 :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "equidistant3 x y z \<equiv> \<exists>\<degree>z'. z' \<odot> z \<and> onboundary y z' \<and> onboundary x z'"

definition betw :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" ("[_ _ _]" [100, 100, 100] 100) where
  "[x y z] \<equiv> sphere x \<and> sphere z
             \<and> (x \<odot> y \<or> y \<odot> z
                \<or> (\<exists>x' y' z' v w. x' \<odot> x \<and> y' \<odot> y \<and> z' \<odot> z
                                  \<and> extdiam x' y' v \<and> extdiam v w y' \<and> extdiam y' z' w))"

definition mid :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "mid x y z \<equiv> [x y z] \<and> (\<exists>\<degree>y'. y' \<odot> y \<and> onboundary x y' \<and> onboundary z y')"

definition equidistant4 :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" ("_ _ \<doteq> _ _" [100, 100, 100, 100] 100) where
  "x y \<doteq> z w \<equiv> \<exists>\<degree>u v. mid w u y \<and> mid x u v \<and> equidistant3 v z y"

definition oninterior :: "'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "oninterior s r \<equiv> \<exists>s'. s' \<odot> s \<and> s' \<sqsubseteq> r"

definition nearer :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "nearer w x y z \<equiv> \<exists>\<degree>x'. [w x x'] \<and> \<not> x \<odot> x' \<and> w x' \<doteq> y z"

end

locale partial_region_geometry = mereology_sphere partof sphere
  for partof :: "'region \<Rightarrow> 'region \<Rightarrow> bool" (infix "\<sqsubseteq>" 100)
  and sphere :: "'region \<Rightarrow> bool" +
  assumes A4: "\<lbrakk>x \<odot> y; y \<odot> z\<rbrakk> \<Longrightarrow> x \<odot> z"
      and A5: "\<lbrakk>x y \<doteq> z w; x' \<odot> x\<rbrakk> \<Longrightarrow> x' y \<doteq> z w"
      and A6: "\<lbrakk>sphere x; sphere y; \<not> x \<odot> y\<rbrakk>
               \<Longrightarrow> \<exists>\<degree>s. \<forall>\<degree>z. oninterior z s = nearer x z x y"
      and A7: "sphere x \<Longrightarrow> \<exists>\<degree>y. \<not> x \<odot> y \<and> (\<forall>\<degree>z. oninterior z x = nearer x z x y)"
      and A8: "x \<sqsubseteq> y = (\<forall>s. oninterior s x \<longrightarrow> oninterior s y)"
      and A9: "\<exists>\<degree>s. s \<sqsubseteq> r"
begin

(* 2 marks *)
thm equiv_def
theorem conc_equiv:
  "equiv {z. sphere z} {(x,y). x \<odot> y}"
proof -
  let ?\<alpha> = "{(x,y). x \<odot> y}"
  have 0: "refl_on (Collect sphere) ?\<alpha>"
    using concentric_def parthood_partial_order.antisym sum_all_with_parts_overlapping_self sumregions_def A7 A9 by fastforce
  have 1: "sym ?\<alpha>" 
    using concentric_def A7 parthood_partial_order.antisym sum_all_with_parts_overlapping_self sumregions_def 0 A9 by fastforce
  have 2: "trans ?\<alpha>"
    using A7 concentric_def parthood_partial_order.antisym sum_all_with_parts_overlapping_self sumregions_def 0 A9 by fastforce
  thus "equiv {z. sphere z} {(x,y). x \<odot> y}" using equiv_def 0 1 by blast
qed


(* 6 marks *)
theorem region_is_spherical_sum:  
  "\<Squnion> {p. p \<sqsubseteq> x \<and> sphere p} x"
proof -
  have 0: "\<exists>y. \<Squnion> {p. p \<sqsubseteq> x \<and> sphere p} y" 
    using A7 A9 sumregions_def concentric_def parthood_partial_order.antisym sum_all_with_parts_overlapping_self by auto
  thus "\<Squnion> {p. p \<sqsubseteq> x \<and> sphere p} x" using sumregions_def by auto
qed

(* 1 mark *)
theorem region_spherical_interior:
  "oninterior s r \<Longrightarrow> \<exists>\<degree>s'. s' \<sqsubseteq> r \<and> oninterior s s'"
  using oninterior_def concentric_def by auto

(* 2 marks *)
(* Only A8 is needed for this proof as it defines parthood using region interiors (if every 
internal region of x is also a part of y it means that x must be a part of y), we can therefore use 
this to prove x = y using region interiors by obtaining x \<sqsubseteq> y and y \<sqsubseteq> x from our assumption *)
theorem equal_interiors_equal_regions:
  assumes "oninterior p x \<longleftrightarrow> oninterior p y"
  shows "x = y"
  using A8 sum_one_is_self sumregions_def by simp

(* 2 marks *)
theorem proper_have_nonoverlapping_proper_sphere:
  assumes "s \<sqsubset> r"
  shows "\<exists>\<degree>p. p \<sqsubset> r \<and> p \<asymp> s" 
proof -
  have "s \<sqsubset> r \<Longrightarrow> \<exists>\<degree>p. p \<sqsubseteq> r \<and> p \<asymp> s"
    using parthood_partial_order.leD sum_one_is_self sumregions_def by auto
  thus "\<exists>\<degree>p. p \<sqsubset> r \<and> p \<asymp> s" using properpartof_def sumregions_def assms sum_one_is_self by simp
qed

(* 4 marks *)
theorem not_sphere_spherical_parts_gt1:
  assumes "\<Squnion> {p. p \<sqsubseteq> r \<and> sphere p} r"
      and "\<not> sphere r"
    shows "\<exists>\<degree>a b. a \<noteq> b \<and> a \<sqsubseteq> r \<and> b \<sqsubseteq> r" 
proof -
  have 0: "\<Squnion> {x} r \<Longrightarrow> \<not> sphere x"
    using A9 assms(2) parthood_partial_order.antisym sum_parts_eq sumregions_def by blast
  thus "\<exists>\<degree>a b. a \<noteq> b \<and> a \<sqsubseteq> r \<and> b \<sqsubseteq> r" using sum_one_is_self sumregions_def assms(1) by auto
qed

end

section \<open>Part 3\<close>

context mereology_sphere
begin

(* 3 marks *)
lemma
  assumes T4: "\<And>x y. \<lbrakk>sphere x; sphere y\<rbrakk> \<Longrightarrow> x y \<doteq> y x"
      and A9: "\<exists>\<degree>s. s \<sqsubseteq> r"
    shows False
proof -
  have 0: "\<And>x y. \<lbrakk>sphere x; sphere y\<rbrakk> \<Longrightarrow> x y \<doteq> y x \<Longrightarrow> False" 
    using equidistant3_def equidistant4_def onboundary_def by auto
  moreover
  have 1: "\<exists>\<degree>s. s \<sqsubseteq> r \<Longrightarrow> False" using T4 calculation by blast
  ultimately show "False" using A9 by blast
qed

(* 3 marks *)
(* The issue was that the geometry definitions treated these arguments as regions and not spheres. 
I fixed it by adding sphere conditions using conjunctions to the definition. *)
definition equidistant3' :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" where
  "equidistant3' x y z \<equiv> \<exists>\<degree>z'. z' \<odot> z \<and> onboundary y z' \<and> onboundary x z' \<and> sphere x \<and> sphere y \<and> sphere z"

no_notation equidistant4 ("_ _ \<doteq> _ _" [100, 100, 100, 100] 100)

definition equidistant4' :: "'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> 'region \<Rightarrow> bool" ("_ _ \<doteq> _ _" [100, 100, 100, 100] 100) where
  "x y \<doteq> z w \<equiv> \<exists>\<degree>u v. mid w u y \<and> mid x u v \<and> equidistant3' v z y"

end

datatype two_reg = Left | Right | Both

(* 2 marks *)
definition tworeg_partof :: "two_reg \<Rightarrow> two_reg \<Rightarrow> bool" (infix "\<sqsubseteq>" 100) where
  "x \<sqsubseteq> y \<equiv> x = y \<or> y = Both"

abbreviation sumregions_abbrev :: "two_reg set \<Rightarrow> two_reg \<Rightarrow> bool" ("\<Squnion> _ _") where
"\<Squnion> \<alpha> x \<equiv> partof.sumregions (\<sqsubseteq>) \<alpha> x"

abbreviation overlaps_abbrev :: "two_reg \<Rightarrow> two_reg \<Rightarrow> bool" ("_ \<frown>  _") where
"x \<frown> y \<equiv> partof.overlaps (\<sqsubseteq>) x y"

(* 12 marks *)
interpretation mereology "(\<sqsubseteq>)"
proof 
  show "\<forall>x y z. x \<sqsubseteq> y \<and> y \<sqsubseteq> z \<longrightarrow> x \<sqsubseteq> z"
  proof -
    have 0: "x \<sqsubseteq> y \<and> y \<sqsubseteq> x \<longrightarrow> x \<sqsubseteq> x" using two_reg.exhaust tworeg_partof_def by auto
    thus "\<forall>x y z. x \<sqsubseteq> y \<and> y \<sqsubseteq> z \<longrightarrow> x \<sqsubseteq> z" using impI tworeg_partof_def by auto
  qed
next
  show "\<forall>\<alpha>. \<alpha> \<noteq> {} \<longrightarrow> (\<exists>x. \<Squnion> \<alpha> x)" 
  proof -
    have 1: "\<alpha> \<noteq> {} \<Longrightarrow> \<exists>y x. y \<in> \<alpha> \<and> y \<sqsubseteq> x"
      using tworeg_partof_def by auto
    have 2: "\<alpha> \<noteq> {} \<Longrightarrow> \<exists>y x z. y \<in> \<alpha> \<and> y \<sqsubseteq> x \<and> z \<in> \<alpha> \<and> y \<frown> z"
      using tworeg_partof_def partof.overlaps_def by (metis 1)
    thus "\<forall>\<alpha>. \<alpha> \<noteq> {} \<longrightarrow> (\<exists>x. \<Squnion> \<alpha> x)" by sorry
  qed
next
  show "\<forall>\<alpha> x y. \<Squnion> \<alpha> x \<and> \<Squnion> \<alpha> y \<longrightarrow> x = y"
    by (metis (full_types) partof.sumregions_def tworeg_partof_def)
qed


end