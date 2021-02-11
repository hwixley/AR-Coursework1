theory cw1q1

imports Main

begin

lemma 1: "A \<or> A \<longrightarrow> A"
  apply(rule impI)
  apply(erule disjE)
  by assumption

lemma 2: "A \<and> A \<longrightarrow> A"
  apply(rule impI)
  apply(erule conjE)
  by assumption

lemma 3: "(\<not>P \<or> R) \<longrightarrow> (P \<longrightarrow> R)"
  apply(rule impI)+
  apply(erule disjE)
   apply(erule notE)
  by assumption

lemma 4: "(\<exists>x. P x \<and> Q x) \<longrightarrow> (\<exists>x. P x) \<and> (\<exists>x. Q x)"
  apply(rule impI)
  apply(rule conjI)
   apply(erule exE)+
   apply(erule conjE)+
   apply(rule exI)
   apply(assumption)
  apply(erule exE)
  apply(erule conjE)
  apply(rule exI)
  by assumption

lemma 5: "(\<not>(\<exists>x. \<not>P x) \<or> R) \<longrightarrow> ((\<exists>x. \<not>P x) \<longrightarrow> R)"
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

lemma 6: "(\<not>(\<exists>x. \<not>P x) \<or> R) \<longrightarrow> ((\<exists>x. \<not>P x) \<longrightarrow> R)"
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

lemma 7: "(\<forall>x. P x) \<longrightarrow> \<not>(\<exists>x. \<not>P x)"
  apply(rule impI)
  apply(rule notI)
  apply(erule exE)
  apply(erule allE)
  apply(erule notE)
  by assumption

lemma 8: "P \<or> \<not>P"

lemma 9: "\<not>\<not>P \<longrightarrow> P"

lemma 10: "(\<not>P \<longrightarrow> P) \<longrightarrow> P"

lemma 11: "(\<not>P \<longrightarrow> False)\<longrightarrow>P"

lemma 12: "(\<not>(\<forall>x. P x \<or> R x)) = (\<exists>x. \<not>P x \<and> \<not>R x)"

lemma 13: "(\<exists>x. P x \<or> R x) = (\<not>((\<forall>x. \<not>P x) \<and> \<not>(\<exists>x. R x)))"

end