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

lemma 6: "(\<not>(\<exists>x. \<not>P x) V R) \<longrightarrow> ((\<exists>x. \<not>P x) \<longrightarrow> R)"

lemma 7:

lemma 8:

lemma 9:

lemma 10:

lemma 11:

lemma 12:

end