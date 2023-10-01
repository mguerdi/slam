theory paper_example_25

imports "../jeha" 

begin

declare [[jeha_trace]]

lemma paper_example_25:
  shows "(\<And>z. z a = True \<Longrightarrow> z b = True) \<Longrightarrow> a = b"
  by (jeha)

end