theory Ch2
imports Main
begin
  fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    "add 0 n = n" |
    "add (Suc m) n = Suc (add m n)"

  lemma add02: "add m 0 = m"
    apply(induction m)
    apply(auto)
  done
end