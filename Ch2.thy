theory Ch2
imports Main
begin
  fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
    "add 0 n = n"
  | "add (Suc m) n = Suc (add m n)"

  lemma add_zero: "add m 0 = m"
    apply(induction m)
    apply(auto)
  done

  lemma add_succ: "add (Suc m) n = add m (Suc n)"
    apply(induction m)
    apply(auto)
  done

  lemma add_comm: "add m n = add n m"
    apply(induction m)
    apply(simp add: add_zero[symmetric])
    apply(auto)
  done
end