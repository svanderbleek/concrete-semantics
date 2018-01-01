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

  lemma add_swap: "add (Suc m) n = add m (Suc n)"
    apply(induction m)
    apply(auto)
  done

  lemma add_comm: "add m n = add n m"
    apply(induction m)
    apply(simp add: add_zero[symmetric])
    apply(simp add: add_swap[symmetric])
  done

  lemma add_asso: "add a (add b c) = add (add a b) c"
    apply(induction a)
    apply(auto)
  done

  fun double :: "nat \<Rightarrow> nat" where
    "double 0 = 0"
  | "double (Suc m) = Suc (Suc (double m))"

  lemma doub_add: "double m = add m m"
    apply(induction m)
    apply(auto)
    apply(simp add: add_swap[symmetric])
  done
end