theory "Finite_Bounded_Lattice" imports Main begin

locale finite_bounded_lattice = finite + bounded_lattice
begin

sublocale comp_fun_commute_sup: comp_fun_commute sup
proof standard
  fix y x
  show "sup y ∘ sup x = sup x ∘ sup y"
  by (simp add: comp_fun_commute.comp_fun_commute comp_fun_idem.axioms(1) comp_fun_idem_sup)
qed

sublocale comp_fun_commute_inf: comp_fun_commute inf
proof standard
  fix y x
  show "inf y ∘ inf x = inf x ∘ inf y"
  by (simp add: comp_fun_commute.comp_fun_commute comp_fun_idem.axioms(1) comp_fun_idem_inf)
qed

definition Inf :: "'a set ⇒ 'a"
  where "Inf A ≡ Finite_Set.fold inf top A"

definition Sup :: "'a set ⇒ 'a"
  where "Sup A ≡ Finite_Set.fold sup bot A"

sublocale complete_lattice Inf Sup inf less_eq less sup bot top
proof standard
  fix x :: 'a and A
  assume mem: "x ∈ A"
  hence neq: "A ≠ {}" by blast
  show "less_eq (Inf A) x"
  using finite[where ?A=A] neq mem proof (induct rule: finite_ne_induct)
    case (singleton y)
    hence y_eq: "y = x" by simp
    have Inf_singleton: "⋀x. Inf {x} = x" unfolding Inf_def by simp
    show ?case unfolding Inf_singleton y_eq by (rule order_refl)
  next
    case (insert y F)
    then show ?case proof (cases "x = y")
      case True
      have x_nmem: "x ∉ F" unfolding True using insert.hyps(3) .
      have Inf_insert: "Inf (insert x F) = inf x (Inf F)"
        unfolding Inf_def using comp_fun_commute_inf.fold_insert finite[where ?A=F] x_nmem .
      show "less_eq (Inf (insert y F)) x" unfolding True[symmetric] Inf_insert using inf.cobounded1 .
    next
      case False
      hence x_mem: "x ∈ F" using insert.prems by force
      have Inf_insert: "Inf (insert y F) = inf y (Inf F)"
        unfolding Inf_def using comp_fun_commute_inf.fold_insert finite insert.hyps(3) .
      show "less_eq (Inf (insert y F)) x"
      unfolding Inf_insert proof -
        show "less_eq (inf y (Inf F)) x"
        proof (rule order_trans)
          show "less_eq (Inf F) x" using insert.hyps(4) x_mem .
        next
          show "less_eq (inf y (Inf F)) (Inf F)" using inf.cobounded2 .
        qed
      qed
    qed
  qed
next
  fix z :: 'a and A
  assume 1: "⋀x. x ∈ A ⟹ less_eq z x"
  show "less_eq z (Inf A)" using finite[where ?A=A] 1
  proof (induct rule: finite_induct)
    case empty
    have Inf_empty: "Inf {} = top" unfolding Inf_def by simp
    show ?case unfolding Inf_empty using top_greatest .
  next
    case (insert x F)
    have Inf_insert: "Inf (insert x F) = inf x (Inf F)"
      unfolding Inf_def using comp_fun_commute_inf.fold_insert finite[where ?A=F] insert.hyps(2) .
    show "less_eq z (Inf (insert x F))"
    unfolding Inf_insert proof (rule le_infI)
      show "less_eq z x" using insert.prems by simp
    next
      show "less_eq z (Inf F)"
      proof (rule insert.hyps(3))
        show "⋀u. u ∈ F ⟹ less_eq z u" using insert.prems by blast
      qed
    qed
  qed
next
  fix x :: 'a and A
  assume mem: "x ∈ A"
  hence neq: "A ≠ {}" by blast
  show "less_eq x (Sup A)" using finite[where ?A=A] neq mem proof (induct rule: finite_ne_induct)
    case (singleton y)
    hence y_eq: "y = x" by simp
    have Sup_singleton: "⋀x. Sup {x} = x" unfolding Sup_def by simp
    show ?case unfolding Sup_singleton y_eq by (rule order_refl)
  next
    case (insert y F)
    then show ?case proof (cases "x = y")
      case True
      have x_nmem: "x ∉ F" unfolding True using insert.hyps(3) .
      have Sup_insert: "Sup (insert x F) = sup x (Sup F)" unfolding Sup_def using comp_fun_commute_sup.fold_insert finite[where ?A=F] x_nmem .
      show "less_eq x (Sup (insert y F))" unfolding True[symmetric] Sup_insert using sup.cobounded1 .
    next
      case False
      hence x_mem: "x ∈ F" using insert.prems by force
      have Sup_insert: "Sup (insert y F) = sup y (Sup F)" unfolding Sup_def using comp_fun_commute_sup.fold_insert finite insert.hyps(3) .
      show "less_eq x (Sup (insert y F))"
      unfolding Sup_insert proof -
        show "less_eq x (sup y (Sup F))"
        proof (rule order_trans)
          show "less_eq x (Sup F)" using insert.hyps(4) x_mem .
        next
          show "less_eq (Sup F) (sup y (Sup F))" using sup.cobounded2 .
        qed
      qed
    qed
  qed
next
  fix z :: 'a and A
  assume 1: "⋀x. x ∈ A ⟹ less_eq x z"
  show "less_eq (Sup A) z" using finite[where ?A=A] 1 proof (induct rule: finite_induct)
    case empty
    have Sup_empty: "Sup {} = bot" unfolding Sup_def by simp
    show ?case unfolding Sup_empty using bot_least .
  next
    case (insert y F)
    have Sup_insert: "Sup (insert y F) = sup y (Sup F)"
      unfolding Sup_def using comp_fun_commute_sup.fold_insert finite[where ?A=F] insert.hyps(2) .
    show "less_eq (Sup (insert y F)) z"
    unfolding Sup_insert proof (rule le_supI)
      show "less_eq y z" using insert.prems by simp
    next
      show "less_eq (Sup F) z"
      proof (rule insert.hyps(3))
        show "⋀x. x ∈ F ⟹ less_eq x z" using insert.prems by blast
      qed
    qed
  qed
next
  show "Inf {} = top" unfolding Inf_def by simp
next
  show "Sup {} = bot" unfolding Sup_def by simp
qed

end
