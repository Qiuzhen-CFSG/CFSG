module

public import Theory.AlgebraicGroup.RootSystems.Exceptional
public import Theory.AlgebraicGroup.RootSystems.Weyl

open Equiv

namespace Theory.AlgebraicGroup

open SimpleGraph StandardRootSystem
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

private def sumOptionEquivOptionSum (α β : Type*) :
    α ⊕ Option β ≃ Option (α ⊕ β) where
  toFun
    | Sum.inl a => some (Sum.inl a)
    | Sum.inr none => none
    | Sum.inr (some b) => some (Sum.inr b)
  invFun
    | none => Sum.inr none
    | some (Sum.inl a) => Sum.inl a
    | some (Sum.inr b) => Sum.inr (some b)
  left_inv x := by cases x with
    | inl a => rfl
    | inr b => cases b <;> rfl
  right_inv x := by cases x with
    | none => rfl
    | some y => cases y <;> rfl

private def threeArmSwap01 (α β γ : Type*) :
    Option (α ⊕ β ⊕ γ) ≃ Option (β ⊕ α ⊕ γ) where
  toFun
    | none => none
    | some (Sum.inl a) => some (Sum.inr (Sum.inl a))
    | some (Sum.inr (Sum.inl b)) => some (Sum.inl b)
    | some (Sum.inr (Sum.inr c)) => some (Sum.inr (Sum.inr c))
  invFun
    | none => none
    | some (Sum.inl b) => some (Sum.inr (Sum.inl b))
    | some (Sum.inr (Sum.inl a)) => some (Sum.inl a)
    | some (Sum.inr (Sum.inr c)) => some (Sum.inr (Sum.inr c))
  left_inv x := by
    rcases x with _ | (_ | (_ | _)) <;> rfl
  right_inv x := by
    rcases x with _ | (_ | (_ | _)) <;> rfl

private def threeArmSwap12 (α β γ : Type*) :
    Option (α ⊕ β ⊕ γ) ≃ Option (α ⊕ γ ⊕ β) where
  toFun
    | none => none
    | some (Sum.inl a) => some (Sum.inl a)
    | some (Sum.inr (Sum.inl b)) => some (Sum.inr (Sum.inr b))
    | some (Sum.inr (Sum.inr c)) => some (Sum.inr (Sum.inl c))
  invFun
    | none => none
    | some (Sum.inl a) => some (Sum.inl a)
    | some (Sum.inr (Sum.inl c)) => some (Sum.inr (Sum.inr c))
    | some (Sum.inr (Sum.inr b)) => some (Sum.inr (Sum.inl b))
  left_inv x := by
    rcases x with _ | (_ | (_ | _)) <;> rfl
  right_inv x := by
    rcases x with _ | (_ | (_ | _)) <;> rfl

private def typeDThreeArmEquiv (c : ℕ) :
    Fin (c + 3) ≃ Option (Fin c ⊕ Fin 1 ⊕ Fin 1) :=
  finSumFinEquiv.symm |>.trans
    (Equiv.sumCongr (Fin.revPerm (n := c))
      ((finSuccEquiv 2).trans
        (Equiv.optionCongr (@finSumFinEquiv 1 1).symm))) |>.trans
    (sumOptionEquivOptionSum (Fin c) (Fin 1 ⊕ Fin 1))

@[simp] private lemma typeDThreeArmEquiv_castAdd (c : ℕ) (i : Fin c) :
    typeDThreeArmEquiv c (Fin.castAdd 3 i) =
      some (Sum.inl (Fin.rev i)) := by
  simp [typeDThreeArmEquiv, sumOptionEquivOptionSum, Equiv.optionCongr]

@[simp] private lemma typeDThreeArmEquiv_center (c : ℕ) :
    typeDThreeArmEquiv c (Fin.natAdd c (0 : Fin 3)) = none := by
  simp [typeDThreeArmEquiv, sumOptionEquivOptionSum, Equiv.optionCongr]

@[simp] private lemma typeDThreeArmEquiv_firstLeaf (c : ℕ) :
    typeDThreeArmEquiv c (Fin.natAdd c (1 : Fin 3)) =
      some (Sum.inr (Sum.inl 0)) := by
  have hs : (finSuccEquiv 2) (1 : Fin 3) = some (0 : Fin 2) := by
    change some (0 : Fin 2) = some (0 : Fin 2)
    rfl
  have hsum : (@finSumFinEquiv 1 1).symm (0 : Fin 2) = Sum.inl 0 := by
    rfl
  simp [typeDThreeArmEquiv, sumOptionEquivOptionSum, Equiv.optionCongr, hs,
    hsum]

@[simp] private lemma typeDThreeArmEquiv_secondLeaf (c : ℕ) :
    typeDThreeArmEquiv c (Fin.natAdd c (2 : Fin 3)) =
      some (Sum.inr (Sum.inr 0)) := by
  have hs : (finSuccEquiv 2) (2 : Fin 3) = some (1 : Fin 2) := by
    change some (1 : Fin 2) = some (1 : Fin 2)
    rfl
  have hsum : (@finSumFinEquiv 1 1).symm (1 : Fin 2) = Sum.inr 0 := by
    rfl
  simp [typeDThreeArmEquiv, sumOptionEquivOptionSum, Equiv.optionCongr, hs,
    hsum]

private def typeEThreeArmEquiv (m : ℕ) :
    Fin (m + 4) ≃ Option (Fin 2 ⊕ Fin 1 ⊕ Fin m) :=
  finCongr (by omega) |>.trans
    finSumFinEquiv.symm |>.trans
    (Equiv.sumCongr (Fin.revPerm (n := 2))
      ((finSuccEquiv (m + 1)).trans
        (Equiv.optionCongr
          ((finCongr (by omega : m + 1 = 1 + m)).trans
            (@finSumFinEquiv 1 m).symm)))) |>.trans
    (sumOptionEquivOptionSum (Fin 2) (Fin 1 ⊕ Fin m))

private def typeE6ThreeArmEquiv :
    Fin 6 ≃ Option (Fin 2 ⊕ Fin 1 ⊕ Fin 2) :=
  (finCongr (by omega : 6 = 2 + 4)).trans (typeEThreeArmEquiv 2)

@[simp] private lemma typeE6ThreeArmEquiv_zero :
    typeE6ThreeArmEquiv 0 = some (Sum.inl 1) := by rfl

@[simp] private lemma typeE6ThreeArmEquiv_one :
    typeE6ThreeArmEquiv 1 = some (Sum.inl 0) := by rfl

@[simp] private lemma typeE6ThreeArmEquiv_two :
    typeE6ThreeArmEquiv 2 = none := by rfl

@[simp] private lemma typeE6ThreeArmEquiv_three :
    typeE6ThreeArmEquiv 3 = some (Sum.inr (Sum.inl 0)) := by rfl

@[simp] private lemma typeE6ThreeArmEquiv_four :
    typeE6ThreeArmEquiv 4 = some (Sum.inr (Sum.inr 0)) := by rfl

@[simp] private lemma typeE6ThreeArmEquiv_five :
    typeE6ThreeArmEquiv 5 = some (Sum.inr (Sum.inr 1)) := by rfl

private def typeE7ThreeArmEquiv :
    Fin 7 ≃ Option (Fin 2 ⊕ Fin 1 ⊕ Fin 3) :=
  (finCongr (by omega : 7 = 3 + 4)).trans (typeEThreeArmEquiv 3)

@[simp] private lemma typeE7ThreeArmEquiv_zero :
    typeE7ThreeArmEquiv 0 = some (Sum.inl 1) := by rfl

@[simp] private lemma typeE7ThreeArmEquiv_one :
    typeE7ThreeArmEquiv 1 = some (Sum.inl 0) := by rfl

@[simp] private lemma typeE7ThreeArmEquiv_two :
    typeE7ThreeArmEquiv 2 = none := by rfl

@[simp] private lemma typeE7ThreeArmEquiv_three :
    typeE7ThreeArmEquiv 3 = some (Sum.inr (Sum.inl 0)) := by rfl

@[simp] private lemma typeE7ThreeArmEquiv_four :
    typeE7ThreeArmEquiv 4 = some (Sum.inr (Sum.inr 0)) := by rfl

@[simp] private lemma typeE7ThreeArmEquiv_five :
    typeE7ThreeArmEquiv 5 = some (Sum.inr (Sum.inr 1)) := by rfl

@[simp] private lemma typeE7ThreeArmEquiv_six :
    typeE7ThreeArmEquiv 6 = some (Sum.inr (Sum.inr 2)) := by rfl

private def typeE8ThreeArmEquiv :
    Fin 8 ≃ Option (Fin 2 ⊕ Fin 1 ⊕ Fin 4) :=
  (finCongr (by omega : 8 = 4 + 4)).trans (typeEThreeArmEquiv 4)

@[simp] private lemma typeE8ThreeArmEquiv_zero :
    typeE8ThreeArmEquiv 0 = some (Sum.inl 1) := by rfl

@[simp] private lemma typeE8ThreeArmEquiv_one :
    typeE8ThreeArmEquiv 1 = some (Sum.inl 0) := by rfl

@[simp] private lemma typeE8ThreeArmEquiv_two :
    typeE8ThreeArmEquiv 2 = none := by rfl

@[simp] private lemma typeE8ThreeArmEquiv_three :
    typeE8ThreeArmEquiv 3 = some (Sum.inr (Sum.inl 0)) := by rfl

@[simp] private lemma typeE8ThreeArmEquiv_four :
    typeE8ThreeArmEquiv 4 = some (Sum.inr (Sum.inr 0)) := by rfl

@[simp] private lemma typeE8ThreeArmEquiv_five :
    typeE8ThreeArmEquiv 5 = some (Sum.inr (Sum.inr 1)) := by rfl

@[simp] private lemma typeE8ThreeArmEquiv_six :
    typeE8ThreeArmEquiv 6 = some (Sum.inr (Sum.inr 2)) := by rfl

@[simp] private lemma typeE8ThreeArmEquiv_seven :
    typeE8ThreeArmEquiv 7 = some (Sum.inr (Sum.inr 3)) := by rfl

private lemma cartan_typeD_of_threeArmNumbering
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (G : SimpleGraph κ) {c : ℕ}
    (hdiag : ∀ i, A i i = 2)
    (e : Option (Fin c ⊕ Fin 1 ⊕ Fin 1) ≃ κ)
    (hcenter0 : ∀ j,
      G.Adj (e none) (e (some (Sum.inl j))) ↔ j.val = 0)
    (hcenter1 : ∀ j,
      G.Adj (e none) (e (some (Sum.inr (Sum.inl j)))) ↔ j = 0)
    (hcenter2 : ∀ j,
      G.Adj (e none) (e (some (Sum.inr (Sum.inr j)))) ↔ j = 0)
    (hpath0 : ∀ j l,
      G.Adj (e (some (Sum.inl j))) (e (some (Sum.inl l))) ↔
        (pathGraph c).Adj j l)
    (hcross01 : ∀ j l,
      ¬G.Adj (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inl l)))))
    (hcross02 : ∀ j l,
      ¬G.Adj (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inr l)))))
    (hcross12 : ∀ j l,
      ¬G.Adj (e (some (Sum.inr (Sum.inl j))))
        (e (some (Sum.inr (Sum.inr l)))))
    (hedge : ∀ x y, G.Adj x y → A x y = -1)
    (hzeroNonadj : ∀ x y, x ≠ y → ¬G.Adj x y → A x y = 0) :
    ∃ e' : Fin (c + 3) ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeDCartanMatrix (c + 1) i j := by
  let e' : Fin (c + 3) ≃ κ := typeDThreeArmEquiv c |>.trans e
  let R : Fin (c + 3) → Fin (c + 3) → Prop := fun i j =>
    (j.val = c + 2 ∧ i.val + 2 = j.val) ∨
    (i.val = c + 2 ∧ j.val + 2 = i.val) ∨
    (j.val ≠ c + 2 ∧ i.val + 1 = j.val) ∨
    (i.val ≠ c + 2 ∧ j.val + 1 = i.val)
  have hqadj : ∀ i j, R i j ↔ G.Adj (e' i) (e' j) := by
    intro i j
    by_cases hi : i.val < c
    · let ii : Fin c := ⟨i.val, hi⟩
      have hiiv : ii.val = i.val := rfl
      have hii : i = Fin.castAdd 3 ii := Fin.ext rfl
      by_cases hj : j.val < c
      · let jj : Fin c := ⟨j.val, hj⟩
        have hjjv : jj.val = j.val := rfl
        have hjj : j = Fin.castAdd 3 jj := Fin.ext rfl
        simp [R, e', hii, hjj, hpath0, pathGraph_adj, Fin.rev]
        omega
      · by_cases hj0 : j.val = c
        · have hjj : j = Fin.natAdd c (0 : Fin 3) := Fin.ext (by simp; omega)
          simp [R, e', hii, hjj, hcenter0, G.adj_comm]
          omega
        · by_cases hj1 : j.val = c + 1
          · have hjj : j = Fin.natAdd c (1 : Fin 3) := Fin.ext (by simp; omega)
            simp [R, e', hii, hjj, hcross01]
            omega
          · have hj2 : j.val = c + 2 := by omega
            have hjj : j = Fin.natAdd c (2 : Fin 3) := Fin.ext (by simp; omega)
            simp [R, e', hii, hjj, hcross02]
            omega
    · by_cases hi0 : i.val = c
      · have hii : i = Fin.natAdd c (0 : Fin 3) := Fin.ext (by simp; omega)
        by_cases hj : j.val < c
        · let jj : Fin c := ⟨j.val, hj⟩
          have hjjv : jj.val = j.val := rfl
          have hjj : j = Fin.castAdd 3 jj := Fin.ext rfl
          simp [R, e', hii, hjj, hcenter0]
          omega
        · by_cases hj0 : j.val = c
          · have hjj : j = Fin.natAdd c (0 : Fin 3) := Fin.ext (by simp; omega)
            simp [R, e', hii, hjj]
          · by_cases hj1 : j.val = c + 1
            · have hjj : j = Fin.natAdd c (1 : Fin 3) := Fin.ext (by simp; omega)
              simp [R, e', hii, hjj, hcenter1]
            · have hjj : j = Fin.natAdd c (2 : Fin 3) := Fin.ext (by simp; omega)
              simp [R, e', hii, hjj, hcenter2]
      · by_cases hi1 : i.val = c + 1
        · have hii : i = Fin.natAdd c (1 : Fin 3) := Fin.ext (by simp; omega)
          by_cases hj : j.val < c
          · let jj : Fin c := ⟨j.val, hj⟩
            have hjjv : jj.val = j.val := rfl
            have hjj : j = Fin.castAdd 3 jj := Fin.ext rfl
            simp [R, e', hii, hjj, hcross01, G.adj_comm]
            omega
          · by_cases hj0 : j.val = c
            · have hjj : j = Fin.natAdd c (0 : Fin 3) := Fin.ext (by simp; omega)
              simp [R, e', hii, hjj, hcenter1, G.adj_comm]
            · by_cases hj1 : j.val = c + 1
              · have hjj : j = Fin.natAdd c (1 : Fin 3) := Fin.ext (by simp; omega)
                simp [R, e', hii, hjj]
              · have hjj : j = Fin.natAdd c (2 : Fin 3) := Fin.ext (by simp; omega)
                simp [R, e', hii, hjj, hcross12]
        · have hi2 : i.val = c + 2 := by omega
          have hii : i = Fin.natAdd c (2 : Fin 3) := Fin.ext (by simp; omega)
          by_cases hj : j.val < c
          · let jj : Fin c := ⟨j.val, hj⟩
            have hjjv : jj.val = j.val := rfl
            have hjj : j = Fin.castAdd 3 jj := Fin.ext rfl
            simp [R, e', hii, hjj, hcross02, G.adj_comm]
            omega
          · by_cases hj0 : j.val = c
            · have hjj : j = Fin.natAdd c (0 : Fin 3) := Fin.ext (by simp; omega)
              simp [R, e', hii, hjj, hcenter2, G.adj_comm]
            · by_cases hj1 : j.val = c + 1
              · have hjj : j = Fin.natAdd c (1 : Fin 3) := Fin.ext (by simp; omega)
                simp [R, e', hii, hjj, hcross12, G.adj_comm]
              · have hjj : j = Fin.natAdd c (2 : Fin 3) := Fin.ext (by simp; omega)
                simp [R, e', hii, hjj]
  have hedgeR : ∀ {i j}, R i j → A (e' i) (e' j) = -1 := by
    intro i j hij
    exact hedge _ _ ((hqadj i j).mp hij)
  have hzeroR : ∀ {i j}, i ≠ j → ¬R i j → A (e' i) (e' j) = 0 := by
    intro i j hij hn
    exact hzeroNonadj _ _ (e'.injective.ne hij) fun hadj =>
      hn ((hqadj i j).mpr hadj)
  refine ⟨e', cartan_forkGraph_eq_typeDCartanMatrix_of_entries A e'
    (fun i => hdiag _)
    (fun {i j} hj hsum => hedgeR (Or.inl ⟨by rw [hj]; rfl, hsum⟩))
    (fun {i j} hi hsum => hedgeR (Or.inr (Or.inl ⟨by rw [hi]; rfl, hsum⟩)))
    (fun {i j} hj hsum => hedgeR (Or.inr (Or.inr (Or.inl ⟨by
      intro hjv
      apply hj
      apply Fin.ext
      exact hjv, hsum⟩))))
    (fun {i j} hi hsum => hedgeR (Or.inr (Or.inr (Or.inr ⟨by
      intro hiv
      apply hi
      apply Fin.ext
      exact hiv, hsum⟩))))
    (fun {i j} hij hj hsum => hzeroR hij fun h => by
      have hjv : j.val = c + 2 := by rw [hj]; rfl
      rcases h with h | h | h | h <;> omega)
    (fun {i j} hij hi hsum => hzeroR hij fun h => by
      have hiv : i.val = c + 2 := by rw [hi]; rfl
      rcases h with h | h | h | h <;> omega)
    (fun {i j} hij hj hi hnext hprev => hzeroR hij fun h => by
      have hjv : j.val ≠ c + 2 := by
        intro hval
        apply hj
        apply Fin.ext
        exact hval
      have hiv : i.val ≠ c + 2 := by
        intro hval
        apply hi
        apply Fin.ext
        exact hval
      rcases h with h | h | h | h
      · exact hjv h.1
      · exact hiv h.1
      · exact hnext h.2
      · exact hprev h.2)⟩

private lemma cartan_typeE6_of_threeArmNumbering
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (G : SimpleGraph κ)
    (hdiag : ∀ i, A i i = 2)
    (e : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 2) ≃ κ)
    (hcenter0 : ∀ j,
      G.Adj (e none) (e (some (Sum.inl j))) ↔ j = 0)
    (hcenter1 : ∀ j,
      G.Adj (e none) (e (some (Sum.inr (Sum.inl j)))) ↔ j = 0)
    (hcenter2 : ∀ j,
      G.Adj (e none) (e (some (Sum.inr (Sum.inr j)))) ↔ j = 0)
    (hpath0 : ∀ j l,
      G.Adj (e (some (Sum.inl j))) (e (some (Sum.inl l))) ↔
        (pathGraph 2).Adj j l)
    (hpath2 : ∀ j l,
      G.Adj (e (some (Sum.inr (Sum.inr j))))
        (e (some (Sum.inr (Sum.inr l)))) ↔
        (pathGraph 2).Adj j l)
    (hcross01 : ∀ j l,
      ¬G.Adj (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inl l)))))
    (hcross02 : ∀ j l,
      ¬G.Adj (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inr l)))))
    (hcross12 : ∀ j l,
      ¬G.Adj (e (some (Sum.inr (Sum.inl j))))
        (e (some (Sum.inr (Sum.inr l)))))
    (hedge : ∀ x y, G.Adj x y → A x y = -1)
    (hzeroNonadj : ∀ x y, x ≠ y → ¬G.Adj x y → A x y = 0) :
    ∃ e' : Fin 6 ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeE6CartanMatrix i j := by
  let e' : Fin 6 ≃ κ := typeE6ThreeArmEquiv.trans e
  have hqadj : ∀ i j : Fin 6,
      typeE6CartanEdge i j ↔
        G.Adj (e' i) (e' j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [e', typeE6CartanEdge, hcenter0, hcenter1, hcenter2, hpath0,
        hpath2, hcross01, hcross02, hcross12, pathGraph_adj, G.adj_comm]
  have hzero : ∀ {i j : Fin 6}, i ≠ j → ¬typeE6CartanEdge i j →
      A (e' i) (e' j) = 0 := by
    intro i j hij hedgeij
    apply hzeroNonadj
    · exact e'.injective.ne hij
    · exact fun hadj => hedgeij ((hqadj i j).mpr hadj)
  refine ⟨e', cartan_forkGraph_eq_typeE6CartanMatrix_of_entries A e' ?_ ?_ hzero⟩
  · intro i
    exact hdiag _
  · intro i j hij
    apply hedge
    exact (hqadj i j).mp hij

private lemma cartan_typeE7_of_threeArmNumbering
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (G : SimpleGraph κ)
    (hdiag : ∀ i, A i i = 2)
    (e : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 3) ≃ κ)
    (hcenter0 : ∀ j,
      G.Adj (e none) (e (some (Sum.inl j))) ↔ j = 0)
    (hcenter1 : ∀ j,
      G.Adj (e none) (e (some (Sum.inr (Sum.inl j)))) ↔ j = 0)
    (hcenter2 : ∀ j,
      G.Adj (e none) (e (some (Sum.inr (Sum.inr j)))) ↔ j = 0)
    (hpath0 : ∀ j l,
      G.Adj (e (some (Sum.inl j))) (e (some (Sum.inl l))) ↔
        (pathGraph 2).Adj j l)
    (hpath2 : ∀ j l,
      G.Adj (e (some (Sum.inr (Sum.inr j))))
        (e (some (Sum.inr (Sum.inr l)))) ↔
        (pathGraph 3).Adj j l)
    (hcross01 : ∀ j l,
      ¬G.Adj (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inl l)))))
    (hcross02 : ∀ j l,
      ¬G.Adj (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inr l)))))
    (hcross12 : ∀ j l,
      ¬G.Adj (e (some (Sum.inr (Sum.inl j))))
        (e (some (Sum.inr (Sum.inr l)))))
    (hedge : ∀ x y, G.Adj x y → A x y = -1)
    (hzeroNonadj : ∀ x y, x ≠ y → ¬G.Adj x y → A x y = 0) :
    ∃ e' : Fin 7 ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeE7CartanMatrix i j := by
  let e' : Fin 7 ≃ κ := typeE7ThreeArmEquiv.trans e
  have hqadj : ∀ i j : Fin 7,
      typeE7CartanEdge i j ↔
        G.Adj (e' i) (e' j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [e', typeE7CartanEdge, hcenter0, hcenter1, hcenter2, hpath0,
        hpath2, hcross01, hcross02, hcross12, pathGraph_adj, G.adj_comm]
  have hzero : ∀ {i j : Fin 7}, i ≠ j → ¬typeE7CartanEdge i j →
      A (e' i) (e' j) = 0 := by
    intro i j hij hedgeij
    apply hzeroNonadj
    · exact e'.injective.ne hij
    · exact fun hadj => hedgeij ((hqadj i j).mpr hadj)
  refine ⟨e', cartan_forkGraph_eq_typeE7CartanMatrix_of_entries A e' ?_ ?_ hzero⟩
  · intro i
    exact hdiag _
  · intro i j hij
    apply hedge
    exact (hqadj i j).mp hij

private lemma cartan_typeE8_of_threeArmNumbering
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (G : SimpleGraph κ)
    (hdiag : ∀ i, A i i = 2)
    (e : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 4) ≃ κ)
    (hcenter0 : ∀ j,
      G.Adj (e none) (e (some (Sum.inl j))) ↔ j = 0)
    (hcenter1 : ∀ j,
      G.Adj (e none) (e (some (Sum.inr (Sum.inl j)))) ↔ j = 0)
    (hcenter2 : ∀ j,
      G.Adj (e none) (e (some (Sum.inr (Sum.inr j)))) ↔ j = 0)
    (hpath0 : ∀ j l,
      G.Adj (e (some (Sum.inl j))) (e (some (Sum.inl l))) ↔
        (pathGraph 2).Adj j l)
    (hpath2 : ∀ j l,
      G.Adj (e (some (Sum.inr (Sum.inr j))))
        (e (some (Sum.inr (Sum.inr l)))) ↔
        (pathGraph 4).Adj j l)
    (hcross01 : ∀ j l,
      ¬G.Adj (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inl l)))))
    (hcross02 : ∀ j l,
      ¬G.Adj (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inr l)))))
    (hcross12 : ∀ j l,
      ¬G.Adj (e (some (Sum.inr (Sum.inl j))))
        (e (some (Sum.inr (Sum.inr l)))))
    (hedge : ∀ x y, G.Adj x y → A x y = -1)
    (hzeroNonadj : ∀ x y, x ≠ y → ¬G.Adj x y → A x y = 0) :
    ∃ e' : Fin 8 ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeE8CartanMatrix i j := by
  let e' : Fin 8 ≃ κ := typeE8ThreeArmEquiv.trans e
  have hqadj : ∀ i j : Fin 8,
      typeE8CartanEdge i j ↔
        G.Adj (e' i) (e' j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [e', typeE8CartanEdge, hcenter0, hcenter1, hcenter2, hpath0,
        hpath2, hcross01, hcross02, hcross12, pathGraph_adj, G.adj_comm]
  have hzero : ∀ {i j : Fin 8}, i ≠ j → ¬typeE8CartanEdge i j →
      A (e' i) (e' j) = 0 := by
    intro i j hij hedgeij
    apply hzeroNonadj
    · exact e'.injective.ne hij
    · exact fun hadj => hedgeij ((hqadj i j).mpr hadj)
  refine ⟨e', cartan_forkGraph_eq_typeE8CartanMatrix_of_entries A e' ?_ ?_ hzero⟩
  · intro i
    exact hdiag _
  · intro i j hij
    apply hedge
    exact (hqadj i j).mp hij

/-- A positive-definite integral Cartan matrix whose support has an exact
three-arm numbering is, after renumbering, of type `D`, `E₆`, `E₇`, or `E₈`. -/
public theorem cartan_three_arm_classification_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    {n0 n1 n2 : ℕ}
    (e : Option (Fin (n0 + 1) ⊕ Fin (n1 + 1) ⊕ Fin (n2 + 1)) ≃ κ)
    (hcenter0 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e none) (e (some (Sum.inl j))) ↔ j = 0)
    (hcenter1 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e none) (e (some (Sum.inr (Sum.inl j)))) ↔ j = 0)
    (hcenter2 : ∀ j,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e none) (e (some (Sum.inr (Sum.inr j)))) ↔ j = 0)
    (hpath0 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inl j))) (e (some (Sum.inl l))) ↔
        (pathGraph (n0 + 1)).Adj j l)
    (hpath1 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inr (Sum.inl j))))
        (e (some (Sum.inr (Sum.inl l)))) ↔
        (pathGraph (n1 + 1)).Adj j l)
    (hpath2 : ∀ j l,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inr (Sum.inr j))))
        (e (some (Sum.inr (Sum.inr l)))) ↔
        (pathGraph (n2 + 1)).Adj j l)
    (hcross01 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inl l)))))
    (hcross02 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inl j))) (e (some (Sum.inr (Sum.inr l)))))
    (hcross12 : ∀ j l,
      ¬(SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
        (e (some (Sum.inr (Sum.inl j))))
        (e (some (Sum.inr (Sum.inr l)))))
    (hdeg : (SimpleGraph.fromRel fun x y => A x y ≠ 0).degree (e none) = 3) :
    (∃ m : ℕ, ∃ e' : Fin (m + 2) ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeDCartanMatrix m i j) ∨
    (∃ e' : Fin 6 ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeE6CartanMatrix i j) ∨
    (∃ e' : Fin 7 ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeE7CartanMatrix i j) ∨
    (∃ e' : Fin 8 ≃ κ,
      ∀ i j, A (e' i) (e' j) = typeE8CartanMatrix i j) := by
  classical
  let G : SimpleGraph κ := SimpleGraph.fromRel fun x y => A x y ≠ 0
  let f0 : Fin (n0 + 1) → κ := fun j => e (some (Sum.inl j))
  let f1 : Fin (n1 + 1) → κ := fun j => e (some (Sum.inr (Sum.inl j)))
  let f2 : Fin (n2 + 1) → κ := fun j => e (some (Sum.inr (Sum.inr j)))
  have hf0 : Function.Injective f0 := by
    intro i j hij
    simpa [f0] using e.injective hij
  have hf1 : Function.Injective f1 := by
    intro i j hij
    simpa [f1] using e.injective hij
  have hf2 : Function.Injective f2 := by
    intro i j hij
    simpa [f2] using e.injective hij
  have hc0 : ∀ j, e none ≠ f0 j := by
    intro j h
    simpa [f0] using e.injective h
  have hc1 : ∀ j, e none ≠ f1 j := by
    intro j h
    simpa [f1] using e.injective h
  have hc2 : ∀ j, e none ≠ f2 j := by
    intro j h
    simpa [f2] using e.injective h
  have h01 : ∀ j l, f0 j ≠ f1 l := by
    intro j l h
    simpa [f0, f1] using e.injective h
  have h02 : ∀ j l, f0 j ≠ f2 l := by
    intro j l h
    simpa [f0, f2] using e.injective h
  have h12 : ∀ j l, f1 j ≠ f2 l := by
    intro j l h
    simpa [f1, f2] using e.injective h
  have h10 : ∀ j l, f1 j ≠ f0 l := fun j l h => h01 l j h.symm
  have h20 : ∀ j l, f2 j ≠ f0 l := fun j l h => h02 l j h.symm
  have h21 : ∀ j l, f2 j ≠ f1 l := fun j l h => h12 l j h.symm
  have hcenter0' : ∀ j, G.Adj (e none) (f0 j) ↔ j = 0 := by
    simpa [G, f0] using hcenter0
  have hcenter1' : ∀ j, G.Adj (e none) (f1 j) ↔ j = 0 := by
    simpa [G, f1] using hcenter1
  have hcenter2' : ∀ j, G.Adj (e none) (f2 j) ↔ j = 0 := by
    simpa [G, f2] using hcenter2
  have hpath0' : ∀ j l, G.Adj (f0 j) (f0 l) ↔
      (pathGraph (n0 + 1)).Adj j l := by
    simpa [G, f0] using hpath0
  have hpath1' : ∀ j l, G.Adj (f1 j) (f1 l) ↔
      (pathGraph (n1 + 1)).Adj j l := by
    simpa [G, f1] using hpath1
  have hpath2' : ∀ j l, G.Adj (f2 j) (f2 l) ↔
      (pathGraph (n2 + 1)).Adj j l := by
    simpa [G, f2] using hpath2
  have hcross01' : ∀ j l, ¬G.Adj (f0 j) (f1 l) := by
    simpa [G, f0, f1] using hcross01
  have hcross02' : ∀ j l, ¬G.Adj (f0 j) (f2 l) := by
    simpa [G, f0, f2] using hcross02
  have hcross12' : ∀ j l, ¬G.Adj (f1 j) (f2 l) := by
    simpa [G, f1, f2] using hcross12
  have hcross10' : ∀ j l, ¬G.Adj (f1 j) (f0 l) := by
    intro j l h
    exact hcross01' l j (by simpa [G.adj_comm] using h)
  have hcross20' : ∀ j l, ¬G.Adj (f2 j) (f0 l) := by
    intro j l h
    exact hcross02' l j (by simpa [G.adj_comm] using h)
  have hcross21' : ∀ j l, ¬G.Adj (f2 j) (f1 l) := by
    intro j l h
    exact hcross12' l j (by simpa [G.adj_comm] using h)
  have hcenterBond0 :
      A (e none) (f0 0) = -1 ∧ A (f0 0) (e none) = -1 :=
    cartanSupport_degree_three_edge_entries_eq_neg_one A d hdiag hrank hpos
      (e none) (f0 0) hdeg (by simpa [G] using (hcenter0' 0).2 rfl)
  have hcenterBond1 :
      A (e none) (f1 0) = -1 ∧ A (f1 0) (e none) = -1 :=
    cartanSupport_degree_three_edge_entries_eq_neg_one A d hdiag hrank hpos
      (e none) (f1 0) hdeg (by simpa [G] using (hcenter1' 0).2 rfl)
  have hcenterBond2 :
      A (e none) (f2 0) = -1 ∧ A (f2 0) (e none) = -1 :=
    cartanSupport_degree_three_edge_entries_eq_neg_one A d hdiag hrank hpos
      (e none) (f2 0) hdeg (by simpa [G] using (hcenter2' 0).2 rfl)
  have hsimple :=
    cartan_three_arm_all_entries_eq_neg_one_of_diagonal_mul_posDef
      A d hdiag hrank hpos (e none) f0 f1 f2 hf0 hf1 hf2 hc0 hc1 hc2
      h01 h02 h12 hcenter0' hcenter1' hcenter2' hpath0' hpath1' hpath2'
      hcross01' hcross02' hcross12' hdeg
  have hedge : ∀ x y, G.Adj x y → A x y = -1 := by
    simpa [G, f0, f1, f2] using
      cartan_three_arm_support_adj_entry_eq_neg_one A e
        hcenter0 hcenter1 hcenter2 hpath0 hpath1 hpath2
        hcross01 hcross02 hcross12 hcenterBond0 hcenterBond1 hcenterBond2
        hsimple.1 hsimple.2.1 hsimple.2.2
  have hzero : ∀ x y, x ≠ y → ¬G.Adj x y → A x y = 0 := by
    intro x y hxy hnadj
    by_contra hne
    apply hnadj
    change x ≠ y ∧ (A x y ≠ 0 ∨ A y x ≠ 0)
    exact ⟨hxy, Or.inl hne⟩
  have hE6 : ¬(2 ≤ n0 + 1 ∧ 2 ≤ n1 + 1 ∧ 2 ≤ n2 + 1) := by
    intro h
    exact not_cartan_three_arm_affineE6_prefix_of_diagonal_mul_posDef
      A d hdiag hpos e hcenter0 hcenter1 hcenter2 hpath0 hpath1 hpath2
      hcross01 hcross02 hcross12 hcenterBond0 hcenterBond1 hcenterBond2
      (by simpa [f0] using hsimple.1) (by simpa [f1] using hsimple.2.1)
      (by simpa [f2] using hsimple.2.2) (by omega) (by omega) (by omega)
  have affineE7_of
      {a b c : ℕ} (g0 : Fin (a + 1) → κ) (g1 : Fin (b + 1) → κ)
      (g2 : Fin (c + 1) → κ)
      (hg0 : Function.Injective g0) (hg1 : Function.Injective g1)
      (hg2 : Function.Injective g2)
      (hgc0 : ∀ j, e none ≠ g0 j) (hgc1 : ∀ j, e none ≠ g1 j)
      (hgc2 : ∀ j, e none ≠ g2 j)
      (hg01 : ∀ j l, g0 j ≠ g1 l) (hg02 : ∀ j l, g0 j ≠ g2 l)
      (hg12 : ∀ j l, g1 j ≠ g2 l)
      (hgn0 : ∀ j, G.Adj (e none) (g0 j) ↔ j = 0)
      (hgn1 : ∀ j, G.Adj (e none) (g1 j) ↔ j = 0)
      (hgn2 : ∀ j, G.Adj (e none) (g2 j) ↔ j = 0)
      (hgp0 : ∀ j l, G.Adj (g0 j) (g0 l) ↔ (pathGraph (a + 1)).Adj j l)
      (hgp1 : ∀ j l, G.Adj (g1 j) (g1 l) ↔ (pathGraph (b + 1)).Adj j l)
      (hgp2 : ∀ j l, G.Adj (g2 j) (g2 l) ↔ (pathGraph (c + 1)).Adj j l)
      (hg01' : ∀ j l, ¬G.Adj (g0 j) (g1 l))
      (hg02' : ∀ j l, ¬G.Adj (g0 j) (g2 l))
      (hg12' : ∀ j l, ¬G.Adj (g1 j) (g2 l))
      (hb : 2 ≤ b) (hc : 2 ≤ c) : False := by
    obtain ⟨ep, hpref⟩ := simpleGraph_three_arm_affineE7_prefix_embedding
      G (e none) g0 g1 g2 hg0 hg1 hg2 hgc0 hgc1 hgc2 hg01 hg02 hg12
      hgn0 hgn1 hgn2 hgp0 hgp1 hgp2 hg01' hg02' hg12' (by omega) (by omega)
    exact not_cartan_affineE7_of_support_numbering A d hdiag hpos ep hpref
      fun i j hij => hedge _ _ ((hpref i j).mpr hij)
  have hE7 : ¬((3 ≤ n0 + 1 ∧ 3 ≤ n1 + 1) ∨
      (3 ≤ n0 + 1 ∧ 3 ≤ n2 + 1) ∨ (3 ≤ n1 + 1 ∧ 3 ≤ n2 + 1)) := by
    rintro (h | h | h)
    · exact affineE7_of f2 f0 f1 hf2 hf0 hf1 hc2 hc0 hc1 h20 h21 h01
        hcenter2' hcenter0' hcenter1' hpath2' hpath0' hpath1'
        hcross20' hcross21' hcross01' (by omega) (by omega)
    · exact affineE7_of f1 f0 f2 hf1 hf0 hf2 hc1 hc0 hc2 h10 h12 h02
        hcenter1' hcenter0' hcenter2' hpath1' hpath0' hpath2'
        hcross10' hcross12' hcross02' (by omega) (by omega)
    · exact affineE7_of f0 f1 f2 hf0 hf1 hf2 hc0 hc1 hc2 h01 h02 h12
        hcenter0' hcenter1' hcenter2' hpath0' hpath1' hpath2'
        hcross01' hcross02' hcross12' (by omega) (by omega)
  have affineE8_of
      {a b c : ℕ} (g0 : Fin (a + 1) → κ) (g1 : Fin (b + 1) → κ)
      (g2 : Fin (c + 1) → κ)
      (hg0 : Function.Injective g0) (hg1 : Function.Injective g1)
      (hg2 : Function.Injective g2)
      (hgc0 : ∀ j, e none ≠ g0 j) (hgc1 : ∀ j, e none ≠ g1 j)
      (hgc2 : ∀ j, e none ≠ g2 j)
      (hg01 : ∀ j l, g0 j ≠ g1 l) (hg02 : ∀ j l, g0 j ≠ g2 l)
      (hg12 : ∀ j l, g1 j ≠ g2 l)
      (hgn0 : ∀ j, G.Adj (e none) (g0 j) ↔ j = 0)
      (hgn1 : ∀ j, G.Adj (e none) (g1 j) ↔ j = 0)
      (hgn2 : ∀ j, G.Adj (e none) (g2 j) ↔ j = 0)
      (hgp0 : ∀ j l, G.Adj (g0 j) (g0 l) ↔ (pathGraph (a + 1)).Adj j l)
      (hgp1 : ∀ j l, G.Adj (g1 j) (g1 l) ↔ (pathGraph (b + 1)).Adj j l)
      (hgp2 : ∀ j l, G.Adj (g2 j) (g2 l) ↔ (pathGraph (c + 1)).Adj j l)
      (hg01' : ∀ j l, ¬G.Adj (g0 j) (g1 l))
      (hg02' : ∀ j l, ¬G.Adj (g0 j) (g2 l))
      (hg12' : ∀ j l, ¬G.Adj (g1 j) (g2 l))
      (hb : 1 ≤ b) (hc : 4 ≤ c) : False := by
    obtain ⟨ep, hpref⟩ := simpleGraph_three_arm_affineE8_prefix_embedding
      G (e none) g0 g1 g2 hg0 hg1 hg2 hgc0 hgc1 hgc2 hg01 hg02 hg12
      hgn0 hgn1 hgn2 hgp0 hgp1 hgp2 hg01' hg02' hg12' (by omega) (by omega)
    exact not_cartan_affineE8_of_support_numbering A d hdiag hpos ep hpref
      fun i j hij => hedge _ _ ((hpref i j).mpr hij)
  have hE8 : ¬((5 ≤ n0 + 1 ∧ 2 ≤ n1 + 1) ∨
      (5 ≤ n0 + 1 ∧ 2 ≤ n2 + 1) ∨ (5 ≤ n1 + 1 ∧ 2 ≤ n0 + 1) ∨
      (5 ≤ n1 + 1 ∧ 2 ≤ n2 + 1) ∨ (5 ≤ n2 + 1 ∧ 2 ≤ n0 + 1) ∨
      (5 ≤ n2 + 1 ∧ 2 ≤ n1 + 1)) := by
    rintro (h | h | h | h | h | h)
    · exact affineE8_of f2 f1 f0 hf2 hf1 hf0 hc2 hc1 hc0 h21 h20 h10
        hcenter2' hcenter1' hcenter0' hpath2' hpath1' hpath0'
        hcross21' hcross20' hcross10' (by omega) (by omega)
    · exact affineE8_of f1 f2 f0 hf1 hf2 hf0 hc1 hc2 hc0 h12 h10 h20
        hcenter1' hcenter2' hcenter0' hpath1' hpath2' hpath0'
        hcross12' hcross10' hcross20' (by omega) (by omega)
    · exact affineE8_of f2 f0 f1 hf2 hf0 hf1 hc2 hc0 hc1 h20 h21 h01
        hcenter2' hcenter0' hcenter1' hpath2' hpath0' hpath1'
        hcross20' hcross21' hcross01' (by omega) (by omega)
    · exact affineE8_of f0 f2 f1 hf0 hf2 hf1 hc0 hc2 hc1 h02 h01 h21
        hcenter0' hcenter2' hcenter1' hpath0' hpath2' hpath1'
        hcross02' hcross01' hcross21' (by omega) (by omega)
    · exact affineE8_of f1 f0 f2 hf1 hf0 hf2 hc1 hc0 hc2 h10 h12 h02
        hcenter1' hcenter0' hcenter2' hpath1' hpath0' hpath2'
        hcross10' hcross12' hcross02' (by omega) (by omega)
    · exact affineE8_of f0 f1 f2 hf0 hf1 hf2 hc0 hc1 hc2 h01 h02 h12
        hcenter0' hcenter1' hcenter2' hpath0' hpath1' hpath2'
        hcross01' hcross02' hcross12' (by omega) (by omega)
  have hcases := nat_three_arm_lengths_exact_cases_of_affine_forbidden
    (n0 + 1) (n1 + 1) (n2 + 1) (by omega) (by omega) (by omega) hE6 hE7 hE8
  rcases hcases with hD | hE6cases | hE7cases | hE8cases
  · have hD' := hD
    have horient : (n0 = 0 ∧ n1 = 0) ∨
        (n0 = 0 ∧ n2 = 0) ∨ (n1 = 0 ∧ n2 = 0) := by
      simp only [Multiset.count_cons, Multiset.count_zero] at hD'
      split at hD' <;> split at hD' <;> split at hD' <;> omega
    rcases horient with h01len | h02len | h12len
    · rcases h01len with ⟨hn0, hn1⟩
      subst n0
      subst n1
      let q : Option (Fin (n2 + 1) ⊕ Fin 1 ⊕ Fin 1) ≃
          Option (Fin 1 ⊕ Fin 1 ⊕ Fin (n2 + 1)) :=
        (threeArmSwap01 (Fin (n2 + 1)) (Fin 1) (Fin 1)).trans
          (threeArmSwap12 (Fin 1) (Fin (n2 + 1)) (Fin 1))
      let e' : Option (Fin (n2 + 1) ⊕ Fin 1 ⊕ Fin 1) ≃ κ := q.trans e
      refine Or.inl ⟨n2 + 2, ?_⟩
      simpa [Nat.add_assoc] using
        (cartan_typeD_of_threeArmNumbering A G hdiag e'
          (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f2]
            using hcenter2' j)
          (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f0]
            using hcenter0' j)
          (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f1]
            using hcenter1' j)
          (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2]
            using hpath2' j l)
          (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2, f0]
            using hcross20' j l)
          (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2, f1]
            using hcross21' j l)
          (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f0, f1]
            using hcross01' j l)
          hedge hzero)
    · rcases h02len with ⟨hn0, hn2⟩
      subst n0
      subst n2
      let q : Option (Fin (n1 + 1) ⊕ Fin 1 ⊕ Fin 1) ≃
          Option (Fin 1 ⊕ Fin (n1 + 1) ⊕ Fin 1) :=
        threeArmSwap01 (Fin (n1 + 1)) (Fin 1) (Fin 1)
      let e' : Option (Fin (n1 + 1) ⊕ Fin 1 ⊕ Fin 1) ≃ κ := q.trans e
      refine Or.inl ⟨n1 + 2, ?_⟩
      simpa [Nat.add_assoc] using
        (cartan_typeD_of_threeArmNumbering A G hdiag e'
          (by intro j; simpa [e', q, threeArmSwap01, f1] using hcenter1' j)
          (by intro j; simpa [e', q, threeArmSwap01, f0] using hcenter0' j)
          (by intro j; simpa [e', q, threeArmSwap01, f2] using hcenter2' j)
          (by intro j l; simpa [e', q, threeArmSwap01, f1] using hpath1' j l)
          (by intro j l; simpa [e', q, threeArmSwap01, f1, f0]
            using hcross10' j l)
          (by intro j l; simpa [e', q, threeArmSwap01, f1, f2]
            using hcross12' j l)
          (by intro j l; simpa [e', q, threeArmSwap01, f0, f2]
            using hcross02' j l)
          hedge hzero)
    · rcases h12len with ⟨hn1, hn2⟩
      subst n1
      subst n2
      refine Or.inl ⟨n0 + 2, ?_⟩
      simpa [Nat.add_assoc] using
        (cartan_typeD_of_threeArmNumbering A G hdiag e
          (by intro j; simpa [f0] using hcenter0' j)
          (by intro j; simpa [f1] using hcenter1' j)
          (by intro j; simpa [f2] using hcenter2' j)
          (by intro j l; simpa [f0] using hpath0' j l)
          (by intro j l; simpa [f0, f1] using hcross01' j l)
          (by intro j l; simpa [f0, f2] using hcross02' j l)
          (by intro j l; simpa [f1, f2] using hcross12' j l)
          hedge hzero)
  · rcases hE6cases with h | h | h
    · have hn0 : n0 = 0 := by omega
      have hn1 : n1 = 1 := by omega
      have hn2 : n2 = 1 := by omega
      subst n0
      subst n1
      subst n2
      let q := threeArmSwap01 (Fin 2) (Fin 1) (Fin 2)
      let e' : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 2) ≃ κ := q.trans e
      refine Or.inr (Or.inl ?_)
      exact cartan_typeE6_of_threeArmNumbering A G hdiag e'
        (by intro j; simpa [e', q, threeArmSwap01, f1] using hcenter1' j)
        (by intro j; simpa [e', q, threeArmSwap01, f0] using hcenter0' j)
        (by intro j; simpa [e', q, threeArmSwap01, f2] using hcenter2' j)
        (by intro j l; simpa [e', q, threeArmSwap01, f1] using hpath1' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, f2] using hpath2' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, f1, f0]
          using hcross10' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, f1, f2]
          using hcross12' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, f0, f2]
          using hcross02' j l)
        hedge hzero
    · have hn0 : n0 = 1 := by omega
      have hn1 : n1 = 0 := by omega
      have hn2 : n2 = 1 := by omega
      subst n0
      subst n1
      subst n2
      refine Or.inr (Or.inl ?_)
      exact cartan_typeE6_of_threeArmNumbering A G hdiag e
        (by intro j; simpa [f0] using hcenter0' j)
        (by intro j; simpa [f1] using hcenter1' j)
        (by intro j; simpa [f2] using hcenter2' j)
        (by intro j l; simpa [f0] using hpath0' j l)
        (by intro j l; simpa [f2] using hpath2' j l)
        (by intro j l; simpa [f0, f1] using hcross01' j l)
        (by intro j l; simpa [f0, f2] using hcross02' j l)
        (by intro j l; simpa [f1, f2] using hcross12' j l)
        hedge hzero
    · have hn0 : n0 = 1 := by omega
      have hn1 : n1 = 1 := by omega
      have hn2 : n2 = 0 := by omega
      subst n0
      subst n1
      subst n2
      let q := threeArmSwap12 (Fin 2) (Fin 1) (Fin 2)
      let e' : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 2) ≃ κ := q.trans e
      refine Or.inr (Or.inl ?_)
      exact cartan_typeE6_of_threeArmNumbering A G hdiag e'
        (by intro j; simpa [e', q, threeArmSwap12, f0] using hcenter0' j)
        (by intro j; simpa [e', q, threeArmSwap12, f2] using hcenter2' j)
        (by intro j; simpa [e', q, threeArmSwap12, f1] using hcenter1' j)
        (by intro j l; simpa [e', q, threeArmSwap12, f0] using hpath0' j l)
        (by intro j l; simpa [e', q, threeArmSwap12, f1] using hpath1' j l)
        (by intro j l; simpa [e', q, threeArmSwap12, f0, f2]
          using hcross02' j l)
        (by intro j l; simpa [e', q, threeArmSwap12, f0, f1]
          using hcross01' j l)
        (by intro j l; simpa [e', q, threeArmSwap12, f2, f1]
          using hcross21' j l)
        hedge hzero
  · rcases hE7cases with h | h | h | h | h | h
    · have hn0 : n0 = 0 := by omega
      have hn1 : n1 = 1 := by omega
      have hn2 : n2 = 2 := by omega
      subst n0
      subst n1
      subst n2
      let q := threeArmSwap01 (Fin 2) (Fin 1) (Fin 3)
      let e' : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 3) ≃ κ := q.trans e
      refine Or.inr (Or.inr (Or.inl ?_))
      exact cartan_typeE7_of_threeArmNumbering A G hdiag e'
        (by intro j; simpa [e', q, threeArmSwap01, f1] using hcenter1' j)
        (by intro j; simpa [e', q, threeArmSwap01, f0] using hcenter0' j)
        (by intro j; simpa [e', q, threeArmSwap01, f2] using hcenter2' j)
        (by intro j l; simpa [e', q, threeArmSwap01, f1] using hpath1' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, f2] using hpath2' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, f1, f0]
          using hcross10' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, f1, f2]
          using hcross12' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, f0, f2]
          using hcross02' j l)
        hedge hzero
    · have hn0 : n0 = 0 := by omega
      have hn1 : n1 = 2 := by omega
      have hn2 : n2 = 1 := by omega
      subst n0
      subst n1
      subst n2
      let q : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 3) ≃
          Option (Fin 1 ⊕ Fin 3 ⊕ Fin 2) :=
        (threeArmSwap01 (Fin 2) (Fin 1) (Fin 3)).trans
          (threeArmSwap12 (Fin 1) (Fin 2) (Fin 3))
      let e' : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 3) ≃ κ := q.trans e
      refine Or.inr (Or.inr (Or.inl ?_))
      exact cartan_typeE7_of_threeArmNumbering A G hdiag e'
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f2]
          using hcenter2' j)
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f0]
          using hcenter0' j)
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f1]
          using hcenter1' j)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2]
          using hpath2' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f1]
          using hpath1' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2, f0]
          using hcross20' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2, f1]
          using hcross21' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f0, f1]
          using hcross01' j l)
        hedge hzero
    · have hn0 : n0 = 1 := by omega
      have hn1 : n1 = 0 := by omega
      have hn2 : n2 = 2 := by omega
      subst n0
      subst n1
      subst n2
      refine Or.inr (Or.inr (Or.inl ?_))
      exact cartan_typeE7_of_threeArmNumbering A G hdiag e
        (by intro j; simpa [f0] using hcenter0' j)
        (by intro j; simpa [f1] using hcenter1' j)
        (by intro j; simpa [f2] using hcenter2' j)
        (by intro j l; simpa [f0] using hpath0' j l)
        (by intro j l; simpa [f2] using hpath2' j l)
        (by intro j l; simpa [f0, f1] using hcross01' j l)
        (by intro j l; simpa [f0, f2] using hcross02' j l)
        (by intro j l; simpa [f1, f2] using hcross12' j l)
        hedge hzero
    · have hn0 : n0 = 1 := by omega
      have hn1 : n1 = 2 := by omega
      have hn2 : n2 = 0 := by omega
      subst n0
      subst n1
      subst n2
      let q := threeArmSwap12 (Fin 2) (Fin 1) (Fin 3)
      let e' : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 3) ≃ κ := q.trans e
      refine Or.inr (Or.inr (Or.inl ?_))
      exact cartan_typeE7_of_threeArmNumbering A G hdiag e'
        (by intro j; simpa [e', q, threeArmSwap12, f0] using hcenter0' j)
        (by intro j; simpa [e', q, threeArmSwap12, f2] using hcenter2' j)
        (by intro j; simpa [e', q, threeArmSwap12, f1] using hcenter1' j)
        (by intro j l; simpa [e', q, threeArmSwap12, f0] using hpath0' j l)
        (by intro j l; simpa [e', q, threeArmSwap12, f1] using hpath1' j l)
        (by intro j l; simpa [e', q, threeArmSwap12, f0, f2]
          using hcross02' j l)
        (by intro j l; simpa [e', q, threeArmSwap12, f0, f1]
          using hcross01' j l)
        (by intro j l; simpa [e', q, threeArmSwap12, f2, f1]
          using hcross21' j l)
        hedge hzero
    · have hn0 : n0 = 2 := by omega
      have hn1 : n1 = 0 := by omega
      have hn2 : n2 = 1 := by omega
      subst n0
      subst n1
      subst n2
      let q : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 3) ≃
          Option (Fin 3 ⊕ Fin 1 ⊕ Fin 2) :=
        ((threeArmSwap01 (Fin 2) (Fin 1) (Fin 3)).trans
          (threeArmSwap12 (Fin 1) (Fin 2) (Fin 3))).trans
          (threeArmSwap01 (Fin 1) (Fin 3) (Fin 2))
      let e' : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 3) ≃ κ := q.trans e
      refine Or.inr (Or.inr (Or.inl ?_))
      exact cartan_typeE7_of_threeArmNumbering A G hdiag e'
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f2]
          using hcenter2' j)
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f1]
          using hcenter1' j)
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f0]
          using hcenter0' j)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2]
          using hpath2' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f0]
          using hpath0' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2, f1]
          using hcross21' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2, f0]
          using hcross20' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f1, f0]
          using hcross10' j l)
        hedge hzero
    · have hn0 : n0 = 2 := by omega
      have hn1 : n1 = 1 := by omega
      have hn2 : n2 = 0 := by omega
      subst n0
      subst n1
      subst n2
      let q : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 3) ≃
          Option (Fin 3 ⊕ Fin 2 ⊕ Fin 1) :=
        (threeArmSwap12 (Fin 2) (Fin 1) (Fin 3)).trans
          (threeArmSwap01 (Fin 2) (Fin 3) (Fin 1))
      let e' : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 3) ≃ κ := q.trans e
      refine Or.inr (Or.inr (Or.inl ?_))
      exact cartan_typeE7_of_threeArmNumbering A G hdiag e'
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f1]
          using hcenter1' j)
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f2]
          using hcenter2' j)
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f0]
          using hcenter0' j)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f1]
          using hpath1' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f0]
          using hpath0' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f1, f2]
          using hcross12' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f1, f0]
          using hcross10' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2, f0]
          using hcross20' j l)
        hedge hzero
  · rcases hE8cases with h | h | h | h | h | h
    · have hn0 : n0 = 0 := by omega
      have hn1 : n1 = 1 := by omega
      have hn2 : n2 = 3 := by omega
      subst n0
      subst n1
      subst n2
      let q := threeArmSwap01 (Fin 2) (Fin 1) (Fin 4)
      let e' : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 4) ≃ κ := q.trans e
      refine Or.inr (Or.inr (Or.inr ?_))
      exact cartan_typeE8_of_threeArmNumbering A G hdiag e'
        (by intro j; simpa [e', q, threeArmSwap01, f1] using hcenter1' j)
        (by intro j; simpa [e', q, threeArmSwap01, f0] using hcenter0' j)
        (by intro j; simpa [e', q, threeArmSwap01, f2] using hcenter2' j)
        (by intro j l; simpa [e', q, threeArmSwap01, f1] using hpath1' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, f2] using hpath2' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, f1, f0]
          using hcross10' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, f1, f2]
          using hcross12' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, f0, f2]
          using hcross02' j l)
        hedge hzero
    · have hn0 : n0 = 0 := by omega
      have hn1 : n1 = 3 := by omega
      have hn2 : n2 = 1 := by omega
      subst n0
      subst n1
      subst n2
      let q : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 4) ≃
          Option (Fin 1 ⊕ Fin 4 ⊕ Fin 2) :=
        (threeArmSwap01 (Fin 2) (Fin 1) (Fin 4)).trans
          (threeArmSwap12 (Fin 1) (Fin 2) (Fin 4))
      let e' : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 4) ≃ κ := q.trans e
      refine Or.inr (Or.inr (Or.inr ?_))
      exact cartan_typeE8_of_threeArmNumbering A G hdiag e'
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f2]
          using hcenter2' j)
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f0]
          using hcenter0' j)
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f1]
          using hcenter1' j)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2]
          using hpath2' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f1]
          using hpath1' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2, f0]
          using hcross20' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2, f1]
          using hcross21' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f0, f1]
          using hcross01' j l)
        hedge hzero
    · have hn0 : n0 = 1 := by omega
      have hn1 : n1 = 0 := by omega
      have hn2 : n2 = 3 := by omega
      subst n0
      subst n1
      subst n2
      refine Or.inr (Or.inr (Or.inr ?_))
      exact cartan_typeE8_of_threeArmNumbering A G hdiag e
        (by intro j; simpa [f0] using hcenter0' j)
        (by intro j; simpa [f1] using hcenter1' j)
        (by intro j; simpa [f2] using hcenter2' j)
        (by intro j l; simpa [f0] using hpath0' j l)
        (by intro j l; simpa [f2] using hpath2' j l)
        (by intro j l; simpa [f0, f1] using hcross01' j l)
        (by intro j l; simpa [f0, f2] using hcross02' j l)
        (by intro j l; simpa [f1, f2] using hcross12' j l)
        hedge hzero
    · have hn0 : n0 = 1 := by omega
      have hn1 : n1 = 3 := by omega
      have hn2 : n2 = 0 := by omega
      subst n0
      subst n1
      subst n2
      let q := threeArmSwap12 (Fin 2) (Fin 1) (Fin 4)
      let e' : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 4) ≃ κ := q.trans e
      refine Or.inr (Or.inr (Or.inr ?_))
      exact cartan_typeE8_of_threeArmNumbering A G hdiag e'
        (by intro j; simpa [e', q, threeArmSwap12, f0] using hcenter0' j)
        (by intro j; simpa [e', q, threeArmSwap12, f2] using hcenter2' j)
        (by intro j; simpa [e', q, threeArmSwap12, f1] using hcenter1' j)
        (by intro j l; simpa [e', q, threeArmSwap12, f0] using hpath0' j l)
        (by intro j l; simpa [e', q, threeArmSwap12, f1] using hpath1' j l)
        (by intro j l; simpa [e', q, threeArmSwap12, f0, f2]
          using hcross02' j l)
        (by intro j l; simpa [e', q, threeArmSwap12, f0, f1]
          using hcross01' j l)
        (by intro j l; simpa [e', q, threeArmSwap12, f2, f1]
          using hcross21' j l)
        hedge hzero
    · have hn0 : n0 = 3 := by omega
      have hn1 : n1 = 0 := by omega
      have hn2 : n2 = 1 := by omega
      subst n0
      subst n1
      subst n2
      let q : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 4) ≃
          Option (Fin 4 ⊕ Fin 1 ⊕ Fin 2) :=
        ((threeArmSwap01 (Fin 2) (Fin 1) (Fin 4)).trans
          (threeArmSwap12 (Fin 1) (Fin 2) (Fin 4))).trans
          (threeArmSwap01 (Fin 1) (Fin 4) (Fin 2))
      let e' : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 4) ≃ κ := q.trans e
      refine Or.inr (Or.inr (Or.inr ?_))
      exact cartan_typeE8_of_threeArmNumbering A G hdiag e'
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f2]
          using hcenter2' j)
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f1]
          using hcenter1' j)
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f0]
          using hcenter0' j)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2]
          using hpath2' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f0]
          using hpath0' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2, f1]
          using hcross21' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2, f0]
          using hcross20' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f1, f0]
          using hcross10' j l)
        hedge hzero
    · have hn0 : n0 = 3 := by omega
      have hn1 : n1 = 1 := by omega
      have hn2 : n2 = 0 := by omega
      subst n0
      subst n1
      subst n2
      let q : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 4) ≃
          Option (Fin 4 ⊕ Fin 2 ⊕ Fin 1) :=
        (threeArmSwap12 (Fin 2) (Fin 1) (Fin 4)).trans
          (threeArmSwap01 (Fin 2) (Fin 4) (Fin 1))
      let e' : Option (Fin 2 ⊕ Fin 1 ⊕ Fin 4) ≃ κ := q.trans e
      refine Or.inr (Or.inr (Or.inr ?_))
      exact cartan_typeE8_of_threeArmNumbering A G hdiag e'
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f1]
          using hcenter1' j)
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f2]
          using hcenter2' j)
        (by intro j; simpa [e', q, threeArmSwap01, threeArmSwap12, f0]
          using hcenter0' j)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f1]
          using hpath1' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f0]
          using hpath0' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f1, f2]
          using hcross12' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f1, f0]
          using hcross10' j l)
        (by intro j l; simpa [e', q, threeArmSwap01, threeArmSwap12, f2, f0]
          using hcross20' j l)
        hedge hzero

end Theory.AlgebraicGroup
