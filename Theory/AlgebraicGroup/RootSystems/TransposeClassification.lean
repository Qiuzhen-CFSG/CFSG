module

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.theorem_1_10_3_d

public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.RootSystemType

/-!
Production helper module for `ag-irreducible-transpose-cartan-classification`. The statement is shared
with its Aux interface; this module supplies the checked proof. The proof
applies finite Cartan classification to `P`; symmetric types use the transpose
hypothesis directly, F4 and G2 use finite reversal permutations, and the B/C
cases construct the opposite equal-rank Dynkin witness from the transpose.
-/

set_option warningAsError false

universe u

namespace Theory.AlgebraicGroup

open StandardRootSystem

public theorem irreducible_base_transpose_comparison
    {ι ι' E E' F F' : Type u} [Finite ι] [Finite ι']
    [AddCommGroup E] [Module ℝ E] [AddCommGroup E'] [Module ℝ E']
    [AddCommGroup F] [Module ℝ F] [AddCommGroup F'] [Module ℝ F']
    (P : RootPairing ι ℝ E E') [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]
    (Q : RootPairing ι' ℝ F F') [Q.IsRootSystem]
    [Q.IsCrystallographic] [Q.IsReduced] [Q.IsIrreducible]
    (baseP : P.Base) (baseQ : Q.Base)
    (f : baseP.support ≃ baseQ.support)
    (htranspose : ∀ i j, baseQ.cartanMatrix (f i) (f j) =
      baseP.cartanMatrix j i) :
    (∃ g : baseP.support ≃ baseQ.support,
      ∀ i j, baseQ.cartanMatrix (g i) (g j) =
        baseP.cartanMatrix i j) ∨
    ∃ m : ℕ,
      ((HasDynkinType P ⟨.B, m⟩ ∧ HasDynkinType Q ⟨.C, m⟩) ∨
        (HasDynkinType P ⟨.C, m⟩ ∧ HasDynkinType Q ⟨.B, m⟩)) := by
  have hAentry : ∀ (m : ℕ) (i j : Fin m),
      typeACartanMatrix m i j = dynkinCartanEntry ⟨.A, m⟩ i j := by
    intro m i j
    by_cases hij : i = j
    · subst j
      simp [typeACartanMatrix, dynkinCartanEntry]
    · simp only [typeACartanMatrix, dynkinCartanEntry, hij, ↓reduceIte]
      by_cases hforward : i.val + 1 = j.val
      · have hforward' : i.succ = j.castSucc := by
          apply Fin.ext
          simp
          omega
        have hreverse : ¬j.val + 1 = i.val := by omega
        simp [hforward, hreverse, hforward']
      · by_cases hreverse : j.val + 1 = i.val
        · have hreverse' : j.succ = i.castSucc := by
            apply Fin.ext
            simp
            omega
          have hforward' : ¬i.val + 1 = j.val := by omega
          simp [hforward, hreverse, hreverse']
        · have hforward' : ¬i.succ = j.castSucc := by
            intro h
            have hh := congrArg Fin.val h
            simp at hh
            omega
          have hreverse' : ¬j.succ = i.castSucc := by
            intro h
            have hh := congrArg Fin.val h
            simp at hh
            omega
          simp [hforward, hreverse, hforward', hreverse']
  have hBentry : ∀ (m : ℕ) (i j : Fin (m + 2)),
      typeBCartanMatrix m i j = dynkinCartanEntry ⟨.B, m + 2⟩ i j := by
    intro m i j
    by_cases hij : i = j
    · subst j
      simp [typeBCartanMatrix, dynkinCartanEntry]
    · simp only [typeBCartanMatrix, dynkinCartanEntry, hij, ↓reduceIte]
      by_cases hforward : i.val + 1 = j.val
      · have hreverse : ¬j.val + 1 = i.val := by omega
        have hjlast : j = Fin.last (m + 1) ↔ j.val = m + 1 := by
          simp [Fin.ext_iff]
        simp [hforward, hreverse, hjlast]
      · by_cases hreverse : j.val + 1 = i.val
        · have hjlast : j = Fin.last (m + 1) ↔ j.val = m + 1 := by
            simp [Fin.ext_iff]
          simp [hforward, hreverse, hjlast]
        · have hjlast : j = Fin.last (m + 1) ↔ j.val = m + 1 := by
            simp [Fin.ext_iff]
          simp [hforward, hreverse, hjlast]
  have hCentry : ∀ (m : ℕ) (i j : Fin (m + 1)),
      typeCCartanMatrix m i j = dynkinCartanEntry ⟨.C, m + 1⟩ i j := by
    intro m i j
    by_cases hij : i = j
    · subst j
      simp [typeCCartanMatrix, dynkinCartanEntry]
    · simp only [typeCCartanMatrix, dynkinCartanEntry, hij, ↓reduceIte]
      by_cases hforward : i.val + 1 = j.val
      · have hreverse : ¬j.val + 1 = i.val := by omega
        simp [hforward, hreverse]
      · by_cases hreverse : j.val + 1 = i.val
        · have hilast : i = Fin.last m ↔ i.val = m := by
            simp [Fin.ext_iff]
          simp [hforward, hreverse, hilast]
        · have hilast : i = Fin.last m ↔ i.val = m := by
            simp [Fin.ext_iff]
          simp [hforward, hreverse, hilast]
  have hBCtranspose : ∀ (m : ℕ) (i j : Fin (m + 2)),
      typeCCartanMatrix (m + 1) i j = typeBCartanMatrix m j i := by
    intro m i j
    by_cases hij : i = j
    · subst j
      simp [typeCCartanMatrix, typeBCartanMatrix]
    · simp only [typeCCartanMatrix, typeBCartanMatrix, hij, eq_comm, ↓reduceIte]
      by_cases hforward : i.val + 1 = j.val
      · have hreverse : ¬j.val + 1 = i.val := by omega
        have hilast : i ≠ Fin.last (m + 1) := by
          intro hi
          have hi' := congrArg Fin.val hi
          simp only [Fin.val_last] at hi'
          omega
        simp [hforward, hreverse, hilast]
      · by_cases hreverse : j.val + 1 = i.val
        · have hjlast : j ≠ Fin.last (m + 1) := by
            intro hj
            have hj' := congrArg Fin.val hj
            simp only [Fin.val_last] at hj'
            omega
          simp [hforward, hreverse, hjlast] <;> omega
        · have hforward' : ¬j.val = i.val + 1 := by omega
          have hreverse' : ¬i.val = j.val + 1 := by omega
          simp [hforward', hreverse']
  have hDsymm : ∀ (m : ℕ) (i j : Fin (m + 2)),
      typeDCartanMatrix m i j = typeDCartanMatrix m j i := by
    intro m i j
    simp only [typeDCartanMatrix]
    split <;> rename_i h1
    all_goals try split <;> try rename_i h2
    all_goals try split <;> try rename_i h3
    all_goals try split <;> try rename_i h4
    all_goals try split <;> try rename_i h5
    all_goals simp_all [eq_comm] <;> omega
  have hF4transpose : ∀ (i j : Fin 4),
      typeF4CartanMatrix (Fin.rev i) (Fin.rev j) = typeF4CartanMatrix j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hG2transpose : ∀ (i j : Fin 2),
      typeG2CartanMatrix (Fin.rev i) (Fin.rev j) = typeG2CartanMatrix j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hE6symm : ∀ (i j : Fin 6),
      typeE6CartanMatrix i j = typeE6CartanMatrix j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hE7symm : ∀ (i j : Fin 7),
      typeE7CartanMatrix i j = typeE7CartanMatrix j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hE8symm : ∀ (i j : Fin 8),
      typeE8CartanMatrix i j = typeE8CartanMatrix j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hAsymm : ∀ (m : ℕ) (i j : Fin m),
      typeACartanMatrix m i j = typeACartanMatrix m j i := by
    intro m i j
    rw [hAentry, hAentry]
    exact dynkinCartanEntry_A_symmetric m i j
  have hAclass := rootSystem_finiteCartanClassification baseP
  rcases hAclass with hA | hB | hC | hD | hE6 | hE7 | hE8 | hF4 | hG2
  · rcases hA with ⟨m, e, he⟩
    left
    refine ⟨f, ?_⟩
    intro i j
    calc
      baseQ.cartanMatrix (f i) (f j) = baseP.cartanMatrix j i := htranspose i j
      _ = typeACartanMatrix m (e.symm j) (e.symm i) := by
        simpa only [Equiv.apply_symm_apply] using
          he (e.symm j) (e.symm i)
      _ = typeACartanMatrix m (e.symm i) (e.symm j) := hAsymm m _ _
      _ = baseP.cartanMatrix i j := by
        simpa only [Equiv.apply_symm_apply] using
          (he (e.symm i) (e.symm j)).symm
  · rcases hB with ⟨m, e, he⟩
    right
    refine ⟨m + 2, Or.inl ⟨?_, ?_⟩⟩
    · refine ⟨baseP, e.symm, ?_⟩
      intro i j
      change baseP.cartanMatrix i j = _
      calc
        _ = typeBCartanMatrix m (e.symm i) (e.symm j) := by
          simpa only [Equiv.apply_symm_apply] using he (e.symm i) (e.symm j)
        _ = dynkinCartanEntry ⟨.B, m + 2⟩ (e.symm i) (e.symm j) :=
          hBentry m _ _
    · let qnum : baseQ.support ≃ Fin (m + 2) := f.symm.trans e.symm
      refine ⟨baseQ, qnum, ?_⟩
      intro x y
      change baseQ.cartanMatrix x y = dynkinCartanEntry ⟨.C, m + 2⟩
        (e.symm (f.symm x)) (e.symm (f.symm y))
      calc
        _ = baseP.cartanMatrix (f.symm y) (f.symm x) := by
          simpa only [Equiv.apply_symm_apply] using
            htranspose (f.symm x) (f.symm y)
        _ = typeBCartanMatrix m (e.symm (f.symm y)) (e.symm (f.symm x)) := by
          simpa only [Equiv.apply_symm_apply] using
            he (e.symm (f.symm y)) (e.symm (f.symm x))
        _ = typeCCartanMatrix (m + 1) (e.symm (f.symm x))
            (e.symm (f.symm y)) := (hBCtranspose m _ _).symm
        _ = dynkinCartanEntry ⟨.C, m + 2⟩ (e.symm (f.symm x))
            (e.symm (f.symm y)) := by
          simpa only [Nat.add_assoc] using
            hCentry (m + 1) (e.symm (f.symm x)) (e.symm (f.symm y))
  · rcases hC with ⟨m, e, he⟩
    cases m with
    | zero =>
        left
        refine ⟨f, ?_⟩
        intro i j
        have hij : i = j := by
          apply e.symm.injective
          exact (Fin.eq_zero _).trans (Fin.eq_zero _).symm
        subst j
        exact htranspose i i
    | succ m =>
        right
        refine ⟨m + 2, Or.inr ⟨?_, ?_⟩⟩
        · refine ⟨baseP, e.symm, ?_⟩
          intro i j
          change baseP.cartanMatrix i j = _
          calc
            _ = typeCCartanMatrix (m + 1) (e.symm i) (e.symm j) := by
              simpa only [Equiv.apply_symm_apply] using he (e.symm i) (e.symm j)
            _ = dynkinCartanEntry ⟨.C, m + 2⟩ (e.symm i) (e.symm j) := by
              simpa only [Nat.add_assoc] using hCentry (m + 1) (e.symm i) (e.symm j)
        · let qnum : baseQ.support ≃ Fin (m + 2) := f.symm.trans e.symm
          refine ⟨baseQ, qnum, ?_⟩
          intro x y
          change baseQ.cartanMatrix x y = dynkinCartanEntry ⟨.B, m + 2⟩
            (e.symm (f.symm x)) (e.symm (f.symm y))
          calc
            _ = baseP.cartanMatrix (f.symm y) (f.symm x) := by
              simpa only [Equiv.apply_symm_apply] using
                htranspose (f.symm x) (f.symm y)
            _ = typeCCartanMatrix (m + 1) (e.symm (f.symm y))
                (e.symm (f.symm x)) := by
              simpa only [Equiv.apply_symm_apply] using
                he (e.symm (f.symm y)) (e.symm (f.symm x))
            _ = typeBCartanMatrix m (e.symm (f.symm x))
                (e.symm (f.symm y)) := hBCtranspose m _ _
            _ = dynkinCartanEntry ⟨.B, m + 2⟩ (e.symm (f.symm x))
                (e.symm (f.symm y)) := hBentry m _ _
  · rcases hD with ⟨m, e, he⟩
    left
    refine ⟨f, ?_⟩
    intro i j
    calc
      baseQ.cartanMatrix (f i) (f j) = baseP.cartanMatrix j i := htranspose i j
      _ = typeDCartanMatrix m (e.symm j) (e.symm i) := by
        simpa only [Equiv.apply_symm_apply] using
          he (e.symm j) (e.symm i)
      _ = typeDCartanMatrix m (e.symm i) (e.symm j) := hDsymm m _ _
      _ = baseP.cartanMatrix i j := by
        simpa only [Equiv.apply_symm_apply] using
          (he (e.symm i) (e.symm j)).symm
  · rcases hE6 with ⟨e, he⟩
    left
    refine ⟨f, ?_⟩
    intro i j
    calc
      baseQ.cartanMatrix (f i) (f j) = baseP.cartanMatrix j i := htranspose i j
      _ = typeE6CartanMatrix (e.symm j) (e.symm i) := by
        simpa only [Equiv.apply_symm_apply] using
          he (e.symm j) (e.symm i)
      _ = typeE6CartanMatrix (e.symm i) (e.symm j) := hE6symm _ _
      _ = baseP.cartanMatrix i j := by
        simpa only [Equiv.apply_symm_apply] using
          (he (e.symm i) (e.symm j)).symm
  · rcases hE7 with ⟨e, he⟩
    left
    refine ⟨f, ?_⟩
    intro i j
    calc
      baseQ.cartanMatrix (f i) (f j) = baseP.cartanMatrix j i := htranspose i j
      _ = typeE7CartanMatrix (e.symm j) (e.symm i) := by
        simpa only [Equiv.apply_symm_apply] using
          he (e.symm j) (e.symm i)
      _ = typeE7CartanMatrix (e.symm i) (e.symm j) := hE7symm _ _
      _ = baseP.cartanMatrix i j := by
        simpa only [Equiv.apply_symm_apply] using
          (he (e.symm i) (e.symm j)).symm
  · rcases hE8 with ⟨e, he⟩
    left
    refine ⟨f, ?_⟩
    intro i j
    calc
      baseQ.cartanMatrix (f i) (f j) = baseP.cartanMatrix j i := htranspose i j
      _ = typeE8CartanMatrix (e.symm j) (e.symm i) := by
        simpa only [Equiv.apply_symm_apply] using
          he (e.symm j) (e.symm i)
      _ = typeE8CartanMatrix (e.symm i) (e.symm j) := hE8symm _ _
      _ = baseP.cartanMatrix i j := by
        simpa only [Equiv.apply_symm_apply] using
          (he (e.symm i) (e.symm j)).symm
  · rcases hF4 with ⟨e, he⟩
    let s : baseP.support ≃ baseP.support :=
      (e.symm.trans (Fin.revPerm : Equiv.Perm (Fin 4))).trans e
    left
    refine ⟨s.trans f, ?_⟩
    intro i j
    have hsi : s i = e (Fin.rev (e.symm i)) := by rfl
    have hsj : s j = e (Fin.rev (e.symm j)) := by rfl
    calc
      baseQ.cartanMatrix ((s.trans f) i) ((s.trans f) j) =
          baseP.cartanMatrix (s j) (s i) := htranspose (s i) (s j)
      _ = typeF4CartanMatrix (Fin.rev (e.symm j)) (Fin.rev (e.symm i)) := by
        rw [hsi, hsj]
        exact he (Fin.rev (e.symm j)) (Fin.rev (e.symm i))
      _ = typeF4CartanMatrix (e.symm i) (e.symm j) := hF4transpose _ _
      _ = baseP.cartanMatrix i j := by
        simpa only [Equiv.apply_symm_apply] using
          (he (e.symm i) (e.symm j)).symm
  · rcases hG2 with ⟨e, he⟩
    let s : baseP.support ≃ baseP.support :=
      (e.symm.trans (Fin.revPerm : Equiv.Perm (Fin 2))).trans e
    left
    refine ⟨s.trans f, ?_⟩
    intro i j
    have hsi : s i = e (Fin.rev (e.symm i)) := by rfl
    have hsj : s j = e (Fin.rev (e.symm j)) := by rfl
    calc
      baseQ.cartanMatrix ((s.trans f) i) ((s.trans f) j) =
          baseP.cartanMatrix (s j) (s i) := htranspose (s i) (s j)
      _ = typeG2CartanMatrix (Fin.rev (e.symm j)) (Fin.rev (e.symm i)) := by
        rw [hsi, hsj]
        exact he (Fin.rev (e.symm j)) (Fin.rev (e.symm i))
      _ = typeG2CartanMatrix (e.symm i) (e.symm j) := hG2transpose _ _
      _ = baseP.cartanMatrix i j := by
        simpa only [Equiv.apply_symm_apply] using
          (he (e.symm i) (e.symm j)).symm

end Theory.AlgebraicGroup
