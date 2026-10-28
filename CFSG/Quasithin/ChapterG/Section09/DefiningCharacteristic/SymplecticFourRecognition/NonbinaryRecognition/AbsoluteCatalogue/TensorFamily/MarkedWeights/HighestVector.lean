module

public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.AbsoluteCatalogue.TensorFamily.MarkedWeights.Labels
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.NonbinaryRecognition.AbsoluteCatalogue.TensorFamily.MarkedWeights.Matrices

/-!
# Marked highest vectors of the symplectic tensor models

The column formulas give unipotent fixation and both simple-coroot characters.
For a negative simple root, a tuple with precisely one second coordinate detects
any factor of the corresponding parity. Thus fixation is equivalent to a zero
label, even when the torus alone cannot distinguish zero from q-1.

Sources: GLS3, 2.8.1(a), 2.8.4, 2.8.6(a), 2.8.10(d),
`refs/KGroup/GLS3/chapter2.tex`; Aschbacher--Smith, G.9.3,
printed pp.356--357 of `refs/quasithin.pdf`.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.MarkedWeights
open Theory.SpecificGroups.SymplecticFour
open Representation.OneCohomology.SymplecticFour

variable {F E : Type*} [Field F] [Finite F] [Algebra (ZMod 2) F] [Field E]
variable {n : ℕ} (e : F →+* E) (S : Finset (Fin (2*n)))

/-- The coordinate basis vector at the constant highest tuple, including the empty tensor. -/
def highestVector : (S → Coordinate) → E := by
  classical
  exact Pi.single (fun _ => .inl 0) 1

@[simp] theorem highestVector_apply (x : S → Coordinate) :
    highestVector (E := E) S x = if x = (fun _ => .inl 0) then 1 else 0 := by
  classical
  simp [highestVector, Pi.single_apply]

@[simp] theorem highestVector_top : highestVector (E := E) S (fun _ => .inl 0) = 1 := by
  simp

theorem highestVector_ne_zero : highestVector (E := E) S ≠ 0 := by
  intro h
  have hh := congrFun h (fun _ => .inl 0)
  simp at hh

/-- Acting on the marked vector selects the corresponding tensor-matrix column. -/
theorem tensorModel_highest_apply (g : Derived F) (x : S → Coordinate) :
    tensorModel e S g (highestVector S) x =
      ∏ j : S, e (((graphDerived F ^ (j.val : ℕ)) g).val.val (x j) (.inl 0)) := by
  classical
  change ((tensorMatrix e S g).mulVec (Pi.single (fun _ => .inl 0) 1)) x = _
  rw [Matrix.mulVec_single]
  simp [tensorMatrix, Matrix.col]

private theorem highest_eigen_of_columns (g : Derived F) (c : S → E)
    (hc : ∀ (j : S) (i : Coordinate),
      e (((graphDerived F ^ (j.val : ℕ)) g).val.val i (.inl 0)) =
        if i = .inl 0 then c j else 0) :
    tensorModel e S g (highestVector S) = (∏ j, c j) • highestVector S := by
  classical
  ext x
  rw [tensorModel_highest_apply]
  simp_rw [hc]
  rw [Fintype.prod_ite_zero]
  simp only [Pi.smul_apply, smul_eq_mul, highestVector_apply, ← funext_iff]
  split_ifs <;> simp

/-- Every marked highest tensor is fixed by the actual standard unipotent group. -/
theorem highestVector_fixed (g : Derived F) (hg : g ∈ U) :
    tensorModel e S g (highestVector S) = highestVector S := by
  have h := highest_eigen_of_columns e S g (fun _ => 1) (by
    intro j i
    rw [graph_unipotent_column g hg]
    split_ifs <;> simp)
  simpa using h

omit [Finite F] [Algebra (ZMod 2) F] in
private theorem prod_weight (s : Fˣ) (p : ℕ) :
    (∏ j : S, e (s:F) ^ (if j.val.val%2=p then 2^(j.val.val/2) else 0)) =
      e (s:F) ^ label S p := by
  classical
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [label, Finset.sum_filter, ← Finset.sum_attach S]
  rfl

/-- The short simple coroot reads the even binary label. -/
theorem corootA_highest (hq : 2 < Nat.card F) (s : Fˣ) :
    tensorModel e S (corootA hq s) (highestVector S) = e (s:F) ^ A S • highestVector S := by
  have h := highest_eigen_of_columns e S (corootA hq s)
    (fun j => e (s:F) ^ (if j.val.val%2=0 then 2^(j.val.val/2) else 0)) (by
      intro j i
      rw [corootA_column]
      split_ifs <;> simp [map_pow])
  rw [prod_weight] at h
  exact h

/-- The long simple coroot reads the odd binary label. -/
theorem corootB_highest (hq : 2 < Nat.card F) (s : Fˣ) :
    tensorModel e S (corootB hq s) (highestVector S) = e (s:F) ^ B S • highestVector S := by
  have h := highest_eigen_of_columns e S (corootB hq s)
    (fun j => e (s:F) ^ (if j.val.val%2=1 then 2^(j.val.val/2) else 0)) (by
      intro j i
      rw [corootB_column]
      split_ifs <;> simp [map_pow])
  rw [prod_weight] at h
  exact h

/-- A single negative-root test detects the zero label, including the q-1 extreme. -/
theorem negativeRoot_highest_iff (hq : 2 < Nat.card F) (p : Fin 2) :
    tensorModel e S (negativeRoot hq p) (highestVector S) = highestVector S ↔
      label S p.val = 0 := by
  classical
  rw [label_eq_zero_iff]
  constructor
  · intro h j hj hp
    let k : S := ⟨j, hj⟩
    let x : S → Coordinate := Function.update (fun _ => .inl 0) k (.inl 1)
    have hx : x ≠ (fun _ => .inl 0) := by
      intro hh
      have := congrFun hh k
      simp [x] at this
    have hm : tensorModel e S (negativeRoot hq p) (highestVector S) x = 1 := by
      rw [tensorModel_highest_apply]
      apply Finset.prod_eq_one
      intro l _
      rw [negativeRoot_column]
      by_cases hl : l = k
      · subst l
        simp [x, k, hp]
      · simp [x, Function.update_of_ne hl]
    have hz := congrFun h x
    rw [hm, highestVector_apply, if_neg hx] at hz
    exact one_ne_zero hz
  · intro h
    have hh := highest_eigen_of_columns e S (negativeRoot hq p) (fun _ => 1) (by
      intro j i
      rw [negativeRoot_column]
      simp only [h j.val j.property, false_and, or_false]
      split_ifs <;> simp)
    simpa using hh

/-- Root 7 is the negative short simple root. -/
theorem root7_highest_iff (hq : 2 < Nat.card F) :
    tensorModel e S (lift hq (rootElement 7 1)) (highestVector S) = highestVector S ↔
      A S = 0 := by
  simpa [negativeRoot] using negativeRoot_highest_iff e S hq 0

/-- Root 3 is the negative long simple root. -/
theorem root3_highest_iff (hq : 2 < Nat.card F) :
    tensorModel e S (lift hq (rootElement 3 1)) (highestVector S) = highestVector S ↔
      B S = 0 := by
  simpa [negativeRoot] using negativeRoot_highest_iff e S hq 1

end CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.SymplecticFourRecognition.Nonbinary.MarkedWeights
