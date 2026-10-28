module

public import Theory.SpecificGroups.SL2.BinaryTetrahedralQuotient
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

/-!
# An embedding of `SL₂(3)` into `SL₂(5)`

The binary-tetrahedral presentation of `SL₂(3)` is sent to explicit matrices
in `SL₂(5)`.  The matrices `I` and `J` satisfy the quaternion relations, while
`S` has order three and cyclically permutes the three noncentral quaternion
generators.  Finite verification establishes the semidirect-product map and
its injectivity; composing with the existing binary-tetrahedral equivalence
therefore gives the required embedding.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace GLS3.Chapter5.SchurPresentation

public abbrev SL25 := Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)

private instance binaryFintype : Fintype BinaryTetrahedral :=
  Fintype.ofEquiv (QuaternionGroup 2 × Multiplicative (ZMod 3))
    SemidirectProduct.equivProd.symm

private def sl25I : SL25 := ⟨![![0, 1], ![4, 0]], by decide⟩
private def sl25J : SL25 := ⟨![![0, 2], ![2, 0]], by decide⟩
private def sl25S : SL25 := ⟨![![1, 2], ![1, 3]], by decide⟩

private def q8ToSL25 : QuaternionGroup 2 →* SL25 where
  toFun
    | .a i => sl25I ^ i.val
    | .xa i => sl25J * sl25I ^ i.val
  map_one' := by decide
  map_mul' := by
    intro x y
    rcases x with i | i <;> rcases y with j | j <;>
      fin_cases i <;> fin_cases j <;> decide

private def c3ToSL25 : Multiplicative (ZMod 3) →* SL25 where
  toFun k := sl25S ^ (Multiplicative.toAdd k).val
  map_one' := by
    change sl25S ^ 0 = 1
    simp
  map_mul' := by
    intro x y
    change ZMod 3 at x y
    fin_cases x <;> fin_cases y <;> decide

private theorem sl25_action_compat (k : Multiplicative (ZMod 3))
    (x : QuaternionGroup 2) :
    q8ToSL25 (q8C3Action k x) =
      c3ToSL25 k * q8ToSL25 x * (c3ToSL25 k)⁻¹ := by
  change ZMod 3 at k
  fin_cases k <;> rcases x with i | i <;> fin_cases i <;> decide

private def binaryTetrahedralToSL25 : BinaryTetrahedral →* SL25 :=
  SemidirectProduct.lift q8ToSL25 c3ToSL25 (by
    intro k
    apply MonoidHom.ext
    intro x
    exact sl25_action_compat k x)

private theorem binaryTetrahedralToSL25_injective :
    Function.Injective binaryTetrahedralToSL25 := by
  intro ⟨x, k⟩ ⟨y, l⟩ h
  rw [← SemidirectProduct.inl_left_mul_inr_right ⟨x, k⟩,
    ← SemidirectProduct.inl_left_mul_inr_right ⟨y, l⟩] at h
  simp [binaryTetrahedralToSL25] at h
  rcases x with i | i <;> rcases y with j | j <;>
    change ZMod 3 at k l
  all_goals fin_cases k <;> fin_cases l <;>
    fin_cases i <;> fin_cases j <;>
    simp [q8ToSL25, c3ToSL25] at h ⊢ <;>
    first | rfl | (exfalso; revert h; decide)

/-- The binary-tetrahedral model of `SL₂(3)` embeds in `SL₂(5)`. -/
public noncomputable def binaryTetrahedralIntoSL25 :
    BinaryTetrahedral →* SL25 := binaryTetrahedralToSL25

public theorem binaryTetrahedralIntoSL25_injective :
    Function.Injective binaryTetrahedralIntoSL25 := binaryTetrahedralToSL25_injective

/-- The natural injective homomorphism `SL₂(3) → SL₂(5)`. -/
public noncomputable def sl23IntoSL25 : SL23 →* SL25 :=
  binaryTetrahedralIntoSL25.comp binaryTetrahedralEquivSL.symm.toMonoidHom

public theorem sl23IntoSL25_injective : Function.Injective sl23IntoSL25 := by
  intro x y h
  apply binaryTetrahedralEquivSL.symm.injective
  apply binaryTetrahedralIntoSL25_injective
  exact h

end GLS3.Chapter5.SchurPresentation
