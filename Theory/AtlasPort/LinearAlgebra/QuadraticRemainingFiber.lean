module

/-
Copyright (c) 2026 Gerald Höhn and the ATLAS contributors. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Source: Atlas/LinearGroups/Orthogonal/SingularCount.lean, revision
8eabb35afe2b5e45bf913a2d05c53e558d2e2917; see LICENSES/ATLAS-CITATION.cff.
Changes: CFSG import paths and Lean 4.33 public module boundaries.
-/

public import Theory.AtlasPort.LinearAlgebra.DotProductFiber

/-! The fibre of `x · y + z² = 0` has qⁿ elements: the zero functional forces z = 0, while a nonzero functional has qⁿ⁻¹ solutions for each z. Valid in every characteristic. -/

@[expose] public section
noncomputable section
namespace Atlas.Orthogonal
variable {n : ℕ} {F : Type*} [Field F]

abbrev BRemaining (x : Fin n → F) :=
  {p : (Fin n → F) × F // Atlas.DotProduct.functional x p.1 + p.2^2=0}

def remainingBZeroEquiv : BRemaining (0 : Fin n → F) ≃ (Fin n → F) where
  toFun p := p.val.1
  invFun y := ⟨(y,0),by simp⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    ·
      have hz : p.val.2^2=0 := by simpa using p.prop
      exact ((pow_eq_zero_iff (by decide : (2:ℕ)≠0)).mp hz).symm
  right_inv _ := rfl

def remainingBEquiv (x : Fin n → F) : BRemaining x ≃
    Σ z : F, {y : Fin n → F // Atlas.DotProduct.functional x y = -z^2} where
  toFun p := ⟨p.val.2,⟨p.val.1,eq_neg_of_add_eq_zero_left p.prop⟩⟩
  invFun p := ⟨(p.2.val,p.1),by rw [p.2.prop]; ring⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_remainingB [Finite F] (x : Fin n → F) :
    Nat.card (BRemaining x) = Nat.card F ^ n := by
  classical
  let := Fintype.ofFinite F
  by_cases hx : x=0
  · subst x
    rw [Nat.card_congr remainingBZeroEquiv,Nat.card_fun,Nat.card_fin]
  · have hn : 0<n := by
      by_contra hn
      have hn : n=0 := by omega
      subst n
      exact hx (Subsingleton.elim _ _)
    rw [Nat.card_congr (remainingBEquiv x),Nat.card_sigma]
    simp_rw [Atlas.DotProduct.card_fiber x hx]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,← Nat.card_eq_fintype_card]
    simp only [Nat.cast_id]
    rw [mul_comm,← pow_succ]
    congr 1
    omega

end Atlas.Orthogonal
