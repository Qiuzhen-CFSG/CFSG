module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Data.ZMod.Basic

/-!
# The binary special linear and projective special linear groups

The center consists of scalar matrices whose scalar squares to one. Over
`ZMod 2` that scalar is one. Thus the actual central quotient map is a
multiplicative equivalence. This identifies the matrix model used for natural
modules with the source notation `L₂(2)` in Aschbacher–Smith B.1.8(2).

The characteristic-two center calculation is also available in the larger
campaign module `BenderSuzuki.Converse.PSL2`; this specialization supplies a
narrow, downward-only interface for representation-theoretic consumers.
-/

public section

namespace Matrix.SpecialLinearGroup

/-- The only central binary determinant-one matrix of degree two is the identity. -/
theorem sl2_two_center_eq_bot :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = ⊥ := by
  apply le_bot_iff.mp
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have hr1 : r = 1 := by
    have htest : ∀ x : ZMod 2, x ^ 2 = 1 → x = 1 := by decide +kernel
    exact htest r (by simpa only [Fintype.card_fin] using hr)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

/-- The canonical central quotient identifies SL₂(2) with PSL₂(2). -/
@[expose] noncomputable def sl2TwoEquivPSL2Two :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 2) :=
  MulEquiv.ofBijective (QuotientGroup.mk' _) ⟨
    (MonoidHom.ker_eq_bot_iff _).mp (by
      rw [QuotientGroup.ker_mk', sl2_two_center_eq_bot]),
    QuotientGroup.mk'_surjective _⟩

/-- This identification is the actual quotient map on representatives. -/
theorem sl2TwoEquivPSL2Two_apply (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) :
    sl2TwoEquivPSL2Two g = QuotientGroup.mk g := rfl
end Matrix.SpecialLinearGroup
