module

public import Theory.Representation.CyclicDefect.RealLine
public import Theory.Character.InnerProductByClasses

/-!
# Regular scalar products in the centralizer convention

Lifted characteristic-polynomial eigenvalues are invariant under conjugation.
Partitioning the regular group sum into conjugacy classes converts its weights
to reciprocal centralizer orders. This identifies the literal coefficient used
by the eleven-block consumer with the usual projective/Brauer pairing.

This change of summation convention does not assert reciprocity or integrality.
Those require actual projective modules (Feit, Chapter I, §17).
-/

public section
noncomputable section
open scoped BigOperators

namespace Representation.CyclicRootLift

variable {K : Type*} [Field K] {m : ℕ} (L : CyclicRootLift K m)
    {G V : Type*} [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Conjugate group elements have the same lifted eigenvalues with multiplicity. -/
theorem value_conj (ρ : Representation K G V) (g a : G) :
    L.value ρ (a * g * a⁻¹) = L.value ρ g := by
  let e : V ≃ₗ[K] V := LinearEquiv.ofLinearMap (ρ a) (ρ a⁻¹)
    (by change ρ a * ρ a⁻¹ = 1; rw [← map_mul, mul_inv_cancel, map_one])
    (by change ρ a⁻¹ * ρ a = 1; rw [← map_mul, inv_mul_cancel, map_one])
  have he : ρ (a * g * a⁻¹) = e.conj (ρ g) := by
    ext v
    simp [e, map_mul, LinearEquiv.conj_apply]
  simp only [value, he, LinearEquiv.charpoly_conj]

end Representation.CyclicRootLift

namespace Representation.CyclicDefect

/-- The regular pairing with arbitrary class functions, computed by classes. -/
theorem regularPairing_eq_sum_div_centralizer
    {G : Type*} [Group G] [Finite G] {I : Type*} [Fintype I]
    (r : I → G) (hr : Function.Bijective (fun i => ConjClasses.mk (r i)))
    (p : ℕ) (φ ψ : G → ℂ) (hφ : IsClassFunction φ) (hψ : IsClassFunction ψ) :
    regularPairing p φ ψ = ∑ i, if ¬ p ∣ orderOf (r i) then
      φ (r i) * star (ψ (r i)) /
        (Nat.card (Subgroup.centralizer ({r i} : Set G)) : ℂ) else 0 := by
  classical
  let Φ : ConjClassFunction G := conjClassFunctionOfInvariant
    (fun g => if ¬ p ∣ orderOf g then φ g else 0) (by
      intro g a
      rw [show orderOf (a * g * a⁻¹) = orderOf g from (MulAut.conj a).orderOf_eq g,
        hφ g a])
  let Ψ : ConjClassFunction G := conjClassFunctionOfInvariant ψ hψ
  have h := classFunctionInner_eq_sum_div_centralizer r hr Φ Ψ
  change regularPairing p φ ψ = _
  have he : regularPairing p φ ψ = classFunctionInner Φ Ψ := by
    unfold regularPairing classFunctionInner
    congr 1
    apply Finset.sum_congr rfl
    intro g _
    change (if ¬ p ∣ orderOf g then φ g * star (ψ g) else 0) =
      (if ¬ p ∣ orderOf g then φ g else 0) * star (ψ g)
    split <;> simp_all
  rw [he, h]
  apply Finset.sum_congr rfl
  intro i _
  change (if ¬ p ∣ orderOf (r i) then φ (r i) else 0) * star (ψ (r i)) / _ = _
  split <;> simp_all

end Representation.CyclicDefect
