module
public import Theory.Representation.HermitianTensorThree.UnipotentRadicals

/-!
# Quadratic identities on large binary Hermitian subspaces

An inner Hermitian operator is linear over the fixed field. A proper kernel
has fixed-field dimension at most eight, hence binary dimension at most 8n.
Consequently a quadratic identity valid on a larger binary subspace holds
on the entire module. This supports the reverse-action argument for the
weak-closure estimate without a nonquadratic-hyperplane assertion.

Source: the Hermitian realization in Aschbacher--Smith H.4.2,
printed pp.380--381 (refs/quasithin.pdf).
-/

open Subgroup Representation Representation.BinaryOffender
open Representation.HermitianTensorThree
open Matrix.PSL3Even.UnipotentGeometry
namespace Representation.HermitianTensorThree.QuadraticSubspaces
public noncomputable section
variable (n : ℕ) [NeZero n]

private theorem linearMap_eq_zero_of_large_kernel
    (f : Space n →ₗ[F n] Space n) (W : Submodule (ZMod 2) (Space n))
    (hW : 8*n < Module.finrank (ZMod 2) W) (hf : ∀ X ∈ W, f X = 0) : f = 0 := by
  by_contra hn
  have hk : LinearMap.ker f ≠ ⊤ := fun h => hn (LinearMap.ker_eq_top.mp h)
  have hd := Submodule.finrank_lt hk
  rw [finrank_space] at hd
  let j : W → LinearMap.ker f := fun X => ⟨X.val,hf X.val X.property⟩
  have hj : Function.Injective j := fun X Y h => Subtype.ext (congrArg (fun Z : LinearMap.ker f => Z.val) h)
  have hc := Nat.card_le_card_of_injective j hj
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
    Module.natCard_eq_pow_finrank (K := F n),card_F,← pow_mul] at hc
  have he := (pow_le_pow_iff_right₀ Nat.one_lt_two).mp hc
  have hm := Nat.mul_le_mul_left n (show Module.finrank (F n) (LinearMap.ker f) ≤ 8 by omega)
  omega

/-- Quadraticity on more than 8n binary dimensions determines the quadratic
identity on the entire nine-dimensional fixed-field Hermitian module. -/
theorem quadratic_of_large_subspace
    (A : Subgroup (Space n ≃ₗ[ZMod 2] Space n)) (hA : A ≤ binaryImage n)
    (W : Submodule (ZMod 2) (Space n)) (hW : 8*n < Module.finrank (ZMod 2) W)
    (hq : ∀ a ∈ A, ∀ b ∈ A, ∀ X ∈ W, a (b X - X) = b X - X) :
    IsQuadratic (UnipotentRadicals.ambientAction n) A := by
  intro a ha b hb X
  obtain ⟨a₀,ha₀⟩ := hA ha
  obtain ⟨b₀,hb₀⟩ := hA hb
  subst a b
  let f := (action n a₀ - LinearMap.id).comp (action n b₀ - LinearMap.id)
  have hf : f = 0 := linearMap_eq_zero_of_large_kernel n f W hW (by
    intro Y hY
    exact sub_eq_zero.mpr (hq _ ha _ hb Y hY))
  have h := LinearMap.congr_fun hf X
  exact sub_eq_zero.mp h

end
end Representation.HermitianTensorThree.QuadraticSubspaces
