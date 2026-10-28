module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Module

/-!
# The central seed in the faithful quotient representation

The subgroup `Z` determines an actual binary subspace of `Vᵢ=⟨Zᴵ⟩`.
Its dimension is two when `|Z|=4`. The pointwise stabilizer of this subspace
in `I/O₂(I)` is precisely the image of the prescribed Sylow subgroup:
this follows directly from the conjugation formula and `C_I(Z)=Tᵢ`.
These are the fixed-space inputs to the FF-module classification comparison;
no group or representation identification is assumed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, final paragraph of 15.4.18, printed p.1163.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
open Subgroup Representation.BinaryOffender Representation.NormalElementaryQuotient
open scoped IsMulCommutative
variable {H : Type*} [Group H]
variable (Z : Subgroup H) [IsElementaryAbelian 2 (moduleClosure Z)]

/-- The binary subspace consisting of the original seed elements. -/
noncomputable def seedSubspace : Submodule (ZMod 2) (Additive (moduleClosure Z)) :=
  subspace (moduleClosure Z) (Z.subgroupOf (moduleClosure Z))

/-- The seed subspace has exactly the underlying elements of Z. -/
noncomputable def seedSubspaceEquiv : seedSubspace Z ≃ Z where
  toFun v := ⟨v.val.toMul, v.property⟩
  invFun z := ⟨Additive.ofMul ⟨z, le_normalClosure z.property⟩, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The source order-four seed is a two-dimensional subspace. -/
theorem seedSubspace_finrank [Finite H] (hZ : Nat.card Z = 4) :
    Module.finrank (ZMod 2) (seedSubspace Z) = 2 := by
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := seedSubspace Z)
  rw [Nat.card_zmod, Nat.card_congr (seedSubspaceEquiv Z), hZ] at hc
  exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) hc.symm

variable (P : Sylow 2 H) (hC : centralizer (Z : Set H) = (P : Subgroup H))

/-- The preimage of the pointwise stabilizer is the actual seed centralizer. -/
theorem seedSubspace_kernel_comap :
    (subspaceKernel (quotientAction P Z hC) (seedSubspace Z) ⊤).comap coreProjection =
      centralizer (Z : Set H) := by
  ext g
  constructor
  · intro hg z hz
    have hh := hg.2 (Additive.ofMul ⟨z, le_normalClosure hz⟩) hz
    have he := congrArg (fun v : Additive (moduleClosure Z) => (v.toMul : H)) hh
    rw [quotientAction_apply] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hg
    refine ⟨mem_top _, ?_⟩
    intro v hv
    apply Additive.toMul.injective
    apply Subtype.ext
    have hc : (v.toMul : H) * g = g * (v.toMul : H) := hg _ hv
    rw [quotientAction_apply, ← hc, mul_inv_cancel_right]

/-- The pointwise stabilizer of the seed is precisely the Sylow image. -/
theorem seedSubspace_kernel :
    subspaceKernel (quotientAction P Z hC) (seedSubspace Z) ⊤ =
      (P : Subgroup H).map coreProjection := by
  apply comap_injective (QuotientGroup.mk'_surjective (pCore 2 H))
  change (subspaceKernel (quotientAction P Z hC) (seedSubspace Z) ⊤).comap coreProjection =
    ((P : Subgroup H).map coreProjection).comap coreProjection
  rw [seedSubspace_kernel_comap Z P hC, hC, comap_map_eq]
  rw [coreProjection, QuotientGroup.ker_mk']
  exact (sup_of_le_left (pCore_isPGroup.le_sylow_of_normal P)).symm

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch
