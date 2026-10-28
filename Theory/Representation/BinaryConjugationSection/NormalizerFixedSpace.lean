module
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Literal fixed spaces of normalizing subgroups

For an elementary abelian two-subgroup `E`, the fixed vectors of the
conjugation representation of `C` under `P ≤ C` are exactly the original
subgroup `E ∩ C_G(P)`. The resulting equivalence converts a source
centralizer order into its binary fixed-space dimension, without replacing
the actor or passing to a different quotient.

Source application: Aschbacher–Smith 10.2.3(4), printed p.746.
-/

public section
open Subgroup Representation.BinaryOffender
open scoped IsMulCommutative
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {C E : Subgroup G} [IsElementaryAbelian 2 E]

/-- Fixed vectors are precisely elements of the literal ambient centralizer. -/
theorem mem_originalFixedSpace_iff (hCE : C ≤ normalizer (E : Set G))
    (P : Subgroup G) (hPC : P ≤ C) (v : Additive E) :
    v ∈ fixedSpace (originalNormalizerAction hCE) (P.subgroupOf C) ↔
      (v.toMul : G) ∈ centralizer (P : Set G) := by
  constructor
  · intro hv p hp
    let p' : P.subgroupOf C := ⟨⟨p,hPC hp⟩,hp⟩
    have h := congrArg (fun w : Additive E => (w.toMul : G)) (hv p')
    dsimp only [MonoidHom.comp_apply] at h
    rw [originalNormalizerAction_apply_coe] at h
    exact mul_inv_eq_iff_eq_mul.mp h
  · intro hv p
    apply Additive.toMul.injective
    apply Subtype.ext
    dsimp only [MonoidHom.comp_apply]
    rw [originalNormalizerAction_apply_coe]
    exact mul_inv_eq_iff_eq_mul.mpr (hv p p.property)

/-- The fixed-space carrier equals the original centralizing subgroup. -/
noncomputable def originalFixedSpaceEquiv
    (hCE : C ≤ normalizer (E : Set G)) (P : Subgroup G) (hPC : P ≤ C) :
    fixedSpace (originalNormalizerAction hCE) (P.subgroupOf C) ≃
      (E ⊓ centralizer (P : Set G) : Subgroup G) where
  toFun v := ⟨v.val.toMul, v.val.toMul.property,
    (mem_originalFixedSpace_iff hCE P hPC v.val).mp v.property⟩
  invFun v := ⟨Additive.ofMul ⟨v,v.property.1⟩,
    (mem_originalFixedSpace_iff hCE P hPC _).mpr v.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Original centralizer order determines the binary fixed-space dimension. -/
theorem finrank_originalFixedSpace_of_card [Finite G]
    (hCE : C ≤ normalizer (E : Set G)) (P : Subgroup G) (hPC : P ≤ C)
    (k : ℕ) (hcard : Nat.card (E ⊓ centralizer (P : Set G) : Subgroup G) = 2 ^ k) :
    Module.finrank (ZMod 2) (fixedSpace (originalNormalizerAction hCE) (P.subgroupOf C)) = k := by
  apply Nat.pow_right_injective (by decide : 1 < 2)
  calc
    2 ^ Module.finrank (ZMod 2)
        (fixedSpace (originalNormalizerAction hCE) (P.subgroupOf C)) =
        Nat.card (fixedSpace (originalNormalizerAction hCE) (P.subgroupOf C)) := by
      simpa only [Nat.card_zmod] using
        (Module.natCard_eq_pow_finrank (K := ZMod 2)
          (V := fixedSpace (originalNormalizerAction hCE) (P.subgroupOf C))).symm
    _ = Nat.card (E ⊓ centralizer (P : Set G) : Subgroup G) :=
      Nat.card_congr (originalFixedSpaceEquiv hCE P hPC)
    _ = 2 ^ k := hcard

end Representation.BinaryConjugationSection
