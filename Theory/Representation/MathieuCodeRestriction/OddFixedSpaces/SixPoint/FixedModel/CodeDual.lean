module

public import Theory.Representation.MathieuCodeRestriction.OddFixedSpaces.SixPoint.FixedModel.Cocode

/-!
# The contragredient model on the actual code fixed space

The code side remains the actual Mathieu code fixed space. The published
code--cocode duality restricts to a normalizer-equivariant map on fixed spaces;
its bijectivity is kept as the precise odd-order fixed-space premise used by
the source assembly. This file never identifies the code fixed space with the
permutation core and never transfers cocode O₂ assertions to the code.
-/

@[expose] public section

open Sporadic.Mathieu Representation.BinaryOffender
namespace MathieuCode.SixPoint
noncomputable section
open scoped Classical

theorem normalizer_preserves_fixedCode (D : Subgroup M24)
    (n : Subgroup.normalizer (D : Set M24)) (v : fixedSpace codeRepresentation D) :
    codeRepresentation n.val v.val ∈ fixedSpace codeRepresentation D := by
  intro d
  have hc : n.val⁻¹ * d.val * n.val ∈ D := by
    simpa only [inv_inv] using (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (D : Set M24)).inv_mem n.property) d.val).mp d.property
  have he := v.property ⟨_, hc⟩
  change codeRepresentation (n.val⁻¹ * d.val * n.val) v.val = v.val at he
  change codeRepresentation d.val (codeRepresentation n.val v.val) = _
  calc
    _ = codeRepresentation (d.val * n.val) v.val := by rw [map_mul, Module.End.mul_apply]
    _ = codeRepresentation n.val (codeRepresentation (n.val⁻¹ * d.val * n.val) v.val) := by
      rw [← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    _ = _ := congrArg (codeRepresentation n.val) he

def normalizerFixedCodeSubrepresentation (D : Subgroup M24) :
    Subrepresentation (codeRepresentation.comp (Subgroup.normalizer (D : Set M24)).subtype) where
  toSubmodule := fixedSpace codeRepresentation D
  apply_mem_toSubmodule n v hv := normalizer_preserves_fixedCode D n ⟨v, hv⟩

def fixedCodeRepresentation (D : Subgroup M24) :
    Representation (ZMod 2) (Subgroup.normalizer (D : Set M24))
      (fixedSpace codeRepresentation D) :=
  (normalizerFixedCodeSubrepresentation D).toRepresentation

@[simp] theorem fixedCodeRepresentation_apply (D : Subgroup M24)
    (n : Subgroup.normalizer (D : Set M24)) (v : fixedSpace codeRepresentation D) :
    (fixedCodeRepresentation D n v).val = codeRepresentation n.val v.val := rfl

def fixedCodeDualMap (D : Subgroup M24) :
    fixedSpace codeRepresentation D →ₗ[ZMod 2]
      Module.Dual (ZMod 2) (fixedSpace cocodeRepresentation D) :=
  (fixedSpace cocodeRepresentation D).dualRestrict.comp
    (codeDuality.toLinearEquiv.toLinearMap.comp (fixedSpace codeRepresentation D).subtype)

@[simp] theorem fixedCodeDualMap_apply (D : Subgroup M24)
    (v : fixedSpace codeRepresentation D) (w : fixedSpace cocodeRepresentation D) :
    fixedCodeDualMap D v w = codeCocodePairing v.val w.val := rfl

def fixedCodeDualMap_intertwining (D : Subgroup M24) :
    (fixedCodeRepresentation D).IntertwiningMap (fixedCocodeRepresentation D).dual := by
  refine { toLinearMap := fixedCodeDualMap D, isIntertwining' := ?_ }
  intro n
  apply LinearMap.ext
  intro v
  apply LinearMap.ext
  intro w
  exact LinearMap.congr_fun
    (LinearMap.congr_fun (codeDuality.isIntertwining' n.val) v.val) w.val

/-- The actual fixed-code contragredient model, under the exact bijectivity
premise supplied by odd-order fixed-space duality in the source assembly. -/
def fixedCodeDuality_of_bijective (D : Subgroup M24)
    (hmap : Function.Bijective (fixedCodeDualMap D)) :
    (fixedCodeRepresentation D).Equiv (fixedCocodeRepresentation D).dual :=
  let f := fixedCodeDualMap_intertwining D
  have hf : Function.Bijective f.toLinearMap := by
    change Function.Bijective (fixedCodeDualMap D)
    exact hmap
  f.ofBijective hf

@[simp] theorem fixedCodeDuality_of_bijective_apply (D : Subgroup M24)
    (hmap : Function.Bijective (fixedCodeDualMap D))
    (v : fixedSpace codeRepresentation D) (w : fixedSpace cocodeRepresentation D) :
    fixedCodeDuality_of_bijective D hmap v w = codeCocodePairing v.val w.val := by
  change (fixedCodeDualMap D v) w = _
  rfl

end
end MathieuCode.SixPoint

namespace MathieuCode.SixPoint
noncomputable section
open scoped Classical

/-- Dualizing the canonical cocode equivalence gives the dual six-point core. -/
def fixedCocodeCoreDualEquiv (D : Subgroup M24)
    (hfix : Nat.card (FixedPoint D) = 6)
    (hdim : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) = 5) :
    (fixedCocodeRepresentation D).dual.Equiv (fixedPointCoreRepresentation D).dual := by
  let e := fixedPointCoreRepresentationEquiv D hfix hdim
  apply Representation.Equiv.mk e.toLinearEquiv.dualMap
  intro n
  apply LinearMap.ext
  intro f
  apply LinearMap.ext
  intro v
  simp only [Representation.dual_apply]
  exact (congrArg f (LinearMap.congr_fun (e.isIntertwining' n⁻¹) v)).symm

def fixedCodeCoreDualEquiv_of_bijective (D : Subgroup M24)
    (hmap : Function.Bijective (fixedCodeDualMap D))
    (hfix : Nat.card (FixedPoint D) = 6)
    (hdim : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) = 5) :
    (fixedCodeRepresentation D).Equiv (fixedPointCoreRepresentation D).dual :=
  (fixedCodeDuality_of_bijective D hmap).trans
    (fixedCocodeCoreDualEquiv D hfix hdim)

end
end MathieuCode.SixPoint

namespace MathieuCode.SixPoint
noncomputable section
open scoped Classical

/-- Odd-order averaging makes the restricted pairing injective on fixed code. -/
theorem fixedCodeDualMap_injective (D : Subgroup M24) (ho : Odd (Nat.card D)) :
    Function.Injective (fixedCodeDualMap D) := by
  let : Fintype D := Fintype.ofFinite D
  intro v w hvw
  have hu : fixedCodeDualMap D (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have hzero : (v - w).val = 0 := by
    apply codeCocodePairing_left_nondegenerate
    intro x
    have hnorm : Representation.norm (cocodeRepresentation.comp D.subtype) x ∈
        fixedSpace cocodeRepresentation D := by
      intro d
      exact Representation.self_norm_apply _ d x
    have hz := LinearMap.congr_fun hu ⟨_, hnorm⟩
    change codeCocodePairing (v - w).val (Representation.norm
        (cocodeRepresentation.comp D.subtype) x) = 0 at hz
    have hp (d : D) : codeCocodePairing (v - w).val
        (cocodeRepresentation d.val x) = codeCocodePairing (v - w).val x := by
      have hi := codeCocodePairing_invariant d.val (v - w).val x
      have hv : codeRepresentation d.val (v - w).val = (v - w).val := by
        rw [show (v - w).val = v.val - w.val by rfl, map_sub]
        have hv1 := v.property d
        have hw1 := w.property d
        change codeRepresentation d.val v.val = v.val at hv1
        change codeRepresentation d.val w.val = w.val at hw1
        rw [hv1, hw1]
      rw [hv] at hi
      exact hi
    simp only [Representation.norm, LinearMap.sum_apply, MonoidHom.comp_apply,
      Subgroup.subtype_apply, map_sum, hp, Finset.sum_const, Finset.card_univ] at hz
    have hc : (Fintype.card D : ZMod 2) = 1 :=
      (show Odd (Fintype.card D) by simpa only [Nat.card_eq_fintype_card] using ho).natCast_zmod_two
    simpa only [← Nat.cast_smul_eq_nsmul (ZMod 2), hc, one_smul] using hz
  exact sub_eq_zero.mp (Subtype.ext hzero)

theorem fixedCodeDualMap_bijective (D : Subgroup M24) (hD : Nat.card D = 3) :
    Function.Bijective (fixedCodeDualMap D) := by
  have hi := fixedCodeDualMap_injective D (by rw [hD]; decide)
  refine ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hi⟩
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic D := isCyclic_of_prime_card hD
  rw [Subspace.dual_finrank_eq]
  exact code_cocode_fixed_finrank_cyclic D

/-- The source fixed-code dual model, with the odd-order premise discharged. -/
def fixedCodeDuality (D : Subgroup M24) (hD : Nat.card D = 3) :
    (fixedCodeRepresentation D).Equiv (fixedCocodeRepresentation D).dual :=
  fixedCodeDuality_of_bijective D (fixedCodeDualMap_bijective D hD)

end
end MathieuCode.SixPoint

namespace MathieuCode.SixPoint
noncomputable section

/-- The actual six-point contragredient code model for an order-three actor. -/
def fixedCodeCoreDualEquiv (D : Subgroup M24) (hD : Nat.card D = 3)
    (hfix : Nat.card (FixedPoint D) = 6)
    (hdim : Module.finrank (ZMod 2) (fixedSpace cocodeRepresentation D) = 5) :
    (fixedCodeRepresentation D).Equiv (fixedPointCoreRepresentation D).dual :=
  (fixedCodeDuality D hD).trans (fixedCocodeCoreDualEquiv D hfix hdim)

end
end MathieuCode.SixPoint
