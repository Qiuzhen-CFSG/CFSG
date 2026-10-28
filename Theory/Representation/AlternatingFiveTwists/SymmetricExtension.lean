module
public import Theory.Representation.AlternatingFiveTwists
public import Theory.Representation.OrthogonalFourMinusRankOne.FivePoint.Ambient

/-!
# Extend the deleted A₅ module on the same S₅ marking

An actual deleted-module equivalence on the normal A₅ subgroup extends to
S₅. First remove its A₅ automorphism twist with a permutation intertwiner.
The full normalizer then supplies an ambient permutation action. Because
it fixes A₅ pointwise, injectivity of the conjugation map S₅ → Aut(A₅)
forces that ambient map to be the identity. The resulting equivalence
uses the original S₅ marking and the augmentation-core carrier.

Source application: Aschbacher–Smith, final argument of 14.7.40,
printed p.1063; the five-point normalizer is K.3.1.2, printed p.454.
-/

public noncomputable section
open Subgroup Representation
namespace Representation.AlternatingFiveTwists
local notation "A5" => alternatingGroup (Fin 5)
local notation "S5" => Equiv.Perm (Fin 5)
local notation "D" => BinaryPermutation.natural (Fin 5)
local notation "δ" => BinaryPermutation.naturalRepresentation (Fin 5)
variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- A deleted-module equivalence on A₅ extends on the same S₅ marking.
Automorphism twists are removed using their actual permutation intertwiners. -/
theorem symmetric_deleted_equiv
    (σ : Representation (ZMod 2) S5 W) (hf : Function.Injective σ)
    (f : A5 ≃* A5) (E : W ≃ₗ[ZMod 2] D)
    (hE : ∀ a : A5, ∀ w, E (σ a.val w) = δ (f a).val (E w)) :
    ∃ e : W ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5),
      ∀ g w, e (σ g w) = BinaryPermutation.coreRepresentation (Fin 5) g (e w) := by
  obtain ⟨c,hc⟩ := deleted_twist f
  let E' := E.trans c.symm
  have hE' (a : A5) (w : W) : E' (σ a.val w) = δ a.val (E' w) := by
    apply c.injective
    change c (c.symm (E (σ a.val w))) = c (δ a.val (c.symm (E w)))
    rw [c.apply_symm_apply, hE]
    have hh := hc a (c.symm (E w))
    change c (δ a.val (c.symm (E w))) = δ (f a).val (c (c.symm (E w))) at hh
    rw [c.apply_symm_apply] at hh
    exact hh.symm
  obtain ⟨p,_,hp,hpA⟩ := OrthogonalFourMinus.FivePoint.exists_ambient_permutation
    σ A5 (MulEquiv.refl A5) E' hE' hf
  have hpId (g : S5) : p g = g := by
    apply (GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      5 (by decide) (by decide)).injective
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    let b : A5 := ⟨g * a.val * g⁻¹, (inferInstance : (A5).Normal).conj_mem a.val a.property g⟩
    have hb := hpA b
    change p (g * a.val * g⁻¹) = g * a.val * g⁻¹ at hb
    rw [map_mul,map_mul,map_inv,hpA a] at hb
    exact hb
  let C := BinaryPermutation.coreEquivNatural (Fin 5) (by decide)
  refine ⟨E'.trans C.symm,?_⟩
  intro g w
  apply C.injective
  change C (C.symm (E' (σ g w))) =
    C (BinaryPermutation.coreRepresentation (Fin 5) g (C.symm (E' w)))
  rw [C.apply_symm_apply, hp, hpId,
    BinaryPermutation.coreEquivNatural_equivariant, C.apply_symm_apply]

end Representation.AlternatingFiveTwists
