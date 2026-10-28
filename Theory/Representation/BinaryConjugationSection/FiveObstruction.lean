module
public import Theory.Representation.BinaryConjugationSection.Restriction
public import Theory.Representation.AlternatingFiveLinearTwoObstruction
public import Theory.Representation.BinaryPermutation.FivePairFaithful
public import Mathlib.FieldTheory.Finiteness
public import Theory.ElementaryAbelian.VectorSpace
/-!
# Natural SL₂(4) sections cannot be deleted permutation modules

Equal module orders remove the central kernel. Faithfulness then descends
the SL₂ action to A₅, contradicting the cubic fixed-space obstruction.
-/
public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups IsMulCommutative
namespace Representation.BinaryConjugationSection
variable {G : Type*} [Group G] {H W B : Subgroup G}
  {F : Type*} [Field F] [CharP F 2]
  [IsElementaryAbelian 2 W]
local instance fiveSourceFieldAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2
set_option backward.isDefEq.respectTransparency false in
theorem not_five_core_of_natural_four (hF : Nat.card F = 4)
    (q : H →* SL(2,F))
    (c : BinaryConjugationSection H W B (SL2.BinarySmall.natural.comp q))
    (a : H →* alternatingGroup (Fin 5)) (ha : Function.Surjective a)
    (e : Additive W ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
    (he : ∀ (g : H) (v : W),
      e (Additive.ofMul ⟨g*v*(g:G)⁻¹,
        (mem_normalizer_iff.mp (c.normalized g.property) v).mp v.property⟩) =
      BinaryPermutation.coreRepresentation (Fin 5) (a g).val (e (Additive.ofMul v))) : False := by
  have hw : Nat.card W = 16 := by
    calc
      Nat.card W = Nat.card (BinaryPermutation.core (Fin 5)) := Nat.card_congr e.toEquiv
      _ = 16 := by
        rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,BinaryPermutation.finrank_core]
        rfl
  have hv : Nat.card (Fin 2 → F) = 16 := by rw [Nat.card_fun,Nat.card_fin,hF]; norm_num
  have hb : B = ⊥ := Subgroup.card_eq_one.mp (by
    have hh := c.card_section
    rw [hw,hv] at hh
    omega)
  have hci : Function.Injective c.coordinates := by
    apply c.coordinates.ker_eq_bot_iff.mp
    rw [c.kernel_eq,hb,bot_subgroupOf]
  let b : BinaryPermutation.core (Fin 5) →+ (Fin 2 → F) :=
    { toFun := fun v => (c.coordinates (e.symm v).toMul).toAdd
      map_zero' := by
        rw [map_zero]
        change (c.coordinates 1).toAdd = 0
        rw [map_one]; rfl
      map_add' := by
        intro v w
        rw [map_add]
        change (c.coordinates ((e.symm v).toMul * (e.symm w).toMul)).toAdd = _
        rw [map_mul]; rfl }
  have hbi : Function.Injective b := by
    intro v w hh
    exact e.symm.injective (hci hh)
  have hb_apply (w : W) : b (e (Additive.ofMul w)) = (c.coordinates w).toAdd := by
    change (c.coordinates (e.symm (e (Additive.ofMul w))).toMul).toAdd = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  have hec (g : H) (v : W) :
      b (BinaryPermutation.coreRepresentation (Fin 5) (a g).val (e (Additive.ofMul v))) =
        (q g).val *ᵥ b (e (Additive.ofMul v)) := by
    rw [←he g v,hb_apply,hb_apply]
    exact c.equivariant g v
  have hk : a.ker ≤ q.ker := by
    intro g hg
    have hg' : a g = 1 := hg
    apply Subtype.ext
    apply Matrix.ext_iff_mulVec.mpr
    intro v
    obtain ⟨w,hw⟩ := c.onto (Multiplicative.ofAdd v)
    have hh := hec g w
    simp only [hg',Subgroup.coe_one,map_one,Module.End.one_apply] at hh
    rw [hb_apply] at hh
    rw [hw] at hh
    simpa using hh.symm
  let r : alternatingGroup (Fin 5) →* SL(2,F) := a.liftOfSurjective ha ⟨q,hk⟩
  have hr (g : H) : r (a g) = q g := a.liftOfRightInverse_comp_apply (Function.surjInv ha) (Function.rightInverse_surjInv ha) ⟨q,hk⟩ g
  have hact (x : alternatingGroup (Fin 5)) (v : BinaryPermutation.core (Fin 5)) :
      b (BinaryPermutation.coreRepresentation (Fin 5) x.val v) = (r x).val *ᵥ b v := by
    obtain ⟨g,rfl⟩ := ha x
    rw [hr]
    have hh := hec g (e.symm v).toMul
    change b (BinaryPermutation.coreRepresentation (Fin 5) (a g).val (e (e.symm v))) =
      (q g).val *ᵥ b (e (e.symm v)) at hh
    simpa only [LinearEquiv.apply_symm_apply] using hh
  have hri : Function.Injective r := by
    intro x y hxy
    apply Subtype.ext
    apply BinaryPermutation.FivePair.core_injective
    apply LinearMap.ext
    intro v
    apply hbi
    rw [hact,hact,hxy]
  exact BinaryPermutation.AlternatingFiveLinearTwo.no_equivariant_core_injection r hri b hbi hact
end Representation.BinaryConjugationSection
