module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.NaturalApplication

/-!
# Lower bound for actual natural-cover commutators

A nontrivial even involution moves at least two dimensions of the binary
natural A₆ module. Equivariance and surjectivity of a cover map put its
four-element displacement image inside the image of the literal group
commutator. Thus the actual commutator has order at least four.
The group above the natural quotient need not split or be elementary.

Contradiction applies this to the original moved cover at a critical pair.
Source: MS93 (3.8), printed p.879.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius

/-- A nontrivial even involution on a natural central cover needs at least
four elements in its actual commutator image. -/
theorem four_le_commutator_card_of_natural
    {H : Type*} [Group H] [Finite H] (P : Subgroup H) [P.Normal]
    (q : P →* Multiplicative (BinaryPermutation.natural (Fin 6)))
    (hq : Function.Surjective q) (π : H →* Equiv.Perm (Fin 6))
    (haction : ∀ g (v : P), (q (MulAut.conjNormal g v)).toAdd =
      BinaryPermutation.naturalRepresentation (Fin 6) (π g) (q v).toAdd)
    (g : H) (heven : π g ∈ alternatingGroup (Fin 6)) (ho : orderOf (π g) = 2) :
    4 ≤ Nat.card (⁅P,zpowers g⁆ : Subgroup H) := by
  let W := BinaryPermutation.natural (Fin 6)
  let ρ := BinaryPermutation.naturalRepresentation (Fin 6)
  let δ : W →ₗ[ZMod 2] W := ρ (π g) - LinearMap.id
  let C := ⁅P,zpowers g⁆
  have hCP : C ≤ P := commutator_le_left _ _
  let f : C →* Multiplicative W := q.comp (inclusion hCP)
  have hmem (v : LinearMap.range δ) : Multiplicative.ofAdd v.val ∈ f.range := by
    obtain ⟨w,hw⟩ := v.property
    obtain ⟨x,hx⟩ := hq (Multiplicative.ofAdd w)
    let c : C := ⟨⁅g,(x : H)⁆, by
      change ⁅g,(x : H)⁆ ∈ ⁅P,zpowers g⁆
      rw [commutator_comm]
      exact commutator_mem_commutator (mem_zpowers g) x.property⟩
    refine ⟨c,?_⟩
    have hc : inclusion hCP c = MulAut.conjNormal g x * x⁻¹ := Subtype.ext rfl
    change q (inclusion hCP c) = _
    rw [hc,map_mul,map_inv]
    apply Multiplicative.toAdd.injective
    have hh : (q (MulAut.conjNormal g x)).toAdd - (q x).toAdd = v.val := by
      rw [haction,hx]
      exact hw
    simpa only [toAdd_mul, toAdd_inv, toAdd_ofAdd, sub_eq_add_neg] using hh
  let i : LinearMap.range δ → f.range := fun v => ⟨Multiplicative.ofAdd v.val,hmem v⟩
  have hi : Function.Injective i := by
    intro v w hh
    apply Subtype.ext
    exact congrArg (fun x : f.range => x.val.toAdd) hh
  have hc : Nat.card (LinearMap.range δ) ≤ Nat.card C :=
    (Nat.card_le_card_of_injective i hi).trans
      (Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective)
  have hρ : Function.Injective (ρ.comp (alternatingGroup (Fin 6)).subtype) :=
    (BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)).comp Subtype.val_injective
  have hl := AlternatingSixInvolutionDisplacement.displacement_lower
    (ρ.comp (alternatingGroup (Fin 6)).subtype) hρ ⟨π g,heven⟩
      ((orderOf_injective (alternatingGroup (Fin 6)).subtype Subtype.val_injective _).symm.trans ho)
  have hp : 2 ^ Module.finrank (ZMod 2) (LinearMap.range δ) = Nat.card (LinearMap.range δ) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact (show 2 ^ 2 ≤ 2 ^ Module.finrank (ZMod 2) (LinearMap.range δ) from
    Nat.pow_le_pow_right (by decide) hl).trans (hp.le.trans hc)

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
