module
public import CFSG.Quasithin.ChapterK.Section01To04.SporadicCatalogue.M11HigmanSimsSourceHS
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup.RationalFusion

/-!
# A fixed-point-free five-element inverted by the elementary outer HS class

The word b⁻¹ a b a b² conjugates the certified five-center generator to an
actual element inverted by the marked elementary outer permutation. Lean checks
this identity on the 100 letters. The existing extraspecial-five calculation
makes this element fixed-point-free in every faithful binary representation of
degree twenty. Twisting the representation transports that conclusion through
any automorphism conjugating the specified outer representative.

This supplies the involution calculation in GM02 Proposition 5.1 (HS paragraph,
author preprint pp.16–17), using a five-element in place of its eleven-element.
The action is the original ATLAS HSG1-p100B0 carrier, with its existing source
attribution. The internal imports expose only the packed certificate helpers.
-/

public section
namespace CFSG.Quasithin.ChapterK.SporadicCatalogue.HSOuterCalculations
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
open Twenty
open Chapter16.OtherPreliminaries.JankoTwoHigmanSims
open Sporadic.LeechRelated.HS
open Sporadic.LeechRelated.HS.FiveSubgroup
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def fiveConjugator : Carrier := b⁻¹ * a * b * a * b * b
private def five : Carrier := fiveConjugator * z * fiveConjugator⁻¹

private theorem elementary_inverts_five :
    generated.normalizerMonoidHom HSOuter.elementaryNormalizer five = five⁻¹ := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem five_order : orderOf five = 5 := by
  exact ((MulAut.conj fiveConjugator).orderOf_eq z).trans
    (orderOf_eq_prime RationalFusion.z_pow_five RationalFusion.z_ne_one)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem z_free (σ : Representation (ZMod 2) Carrier V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 20) :
    fixedSpace σ (zpowers z) = ⊥ := by
  have hz : (center subgroup).map subgroup.subtype = zpowers z := by
    let : IsExtraspecial 5 subgroup :=
      IsExtraspecial.of_noncommutative_card_prime_cube card_subgroup subgroup_not_commutative
    have hzm : (⟨z, RationalFusion.z_mem_subgroup⟩ : subgroup) ∈ center subgroup := by
      apply Subgroup.mem_center_iff.mpr
      intro g
      exact Subtype.ext (RationalFusion.z_mem_centralizer g g.property)
    apply (eq_of_le_of_card_ge (zpowers_le.mpr (mem_map.mpr ⟨_, hzm, rfl⟩)) ?_).symm
    change Nat.card ((center subgroup).map subgroup.subtype) ≤ Nat.card (zpowers z)
    rw [Nat.card_zpowers,
      orderOf_eq_prime RationalFusion.z_pow_five RationalFusion.z_ne_one,
      Subgroup.card_map_of_injective subgroup.subtype_injective,
      IsExtraspecial.center_order_p 5 subgroup]
  rw [← hz]
  exact AbsoluteWindow.fiveCenter_fixed_eq_bot_of_finrank_twenty σ hf hd

private theorem five_free (σ : Representation (ZMod 2) Carrier V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 20) :
    fixedSpace σ (zpowers five) = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  have he := (fixedSpaceConjEquiv σ (zpowers z) fiveConjugator).finrank_eq
  rw [MonoidHom.map_zpowers, z_free σ hf hd, finrank_bot] at he
  exact he.symm

/-- Each conjugate automorphism in the elementary outer class inverts an
actual order-five element that is fixed-point-free in every faithful
binary representation of degree twenty. -/
theorem elementary_inverts_free_five
    (σ : Representation (ZMod 2) Carrier V)
    (hf : Function.Injective σ) (hd : Module.finrank (ZMod 2) V = 20)
    {r : MulAut Carrier}
    (hr : IsConj (generated.normalizerMonoidHom HSOuter.elementaryNormalizer) r) :
    ∃ x : Carrier, orderOf x = 5 ∧ r x = x⁻¹ ∧ fixedSpace σ (zpowers x) = ⊥ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hr
  refine ⟨c five, (c.orderOf_eq five).trans five_order, ?_, ?_⟩
  · rw [← hc]
    change c ((generated.normalizerMonoidHom HSOuter.elementaryNormalizer)
      (c.symm (c five))) = (c five)⁻¹
    rw [c.symm_apply_apply, elementary_inverts_five, map_inv]
  · have he := five_free (σ.comp c.toMonoidHom) (hf.comp c.injective) hd
    rw [fixedSpace_comp_map, MonoidHom.map_zpowers] at he
    exact he

end CFSG.Quasithin.ChapterK.SporadicCatalogue.HSOuterCalculations
