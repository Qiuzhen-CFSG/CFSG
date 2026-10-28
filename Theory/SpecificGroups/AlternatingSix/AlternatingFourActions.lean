module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.ExceptionalFixed
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.Inner
public import Theory.SpecificGroups.AlternatingSix.OuterInvolutionExtension.NaturalCoordinates
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.InvolutionGeometry.FourNormalizers.SixParabolicTypes
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.Transport

/-!
# Four-subgroup actions in the actual A₆ component

A nonidentity involution fixing an embedded A₄ has a fixed group whose order
is divisible by twelve. The inner and exceptional fixed-group orders exclude
both other automorphism types, giving transposition coordinates. Normalizers
of an actual Klein four-group act through the natural S₆ in these same
coordinates. The ambient statements retain the literal conjugation map.

Source: Aschbacher–Smith, 2.4.32–35, printed pp.547–548.
-/

public section
open Subgroup
namespace AlternatingSix
open ShadowLocal

/-- A genuine involution fixing an actual A₄ belongs to the natural outer class. -/
theorem alternatingFour_fixed_involution_natural_outer
    (L : Subgroup A6) (eL : L ≃* alternatingGroup (Fin 4))
    (a : AutA6) (ha : orderOf a = 2) (hf : ∀ l ∈ L, a l = l) :
    a ∈ natural ∧ a ∉ ShadowLocal.inner := by
  have hc : Nat.card L = 12 := by
    rw [Nat.card_congr eL.toEquiv, Nat.card_eq_fintype_card]
    decide
  have hd := card_dvd_of_le (show L ≤ GLS3.Chapter5.automorphismFixedSubgroup a from hf)
  constructor
  · by_contra hn
    rw [hc, outside_natural_involution_fixed_card a ha hn] at hd
    norm_num at hd
  · rintro ⟨g, rfl⟩
    have hg : orderOf g = 2 := (orderOf_injective _ inner_injective g).symm.trans ha
    rw [hc, inner_involution_fixed_card g hg] at hd
    norm_num at hd

/-- The original fixed A₄ gives coordinates in which the actor is a transposition. -/
theorem alternatingFour_fixed_involution_coordinates
    (L : Subgroup A6) (eL : L ≃* alternatingGroup (Fin 4))
    (a : AutA6) (ha : orderOf a = 2) (hf : ∀ l ∈ L, a l = l) :
    ∃ (e : MulAut A6) (s : Equiv.Perm (Fin 6)), s.IsSwap ∧
      MulAut.congr e a = permutationAction s := by
  have h := alternatingFour_fixed_involution_natural_outer L eL a ha hf
  exact OuterInvolutionExtension.natural_involution_transposition_coordinates a
    (ha ▸ pow_orderOf_eq_one a) h.1 h.2

end AlternatingSix

namespace AlternatingSix.ShadowLocal
variable {H : Type*} [Group H]

/-- The actual normalizer of an embedded four-group acts through the natural S₆. -/
theorem conjugationAction_natural_of_normalizes_four
    (K : Subgroup H) [K.Normal] (e : K ≃* A6)
    (U : Subgroup H) [IsKleinFour U] (hUK : U ≤ K)
    (r : H) (hr : r ∈ normalizer (U : Set H)) :
    conjugationAction K e r ∈ natural := by
  let F := (U.subgroupOf K).map e.toMonoidHom
  let eF : U ≃* F := (subgroupOfEquivOfLe hUK).symm.trans
    ((U.subgroupOf K).equivMapOfInjective e.toMonoidHom e.injective)
  let : IsKleinFour F := {
    card_four := (Nat.card_congr eF.toEquiv).symm.trans IsKleinFour.card_four
    exponent_two := (Monoid.exponent_eq_of_mulEquiv eF).symm.trans IsKleinFour.exponent_two }
  apply FourNormalizers.SixParabolics.four_stabilizer_natural F
  apply eq_of_le_of_card_ge
  · rintro _ ⟨y,hy,rfl⟩
    obtain ⟨v,hv,rfl⟩ := hy
    refine ⟨MulAut.conjNormal r v, ?_, (conjugationAction_apply K e r v).symm⟩
    change r * (v : H) * r⁻¹ ∈ U
    exact (mem_normalizer_iff.mp hr (v : H)).mp hv
  · exact (card_map_of_injective (K := F) (conjugationAction K e r).injective).ge

/-- A whole actual normalizer subgroup has natural action, in any A₆ coordinates. -/
theorem conjugationAction_map_natural_of_normalizes_four
    (K : Subgroup H) [K.Normal] (e : K ≃* A6)
    (U R : Subgroup H) [IsKleinFour U] (hUK : U ≤ K)
    (hR : R ≤ normalizer (U : Set H)) :
    R.map (conjugationAction K e) ≤ natural := by
  rintro _ ⟨r,hr,rfl⟩
  exact conjugationAction_natural_of_normalizes_four K e U hUK r (hR hr)

end AlternatingSix.ShadowLocal
