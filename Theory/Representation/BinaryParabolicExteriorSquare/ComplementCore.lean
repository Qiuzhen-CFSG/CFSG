module
public import Theory.Representation.BinaryParabolicExteriorSquare.PlaneRadicalCore
public import Theory.Representation.BinaryParabolicExteriorSquare.ComplementCubic

/-!
# The radical for a cubic fixing the marked plane

The upper-right block group of order sixteen, together with the cubic
rotating the complementary plane, has that block group as its two-core
and quotient of order three. A surjection with two-group kernel recovers the original
radical and its quotient. The cubic fixes the marked natural plane, so
these coordinates agree with the common scalar actor in the first tensor.

Source application: Aschbacher--Smith, The Classification of Quasithin
Groups, 13.8.31(3), printed p.965, with Notation 13.2.1 on p.877.
-/

@[expose] public noncomputable section
open Subgroup
namespace Representation.BinaryParabolicExteriorSquare.PlaneRadical
open PlaneSpan

theorem complement_normalizes : complementElement ∈ normalizer (radical : Set SL) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,⟨v,rfl⟩,rfl⟩
    refine ⟨Multiplicative.ofAdd (Matrix.mulVec complementRadicalCubic v.toAdd),?_⟩
    exact (complement_radical_conjugation complementElement rfl v.toAdd).symm
  · exact (card_map_of_injective (K := radical)
      (f := (MulAut.conj complementElement).toMonoidHom) (MulAut.conj complementElement).injective).ge

def complementLocal : Subgroup SL := radical ⊔ zpowers complementElement

theorem complementLocal_normalizes : complementLocal ≤ normalizer (radical : Set SL) :=
  sup_le radical.le_normalizer (zpowers_le.mpr complement_normalizes)

instance complement_radical_normal : (radical.subgroupOf complementLocal).Normal :=
  (normal_subgroupOf_iff_le_normalizer (show radical ≤ complementLocal from le_sup_left)).mpr
    complementLocal_normalizes

theorem complementLocal_quotient_card : Nat.card (complementLocal ⧸ radical.subgroupOf complementLocal) = 3 := by
  let R := radical.subgroupOf complementLocal
  let C := (zpowers complementElement).subgroupOf complementLocal
  have hRC : R ⊔ C = ⊤ := by
    rw [←subgroupOf_sup (show radical ≤ complementLocal from le_sup_left)
      (show zpowers complementElement ≤ complementLocal from le_sup_right)]
    exact subgroupOf_self complementLocal
  have hdis : Disjoint radical (zpowers complementElement) :=
    disjoint_of_coprime_natCard (by rw [radical_card,Nat.card_zpowers,complementElement_order]; decide)
  have hRCbot : R ⊓ C = ⊥ := by
    apply bot_unique
    intro x hx
    exact Subtype.ext (hdis.le_bot ⟨hx.1,hx.2⟩)
  have hc : Nat.card C = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show zpowers complementElement ≤ complementLocal from le_sup_right)).toEquiv).trans
      ((Nat.card_zpowers complementElement).trans complementElement_order)
  change R.index = 3
  rw [←relIndex_top_right R,←hRC,relIndex_sup_left,←inf_relIndex_left,inf_comm C R,hRCbot,relIndex_bot_left,hc]

theorem complementLocal_twoCore : pCore 2 complementLocal = radical.subgroupOf complementLocal := by
  let R := radical.subgroupOf complementLocal
  have hR : R ≤ pCore 2 complementLocal :=
    le_sSup ⟨inferInstance,radical_two_group.comap_subtype⟩
  apply le_antisymm ?_ hR
  let q := QuotientGroup.mk' R
  have hp : IsPGroup 2 ((pCore 2 complementLocal).map q) := pCore_isPGroup.map q
  have hthree : IsPGroup 3 (complementLocal ⧸ R) :=
    IsPGroup.of_card (n := 1) (by simpa using complementLocal_quotient_card)
  have hbot : (pCore 2 complementLocal).map q = ⊥ := by
    have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ hp (hthree.to_subgroup ⊤)
    simpa using hd.eq_bot
  have hh := (Subgroup.map_eq_bot_iff _).mp hbot
  simpa only [q,QuotientGroup.ker_mk'] using hh

end Representation.BinaryParabolicExteriorSquare.PlaneRadical

namespace Representation.BinaryParabolicExteriorSquare.PlaneRadical
open PlaneSpan

/-- The actual two-core and its quotient are recovered from the local matrix image. -/
theorem lifted_complement_twoCore
    {D : Type*} [Group D] [Finite D]
    (π : D →* SL) (hker : IsPGroup 2 π.ker) (himage : π.range = complementLocal) :
    (pCore 2 D).map π = radical ∧ Nat.card (D ⧸ pCore 2 D) = 3 := by
  let f : D →* complementLocal := π.codRestrict _ (fun d => himage ▸ (show π d ∈ π.range from ⟨d,rfl⟩))
  have hf : Function.Surjective f := by
    intro x
    have hx : x.val ∈ π.range := by rw [himage]; exact x.property
    obtain ⟨d,hd⟩ := hx
    exact ⟨d,Subtype.ext hd⟩
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = π.ker := by ext d; exact Subtype.ext_iff
    rw [he]
    exact hker
  have hm : (pCore 2 D).map f = pCore 2 complementLocal := by
    rw [←f.comap_pCore_of_ker_isPGroup hf hk,map_comap_eq_self]
    rw [f.range_eq_top_of_surjective hf]
    exact le_top
  constructor
  · have hh := congrArg (map complementLocal.subtype) hm
    rw [map_map,complementLocal_twoCore,
      map_subgroupOf_eq_of_le (show radical ≤ complementLocal from le_sup_left)] at hh
    exact hh
  · change (pCore 2 D).index = 3
    rw [←index_map_eq (pCore 2 D) hf (le_sSup ⟨inferInstance,hk⟩),hm,complementLocal_twoCore]
    exact complementLocal_quotient_card

end Representation.BinaryParabolicExteriorSquare.PlaneRadical
