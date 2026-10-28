module
public import Theory.Representation.BinaryParabolicExteriorSquare.PlaneRadical
public import Theory.Representation.BinaryParabolicExteriorSquare.MarkedCubic
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The two-core of the cubic plane subgroup

The binary upper-right-block group has order sixteen and is normalized by
the marked plane cubic. Their join has quotient of order three by that
block group, which is therefore its actual two-core. A surjection with
two-group kernel lifts this equality to the original two-core and retains
the literal radical image and the order-three quotient.

Source application: O₂(L₀*) in the surrounding chief-factor calculation of
Aschbacher–Smith, *The Classification of Quasithin Groups*, 13.8.31(3),
printed p.965. Identifying the local matrix image remains the source
application's explicit premise.
-/

@[expose] public noncomputable section
open Subgroup
namespace Representation.BinaryParabolicExteriorSquare.PlaneRadical
open PlaneSpan

theorem radical_card : Nat.card radical = 16 := by
  rw [Nat.card_congr coordinates.toEquiv]
  simp [Four,Bit]

theorem radical_two_group : IsPGroup 2 radical :=
  IsPGroup.of_card (n := 4) (by simpa using radical_card)

theorem cubic_normalizes : cubicElement ∈ normalizer (radical : Set SL) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x,⟨v,rfl⟩,rfl⟩
    refine ⟨Multiplicative.ofAdd (Matrix.mulVec pairedCubic v.toAdd),?_⟩
    exact (cubic_conjugation cubicElement rfl v.toAdd).symm
  · exact (card_map_of_injective (K := radical)
      (f := (MulAut.conj cubicElement).toMonoidHom) (MulAut.conj cubicElement).injective).ge

def cubicLocal : Subgroup SL := radical ⊔ zpowers cubicElement

theorem cubicLocal_normalizes : cubicLocal ≤ normalizer (radical : Set SL) :=
  sup_le radical.le_normalizer (zpowers_le.mpr cubic_normalizes)

instance radical_normal : (radical.subgroupOf cubicLocal).Normal :=
  (normal_subgroupOf_iff_le_normalizer (show radical ≤ cubicLocal from le_sup_left)).mpr
    cubicLocal_normalizes

theorem cubicLocal_quotient_card : Nat.card (cubicLocal ⧸ radical.subgroupOf cubicLocal) = 3 := by
  let R := radical.subgroupOf cubicLocal
  let C := (zpowers cubicElement).subgroupOf cubicLocal
  have hRC : R ⊔ C = ⊤ := by
    rw [←subgroupOf_sup (show radical ≤ cubicLocal from le_sup_left)
      (show zpowers cubicElement ≤ cubicLocal from le_sup_right)]
    exact subgroupOf_self cubicLocal
  have hdis : Disjoint radical (zpowers cubicElement) :=
    disjoint_of_coprime_natCard (by rw [radical_card,Nat.card_zpowers,cubicElement_order]; decide)
  have hRCbot : R ⊓ C = ⊥ := by
    apply bot_unique
    intro x hx
    exact Subtype.ext (hdis.le_bot ⟨hx.1,hx.2⟩)
  have hc : Nat.card C = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe (show zpowers cubicElement ≤ cubicLocal from le_sup_right)).toEquiv).trans
      ((Nat.card_zpowers cubicElement).trans cubicElement_order)
  change R.index = 3
  rw [←relIndex_top_right R,←hRC,relIndex_sup_left,←inf_relIndex_left,inf_comm C R,hRCbot,relIndex_bot_left,hc]

theorem cubicLocal_twoCore : pCore 2 cubicLocal = radical.subgroupOf cubicLocal := by
  let R := radical.subgroupOf cubicLocal
  have hR : R ≤ pCore 2 cubicLocal :=
    le_sSup ⟨inferInstance,radical_two_group.comap_subtype⟩
  apply le_antisymm ?_ hR
  let q := QuotientGroup.mk' R
  have hp : IsPGroup 2 ((pCore 2 cubicLocal).map q) := pCore_isPGroup.map q
  have hthree : IsPGroup 3 (cubicLocal ⧸ R) :=
    IsPGroup.of_card (n := 1) (by simpa using cubicLocal_quotient_card)
  have hbot : (pCore 2 cubicLocal).map q = ⊥ := by
    have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) _ _ hp (hthree.to_subgroup ⊤)
    simpa using hd.eq_bot
  have hh := (Subgroup.map_eq_bot_iff _).mp hbot
  simpa only [q,QuotientGroup.ker_mk'] using hh

end Representation.BinaryParabolicExteriorSquare.PlaneRadical

namespace Representation.BinaryParabolicExteriorSquare.PlaneRadical
open PlaneSpan

/-- The actual two-core and its quotient are recovered from the local matrix image. -/
theorem lifted_twoCore
    {D : Type*} [Group D] [Finite D]
    (π : D →* SL) (hker : IsPGroup 2 π.ker) (himage : π.range = cubicLocal) :
    (pCore 2 D).map π = radical ∧ Nat.card (D ⧸ pCore 2 D) = 3 := by
  let f : D →* cubicLocal := π.codRestrict _ (fun d => himage ▸ (show π d ∈ π.range from ⟨d,rfl⟩))
  have hf : Function.Surjective f := by
    intro x
    have hx : x.val ∈ π.range := by rw [himage]; exact x.property
    obtain ⟨d,hd⟩ := hx
    exact ⟨d,Subtype.ext hd⟩
  have hk : IsPGroup 2 f.ker := by
    have he : f.ker = π.ker := by ext d; exact Subtype.ext_iff
    rw [he]
    exact hker
  have hm : (pCore 2 D).map f = pCore 2 cubicLocal := by
    rw [←f.comap_pCore_of_ker_isPGroup hf hk,map_comap_eq_self]
    rw [f.range_eq_top_of_surjective hf]
    exact le_top
  constructor
  · have hh := congrArg (map cubicLocal.subtype) hm
    rw [map_map,cubicLocal_twoCore,
      map_subgroupOf_eq_of_le (show radical ≤ cubicLocal from le_sup_left)] at hh
    exact hh
  · change (pCore 2 D).index = 3
    rw [←index_map_eq (pCore 2 D) hf (le_sSup ⟨inferInstance,hk⟩),hm,cubicLocal_twoCore]
    exact cubicLocal_quotient_card

end Representation.BinaryParabolicExteriorSquare.PlaneRadical
