module
public import Stellmacher.SectionNine.NineTenTransvectionIntersection
public import Stellmacher.SectionNine.NineNineOutsideCenterConjugator
public import Stellmacher.SectionNine.NineNineTerminalIntersectionNormality

/-!
# A neighbor mover centralizing the retained transvection displacement

For an actual terminal module of order thirty-two with the wreath core
quotient and backward intersection of order eight, retain a first-module
actor with full displacement order two and quotient displacement order two.
There is an element of the middle stabilizer centralizing that literal
displacement and moving the terminal vertex to the backward vertex.

The invariant-four transvection geometry places the line inside the
intersection and outside the middle center. The exact intersection is
an elementary group of order eight, contains that center, and is normalized
by the middle stabilizer. The established outside-center conjugator corrects
a neighbor mover by a middle-core element to fix the selected line.

This is the centralizing-neighbor assertion following Stellmacher (9.10)(6),
printed p.58, for the retained cyclic displacement. Actual coatom or supplied
path transvection producers furnish its order and index assumptions. Any
identification with the full initial-center commutator is kept separate.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_transvection_centralizing_neighbor
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hUcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^5)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2TwoWreathC2)
    (hIcard : Nat.card (VAt ctx.Γ ctx.criticalPath.a' ⊓ VAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) : Subgroup G) = 2^3)
    (actor : GAt ctx.Γ ctx.criticalPath.a')
    (hactorFirst : (actor:G) ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hcard : Nat.card (⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers (actor:G)⁆ : Subgroup G) = 2)
    (hindex : QuotientCardEq
      (⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers (actor:G)⁆ ⊔ ZAt ctx.Γ ctx.criticalPath.a')
      (ZAt ctx.Γ ctx.criticalPath.a') 2) :
    ∃ y : G,
      y ∈ GAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ∧
      y ∈ Subgroup.centralizer
        ((⁅VAt ctx.Γ ctx.criticalPath.a',Subgroup.zpowers (actor:G)⁆ : Subgroup G) : Set G) ∧
      ctx.Γ.act y ctx.criticalPath.a' = ctx.criticalPath.path
        ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let I := VAt Γ cp.a' ⊓ VAt Γ
    (cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
  let R := ⁅VAt Γ cp.a',Subgroup.zpowers (actor:G)⁆
  have hshort : 1 < cp.length := by change 3 < cp.length at hb; omega
  have hgeometry := nine_ten_transvection_displacement_intersection_geometry
    ctx hb hUcard hmodel hIcard actor hactorFirst hindex
  obtain ⟨hZI,hIQ,hPI⟩ := nine_nine_terminal_intersection_core_normalized ctx hshort
  let _ : IsElementaryAbelian 2 (VAt Γ cp.a') :=
    (nine_three_second_extraction_inputs ctx.toLocalContext hshort).2.2.1
  have hIelem : IsElementaryAbelian 2 I := by
    refine {
      toIsMulCommutative := Subgroup.le_centralizer_iff_isMulCommutative.mp
        ((inf_le_left.trans (Subgroup.le_centralizer_iff_isMulCommutative.mpr
          (inferInstance : IsMulCommutative (VAt Γ cp.a')))).trans
            (Subgroup.centralizer_le inf_le_left))
      exponent_dvd_p := ?_ }
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro point
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (A := VAt Γ cp.a') (point:G) point.property.1)
  exact nine_nine_outside_center_centralizing_conjugator ctx hshort I hIcard hIelem
    hZI hIQ hPI R hcard hgeometry.1 hgeometry.2

end Stellmacher.SectionNine
