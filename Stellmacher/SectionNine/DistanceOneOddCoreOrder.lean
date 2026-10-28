module
public import Stellmacher.SectionNine.DistanceOneInitialCenterOrder
public import Stellmacher.SectionNine.DistanceOneRelativeOddOrder
public import Theory.Representation.FaithfulSixteenPGroupNine
/-!
# The faithful initial odd core has order nine

At critical distance one, the actual faithful quotient's odd core is an odd
prime-power group by the local quotient residual calculation. The relative
exceptional action supplies its commutator subgroup of order nine and the
initial center of order sixteen. Faithfulness of the supplied quotient action
on that center embeds the odd core in `GL₄(2)`. The three-part divisibility
then forces the prime to be three and the odd core to have order nine.
The commutator subgroup has the same order and is contained in the odd core,
so it equals the odd core.

Source: Stellmacher (9.1), relation (8), Journal of Algebra 190 (1997), p.47,
`refs/files/stellmacher-n-group.pdf`. All subgroup and action instances are
those supplied by the original quotient witness.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_faithful_odd_core_order
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer
        (ZAt ctx.Γ ctx.criticalPath.a : Set G)) (ZAt ctx.Γ ctx.criticalPath.a)) :
    let _ := w.groupX
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    let X := (V.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection
    Nat.card (SectionOne.oddCore w.X) = 9 ∧
      ⁅SectionOne.oddCore w.X,X⁆ = SectionOne.oddCore w.X := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let V := (z Γ cp.a ⊓ stabilizer Γ next) ⊔ (z Γ next ⊓ stabilizer Γ cp.a)
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  let X := (V.subgroupOf P).map w.projection
  let W := SectionOne.oddCore w.X
  let F := ⁅W,X⁆
  change Nat.card W=9 ∧ F=W
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ : IsElementaryAbelian 2 Za := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  let _ : W.Normal := pPrimeCore_normal
  have hFW : F ≤ W := Subgroup.commutator_le_left _ _
  have hFcard : Nat.card F=9 := (distance_one_relative_odd_order ctx hb data w).1
  have h9 : 9 ∣ Nat.card W := hFcard ▸ Subgroup.card_dvd_of_le hFW
  let _ : FaithfulSMul W Za := ⟨by
    intro a b hab
    apply Subtype.ext
    apply w.action_injective
    apply MulEquiv.ext
    intro v
    exact hab v⟩
  obtain ⟨p,hp,_hodd,hWp⟩ := SectionEight.local_quotient_oddCore_is_odd_pGroup
    ctx.sectionSeven Γ cp w
  let _ : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card W=9 := (Representation.card_nine_of_faithful_sixteen_pGroup
    hWp (distance_one_initial_center_card_sixteen ctx hb data w) h9).2
  exact ⟨hcard,Subgroup.eq_of_le_of_card_ge hFW (by rw [hcard,hFcard])⟩
end Stellmacher.SectionNine
