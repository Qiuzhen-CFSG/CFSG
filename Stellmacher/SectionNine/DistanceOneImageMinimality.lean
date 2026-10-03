module
public import Stellmacher.SectionNine.DistanceOneNoFixedHyperplane
public import Stellmacher.SectionNine.DistanceOneImagePreparation
public import Stellmacher.SectionOne.NontransvectionMinimality
/-!
# Minimum measure for the extracted faithful image

For any faithful quotient witness on the actual initial center of a
length-one extraction, every nontrivial subgroup of the image of the
cross-center product has Section One measure at least two.

The actual image is elementary abelian. Its nontrivial subgroups have no
fixed hyperplane by the source-(2)/(3) centralizer argument. The standing
Section One action hypotheses hold for this same faithful witness, so the
order-two minimizer from (1.5), through NontransvectionMinimality, gives the
bound. No faithful classification or later local conclusion is assumed.

This is the lower bound in Stellmacher (9.1), relation (6), Journal of
Algebra 190 (1997), printed p.47, refs/files/stellmacher-n-group.pdf.
Together with the separate calculation that the whole-image measure is
two, this lower bound gives the source minimum assertion.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_image_m_minimal
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : ctx.criticalPath.length = 1) (data : DistanceOneActionData ctx)
    (w : QuotientModuleWitness (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓ Subgroup.centralizer
        (ZAt ctx.Γ ctx.criticalPath.a : Set G)) (ZAt ctx.Γ ctx.criticalPath.a)) :
    let next := ctx.Γ.act data.x⁻¹ ctx.criticalPath.a
    let V := (z ctx.Γ ctx.criticalPath.a ⊓ stabilizer ctx.Γ next) ⊔
      (z ctx.Γ next ⊓ stabilizer ctx.Γ ctx.criticalPath.a)
    let _ := w.groupX
    let _ := MulDistribMulAction.compHom (ZAt ctx.Γ ctx.criticalPath.a) w.action
    ∀ X : Subgroup w.X, X ≤ (V.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection →
      X ≠ ⊥ → 2 ≤ SectionOne.m (V := ZAt ctx.Γ ctx.criticalPath.a) X := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let next := Γ.act data.x⁻¹ cp.a
  let P := GAt Γ cp.a
  let Za := ZAt Γ cp.a
  let V := (z Γ cp.a ⊓ stabilizer Γ next) ⊔ (z Γ next ⊓ stabilizer Γ cp.a)
  let _ := w.groupX
  let _ := w.finiteX
  let _ := MulDistribMulAction.compHom Za w.action
  change ∀ X : Subgroup w.X, X ≤ (V.subgroupOf P).map w.projection →
      X ≠ ⊥ → 2 ≤ SectionOne.m (V := Za) X
  intro X hX hXne
  have hV := distance_one_image_elementary ctx data w
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ : IsElementaryAbelian 2 Za := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  have hsetup := SectionEight.local_quotient_sylow_action_setup ctx.sectionSeven Γ cp w
  apply SectionOne.m_ge_two_of_no_transvection hsetup.1 _ hV ?_ X hX hXne
  intro Y hY hcard
  apply distance_one_image_fixed_index_ne_two ctx hb data w Y hY
  intro hbot
  simp only [hbot, Subgroup.card_bot] at hcard
  omega
end Stellmacher.SectionNine
