module
public import Stellmacher.SectionNine.DistanceOneImagePreparation
public import Stellmacher.SectionNine.DistanceOneImageMinimality
public import Stellmacher.SectionOne.RelativeExceptionalAction

/-!
# The actual double-SL2 relative action in (9.1)

For any supplied faithful quotient witness on the initial center at critical
distance one, let X be the image of the actual cross-center product and
F=[O₂′(bar G),X]. The relative group F X is isomorphic to SL₂(2)×SL₂(2),
and its odd-core commutator module, expressed on the original center,
has order sixteen.

The genuine graph action setup supplies Section One hypotheses. The actual
image is elementary, has order at least four and measure two; every nontrivial
subgroup has measure at least two. If the full image were quadratic, the
proved source-(5) bound would force its order at most two. The relative
exceptional-action theorem therefore applies the bounded form of (1.6),
retaining the actual odd commutator and inherited action on the center.

This proves Stellmacher (9.1), the group and module calculation in relation
(7), Journal of Algebra190 (1997), p.47, from refs/files/stellmacher-n-group.pdf.
It does not yet assert that the odd-core fixed complement vanishes or that
the whole faithful initial quotient is a wreath product; those are the
subsequent source-(8) calculations.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem distance_one_relative_double_sl2
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
    let X := (V.subgroupOf (GAt ctx.Γ ctx.criticalPath.a)).map w.projection
    let F := ⁅SectionOne.oddCore w.X,X⁆
    Nonempty ((F ⊔ X : Subgroup w.X) ≃* (SL2Two × SL2Two)) ∧
      Nat.card (commutatorAction F (ZAt ctx.Γ ctx.criticalPath.a)) = 16 := by
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
  let F := ⁅SectionOne.oddCore w.X,X⁆
  change Nonempty ((F ⊔ X : Subgroup w.X) ≃* (SL2Two × SL2Two)) ∧
    Nat.card (commutatorAction F Za) = 16
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  let _ : IsElementaryAbelian 2 Za := z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hfirst
  have hsetup := SectionEight.local_quotient_sylow_action_setup ctx.sectionSeven Γ cp w
  have hX := distance_one_image_elementary ctx data w
  have hmeasure := distance_one_image_m_two ctx hb data w
  have hmin : ∀ Y : Subgroup w.X, Y ≤ X → Y ≠ ⊥ →
      SectionOne.m (V := Za) X ≤ SectionOne.m (V := Za) Y := by
    intro Y hYX hYne
    rw [hmeasure.2]
    exact distance_one_image_m_minimal ctx hb data w Y hYX hYne
  have hnon : commutatorAction₂ X Za ≠ ⊥ := by
    intro hquad
    have hsmall := distance_one_quadratic_image_card_le_two ctx hb data w X le_rfl hquad
    have hlarge : 4 ≤ Nat.card X := hmeasure.1
    omega
  exact SectionOne.relative_doubleSL2_of_m_two_nonquadratic hsetup.1 X hX
    hmeasure.1 hmeasure.2 hmin hnon
end Stellmacher.SectionNine
