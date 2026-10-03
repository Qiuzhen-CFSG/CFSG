module

public import Stellmacher.SectionNine.NineTenNormalizedResidualWitnesses
public import Stellmacher.SectionNine.NineTenSelectedTransvectionActor
public import Stellmacher.SectionNine.NineTenResidualSupportControl
public import Stellmacher.SectionNine.NineTenConjugatedCenterSupport
public import Stellmacher.SectionNine.NineNextTransvectionFactor

/-!
# A selected support for both actual extractions in (9.10)

For the supplied normalized context and both actual geometric data packets,
select a canonical transvection factor in the literal faithful action on
terminal V modulo its center. The image of the retained terminal neighbor
center lies in the join of this factor's support and the penultimate-center
image. The action, normality and elementary-module instances, kernel, faithful
Section One hypotheses, and selected actor remain in the conclusion.

First choose an initial-center transvection outside the retained first coatom;
this follows from center noncommutation and the first coatom's centralization.
The actual second coatom gives its transvection displacement. The uniform
first-extraction residual bound places the actual first conjugator image in
this actor's odd-core commutator and hence its canonical factor. The exact
quotient-action formula then gives the center-image support containment.

This proves the selected-support assertion following Stellmacher (9.10)(3)--(4),
printed p.57. Both extractions are inputs and stay fixed throughout: there is
no new normalization, no replacement terminal neighbor, and no identification
of the generic extraction group with the source's smaller center-generated E.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_ten_selected_factor_support
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hterminalNot : ¬ ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (hfirstNot : ¬ ZAt ctx.Γ ctx.criticalPath.firstStep ≤ VAt ctx.Γ ctx.criticalPath.a')
    (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
      (VAt ctx.Γ ctx.criticalPath.a') E A0 actor)
    (hnew : ctx.Γ.act data.x⁻¹ second = ctx.criticalPath.a)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcenters : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥)
    (firstActor : G) (firstE firstA0 : Subgroup G)
    (firstData : NineThreeGeometricData ctx.Γ ctx.criticalPath.a'
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)
      (VAt ctx.Γ ctx.criticalPath.firstStep) firstE firstA0 firstActor)
    (hfirstNew : ctx.Γ.act firstData.x⁻¹
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) =
        neighbor)
    (hfirstActors : ∀ b : G, b ∈ VAt ctx.Γ ctx.criticalPath.firstStep → b ∉ firstA0 →
      twoResidualIn firstE ≤ ⁅twoResidualIn firstE, Subgroup.zpowers b⁆) :
    let penultimate := ctx.criticalPath.path
      ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    ∃ selected : GAt ctx.Γ ctx.criticalPath.a',
      (selected : G) ∈ ZAt ctx.Γ ctx.criticalPath.a ∧
      (selected : G) ∉ GAt ctx.Γ neighbor ∧
      (selected : G) ∉ QAt ctx.Γ ctx.criticalPath.a' ∧
      ∃ hN : ((ZAt ctx.Γ ctx.criticalPath.a').subgroupOf
        (VAt ctx.Γ ctx.criticalPath.a')).Normal,
        let _ := hN
        let P := GAt ctx.Γ ctx.criticalPath.a'
        let U := VAt ctx.Γ ctx.criticalPath.a'
        let Z := (ZAt ctx.Γ ctx.criticalPath.a').subgroupOf U
        ∃ hW : IsElementaryAbelian 2 (U ⧸ Z),
          let _ := hW
          ∃ action : P →* MulAut (U ⧸ Z),
            let D : Subgroup action.range :=
              ⁅SectionOne.oddCore action.range, Subgroup.zpowers (action.rangeRestrict selected)⁆ ⊔
                Subgroup.zpowers (action.rangeRestrict selected)
            (∀ mover : P, ∀ point : U,
              action mover (QuotientGroup.mk' Z point) = QuotientGroup.mk' Z
                ⟨(mover : G) * (point : G) * (mover : G)⁻¹,
                  (Subgroup.mem_normalizer_iff.mp
                    (stabilizer_le_normalizer_v ctx.Γ ctx.criticalPath.a' mover.property)
                      point).mp point.property⟩) ∧
              action.ker = pCore 2 P ∧
              SectionOne.Hypotheses action.range (U ⧸ Z) ∧
              SectionOne.IsOneSevenFactor (V := U ⧸ Z) D ∧
              ((ZAt ctx.Γ neighbor).subgroupOf U).map (QuotientGroup.mk' Z) ≤
                commutatorAction D (U ⧸ Z) ⊔
                  ((ZAt ctx.Γ penultimate).subgroupOf U).map (QuotientGroup.mk' Z) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hindex : QuotientCardEq (VAt Γ cp.a') (VAt Γ cp.a' ⊓ GAt Γ cp.a) 2 := by
    have hcoatom : A0 = VAt Γ cp.a' ⊓ GAt Γ cp.a := by
      simpa only [hnew] using data.coatom_eq
    change Nat.card (VAt Γ cp.a') = 2 * Nat.card (VAt Γ cp.a' ⊓ GAt Γ cp.a : Subgroup G)
    rw [← hcoatom]
    exact data.coatom_card
  obtain ⟨selected, hselected, hselectedNotGroup, hselectedNotCore, _, hdisplacement⟩ :=
    nine_ten_initial_transvection_outside_first_coatom ctx hb hterminalNot hfirstNot
      neighbor hneighbor hcenters hindex
  have hfirstContain := (lemma_seven_four ctx.sectionSeven Γ cp).first_containment
  have hselectedP : selected ∈ GAt Γ cp.a' := hfirstContain.2 (hfirstContain.1 hselected)
  let selectedP : GAt Γ cp.a' := ⟨selected, hselectedP⟩
  obtain ⟨alignment, _, halign⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  obtain ⟨hN, hW, action, hformula, hkernel, _, _, _, hyp, hfactor⟩ :=
    nine_next_transvection_factor ctx hb cp.a' ⟨alignment, halign⟩ selectedP hdisplacement
  let _ := hN
  let _ := hW
  have hselectedFirstCoatom : selected ∉ firstA0 := by
    intro hmem
    have hcoatom := firstData.coatom_eq
    change firstA0 = VAt Γ cp.firstStep ⊓ GAt Γ (Γ.act firstData.x⁻¹ penultimate) at hcoatom
    rw [hfirstNew] at hcoatom
    exact hselectedNotGroup (hcoatom ▸ hmem).2
  have hkernel' : pCore 2 (GAt Γ cp.a') ≤ action.rangeRestrict.ker :=
    ((MonoidHom.ker_rangeRestrict action).trans hkernel).symm.le
  have hresidual := nine_ten_extracted_residual_image_le_actor_commutator ctx.toLocalContext
    cp.a' penultimate (VAt Γ cp.firstStep) firstE firstA0 firstActor firstData hfirstActors
    action.rangeRestrict action.rangeRestrict_surjective hkernel' selectedP
    (hfirstContain.1 hselected) hselectedFirstCoatom
  let D : Subgroup action.range :=
    ⁅SectionOne.oddCore action.range, Subgroup.zpowers (action.rangeRestrict selectedP)⁆ ⊔
      Subgroup.zpowers (action.rangeRestrict selectedP)
  have hresidualD : ((twoResidualIn firstE).subgroupOf (GAt Γ cp.a')).map
      action.rangeRestrict ≤ D := hresidual.trans le_sup_left
  have hpen := (nine_three_initial_extraction_inputs ctx.toLocalContext hb).1
  have hsupport := nine_ten_conjugated_center_image_le_support_join Γ cp.a' penultimate
    hpen (VAt Γ cp.firstStep) firstE firstA0 firstActor firstData action hformula D hresidualD
  rw [hfirstNew] at hsupport
  exact ⟨selectedP, hselected, hselectedNotGroup, hselectedNotCore,
    hN, hW, action, hformula, hkernel, hyp, hfactor, hsupport⟩

end Stellmacher.SectionNine
