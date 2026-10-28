module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.NormalClosure
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalLonger.OriginalResidual

/-!
# The original residual action on the mixed subgroup

Retain the actual graph, critical path, normalized extractions and nontrivial
mixed subgroup I from the large-center source construction. The extracted
full Baumann commutator is the next vertex's entire two-residual. That
residual centralizes I and normally generates O²(G), while the normal closure
of I contains O²(G). The initial vertex's residual must therefore move I:
otherwise both original residuals, hence O²(G), would centralize I.

This is a faithful-pair constraint on the source configuration. It retains
the central-next/moving-initial orientation of (7.5), and neither asserts
subnormality in C(I) nor assumes the desired amalgam classification.

Source: Stellmacher (9.3), Journal of Algebra 190 (1997), pp.49--50,
and Aschbacher--Smith F.6.6--8,13. The application is the actual cubic
Goldschmidt pair occurring in F.1.12 and F.6.5.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterF
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}
open Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven
open Stellmacher.SectionsFiveToSeven.CosetGraphContext
open Stellmacher.SectionsFiveToSeven.SevenSix Stellmacher.SectionNine

/-- The same source witnesses retain both normal closures and the nontrivial
action of the original initial residual on the actual mixed subgroup. -/
theorem IsGoldschmidtTriple.exists_mixed_original_residual_action
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hg₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hg₂ : generalizedFitting G₂ = pCore 2 G₂)
    (Γ : CosetGraphContext.{u,u} G (G₁ ⊓ G₂) G₁ G₂) (cp : CriticalPath Γ)
    (hcomm : ⁅z Γ cp.a,z Γ cp.a'⁆ = ⊥)
    (hlarge : 4 < Nat.card (ZAt Γ cp.a)) :
    let ctx : SectionNineLocalContext G (G₁ ⊓ G₂) G₁ G₂ :=
      ⟨h.sectionSeven_of_characteristic_two hcore hg₁ hg₂, Γ, cp, hcomm⟩
    ∃ first : LocalLonger.FirstConfigurationData ctx,
      ∃ second : LocalLonger.SecondConfigurationData ctx first,
        ∃ config : LocalLonger.NormalizedGeometry ctx first second,
          LocalLonger.MixedCentralizerData ctx first second config ∧
          LocalLonger.extractedFullCommutator ctx first second config =
            twoResidualIn (GAt Γ cp.firstStep) ∧
          twoResidualIn (GAt Γ cp.firstStep) ≤
            centralizer (LocalLonger.mixedSubgroup ctx first second config : Set G) ∧
          normalClosure (LocalLonger.extractedFullCommutator ctx first second config : Set G) =
            pResidual 2 G ∧
          pResidual 2 G ≤ normalClosure
            (LocalLonger.mixedSubgroup ctx first second config : Set G) ∧
          ¬ twoResidualIn (GAt Γ cp.a) ≤
            centralizer (LocalLonger.mixedSubgroup ctx first second config : Set G) := by
  have hres (P : Subgroup G) : twoResidualIn P = (pResidual 2 P).map P.subtype := by
    rw [twoResidualIn, twoResidualAmbient, Stellmacher.SectionThree.twoResidualSubgroup_eq_hktPResidual']
    congr 1
    apply le_antisymm
    · exact BenderSuzuki.External.hktPResidual_le _ inferInstance (isPGroup_quotient_pResidual 2)
    · exact sInf_le ⟨BenderSuzuki.External.hktPResidual_normal,
        BenderSuzuki.External.hktPResidual_quotient_isPGroup⟩
  have hnext : normalClosure (twoResidualIn (GAt Γ cp.firstStep) : Set G) =
      pResidual 2 G := by
    change normalClosure (twoResidualIn (Γ.stabilizer cp.firstStep) : Set G) = _
    rcases cp.edge_stabilizers_are_P with hp | hp
    · rw [hp.2,hres]
      exact IsGoldschmidtTriple.normalClosure_left_residual h.symm hcore hg₂ hg₁
    · rw [hp.2,hres]
      exact IsGoldschmidtTriple.normalClosure_left_residual h hcore hg₁ hg₂
  let ctx : SectionNineLocalContext G (G₁ ⊓ G₂) G₁ G₂ :=
    ⟨h.sectionSeven_of_characteristic_two hcore hg₁ hg₂, Γ, cp, hcomm⟩
  obtain ⟨first,second,config,data,heq,hcent⟩ :=
    h.exists_original_residual_mixed_centralizer hcore hg₁ hg₂ Γ cp hcomm hlarge
  have hn : normalClosure (LocalLonger.extractedFullCommutator ctx first second config : Set G) =
      pResidual 2 G :=
    (congrArg (fun U : Subgroup G => normalClosure (U : Set G)) heq).trans hnext
  have hi : pResidual 2 G ≤ normalClosure
      (LocalLonger.mixedSubgroup ctx first second config : Set G) :=
    IsGoldschmidtTriple.twoResidual_le_normalClosure_of_nontrivial_two_subgroup h hcore hg₁ hg₂ _ data.two_group data.nontrivial
  have hmove : ¬ twoResidualIn (GAt Γ cp.a) ≤
      centralizer (LocalLonger.mixedSubgroup ctx first second config : Set G) := by
    intro hc
    apply IsGoldschmidtTriple.two_subgroup_not_centralize_twoResidual h hcore hg₁ hg₂ _ data.two_group data.nontrivial
    apply le_centralizer_iff.mpr
    rw [h.twoResidual_eq_sup]
    change twoResidualIn (Γ.stabilizer cp.a) ≤ _ at hc
    have hcn : twoResidualIn (Γ.stabilizer cp.firstStep) ≤
        centralizer (LocalLonger.mixedSubgroup ctx first second config : Set G) := hcent
    rcases cp.edge_stabilizers_are_P with hp | hp
    · rw [hp.1,hres] at hc
      rw [hp.2,hres] at hcn
      exact sup_le hc hcn
    · rw [hp.1,hres] at hc
      rw [hp.2,hres] at hcn
      exact sup_le hcn hc
  exact ⟨first,second,config,data,heq,hcent,hn,hi,hmove⟩
end CFSG.Quasithin.ChapterF
