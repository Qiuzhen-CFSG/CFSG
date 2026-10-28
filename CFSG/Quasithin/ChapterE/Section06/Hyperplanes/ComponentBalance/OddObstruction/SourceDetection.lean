module
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.SourceLocal
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction.Extraction

/-!
# The original E.6.19 detected component with earlier inputs discharged

A subgroup with nontrivial two-core embeds in that core's two-local normalizer.
Its actual two-core quotient is therefore SQTK, so the proved 1.2.1(3) orbit
theorem applies to each C-component. SourceLocal supplies all Chapter 1.1
inheritance facts. The existing quotient detector then produces an ordinary
component with the literal nontrivial action-centralizer odd core.

No corank-two restriction, model, odd-core inspection, or component witness
is assumed here. Those later inspections consume this original detector.
Source: Aschbacher–Smith, E.6.19, printed p.252; 1.2.1(3), p.504.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {T : Sylow 2 G} {M V A U : Subgroup G}

/-- Supply the normal-or-two-conjugates theorem in every original H-overgroup. -/
theorem source_cComponent_orbits (h : HypothesisE61 K T M V)
    {H : Subgroup G} (hH : H ∈ Chapter1.H G) {B : Subgroup H} (hB : B.IsCComponent) :
    B.Normal ∨ (normalizer (B : Set H)).index = 2 := by
  let R := H.pCoreIn 2
  have hHN : H ≤ normalizer (R : Set G) := H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hs : IsSQTK K H :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hHN)).mp
      ((h.simpleQTKE.twoLocal_sqtk ⟨R,hH,isPGroup_pCoreIn 2 H,rfl⟩).subgroup
        (H.subgroupOf (normalizer (R : Set G))))
  have hq : IsSQTK K (H ⧸ pCore 2 H) := by
    refine ⟨?_,hs.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
      (hs.stronglyQuasithin p hp ho)
  exact Chapter1.Section02.proposition_1_2_1_three_orbit_source hq hB

/-- The literal E.6.19 detector now needs only its original source hypotheses. -/
theorem source_detectedComponent
    (h : HypothesisE61 KnownSimple.IsKnownSimple T M V)
    (hA : A ∈ obstructionFamily M V) (hAU : A ≤ U) (hUV : U ≤ V)
    (hfail : ¬ oddCentralizer U ≤ oddCentralizer A) :
    ∃ L : Subgroup G, DetectedComponent A U V L := by
  exact Extraction.exists_detectedComponent h (source_earlierLocalFacts h)
    (fun _ hH _ hB => source_cComponent_orbits h hH hB) hA hAU hUV hfail
end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.OddObstruction
