module

public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete

/-!
# Source containment and normality of a local C-component

A.3.12 supplies the unique containing component in the actual two-core
quotient. The proved orbit bound from noncentral A.3.6 gives normality or
two conjugates. The original Sylow subgroup normalizes the selected local
component, so it normalizes its unique containing component and rules out
an orbit of length two. No component-model list is needed for this deduction.

Source: Aschbacher–Smith 1.2.4, printed p.505, using A.3.8 and A.3.12.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original 1.2.4 containment and normality, retaining only genuine A/C. -/
theorem lemma_1_2_4_containment_normality_of_theoremsAC
    (hA : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple X)
    (hC : ∀ (X : Type u) [Group X] [Finite X],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple X)
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ L G S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G)) :
    ∃! K : Subgroup G, K.IsCComponent ∧ B ≤ K ∧ K.Normal := by
  obtain ⟨K, ⟨hK,hBK⟩,hu⟩ :=
    lemma_1_2_4_containment_of_A_3_12 (containment_of_theoremsAC hA hC) hQ S hB
  have horbit : K.Normal ∨ (normalizer (K : Set G)).index = 2 := by
    let := pCore_isNilpotent (p := 2) (G := G)
    have hbar := ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
      (ChapterA.Section03.CComponentCommutation.noncentralStructureInput KnownSimple.IsKnownSimple)
      hQ (pCore_quotient_pCore_eq_bot 2) (hK.map_quotient (pCore 2 G))
    rcases hbar with hn | hi
    · exact Or.inl (cComponent_normal_of_quotient_normal hK (pCore 2 G) hn)
    · exact Or.inr ((cComponent_normalizer_index_quotient hK (pCore 2 G)).symm.trans hi)
  refine ⟨K, ⟨hK,hBK,?_⟩, fun D hD => hu D ⟨hD.1,hD.2.1⟩⟩
  exact cComponent_normal_of_unique_of_orbit_two hK hBK
    (fun D hD hBD => hu D ⟨hD,hBD⟩) S hSB horbit

/-- The full known-simple catalogue discharges both earlier universal inputs. -/
theorem lemma_1_2_4_containment_normality_source
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ L G S)
    (hSB : (S : Subgroup G) ≤ normalizer (B : Set G)) :
    ∃! K : Subgroup G, K.IsCComponent ∧ B ≤ K ∧ K.Normal :=
  lemma_1_2_4_containment_normality_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)) hQ S hB hSB

end CFSG.Quasithin.Chapter1.Section02
