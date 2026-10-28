module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Embeddings
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.CComponentCommutation
/-!
# Relative normality in the model-valued local embedding theorem

The actual A.3.7 commutation theorem and the SQTK odd-rank bound limit
C-component orbits to at most two. A unique containing component of a
Sylow-invariant local component is therefore normal. This discharges the
A.3.8 input in the model-valued 1.2.4 application; the genuine universal
A.3.12 classification remains explicit. The older public interface is
preserved in its original module.
Source: Aschbacher–Smith 1.2.4, p.504, used in C.5.13, p.162.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
open Chapter1
universe u
/-- The original model-valued 1.2.4 conclusion, with its relative-normality
step supplied by the proved source orbit bound. -/
theorem lemma_1_2_4_of_A_3_12 {G : Type u} [Group G] [Finite G]
    {𝒦 : GroupClass.{u}}
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents T → A312Conclusion B)
    (hQ : IsSQTK 𝒦 (G ⧸ pCore 2 G))
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ L G S) :
    ∃ K : Subgroup G, K.IsCComponent ∧ B ≤ K ∧
      (∀ D : Subgroup G, D.IsCComponent → B ≤ D → D = K) ∧
      A312Embedding (B.map (QuotientGroup.mk' (pCore 2 G)))
        (K.map (QuotientGroup.mk' (pCore 2 G))) ∧
      ((S : Subgroup G) ≤ normalizer (B : Set G) → K.Normal) := by
  let := pCore_isNilpotent (p := 2) (G := G)
  let := mem_L_isPerfect hB
  let q := QuotientGroup.mk' (pCore 2 G)
  have hBq : B.map q ∈ ChapterA.Section03.localCComponents
      (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))) := by
    simpa only [Sylow.coe_mapSurjective] using mem_L_map_twoCore_mem_localCComponents hB
  obtain ⟨Kbar, hKbar, hBKbar, hu, hemb⟩ := hA312 _ hQ (pCore_quotient_pCore_eq_bot 2)
    (S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 G))) _ hBq
  obtain ⟨K, hK, hBK, he⟩ := exists_cComponent_lift_containing_map (pCore 2 G) hKbar hBKbar
  have unique : ∀ D : Subgroup G, D.IsCComponent → B ≤ D → D = K := by
    intro D hD hBD
    apply hD.eq_of_map_quotient_eq hK (pCore 2 G)
    exact (hu _ (hD.map_quotient _) (map_mono hBD)).trans he.symm
  refine ⟨K, hK, hBK, unique, he.symm ▸ hemb, ?_⟩
  intro hSB
  apply cComponent_normal_of_unique_of_orbit_two hK hBK unique S hSB
  apply cComponent_normal_or_index_two_of_quotient hK (pCore 2 G)
  exact ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
    (ChapterA.Section03.CComponentCommutation.noncentralStructureInput 𝒦)
    hQ (pCore_quotient_pCore_eq_bot 2) (hK.map_quotient _)

end CFSG.Quasithin.Chapter1.Section02
