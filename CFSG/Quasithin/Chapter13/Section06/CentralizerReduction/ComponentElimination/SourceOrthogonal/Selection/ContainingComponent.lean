module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentModules
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Orbits
public import Theory.Quasithin.Rank

/-!
# The containing C-component supplied by 1.2.4

Apply the actual local-component lifting theorem inside C_G(v). Its Sylow
subgroup is the restriction of Tᵥ, and all subgroup inclusions are transported
through the literal subtype map. The resulting ambient K₊ contains K and is
normal relative to C_G(v), without asserting normality in G.

The earlier universal A.3.12 containment and A.3.8 orbit alternatives remain
explicit, as permitted by the Chapter 13 source contract. This module proves
their application hypotheses. It does not identify this K₊ with the action
image K⁺, or assume that K = K₊.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.2.4, printed p.505, and the final paragraph of 13.6.23, printed p.933.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
open ComponentSelection
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The source containing component and its relative normality, from genuine 1.2.4. -/
theorem exists_containing_component {𝒦 : GroupClass.{u}}
    (hA312 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ (T : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents T →
      ∃! D : Subgroup X, D.IsCComponent ∧ B ≤ D)
    (hA38 : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK 𝒦 X → pCore 2 X = ⊥ → ∀ D : Subgroup X, D.IsCComponent →
      D.Normal ∨ (normalizer (D : Set X)).index = 2 ∧
        Chapter1.Section02.NonnormalCComponentModel D)
    (K L T : Subgroup G) (z v : G)
    (hlocal : IsSQTK 𝒦 (Gv v))
    (hSyl : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hK : K ∈ Yz L T z v)
    (hn : Tv T v ≤ normalizer (K : Set G)) :
    ∃ D : Subgroup G, D ∈ Chapter1.cComponentsIn (Gv v) ∧ K ≤ D ∧
      Gv v ≤ normalizer (D : Set G) := by
  have hQ : IsSQTK 𝒦 (Gv v ⧸ pCore 2 (Gv v)) := by
    refine ⟨?_, hlocal.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hlocal.stronglyQuasithin p hp ho)
  obtain ⟨S, hS⟩ := hSyl
  have hTS : (Tv T v).subgroupOf (Gv v) = (S : Subgroup (Gv v)) := by
    rw [← hS]
    exact comap_map_eq_self_of_injective (Gv v).subtype_injective _
  have hKS : K.subgroupOf (Gv v) ∈ Chapter1.L (Gv v) S := by
    rw [← hTS]
    exact (Chapter1.mem_LIn_iff_subgroupOf inf_le_right hK.1.1).mp hK.1
  have hSN : (S : Subgroup (Gv v)) ≤ normalizer (K.subgroupOf (Gv v) : Set _) := by
    rw [← hTS, ← subgroupOf_normalizer_eq hK.1.1]
    exact comap_mono hn
  obtain ⟨D, hD, hKD, _, hDn⟩ :=
    Chapter1.Section02.lemma_1_2_4_containment_normality_of_A_3_12_A_3_8
      hA312 hA38 hQ S hKS
  let A := D.map (Gv v).subtype
  have hAG : A ≤ Gv v := map_subtype_le D
  have he : A.subgroupOf (Gv v) = D :=
    comap_map_eq_self_of_injective (Gv v).subtype_injective D
  refine ⟨A, ⟨hAG, he.symm ▸ hD⟩, ?_, ?_⟩
  · have hh := map_mono (f := (Gv v).subtype) hKD
    rwa [map_subgroupOf_eq_of_le hK.1.1] at hh
  · apply (normal_subgroupOf_iff_le_normalizer hAG).mp
    rw [he]
    exact hDn hSN

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.Selection
