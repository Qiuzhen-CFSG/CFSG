module
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.Source
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Source containment for an index-at-most-two Sylow subgroup

The original index-two local-component lemma gives a unique ambient
C-component containing a member of the local family. Its universal A.3.3(7)
input is the proved C-component commutator dichotomy, and A.3.9(1) follows
from the completed Theorems A and C. At index one, the local family is the
full-Sylow family and A.3.12 gives the same containment.

The component orbit has size at most two. Its normalizer therefore contains
the ambient two-residual, so every two-perfect subgroup normalizes the
selected component. This is the precise 1.2.5 and 1.2.1(3) step used in the
exceptional branch of Aschbacher--Smith 13.5.15, printed pp.920--921.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Original 1.2.5, including the index-one case, with all earlier A/C
inputs discharged at the full known-simple carrier boundary. -/
theorem index_le_two_local_component_source
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    (S : Sylow 2 G) {R L : Subgroup G}
    (hRS : R ≤ S) (hi : R.relIndex (S : Subgroup G) ≤ 2)
    (hL : L ∈ Chapter1.L G R) :
    ∃! K : Subgroup G, K.IsCComponent ∧ L ≤ K := by
  have hpos : 0 < R.relIndex (S : Subgroup G) :=
    Nat.pos_of_ne_zero (R.subgroupOf (S : Subgroup G)).index_ne_zero_of_finite
  have hindex : R.relIndex (S : Subgroup G) = 1 ∨
      R.relIndex (S : Subgroup G) = 2 := by omega
  rcases hindex with hindex | hindex
  · have hRS' : R = (S : Subgroup G) :=
      le_antisymm hRS (Subgroup.relIndex_eq_one.mp hindex)
    subst R
    exact lemma_1_2_4_containment_of_A_3_12
      (containment_of_theoremsAC
        (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
        (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X)))
      hQ S hL
  · exact lemma_1_2_5_of_A_3_3_7_of_A_3_9
      (fun X _ _ B D hB => hB.commutator_le_radical_or_eq_iSup_conjugates D)
      (fun X _ _ hX hO =>
        ChapterA.Section03.SourceComponents.generation
          (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
          (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
            (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y)))
          hX hO)
      hQ S hRS hindex hL

/-- The ambient two-residual normalizes each C-component in the source SQTK
situation, since its conjugacy orbit has size one or two. -/
theorem twoPerfect_normalizes_cComponent_source
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    {K A : Subgroup G} (hK : K.IsCComponent) (hA : IsPPerfect 2 A) :
    A ≤ normalizer (K : Set G) := by
  have hres : A ≤ pResidual 2 G := le_pResidual_of_isPPerfect A hA
  rcases proposition_1_2_1_three_orbit_source hQ hK with hn | hi
  · let _ := hn
    rw [normalizer_eq_top]
    exact le_top
  · let N := normalizer (K : Set G)
    let : N.Normal := N.normal_of_index_eq_two hi
    have hcard : Nat.card (G ⧸ N) = 2 := by
      change N.index = 2 at hi
      simpa only [N.index_eq_card] using hi
    have htwo : IsPGroup 2 (G ⧸ N) :=
      IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hcard)
    exact hres.trans (sInf_le ⟨inferInstance, htwo⟩)

/-- The component selected at index at most two is normalized by every
two-perfect ambient subgroup, including the actual residual in 13.5.15. -/
theorem index_le_two_local_component_with_normalizers_source
    (hQ : IsSQTK KnownSimple.IsKnownSimple (G ⧸ pCore 2 G))
    (S : Sylow 2 G) {R L : Subgroup G}
    (hRS : R ≤ S) (hi : R.relIndex (S : Subgroup G) ≤ 2)
    (hL : L ∈ Chapter1.L G R) :
    ∃! K : Subgroup G,
      K.IsCComponent ∧ L ≤ K ∧
        ∀ A : Subgroup G, IsPPerfect 2 A → A ≤ normalizer (K : Set G) := by
  obtain ⟨K, hK, hu⟩ := index_le_two_local_component_source hQ S hRS hi hL
  refine ⟨K, ⟨hK.1, hK.2, fun A hA =>
    twoPerfect_normalizes_cComponent_source hQ hK.1 hA⟩, ?_⟩
  intro J hJ
  exact hu J ⟨hJ.1, hJ.2.1⟩

end CFSG.Quasithin.Chapter1.Section02
