module

public import CFSG.Quasithin.Chapter1.Section02.Uniqueness
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ComponentOrbitBound
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow

/-!
# Nonsolvable uniqueness from the noncentral structural branch

A.3.7 and the odd-rank argument already give the normal-or-index-two
alternative from the genuine noncentral branch of A.3.6. This is exactly
the orbit information used by Theorem 1.2.7. Condition (E) supplies its
characteristic-two input through the proved Lemma 1.1.4(6).

The theorem retains the actual ambient group, Sylow subgroup and chosen
local component, and supplies every uniqueness conclusion. Universal
A.3.12 containment and the noncentral structural theorem remain genuine
earlier inputs; no component-model assertion is assumed or discarded.
The full A.3.8 classification and the older uniqueness API are unchanged.

Source: Aschbacher–Smith, combined manuscript, A.3.7–8, pp.45–46;
Lemma 1.1.4(6), pp.501–502; Theorem 1.2.7, p.506.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Full source uniqueness from A.3.12 containment and noncentral A.3.6.
The latter has the existing source producer
`qt-a03-noncentral-fitting-structure`; the actual chosen local component
and its Sylow orbit are retained throughout the conclusion. -/
theorem nonsolvable_uniqueness_of_noncentral_structure
    {κ : GroupClass.{u}}
    (hContainment : ∀ (X : Type u) [Group X] [Finite X],
      IsSQTK κ X → pCore 2 X = ⊥ → ∀ (S : Sylow 2 X) (B : Subgroup X),
      B ∈ ChapterA.Section03.localCComponents S →
      ∃! K : Subgroup X, K.IsCComponent ∧ B ≤ K)
    (h36 : ChapterA.Section03.CComponentCommutation.NoncentralStructureInput κ)
    (hG : IsSimpleQTKE κ G) (T : Sylow 2 G) {L : Subgroup G}
    (hL : L ∈ LStar G (T : Subgroup G)) : NonsolvableUniquenessConclusion T L := by
  apply nonsolvable_uniqueness_of_orbit_inputs hContainment
    (fun X _ _ hX hO B hB =>
      ChapterA.Section03.ComponentOrbitBound.normal_or_index_two_of_noncentral_structure
        h36 hX hO hB)
    (fun X _ _ hX S => Chapter1.lemma_1_1_4_6 S (hX.evenCharacteristic S)) hG T hL

end CFSG.Quasithin.Chapter1.Section02
