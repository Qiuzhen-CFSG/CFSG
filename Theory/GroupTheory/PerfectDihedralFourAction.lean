module

public import GorensteinWalter.GWLemma21Trichotomy
public import Theory.GroupTheory.PerfectSmallNormalizer

/-!
# Nontrivial odd action on four-groups in perfect dihedral-Sylow groups

A perfect finite group has no proper subgroup of index at most four.
Consequently only the first branch of Gorenstein--Walter Lemma 2.1 can
occur. Every four-group then has a normalizer element whose square acts
nontrivially on it. No prescribed matrix coordinates or four-group fusion
class is needed.

This supplies the normalizer action used in the quadratic semilinear PSL₂
four-group centralizer calculation. Source: Gorenstein--Walter, Part I,
Lemma 2.1, as proved in `GWLemma21Trichotomy`.
-/

public section
open Subgroup GorensteinWalter
namespace Theory.GroupTheory

/-- Every four-group in a perfect finite group with dihedral Sylow
2-subgroups has a normalizer action not annihilated by squaring. -/
theorem perfect_dihedral_four_normalizer_action
    {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]
    (hdihedral : HasDihedralSylowTwo G) (A : Subgroup G) (hA : IsKleinFour A) :
    ∃ n ∈ normalizer (A : Set G), n ^ 2 ∉ centralizer (A : Set G) := by
  let : Group.IsPerfect (⊤ : Subgroup G) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv (G := G)).symm.toMonoidHom)
      (Subgroup.topEquiv (G := G)).symm.surjective
  have hsmall : ∀ N : Subgroup G, N.index ≤ 4 → N = ⊤ := by
    intro N hN
    exact top_unique ((perfect_le_normalCore_of_index_le_four ⊤ N hN).trans N.normalCore_le)
  have hno2 : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 2 := by
    rintro ⟨N, _, hi⟩
    have h := hsmall N (by omega)
    rw [h, index_top] at hi
    omega
  have hno4 : ¬ ∃ N : Subgroup G, N.Normal ∧ N.index = 4 := by
    rintro ⟨N, _, hi⟩
    have h := hsmall N (by omega)
    rw [h, index_top] at hi
    omega
  obtain h | h | h := gw_lemma_2_1 hdihedral
  · have hAp : IsPGroup 2 A := IsPGroup.of_card (n := 2) (by
      rw [hA.card_four]; decide)
    obtain ⟨T, hAT⟩ := hAp.exists_le_sylow
    have hn := h.2.2 T A hAT hA
    by_contra! hall
    exact hn.2 (fun n hn => ⟨hn, hall n hn⟩)
  · exact (hno2 h.1).elim
  · exact (hno4 h.1).elim

end Theory.GroupTheory
