module

public import Theory.GroupTheory.MinimalParabolicGeneration
public import Mathlib.GroupTheory.Sylow

/-!
# Normal subgroups centralizing a Sylow subgroup in a minimal parabolic

A nonnormal Sylow subgroup with a unique maximal overgroup normally generates
the group: otherwise Frattini's argument puts the group inside that maximal
overgroup. Consequently a normal subgroup centralized by the Sylow subgroup
is central in the whole group.

This elementary fact changes the normal first alternative in pushing-up
results into the central first alternative of Aschbacher–Smith C.1.18,
*The Classification of Quasithin Groups*, combined manuscript (1 March 2004),
printed p.126. The proof requires only the source minimal-parabolic condition.
-/

public section

namespace Sylow

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A Sylow subgroup in a minimal parabolic lies in no proper normal subgroup. -/
theorem normal_eq_top_of_uniqueMaximal (T : Sylow p G)
    (hunique : Order.HasUniqueMaximalOver (T : Subgroup G) ⊤)
    (hnormal : ¬ (T : Subgroup G).Normal)
    (N : Subgroup G) [N.Normal] (hTN : (T : Subgroup G) ≤ N) : N = ⊤ := by
  by_contra hN
  obtain ⟨M, hM, _⟩ := hunique.2
  have hNM : N ≤ M := hunique.le_maximal hM hTN (lt_top_iff_ne_top.mpr hN)
  have hnormalizer : Subgroup.normalizer (T : Set G) < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    exact fun h => hnormal (Subgroup.normalizer_eq_top_iff.mp h)
  have hnormalizerM : Subgroup.normalizer (T : Set G) ≤ M :=
    hunique.le_maximal hM Subgroup.le_normalizer hnormalizer
  have htop : (⊤ : Subgroup G) ≤ M := by
    rw [← T.normalizer_sup_eq_top' hTN]
    exact sup_le hnormalizerM hNM
  exact hM.2.ne (top_unique htop)

/-- A normal subgroup centralized by the Sylow subgroup of a minimal
parabolic is central in the ambient group. -/
theorem le_center_of_normal_of_uniqueMaximal (T : Sylow p G)
    (hunique : Order.HasUniqueMaximalOver (T : Subgroup G) ⊤)
    (hnormal : ¬ (T : Subgroup G).Normal)
    (D : Subgroup G) [D.Normal]
    (hTD : (T : Subgroup G) ≤ Subgroup.centralizer (D : Set G)) :
    D ≤ Subgroup.center G := by
  exact Subgroup.centralizer_eq_top_iff_subset.mp
    (T.normal_eq_top_of_uniqueMaximal hunique hnormal _ hTD)

end Sylow
