module

public import Theory.GroupTheory.RankOneSylowExtension
public import Theory.GroupTheory.SylowNormalRestriction

/-!
# Unique proper Sylow overgroups in an extension

Let a normal subgroup L supplement an ambient Sylow p-subgroup S.
If every intrinsic Sylow p-subgroup of L has a proper normalizer containing
all its proper overgroups, then `N_G(S ∩ L)` has the same property in G.
Sylow restriction proves properness; the rank-one overgroup dichotomy
forces an overgroup outside the normalizer to contain L and hence all G.

This supplies the ambient Borel in the PSU₃ case of Aschbacher–Smith
E.1.14(1), printed p.214, without restrictions on the outer action.
-/

public section
namespace Subgroup.RankOneSylowExtension
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The normalizer of the actual Sylow intersection is the unique proper
Sylow overgroup bound in the extension. -/
theorem ambient_normalizer_properties (L : Subgroup G) [L.Normal] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (hgen : L ⊔ (S : Subgroup G) = ⊤)
    (hproper : ∀ P : Sylow p L, normalizer (P : Set L) ≠ ⊤)
    (huniq : ∀ P : Sylow p L, ∀ M : Subgroup L,
      (P : Subgroup L) ≤ M → M ≠ ⊤ → M ≤ normalizer (P : Set L)) :
    normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ≠ ⊤ ∧
    (S : Subgroup G) ≤ normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) ∧
    ∀ M : Subgroup G, (S : Subgroup G) ≤ M → M ≠ ⊤ →
      M ≤ normalizer (((S : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  obtain ⟨P, hP⟩ := S.exists_sylow_map_eq_inf_of_normal L
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    have hc := congrArg (Subgroup.comap L.subtype) htop
    rw [← hP, comap_normalizer_eq_of_le_range (map_le_range _ _),
      comap_map_eq_self_of_injective Subtype.val_injective, comap_top] at hc
    exact hproper P hc
  · apply le_normalizer_iff.mpr
    intro s hs x hx
    exact ⟨S.mul_mem (S.mul_mem hs hx.1) (S.inv_mem hs),
      (inferInstance : L.Normal).conj_mem x hx.2 s⟩
  · intro M hSM hM
    rcases RankOneSylowExtension.le_or_le_normalizer L P (huniq P) M
      (hP ▸ inf_le_left.trans hSM) with hLM | hMB
    · exact (hM (top_unique (hgen ▸ sup_le hLM hSM))).elim
    · rwa [hP] at hMB

end Subgroup.RankOneSylowExtension
