module

public import CFSG.Quasithin.Chapter1.Section03.Basic
public import CFSG.Quasithin.MainForward.SourceFamilies
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.SectionCentralizer

/-!
# The faithful solvable uniqueness families

The families are the intersections with the actual X_f of A.4.5–7.
In particular, the star retains the exclusion defining XiStar; it is
not maximality in Xi. The local-family bridge identifies the existing
forward-reduction L_f with the canonical Chapter 1 L definition.

The final definition expresses inner action on B/O₂(B) by the product
B C_G(B/O₂(B)). It retains the actual section centralizer, including
normalization of B, for the model-action calculations in 1.3.9(1).

Source: Aschbacher–Smith, combined manuscript (1 March 2004), pp.507, 514.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter1
open ChapterA.Section04
variable {G : Type*} [Group G]

/-- The family Ξ_f(G,T), using the genuine internal-module predicate. -/
def XiF (G : Type*) [Group G] (T : Subgroup G) : Set (Subgroup G) :=
  Xi G T ∩ {X | IsFaithfulSignalizerType X}

/-- The family Ξ_f*(G,T) = Ξ_f(G,T) ∩ Ξ*(G,T). -/
def XiStarF (G : Type*) [Group G] (T : Subgroup G) : Set (Subgroup G) :=
  XiF G T ∩ XiStar G T

namespace Terminal

/-- The two existing definitions of the local family agree for an ambient Sylow subgroup. -/
theorem mem_L_iff_localComponents (T : Sylow 2 G) (B : Subgroup G) :
    B ∈ L G T ↔ B ∈ MainForward.localComponents T := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro he
    exact h.2.2 (by change (pCore 2 (B ⊔ (T : Subgroup G) : Subgroup G)).map _ = ⊥; rw [he, Subgroup.map_bot])
  · intro h
    refine ⟨h.1, ⟨T.subtype le_sup_right, ?_⟩, ?_⟩
    · simp only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right]
    · exact fun he => h.2 ((map_eq_bot_iff_of_injective _ (B ⊔ (T : Subgroup G)).subtype_injective).mp he)

/-- Preimage of the inner automorphisms on B/O₂(B), in the ambient normalizer. -/
def innerTwoQuotientNormalizer (B : Subgroup G) : Subgroup G :=
  B ⊔ twoSectionCentralizer B ⊤

/-- The product description makes the inner-action convention explicit. -/
theorem mem_innerTwoQuotientNormalizer_iff (B : Subgroup G) (g : G) :
    g ∈ innerTwoQuotientNormalizer B ↔
      ∃ b ∈ B, ∃ c ∈ twoSectionCentralizer B ⊤, b * c = g := by
  have hn : B ≤ normalizer (twoSectionCentralizer B ⊤ : Set G) :=
    B.le_normalizer.trans (by simpa only [top_inf_eq] using normalizer_twoSectionCentralizer B ⊤)
  change g ∈ B ⊔ twoSectionCentralizer B ⊤ ↔ _
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right B _ hn]
  rfl

end Terminal
end CFSG.Quasithin.Chapter1
end
