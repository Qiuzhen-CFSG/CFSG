module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.SylowRank.Contracts
public import CFSG.Quasithin.Chapter16.Section04To05.SylowSymmetry.Consequences
public import Theory.GroupTheory.DisjointConjugateCenter


/-!
# Reducing the small-center configuration to the full Sylow subgroup

In the genuine intersection setup, the central involution makes T_C
nontrivial, and T normalizes both Sylow factors. Centerlessness separates
the factors. A conjugator normalizing T₁ and carrying K to K′ makes T_C
and its conjugate disjoint, using the actual 16.4.2(1) intersection R ∩ K = 1.

The finite-group center argument gives Z(T₁) = Z(T_L) × Z_C, with both
factors of order two and centralized by T. A nontrivial R normal in T₁
therefore meets Z(T). The existing 16.5.2(1) proof then puts the chosen
16.4.2(4) conjugator in N_G(T).

The intrinsic centralizer formula and |Z(T_L)| = 2 are explicit inputs
here; their deduction from the quotient rank hypotheses remains separate.
This module does not yet prove the Sylow alternatives or the final
characteristic derived-center contradiction in 16.5.7.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
Lemma 16.5.7, printed p.1198, using Lemmas 16.4.2 and 16.5.2(1).
-/

public section

namespace CFSG.Quasithin.Chapter16.Intersections.SylowRank
open Subgroup
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z g : G} {L R : Subgroup G}

/-- The central factor is nontrivial because it contains the fixed involution z. -/
theorem commutingSylow_ne_bot (h : IntersectionSetup T z L g R) :
    commutingSylow T L ≠ ⊥ := by
  have hz : z ∈ commutingSylow T L := by
    refine ⟨h.mem_sylow, ?_⟩
    intro l hl
    exact mem_centralizer_singleton_iff.mp (h.component.1 hl)
  intro he
  rw [he, mem_bot] at hz
  have hh := h.involution
  rw [hz, orderOf_one] at hh
  norm_num at hh

/-- Both actual Sylow intersections are normal in T. -/
theorem sylow_normalizes_factors (h : IntersectionSetup T z L g R) :
    (T : Subgroup G) ≤ normalizer (componentSylow T L : Set G) ∧
    (T : Subgroup G) ≤ normalizer (commutingSylow T L : Set G) := by
  constructor
  · exact (le_inf (T : Subgroup G).le_normalizer h.sylow_normalizes).trans
      inf_normalizer_le_normalizer_inf
  · exact (le_inf (T : Subgroup G).le_normalizer
      (h.normalizers_eq ▸ h.sylow_normalizes)).trans inf_normalizer_le_normalizer_inf

omit [Finite G] in
/-- The ambient centralizer factors are disjoint when the component is centerless. -/
theorem sylow_factors_disjoint (hZ : center L = ⊥) :
    Disjoint (componentSylow T L) (commutingSylow T L) :=
  (disjoint_centralizer_of_center_eq_bot hZ).mono inf_le_right inf_le_right

/-- Disjointness of the conjugated central factors follows from the genuine
16.4.2(1) input R ∩ K = 1 and the normalizing conjugator. -/
theorem commutingSylow_disjoint_conjugate
    (h : IntersectionSetup T z L g R) {S : Subgroup G} {a : G}
    (hSP : S ≤ (T : Subgroup G)) (hCS : commutingSylow T L ≤ S)
    (ha : a ∈ normalizer (S : Set G))
    (haK : (centralizer (L : Set G)).conjBy a = (centralizer (L : Set G)).conjBy g)
    (hRK : Disjoint R (centralizer (L : Set G))) :
    Disjoint (commutingSylow T L) ((commutingSylow T L).conjBy a) := by
  have hcR : (commutingSylow T L).conjBy a ≤ R := by
    rw [h.eq_intersection]
    refine le_inf ?_ ?_
    · rw [← haK]
      exact map_mono inf_le_right
    · calc
        (commutingSylow T L).conjBy a ≤ S.conjBy a := map_mono hCS
        _ = S := mem_normalizer_iff_map_conj_eq.mp ha
        _ ≤ (T : Subgroup G) := hSP
  exact hRK.symm.mono inf_le_right hcR

/-- The center decomposition, the order of Z_C, and centrality in T in the
first paragraph on p.1198. The two intrinsic centralizer inputs are left
visible; they must be deduced from the projected rank hypotheses. -/
theorem center_decomposition_and_order
    (h : IntersectionSetup T z L g R) {S : Subgroup G} {a : G}
    (hZ : center L = ⊥)
    (hSP : S ≤ (T : Subgroup G))
    (hAS : componentSylow T L ≤ S) (hCS : commutingSylow T L ≤ S)
    (hSn : (T : Subgroup G) ≤ normalizer (S : Set G))
    (hZA : Nat.card (centerIn (componentSylow T L)) = 2)
    (hcent : (T : Subgroup G) ⊓ centralizer (componentSylow T L : Set G) =
      commutingSylow T L ⊔ centerIn (componentSylow T L))
    (ha : a ∈ normalizer (S : Set G))
    (haK : (centralizer (L : Set G)).conjBy a = (centralizer (L : Set G)).conjBy g)
    (hRK : Disjoint R (centralizer (L : Set G))) :
    centerIn S = centerIn (componentSylow T L) ⊔
      (commutingSylow T L ⊓ centralizer (S : Set G)) ∧
    Nat.card ↥(commutingSylow T L ⊓ centralizer (S : Set G)) = 2 ∧
    centerIn S ≤ centralizer (T : Set G) := by
  have hn := sylow_normalizes_factors h
  exact centerIn_rank_two_of_disjoint_conjugate T.isPGroup' hSP hAS hCS hSn
    hn.1 hn.2 (commutingSylow_ne_bot h) (sylow_factors_disjoint hZ) hZA hcent ha
    (commutingSylow_disjoint_conjugate h hSP hCS ha haK hRK)

/-- The component factor in the center decomposition is exactly Z(T_L),
not just an abstract subgroup of order two. -/
theorem center_intersection_component
    (h : IntersectionSetup T z L g R) {S : Subgroup G}
    (hSP : S ≤ (T : Subgroup G)) (hAS : componentSylow T L ≤ S)
    (hZA : Nat.card (centerIn (componentSylow T L)) = 2) :
    centerIn S ⊓ componentSylow T L = centerIn (componentSylow T L) := by
  have hz := centerIn_centralizes_of_card_two hZA (sylow_normalizes_factors h).1
  apply le_antisymm
  · exact le_inf inf_le_right (inf_le_left.trans
      (inf_le_right.trans (centralizer_le hAS)))
  · exact le_inf (le_inf (inf_le_left.trans hAS)
      (hz.trans (centralizer_le hSP))) inf_le_left

/-- The two disjoint central factors each have order two. -/
theorem center_order_four
    (h : IntersectionSetup T z L g R) {S : Subgroup G} {a : G}
    (hZ : center L = ⊥)
    (hSP : S ≤ (T : Subgroup G))
    (hAS : componentSylow T L ≤ S) (hCS : commutingSylow T L ≤ S)
    (hSn : (T : Subgroup G) ≤ normalizer (S : Set G))
    (hZA : Nat.card (centerIn (componentSylow T L)) = 2)
    (hcent : (T : Subgroup G) ⊓ centralizer (componentSylow T L : Set G) =
      commutingSylow T L ⊔ centerIn (componentSylow T L))
    (ha : a ∈ normalizer (S : Set G))
    (haK : (centralizer (L : Set G)).conjBy a = (centralizer (L : Set G)).conjBy g)
    (hRK : Disjoint R (centralizer (L : Set G))) :
    Nat.card (centerIn S) = 4 := by
  obtain ⟨he, hcard, _⟩ := center_decomposition_and_order h hZ hSP hAS hCS hSn
    hZA hcent ha haK hRK
  have hz := centerIn_centralizes_of_card_two hZA (sylow_normalizes_factors h).1
  rw [he, card_sup_eq_mul_of_normalizes_of_disjoint]
  · rw [hZA, hcard]
  · exact (inf_le_left.trans (hCS.trans (hSP.trans (le_centralizer_iff.mp hz)))).trans
      (centralizer_le_normalizer _)
  · exact (sylow_factors_disjoint hZ).mono inf_le_left inf_le_left

/-- Normality of R in either candidate T₁ forces R to meet Z(T).
The chosen 16.4.2(4) conjugator therefore normalizes the full T, by 16.5.2(1).
This is the reduction from the half-Sylow case in the proof of 16.5.7. -/
theorem normalizing_conjugator_of_small_center
    (h : IntersectionSetup T z L g R) {S : Subgroup G} {a : G}
    (hZ : center L = ⊥)
    (hSP : S ≤ (T : Subgroup G))
    (hAS : componentSylow T L ≤ S) (hCS : commutingSylow T L ≤ S)
    (hSn : (T : Subgroup G) ≤ normalizer (S : Set G))
    (hZA : Nat.card (centerIn (componentSylow T L)) = 2)
    (hcent : (T : Subgroup G) ⊓ centralizer (componentSylow T L : Set G) =
      commutingSylow T L ⊔ centerIn (componentSylow T L))
    (ha : a ∈ normalizer (S : Set G))
    (haK : (centralizer (L : Set G)).conjBy a = (centralizer (L : Set G)).conjBy g)
    (hRK : Disjoint R (centralizer (L : Set G)))
    (hRS : R ≤ S) (hRn : S ≤ normalizer (R : Set G))
    (htransport : (T : Subgroup G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
      (T : Subgroup G).conjBy g) :
    R ⊓ centralizer (T : Set G) ≠ ⊥ ∧ g ∈ normalizer (T : Set G) := by
  have hZSP := (center_decomposition_and_order h hZ hSP hAS hCS hSn hZA hcent
    ha haK hRK).2.2
  have hne := inf_centerIn_ne_bot_of_centerIn_le
    (T.isPGroup'.of_injective (inclusion hSP) (inclusion_injective _))
    (h.sylow.ne_bot_of_even h.mem_delta.2.2) hRS hRn hSP hZSP
  have he : R ⊓ centerIn (T : Subgroup G) = R ⊓ centralizer (T : Set G) := by
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, h.le_sylow hx.1, hx.2⟩⟩
  rw [he] at hne
  exact ⟨hne, h.conjugator_normalizes_sylow hne htransport⟩

end CFSG.Quasithin.Chapter16.Intersections.SylowRank
