module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Setup
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Geometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Commuting
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.NormalizerGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.CosetDistribution.Distribution.Incidences

/-!
# Assembly of the literal Bender distribution from inversion incidences

The normalizer geometry gives preliminary fiber sizes 0, 1, 2, 3, 6, 7.
The commuting-incidence identity and the sextuple count exclude size two.
The remaining incidence counts give the coefficients of `b₃`, `b₆`, `b₇`
and the centralized singleton count. The already proved free conjugation
action supplies `m`, rather than taking singleton divisibility as an input.

The final theorem constructs the normalizer geometry from the supplied prime
and normalizer data, then applies the proved inversion and centralization
incidences. Thus no geometry, incidence or distribution premise remains.
The earlier prime and normalizer data are retained as explicit source inputs.

Source: H. Bender, *Finite groups with large subgroups*, Illinois J. Math.
18 (1974), §4, printed pp.226–227, the distribution following (4.3).
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData

/-- The source incidence equations imply the literal coset distribution.
This is an intermediate assembly: it does not assert the incidence equations
or the normalizer geometry without their explicit premises. -/
public theorem bender_distributionData_of_incidence_counts
    {G : Type*} [Group G] [Finite G]
    (h : Janko1CentralizerData G) (d e : ℕ)
    (normalizerData : BenderNormalizerData h)
    (geometry : BenderNormalizerGeometry h)
    (he : e ≤ 1)
    (hseven : Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 7) = 56 * e)
    (hsix : Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 6) = 168)
    (hthree : Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 3) +
      Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 6) = 168 * d)
    (htwo : Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 2) +
      Nat.card (BenderInvolutionsInFibers (normalizer (h.sylow : Set G)) 6) = 168)
    (hcentral : Nat.card (BenderCentralizedSingletons (normalizer (h.sylow : Set G))) +
      56 * (1 + e) = 56 * d) :
    Nonempty (BenderDistributionData h d) := by
  let H := normalizer (h.sylow : Set G)
  rw [bender_involutionsInFibers_card] at hseven hsix
  rw [bender_involutionsInFibers_card, bender_involutionsInFibers_card] at hthree htwo
  have hb2 : benderCosetCount H 2 = 0 := by dsimp [H]; omega
  have hb3 : benderCosetCount H 3 = 56 * (d - 1) := by dsimp [H]; omega
  have hb6 : benderCosetCount H 6 = 28 := by dsimp [H]; omega
  have hb7 : benderCosetCount H 7 = 8 * e := by dsimp [H]; omega
  have hed : e + 1 ≤ d := by omega
  have hc : Nat.card (BenderCentralizedSingletons H) = 56 * (d - 1 - e) := by
    dsimp [H]
    omega
  obtain ⟨m, hm⟩ := bender_single_cosets H
  have hcardH : Nat.card H = 168 := normalizerData.normalizer_card
  rw [hcardH] at hm
  refine ⟨{
    e := e
    m := m
    e_le_one := he
    e_add_one_le_d := hed
    fiber_sizes := ?_
    centralized_singletons := hc
    single_cosets := hm
    triple_cosets := hb3
    sextuple_cosets := hb6
    septuple_cosets := hb7 }⟩
  intro ω hω
  have hnot2 : Nat.card (BenderFiber H ω) ≠ 2 := by
    intro h2
    let Ω := {ω : G ⧸ H // ω ≠ benderBaseCoset H ∧ Nat.card (BenderFiber H ω) = 2}
    have : Nonempty Ω := ⟨⟨ω, hω, h2⟩⟩
    have : Finite Ω := by unfold Ω; infer_instance
    have hpos := Nat.card_pos (α := Ω)
    change 0 < benderCosetCount H 2 at hpos
    omega
  rcases geometry.fiber_sizes_with_two ω hω with hc | hc | hc | hc | hc | hc
  · exact Or.inl hc
  · exact Or.inr (Or.inl hc)
  · exact (hnot2 hc).elim
  · exact Or.inr (Or.inr (Or.inl hc))
  · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr hc)))

/-- Bender's actual non-base coset distribution following (4.3), including
singleton orbit divisibility. The supplied prime and normalizer data suffice:
the subgroup geometry and all five incidence equations are proved here through
their producers, rather than required as additional hypotheses. -/
public theorem bender_distributionData
    {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (h : Janko1CentralizerData G) (d : ℕ)
    (localData : BenderPrimeData G d) (normalizerData : BenderNormalizerData h) :
    Nonempty (BenderDistributionData h d) := by
  have geometry := h.bender_normalizerGeometry localData normalizerData
  obtain ⟨e, he, hseven, hsix, hthree, htwo, hcentral⟩ :=
    h.bender_inversion_incidence_counts d localData normalizerData geometry
  exact h.bender_distributionData_of_incidence_counts d e normalizerData geometry
    he hseven hsix hthree htwo hcentral

end CFSG.Quasithin.Janko1CentralizerData
