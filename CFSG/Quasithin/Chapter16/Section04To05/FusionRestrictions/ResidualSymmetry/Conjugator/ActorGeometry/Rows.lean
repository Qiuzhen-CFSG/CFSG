module

public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Conjugator.ActorGeometry
public import CFSG.Quasithin.Chapter16.Section04To05.FusionRestrictions.ResidualSymmetry.Exceptional

/-!
# Supplying the selected residual inputs from actual exceptional rows

The earlier involution table for L transports to its actual conjugate.
The accepted exceptional calculation therefore discharges both two-perfectness
inputs in `ResidualInputs`, while preserving the selected element g and all
cross-containments. The fixed-subgroup rows, their markings and the bound n > 2
remain explicit earlier source inputs. No residual equality is assumed.

Source: Aschbacher–Smith, 16.1.4, 16.4.8, and 16.5.5,
printed pp.1171, 1187–1188, and 1197.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator

open Subgroup Theory.GroupTheory

variable {G : Type*} [Group G] [Finite G]

/-- The existing local calculation supplies both exceptional perfectness fields.
The inputs are the same actual table and faithful actions used by
`Exceptional.exists_common_residual_conjugate_of_rows`. -/
theorem ResidualInputs.of_rows
    {T : Sylow 2 G} {z g : G} {L R : Subgroup G}
    (h : IntersectionSetup T z L g R)
    (hselected : (T : Subgroup G) ⊓
      normalizer ((centralizer (L : Set G)).conjBy g : Set G) ≤
        (T : Subgroup G).conjBy g)
    (htransport : R = (commutingSylow T L).conjBy g)
    (hforward : ∀ u ∈ R, orderOf u = 2 →
      modifiedCentralizerResidual L u ≤ L.conjBy g)
    (hbackward : ∀ i ∈ commutingSylow T L, orderOf i = 2 →
      modifiedCentralizerResidual (L.conjBy g) i ≤ L)
    (hfaithR : R ⊓ centralizer (L : Set G) = ⊥)
    (hnormalC : commutingSylow T L ≤ normalizer (L.conjBy g : Set G))
    (hfaithC : commutingSylow T L ⊓ centralizer (L.conjBy g : Set G) = ⊥)
    (hrows : HasEvenLinearThreeType L → ∃ n : ℕ,
      2 < n ∧ Even n ∧ ClassicalGroup.IsPSL L 3 (2 ^ n) ∧
        Exceptional.InvolutionRows L n) : ResidualInputs T z L g R := by
  have hboth (hL : HasEvenLinearThreeType L) :
      (∀ u ∈ R, orderOf u = 2 → IsPPerfect 2 (modifiedCentralizerResidual L u)) ∧
      (∀ i ∈ commutingSylow T L, orderOf i = 2 →
        IsPPerfect 2 (modifiedCentralizerResidual (L.conjBy g) i)) := by
    obtain ⟨n, hn, he, hm, hr⟩ := hrows hL
    exact Exceptional.conjugate_actors_twoPerfect hn he hm hr
      (h.le_sylow.trans h.sylow_normalizes) hfaithR hnormalC hfaithC
  exact ⟨h, hselected, htransport, hforward, hbackward,
    fun hL => (hboth hL).1,
    fun hL => (hboth ((hasEvenLinearThreeType_map_iff L (MulAut.conj g)).mp hL)).2⟩

end CFSG.Quasithin.Chapter16.Intersections.ResidualSymmetry.Conjugator
