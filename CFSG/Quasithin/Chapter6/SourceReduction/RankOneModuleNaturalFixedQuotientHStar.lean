module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientOmega
public import CFSG.Quasithin.Chapter6.Section01.SourceHStarMixedLeftSource

/-!
# The original noncentral H-star branch constructs its left natural quotient

If an actual H-star member moves the original Sylow omega-center, the
rank-one comparison theorem forces Thompson movement on the original
reduced module. The completed moving branch of 6.1.4 then gives the natural
quotient on the literal L-span of omega. Thus every left field of the
mixed F.1.1 construction follows from the original noncentral H-star data,
without waiting for the separate stationary proof of 6.1.4.
-/
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- Actual H-star movement supplies its own natural quotient on the original omega-span. -/
theorem omega_natural_fixed_quotient_of_hstar_moves
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n := by
  have hZ : ¬ omegaOneCenterAmbient (T : Subgroup G) ≤ (center H).map H.subtype := by
    intro hz
    apply hZH
    apply commutator_eq_bot_iff_le_centralizer.mpr
    intro z hzZ x hx
    obtain ⟨a,ha,rfl⟩ := hz hzZ
    exact congrArg H.subtype ((mem_center_iff.mp ha) ⟨x,hx⟩)
  exact h.omega_natural_fixed_quotient_of_thompson_moves hout
    ((h.rankOneInput hout).thompson_moves_of_noncentral_omega
      (h.maximal_eq_normalizer_L ▸ hH) hZ)

/-- The noncentral H-star branch supplies all original mixed-left fields. -/
theorem mixed_left_source_of_hstar_moves
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥) :
    let S := ChapterB.baumann (T : Subgroup G)
    Chapter1.IsSylowIn 2 S (L ⊔ S) ∧
      ClassicalGroup.IsPSL ((L ⊔ S : Subgroup G) ⧸ pCore 2 (L ⊔ S : Subgroup G))
        2 (2 ^ n) ∧
      generalizedFitting (L ⊔ S : Subgroup G) = pCore 2 (L ⊔ S : Subgroup G) ∧
      ∃ A : Subgroup G, A ≤ RankOneGeneric.localBorel T L ∧
        IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (RankOneGeneric.localBorel T L)) ∧
        (A : Set G) * (T : Set G) = (T : Set G) * (A : Set G) ∧
        A ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) = ⊥ ∧
        A ⊔ H ∈ Chapter1.HOver G (T : Set G) ∧
        A ≤ normalizer (S : Set G) ∧
        ChapterF.Source.borel (L ⊔ S) S = S ⊔ A :=
  h.mixed_left_source_of_natural_quotient hout hH
    (h.omega_natural_fixed_quotient_of_hstar_moves hout hH hZH) hZH

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
