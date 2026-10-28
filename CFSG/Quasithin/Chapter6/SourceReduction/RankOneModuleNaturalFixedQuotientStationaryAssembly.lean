module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientStationaryOmega
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientNaturalSeedThompson
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientHermitianSeed

/-!
# The original natural-or-Hermitian source reduction above degree two

The actual full reduced enlargement either has Thompson movement, giving
its natural quotient, or has zero fixed subgroup and an invariant chosen
constituent. A natural constituent exhausts the original moved layer by
the proved weak-closure contradiction; odd-index averaging then identifies
the original omega-span. A Hermitian constituent exhausts the entire full
reduced subgroup by the common-section budget and first cohomology.

Thus above degree two the sole remaining failure of the required omega
quotient has the whole original R₂(LT) Hermitian model. No constituent or
classification premise is supplied. The degree-two deleted-module row
and the Hermitian geometry are separate remaining source steps.
Source: Aschbacher--Smith 6.1.4, printed pp.664--666, using 5.1.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
open scoped IsMulCommutative
attribute [local instance] SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}

/-- The natural omega quotient or a whole Hermitian full-reduced model,
constructed on the same original groups above degree two. -/
theorem omega_natural_or_hermitian_enlargement_of_degree_ne_two
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M) (hn : n ≠ 2) :
    IsNaturalFixedQuotient L
      (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L) n ∨
    ∃ s : ℕ, n = 2*s ∧ ∃ hs : 1 < s, letI : NeZero s := ⟨by omega⟩;
      elementaryAbelianMaxJ (T : Subgroup G) ≤
        centralizer (reducedSubgroup (L ⊔ (T : Subgroup G)) : Set G) ∧
      IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
        (SL2.BinarySmall.hermitian s) := by
  let hR := h.reduced_enlargement
  let hi := hR.rankOneInput hout
  by_cases hj : elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (reducedSubgroup (L ⊔ (T : Subgroup G)) : Set G)
  · have hjlayer := hj.trans (centralizer_le hR.layer_le_V)
    obtain ⟨U,D,hU,horbit,hfixed,hnat | hherm⟩ :=
      hR.stationary_layer_seed_models hout hjlayer
    · have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) := by
        rw [←horbit]
        exact D.sourceOrbit_weakClosure_setup.normalizes
      have he := RankOneRecognition.original_natural_seed_eq_layer hR hout hU hnat hTU
      exact Or.inl (h.omega_natural_fixed_quotient_of_stationary_natural_enlargement hout hj
        (he ▸ hnat))
    · obtain ⟨s,he,hs,hm⟩ := hherm
      let : NeZero s := ⟨hs.ne'⟩
      have hs' : 1 < s := by omega
      have hTU : (T : Subgroup G) ≤ normalizer (U : Set G) := by
        rw [←horbit]
        exact D.sourceOrbit_weakClosure_setup.normalizes
      obtain ⟨H,hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hi.outside
      have hc := hi.reduced_fixed_eq_bot_of_outside_centralizes hH
        (hi.omega_centralizes_of_thompson_centralizes hH hj)
      exact Or.inr ⟨s,he,hs',hj,
        hi.hermitian_model_of_seed (hU.trans hR.layer_le_V) hTU hm hs' hc⟩
  · exact Or.inl (hR.omega_natural_fixed_quotient_of_thompson_moves hout hj)

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
