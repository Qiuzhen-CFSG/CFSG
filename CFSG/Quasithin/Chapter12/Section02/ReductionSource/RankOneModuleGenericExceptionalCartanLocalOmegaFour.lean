module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalOmegaFour
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Chapter 12 omega geometry in the original Cartan four-space

The canonical reduced module supplies the universal Input. Apply the
cubic fixed-space comparison and local uniqueness on the original subgroups:
omega has order two, lies in the four-space, and has no residual-fixed point.
No centralization or degree-two conclusion is assumed.

Source: Aschbacher–Smith 5.1.13 and 12.2.2, printed pp.637–638,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y X C K : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The actual escaping cubic and left component have the same omega-fixed subgroup. -/
theorem rankOne_local_cartan_omega_cubic_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (a : LocalA7Configuration T L H X K)
    (c : CartanPair T L H A B) (d : LocalCartanWitness T H A Y X C) :
    omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (C : Set G) =
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) :=
  a.omega_cubic_fixed_eq_left
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c d

/-- The universal noncentral witness has the original order-two omega-center
inside the four-space, with trivial residual fixed subgroup. -/
theorem rankOne_local_cartan_noncentral_omega_four
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, LocalA7Configuration T L H X K ∧
      Nat.card (localOmegaModule T K) = 16 ∧
      omegaOneCenterAmbient (T : Subgroup G) ≤ localOmegaModule T K ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G)) = 2 ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (residual H : Set G) = ⊥ :=
  localCartan_noncentral_omega_four
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hXC

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
