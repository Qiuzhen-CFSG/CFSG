module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRightNatural
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The right natural module for the original Chapter 12 Cartan inputs

Apply the proved FF reduction and the literal residual action to the
original chosen module. The residual moves the entire four-dimensional
omega commutator; no configuration or module coordinates are assumed.
The subsequent block exclusions and torus argument remain necessary.

Source: Aschbacher–Smith 5.1.13 and 12.2.2, printed pp.637–638,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B Y X C : Subgroup G}
  (D : ChosenModule T L V)
include D

/-- The literal right residual moves the complete four-space under the
original noncentral Cartan hypotheses. -/
theorem rankOne_local_cartan_noncentral_right_full_movement
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
      ⁅localOmegaModule T K,residual H⁆ = localOmegaModule T K :=
  localCartan_noncentral_right_full_movement
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hXC

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
