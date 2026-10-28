module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalSix
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Six-space control on the original Chapter 12 input

The universal chosen-module adapter applies the six-dimensional normalizer
control to the original omega-center and residual of H. If the escaping
cubic centralizes omega, the completed FF reduction consequently leaves
only the four-space, with the literal quotient and fixed-space conclusions.
The remaining source comparisons belong to the local Cartan classification.

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

/-- The six-space centralizer normalizes the original residual section. -/
theorem rankOne_local_cartan_a7_six_normalizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (a : LocalA7Configuration T L H X K)
    (d : LocalCartanWitness T H A Y X C)
    (hc : Nat.card (localOmegaModule T K) = 64) :
    (K ⊔ (T : Subgroup G)) ⊓ omegaCentralizer T ≤ normalizer (residual H : Set G) :=
  a.six_omega_centralizer_le_residual_normalizer
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen d hc

/-- In the centralizing-cubic branch the original FF configuration is a
four-space, including its residual action and whole Sylow-join quotient. -/
theorem rankOne_local_cartan_noncentral_four_of_cubic_centralizes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (hXC : ¬ X ≤ omegaCentralizer T)
    (hc : C ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, LocalA7Configuration T L H X K ∧
      Nat.card (localOmegaModule T K) = 16 ∧
      localOmegaModule T K ⊓ centralizer (residual H : Set G) = ⊥ ∧
      Nonempty (((K ⊔ (T : Subgroup G) : Subgroup G) ⧸
        pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)) ≃* alternatingGroup (Fin 7)) ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (residual H : Set G) =
        omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (K : Set G) ∧
      Nat.card (omegaOneCenterAmbient (T : Subgroup G) ⊓ localOmegaModule T K : Subgroup G) = 2 :=
  localCartan_noncentral_four_of_cubic_centralizes
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hXC hc

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
