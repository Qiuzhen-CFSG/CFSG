module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalRightThompson
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# The original Chapter 12 right Thompson comparison

Apply the universal rank-one adapter to the chosen reduced module. The
four-space action identifies the literal original Thompson and Baumann
images, lifts its normalizer through the two-core and proves generation
with the original omega-centralizer. The final application uses the
completed FF reduction and six-space exclusion; no A₇ configuration is
assumed there. Centralization by the cubic remains the stated source
branch, to be discharged in the local Cartan classification argument.

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

/-- The right generation statement uses the original chosen Sylow and U. -/
theorem rankOne_local_cartan_four_thompson_generation
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (a : LocalA7Configuration T L H X K) (hc : Nat.card (localOmegaModule T K) = 16) :
    Nat.card (localOmegaModule T K ⊓
      centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) : Subgroup G) = 4 ∧
    (((K ⊔ (T : Subgroup G)) ⊓ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ⊔
      ((K ⊔ (T : Subgroup G)) ⊓ omegaCentralizer T) = K ⊔ (T : Subgroup G)) := by
  have hi := D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl
  exact ⟨a.four_thompson_fixed_card hi hc,a.four_thompson_normalizer_generation hi hc⟩

/-- The actual centralizing-cubic branch supplies its own A₇ configuration
and the original four-space normalizer calculation. -/
theorem rankOne_local_cartan_noncentral_four_thompson
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (hXC : ¬ X ≤ omegaCentralizer T)
    (hd : C ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, LocalA7Configuration T L H X K ∧
      Nat.card (localOmegaModule T K) = 16 ∧
      Nat.card (localOmegaModule T K ⊓
        centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) : Subgroup G) = 4 ∧
      (((K ⊔ (T : Subgroup G)) ⊓ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)) ⊔
        ((K ⊔ (T : Subgroup G)) ⊓ omegaCentralizer T) = K ⊔ (T : Subgroup G)) ∧
      (let M := K ⊔ (T : Subgroup G)
       let J := (elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf M
       let B₀ := (ChapterB.baumann (T : Subgroup G)).subgroupOf M
       ∃ q : M →* alternatingGroup (Fin 7), Function.Surjective q ∧
         q.ker = pCore 2 M ∧ J.map q = B₀.map q ∧ IsElementaryAbelian 2 (J.map q) ∧
         Nat.card (J.map q) = 4 ∧
         normalizer (J : Set M) = (normalizer (J.map q : Set (alternatingGroup (Fin 7)))).comap q) :=
  localCartan_noncentral_four_thompson_of_cubic_centralizes
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hXC hd
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
