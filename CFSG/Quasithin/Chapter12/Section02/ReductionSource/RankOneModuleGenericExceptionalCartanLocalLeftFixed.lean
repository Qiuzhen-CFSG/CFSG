module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalLeftFixed
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalCartanLocal

/-!
# Left fixed spaces in the original Chapter 12 Cartan argument

The universal input adapter retains the whole reduced subgroup R₂(LT).
The actual Hall plane and omega-centralizer generate the right A₇ join,
so uniqueness over LT eliminates its left fixed spaces. The Cartan meets
the maximal component in exactly the original escaping cubic. The final
application uses the completed FF reduction and adds no configuration,
fixed-space, splitting or field-degree hypothesis.

The two block exclusions and torus argument are still needed to exclude
this noncentral configuration and establish the original Cartan theorem.
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

/-- The actual Hall plane generates the whole right join together with its
omega-centralizer; all subgroups remain in the original ambient group. -/
theorem rankOne_local_cartan_hall_omega_generation
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (a : LocalA7Configuration T L H X K)
    (c : CartanPair T L H A B) (d : LocalCartanWitness T H A Y X C) :
    B ⊔ C ⊔ ((K ⊔ (T : Subgroup G)) ⊓ omegaCentralizer T) =
      K ⊔ (T : Subgroup G) :=
  a.four_hall_omega_generation
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c d

/-- The original Cartan intersection is exactly the witnessed cubic. -/
theorem rankOne_local_cartan_intersection_eq_cubic
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (a : LocalA7Configuration T L H X K)
    (c : CartanPair T L H A B) (d : LocalCartanWitness T H A Y X C) :
    A ⊓ K = C :=
  a.cartan_intersection_eq_cubic
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) c d

/-- The original noncentral witness supplies both full-layer fixed-space
vanishings and the cubic comparison, without assuming the A₇ configuration. -/
theorem rankOne_local_cartan_noncentral_left_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    {n : ℕ} (hn : 1 < n)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (d : LocalCartanWitness T H A Y X C) (hXC : ¬ X ≤ omegaCentralizer T) :
    ∃ K : Subgroup G, LocalA7Configuration T L H X K ∧ A ⊓ K = C ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ ∧
      RankOneModule.wholeReduced T L ⊓ centralizer (L : Set G) = ⊥ ∧
      RankOneModule.commutatorLayer T L ⊓ centralizer (L : Set G) = ⊥ ∧
      RankOneModule.wholeReduced T L ⊓ centralizer (C : Set G) = ⊥ ∧
      omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (C : Set G) = ⊥ :=
  localCartan_noncentral_left_fixed
    (D.rankOne_generic_input_of_many h.toHypothesis1221 hmany hn hpsl) hH hgen c hY d hXC

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
