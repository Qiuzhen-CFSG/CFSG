module

public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.Basic
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.OddCyclicThreeNormalizer
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Centrality of the moved Fitting subgroup

Under the local-plane law, every nontrivial [F(G),A] has order three.
F(G) normalizes each such commutator. Since O₂(G)=1 makes F(G) odd,
its action on this cyclic group is trivial. Generation by the individual
commutators therefore puts [F(G),J*] in Z(F(G)). This supplies the
centralization input used in the final argument of B.1.9(5).

Source: Aschbacher–Smith, B.1.9(2),(5), printed pp.71–72.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- The original Fitting subgroup has odd order when the two-core is trivial. -/
theorem fitting_odd_of_twoCore_eq_bot (hcore : pCore 2 G = ⊥) :
    Odd (Nat.card (fittingSubgroup G)) := by
  have ho := Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := G))
  exact ho.of_dvd_nat (card_dvd_of_le (fitting_le_pPrimeCore_of_pCore_eq_bot 2 hcore))

/-- Each local cubic commutator centralizes all of F(G), not just the other
cubic factors. -/
theorem minimalMovedFactor_le_centralizer_fitting
    (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ)
    {X : Subgroup G} (hX : X ∈ minimalMovedFactors ρ) :
    X ≤ centralizer (fittingSubgroup G : Set G) := by
  obtain ⟨A, hA, hn, rfl⟩ := hX
  obtain ⟨d⟩ := hlocal A hA hn
  apply commutator_eq_bot_iff_le_centralizer.mp
  exact commutator_eq_bot_of_odd_normalizes_card_three
    ⁅fittingSubgroup G, A⁆ (fittingSubgroup G) d.odd_card
    (Nat.coprime_two_left.mpr (fitting_odd_of_twoCore_eq_bot hcore))
    (normalizer_commutator_ge_left _ _)

/-- The centralization conclusion required by the parent's clause-(5) assembly. -/
theorem fittingMoved_le_centralizer_fitting
    (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ) :
    fittingMoved ρ ≤ centralizer (fittingSubgroup G : Set G) := by
  rw [fittingMoved_eq_sSup]
  exact sSup_le fun _ hX => minimalMovedFactor_le_centralizer_fitting ρ hcore hlocal hX

/-- The source's coprime splitting for a single noncentral minimal offender.
The acted-on group is the solvable Fitting subgroup of the original G. -/
theorem fitting_eq_local_commutator_sup_centralizer
    (hcore : pCore 2 G = ⊥) (hlocal : LocalPlaneLaw ρ)
    {A : Subgroup G} (hA : IsMinimalBestOffender ρ A)
    (hn : ⁅fittingSubgroup G, A⁆ ≠ ⊥) :
    fittingSubgroup G = ⁅fittingSubgroup G, A⁆ ⊔
      (fittingSubgroup G ⊓ centralizer (A : Set G)) := by
  obtain ⟨d⟩ := hlocal A hA hn
  apply eq_commutator_sup_centralizer_of_solvable_coprime _ _ le_normalizer_of_normal
    inferInstance
  rw [d.actor_card]
  exact Nat.coprime_two_left.mpr (fitting_odd_of_twoCore_eq_bot hcore)

end CFSG.Quasithin.ChapterB.FittingStructure
