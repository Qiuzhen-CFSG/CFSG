module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSelectionSylow
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusionNumericalAssembly

/-!
# Applying invariant Sylow selection to the cyclic-block branch

An arbitrary seed may be replaced by the already constructed inverted
prime pair in the same H and for the same p. Sylow equivalence transfers
the small-group alternatives, and the normalizer-quotient selection gives
the complete invariant odd analysis on the canonical H-orbit.

The cyclic-block consumer now requires only the small odd-group alternatives
and the terminal component-module contradiction. Invariant Sylow selection,
Frattini control, the residual identity, the numerical reduction and block
recognition are discharged on the original subgroups and actions.
Final assembly and both remaining local obligations stay with
qt-d-12213-cyclic-block; this is not an unconditional 12.2.21–24 theorem.
Source: Aschbacher–Smith, printed pp.802–804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {d : ℕ}

/-- Complete invariant selection for any initial seed once its small
odd-group alternatives are established. The original H and p are retained. -/
theorem CyclicConstructionSeed.invariantSelection_of_alternatives
    {p : ℕ} {H P U : Subgroup G} {g : G}
    (S : CyclicConstructionSeed T L V d p H P U g)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (halt : Nat.card P = p ∨
      (IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
      (IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧ Monoid.exponent P = p)) :
    ∃ P' U' g' v, CyclicInvariantSelection T L V d p H P' U' g' v := by
  obtain ⟨r, P', U', g', v, R, hg, hv, _, hvU, hi⟩ :=
    chosen_hstar_exists_cyclicConstructionSeed D A hTV hTI S.hstar
  have hP'H : P' ≤ H := R.overgroup ▸ le_sup_left
  have hrp : r = p := S.prime_eq_of_odd_prime_element R.prime R.odd_prime
    ⟨g', hP'H R.generator_mem⟩ ((Subgroup.orderOf_coe _).symm.trans hg)
  rw [hrp] at R hg
  obtain ⟨Q, hQ⟩ := R.sylow
  have halt' := S.alternatives_of_sylow halt Q
  dsimp only at halt'
  rw [hQ] at halt'
  obtain ⟨P'', hP''⟩ := R.invariantSelection_of_small_alternatives D A hTV hTI halt' hg hv hvU hi
  exact ⟨P'', U', g', v, hP''⟩

/-- Apply invariant selection and the canonical-orbit construction to the
original natural-action hypotheses. Only small-group recognition is explicit. -/
theorem invariantOddLocalAnalysis_of_small_odd_alternatives
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hTI : IsTISubgroup V)
    (smallStep : ∀ p H P U g, CyclicConstructionSeed T L V d p H P U g →
      Nat.card P = p ∨
        (IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
        (IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧ Monoid.exponent P = p)) :
    ∃ p H P U W g v, InvariantOddLocalAnalysis T L V d p H P U W g v := by
  have hTV := ((structural G T L h).2.2 V D).1
  obtain ⟨p, H, P, U, g, S⟩ := exists_cyclicConstructionSeed D A hTV hTI
  obtain ⟨P', U', g', v, R⟩ :=
    S.invariantSelection_of_alternatives D A hTV hTI (smallStep p H P U g S)
  exact ⟨p, H, P', U', componentOrbit (H.pCoreIn 2 ⊓ V) H, g', v,
    R.invariantOddLocalAnalysis D A hTV hTI⟩

/-- Invariant Sylow selection is discharged in the actual cyclic-block
consumer. Small-group recognition and the terminal contradiction remain. -/
theorem cyclicLocalAnalysis_of_small_odd_alternatives_and_terminal_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (smallStep : ∀ p H P U g, CyclicConstructionSeed T L V d p H P U g →
      Nat.card P = p ∨
        (IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
        (IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧ Monoid.exponent P = p))
    (terminal : ∀ p H P U W g v,
      InvariantOddLocalAnalysis T L V d p H P U W g v →
      IsExtraspecial p P → Nat.card P = p ^ 3 → Monoid.exponent P = p →
      W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ →
      p = 3 → d = 3 → Nat.card W = 64 →
      W ≤ centralizer (H.pCoreIn 2 : Set G) →
      H ≤ normalizer (((frattini P).map P.subtype ⊔ W : Subgroup G) : Set G) →
      H ≤ normalizer ((H.pCoreIn 2 ⊓ centralizer
        (((frattini P).map P.subtype : Subgroup G) : Set G) : Subgroup G) : Set G) →
      False) :
    ∃ H P U, CyclicLocalAnalysis T L V d H P U := by
  have hTV := ((structural G T L h).2.2 V D).1
  apply cyclicLocalAnalysis_of_nonprime_selection_and_terminal_core h D structural A hnone hTI _ terminal
  intro p H P U g S _
  exact S.invariantSelection_of_alternatives D A hTV hTI (smallStep p H P U g S)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
