module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSelectionNormalizer
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusionNumericalAssembly

/-!
# Applying Frattini control to the original cyclic branch

The original natural-action hypotheses produce a seed whose extraspecial
Frattini subgroup normalizes V and admits a fixed element outside O₂(H).
For any selected small odd subgroup and invariant inverter, the proved
Frattini control, star inversion and residual formula complete the invariant
odd analysis on its canonical orbit.

The final application feeds this record to the existing numerical reduction
and block recognition. The small odd alternatives, invariant Sylow choice,
and terminal component-module contradiction remain with qt-d-12213-cyclic-block.
Source: Aschbacher–Smith, 12.2.21–24, printed pp.802–804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {d : ℕ}

/-- The constructed seed satisfies Frattini control before invariant selection. -/
theorem exists_cyclicConstructionSeed_with_frattini_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hTI : IsTISubgroup V) :
    ∃ p H P U g, ∃ _S : CyclicConstructionSeed T L V d p H P U g,
      (pResidual 2 H).map H.subtype = P ⊔ componentOrbit (H.pCoreIn 2 ⊓ V) H ∧
      (IsExtraspecial p P →
        (frattini P).map P.subtype ≤ normalizer (V : Set G)) ∧
      (IsExtraspecial p P → ∃ v ∈ V, v ∉ H.pCoreIn 2 ∧ v ∉ U ∧
        v ∈ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G)) := by
  have hTV := ((structural G T L h).2.2 V D).1
  obtain ⟨p, H, P, U, g, S⟩ := exists_cyclicConstructionSeed D A hTV hTI
  exact ⟨p, H, P, U, g, S, S.residual D A hTV,
    S.frattini_normalizes_chosen_of_extraspecial D A hTV hTI,
    S.exists_frattini_fixed_outside_pair_core D A hTV hTI⟩

/-- The constructed prime rotation retains its original inverter, which in
the extraspecial branch fixes Φ(P) and normalizes the source index-p subgroup. -/
theorem exists_cyclicConstructionSeed_with_frattini_rotation
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hTI : IsTISubgroup V) :
    ∃ p H P U g v, ∃ _S : CyclicConstructionSeed T L V d p H P U g,
      orderOf g = p ∧ v ∈ V ∧ v ∉ U ∧ v * g * v⁻¹ = g⁻¹ ∧
      (IsExtraspecial p P →
        v ∈ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) ∧
        v ∈ normalizer (((frattini P).map P.subtype ⊔ zpowers g : Subgroup G) : Set G)) ∧
      (IsExtraspecial p P → Nat.card P = p ^ 3 →
        Nat.card ((frattini P).map P.subtype ⊔ zpowers g : Subgroup G) = p ^ 2 ∧
        ((frattini P).map P.subtype ⊔ zpowers g).relIndex P = p ∧
        P ≤ normalizer (((frattini P).map P.subtype ⊔ zpowers g : Subgroup G) : Set G)) := by
  have hTV := ((structural G T L h).2.2 V D).1
  obtain ⟨H, hH⟩ := A.exists_hstar
  obtain ⟨p, P, U, g, v, S, hg, hv, _, hvU, hi⟩ :=
    chosen_hstar_exists_cyclicConstructionSeed D A hTV hTI hH
  exact ⟨p, H, P, U, g, v, S, hg, hv, hvU, hi,
    fun he => ⟨S.inverter_centralizes_frattini_of_extraspecial D A hTV hTI he hv hi,
      S.inverter_normalizes_frattini_rotation D A hTV hTI he hv hi⟩,
    fun he hc => S.frattini_rotation_index_of_extraspecial D A hTV hTI he hc hg⟩

/-- The original prime pair supplies the normalizer-quotient seed in either
nonprime small-group branch, retaining its generator and inverter. -/
theorem exists_cyclicConstructionSeed_with_normalizer_seed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hTI : IsTISubgroup V) :
    ∃ p H P U g v, ∃ _S : CyclicConstructionSeed T L V d p H P U g,
      orderOf g = p ∧ v ∈ V ∧ v ∉ U ∧ v * g * v⁻¹ = g⁻¹ ∧
      ((IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
        (IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧ Monoid.exponent P = p) →
        ∃ B : Subgroup G, B ≤ P ∧ (frattini P).map P.subtype ≤ B ∧
          g ∈ B ∧ B.relIndex P = p ∧ P ≤ normalizer (B : Set G) ∧
          v ∈ normalizer (B : Set G)) := by
  have hTV := ((structural G T L h).2.2 V D).1
  obtain ⟨H, hH⟩ := A.exists_hstar
  obtain ⟨p, P, U, g, v, S, hg, hv, _, hvU, hi⟩ :=
    chosen_hstar_exists_cyclicConstructionSeed D A hTV hTI hH
  refine ⟨p, H, P, U, g, v, S, hg, hv, hvU, hi, ?_⟩
  intro halt
  have hne : Nat.card P ≠ p := by
    rcases halt with ⟨_, hc⟩ | ⟨_, hc, _⟩
    · rw [hc]
      exact ne_of_gt (by nlinarith [S.prime.two_le])
    · rw [hc]
      have hp := S.prime.two_le
      have hs : p < p ^ 2 := by nlinarith
      have hm : p ^ 2 < p ^ 3 := by
        calc p ^ 2 = p ^ 2 * 1 := by simp
             _ < p ^ 2 * p := Nat.mul_lt_mul_of_pos_left (by omega) (pow_pos S.prime.pos _)
             _ = p ^ 3 := by ring
      exact ne_of_gt (hs.trans hm)
  exact S.exists_index_prime_normalizer_seed D A hTV hTI (Or.inr halt) hne hg hv hi

/-- The literal canonical orbit carries the complete odd analysis once the
small subgroup and its invariant inverter have been selected. -/
theorem CyclicConstructionSeed.invariantOddLocalAnalysis_of_small_invariant_inverter
    {p : ℕ} {H P U : Subgroup G} {g v : G}
    (S : CyclicConstructionSeed T L V d p H P U g)
    (D : ChosenModule T L V) (A : NaturalLocalAnalysis T L V d)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hTI : IsTISubgroup V)
    (halt : Nat.card P = p ∨
      (IsElementaryAbelian p P ∧ Nat.card P = p ^ 2) ∨
      (IsExtraspecial p P ∧ Nat.card P = p ^ 3 ∧ Monoid.exponent P = p))
    (hg : orderOf g = p) (hv : v ∈ V) (hvU : v ∉ U)
    (hi : v * g * v⁻¹ = g⁻¹) (hvP : v ∈ normalizer (P : Set G)) :
    InvariantOddLocalAnalysis T L V d p H P U
      (componentOrbit (H.pCoreIn 2 ⊓ V) H) g v := by
  have R := S.invariantSelection_of_small_invariant_inverter D A hTV hTI halt hg hv hvU hi hvP
  exact R.invariantOddLocalAnalysis D A hTV hTI

/-- Frattini normalization, quotient inversion, the residual identity, the
numerical reduction and the block step are all discharged in this consumer.
The remaining selection supplies only the small odd subgroup and its inverter. -/
theorem cyclicLocalAnalysis_of_small_invariant_selection_and_terminal_core
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (selectionStep : ∀ p H P U g, CyclicConstructionSeed T L V d p H P U g →
      Nat.card P ≠ p → ∃ P' U' g' v, ∃ _S : CyclicConstructionSeed T L V d p H P' U' g',
        (Nat.card P' = p ∨
          (IsElementaryAbelian p P' ∧ Nat.card P' = p ^ 2) ∨
          (IsExtraspecial p P' ∧ Nat.card P' = p ^ 3 ∧ Monoid.exponent P' = p)) ∧
        orderOf g' = p ∧ v ∈ V ∧ v ∉ U' ∧ v * g' * v⁻¹ = g'⁻¹ ∧
        v ∈ normalizer (P' : Set G))
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
  apply cyclicLocalAnalysis_of_nonprime_selection_and_terminal_core
    h D structural A hnone hTI _ terminal
  intro p H P U g S hc
  obtain ⟨P', U', g', v, R, halt, hg, hv, hvU, hi, hvP⟩ :=
    selectionStep p H P U g S hc
  exact ⟨P', U', g', v,
    R.invariantSelection_of_small_invariant_inverter D A hTV hTI halt hg hv hvU hi hvP⟩

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
