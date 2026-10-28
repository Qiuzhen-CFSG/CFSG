module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearLayerMultiplicity

/-!
# The exceptional whole-layer conclusion from field four and Borel fixation

Combine the proved positive finite-copy decomposition with the bound from
the cubic ratio of the actual whole action. This gives one or two A₅ modules
on the literal full commutator layer, and then the existing exceptional-exit
consumer supplies the relative component. Residual centralization and exact
maximal-overgroup uniqueness are retained from their proved source producer.

Only the independent field-four exponent and local Borel centralization
remain explicit. Their producer is qt-d-1222-linear-field-four-borel;
qt-d-1222-rankone-exceptional-linear-analysis retains unconditional assembly,
and qt-d-1222-rankone-generic-exceptional retains the enclosing exceptional
branch. None of the former local splitting, invariance, quotient faithfulness
or multiplicity premises remains.

Source: Aschbacher--Smith 5.1.14(3--4), 5.1.19 and 12.2.2,
refs/quasithin.pdf, printed pp.638--639,643--644,795.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}

namespace ChosenModule
open RankOneModule Chapter6.Source.RankOneGeneric

/-- Positive finite copies on the whole layer, bounded using the whole actor. -/
theorem rankOne_linear_bounded_copies_of_borel
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    {n : ℕ} (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hn : n = 2)
    (hB : localBorel T L ≤ omegaCentralizer T) :
    wholeReduced T L = commutatorLayer T L ∧
      ∃ k : ℕ, 0 < k ∧ k ≤ 2 ∧ Chapter6.Source.IsConjugationModel L
        (commutatorLayer T L) (Chapter6.Source.a5Copies k) := by
  obtain ⟨heq,k,hk,hm⟩ := D.rankOne_linear_layer_decomposition_of_borel
    h hH hK hnf hpsl hn hB
  exact ⟨heq,k,hk,D.rankOne_linear_layer_multiplicity h hH heq hm,hm⟩

/-- The entire exceptional A₅ layer in the original source configuration.
Residual maximality and nonfaithfulness are discharged; the independent
field-four/Borel producer supplies precisely `hn` and `hB`. -/
theorem rankOne_linear_whole_layer_of_field_four_borel
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {n : ℕ} (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hn : n = 2)
    (hB : localBorel T L ≤ omegaCentralizer T) :
    Chapter6.Source.IsOneOrTwoA5Modules L (commutatorLayer T L) := by
  obtain ⟨hK,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  obtain ⟨_,k,hk,hk2,hm⟩ := D.rankOne_linear_bounded_copies_of_borel
    h.toHypothesis1221 hH hK hnf hpsl hn hB
  exact Chapter6.Source.oneOrTwoA5Modules_of_copies hk hk2 hm

/-- All three original linear source conclusions, retaining literal residual
centralization and maximal-overgroup uniqueness along with the whole module. -/
theorem rankOne_exceptional_linear_source_inputs_of_field_four_borel
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {n : ℕ} (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hn : n = 2)
    (hB : localBorel T L ≤ omegaCentralizer T) :
    Chapter6.Source.IsOneOrTwoA5Modules L (commutatorLayer T L) ∧
      residual H ≤ omegaCentralizer T ∧
      ∀ N : Subgroup G, IsMaximalTwoLocal N → H ≤ N →
        N = normalizer (residual H : Set G) :=
  ⟨D.rankOne_linear_whole_layer_of_field_four_borel h hmany hH hlinear hpsl hn hB,
    D.rankOne_linear_residual_geometry h hmany hH hlinear⟩

/-- The actual exceptional-exit consumer after whole-layer recognition.
Final unconditional assembly retains `qt-d-1222-linear-field-four-borel`;
no decomposition, multiplicity, invariance or semisimplicity premise remains. -/
theorem rankOne_exceptional_linear_of_field_four_borel
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    {n : ℕ} (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n)) (hn : n = 2)
    (hB : localBorel T L ≤ omegaCentralizer T) : ExceptionalExit T L H := by
  obtain ⟨hK,hnf⟩ := D.rankOne_linear_residual_maximal_nonfaithful h hmany hH hlinear
  obtain ⟨_,k,hk,hk2,hm⟩ := D.rankOne_linear_bounded_copies_of_borel
    h.toHypothesis1221 hH hK hnf hpsl hn hB
  exact D.rankOne_exceptional_linear_of_bounded_copies
    h.toHypothesis1221 hH hlinear hK hnf hk hk2 hm

end ChosenModule

end CFSG.Quasithin.Chapter12.Section02
