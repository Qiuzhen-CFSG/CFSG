module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicExclusionCoreResidual
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationCyclicConstructionSelectionAssembly

/-!
# Applying the extraspecial action and core calculations

The numerical step now receives the proved literal Frattini displacement
and faithful action on V, its fixed complement of order two, and the
exact degree bound and divisibility for W. Once it gives p=d=3 and |W|=64, the terminal
component argument receives the proved centralization of O₂(H), normality
of Y=Φ(P)W, and normality of C_{O₂(H)}(Φ(P)). These conclusions are supplied
to the existing cyclic-block assembly on the same subgroups and actions.

Nonprime invariant selection, the remaining numerical reduction, and the
terminal component contradiction are still source obligations owned by
qt-d-12213-cyclic-block. This conditional application does not assert the
unconditional source theorem.
Source: Aschbacher–Smith, 12.2.21–24, printed pp.802–804.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {d : ℕ}

/-- Apply the new Frattini-action and binary-three core results to the original
cyclic-block consumer. Nonprime selection, the remaining rank-one numerical
argument, and the terminal component argument remain with this source owner. -/
theorem cyclicLocalAnalysis_of_nonprime_selection_and_extraspecial_core_steps
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (A : NaturalLocalAnalysis T L V d) (hnone : NoEscape L V) (hTI : IsTISubgroup V)
    (selectionStep : ∀ p H P U g, CyclicConstructionSeed T L V d p H P U g →
      Nat.card P ≠ p → ∃ P' U' g' v, CyclicInvariantSelection T L V d p H P' U' g' v)
    (numerical : ∀ p H P U W g v,
      (S : InvariantOddLocalAnalysis T L V d p H P U W g v) →
      IsExtraspecial p P → Nat.card P = p ^ 3 → Monoid.exponent P = p →
      W ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) = ⊥ →
      ⁅V, (frattini P).map P.subtype⁆ = W ⊓ V →
      Function.Injective (V.normalizerMonoidHom.comp (inclusion S.frattini_normalizes)) →
      Nat.card (V ⊓ centralizer (((frattini P).map P.subtype : Subgroup G) : Set G) :
        Subgroup G) = 2 →
      (letI := S.elementary
       p * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) (Additive W) ∧
         p * orderOf (2 : ZMod p) ∣ Module.finrank (ZMod 2) (Additive W)) →
      p = 3 ∧ d = 3 ∧ Nat.card W = 64)
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
  apply cyclicLocalAnalysis_of_nonprime_selection_and_extraspecial_steps
    h D structural A hnone hTI selectionStep
  · intro p H P U W g v S he hc hx hf
    exact numerical p H P U W g v S he hc hx hf
      (S.frattini_moves_chosen D A hf) (S.frattini_chosen_action_faithful A he hf)
      (S.chosen_split_frattini D A hf).2.2 (S.extraspecial_module_degree A he hc hf)
  · intro p H P U W g v S he hc hx hf hp hd hW
    exact terminal p H P U W g v S he hc hx hf hp hd hW
      (S.extraspecial_binary_three_module_centralizes_core A he hc hf hp hW)
      (S.extraspecial_frattini_module_normal he)
      (S.extraspecial_binary_three_core_centralizer_normal A he hc hf hp hW)

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource
