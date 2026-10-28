module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalPairQuotient
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalPairFusion

/-!
# The literal two-core and quotient of the original layer pair

Internal fusion removes the central orthogonal-action kernel for the actual
whole reduced layer. The quaternion subgroup is the actual embedded O₂ of
the generated pair, whose quotient is S₃. The chosen module discharges the
original E.6.1 hypotheses used by hyperplane uniqueness.

Source: Aschbacher--Smith, 6.2.6(2), printed p.682.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The source pair core is its literal two-core, with symmetric-three quotient. -/
theorem source_local_non_two_pair_twoCore_quotient
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hleft : (commutatorLayer T L ⊓ normalizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G)).relIndex
        (commutatorLayer T L) = 2)
    (hright : ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom ⊓
      normalizer (commutatorLayer T L : Set G)).relIndex
        ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom) = 2)
    (hnon : ¬ IsPGroup 2 (commutatorLayer T L ⊔
      (commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    let B := commutatorLayer T L
    let A := B.map (MulAut.conj g).toMonoidHom
    let J := B ⊔ A
    localPairCore B A = J.pCoreIn 2 ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n :=
    hnatural.1 ▸ hnatural.2.1
  exact local_non_two_pair_twoCore_quotient h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    g hleft hright hnon

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
