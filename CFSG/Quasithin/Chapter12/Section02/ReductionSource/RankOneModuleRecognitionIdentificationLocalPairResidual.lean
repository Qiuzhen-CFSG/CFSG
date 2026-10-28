module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalPairResidual
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalPairQuotient

/-!
# The non-two-pair clause for the whole reduced layer

The chosen module supplies E.6.1, and the explicit natural-module premise
supplies the order-sixteen layer. The Chapter 6 source analysis then proves
all four conclusions of LocalAnalysis.non_two_pair on the original carriers:
the quaternion two-core, symmetric-three quotient, containment in O² and
the precise center/intersection identity. No LocalAnalysis witness or later
recognition theorem is assumed.

Source: Aschbacher--Smith, 6.2.6(2), printed p.682.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Discharge `LocalAnalysis.non_two_pair` for the actual whole reduced layer. -/
theorem source_local_non_two_pair
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
    Nonempty (QuaternionCentralProductData (pCore 2 J)) ∧
      Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3)) ∧
      pCore 2 J ≤ pResidual 2 J ∧
      B ⊓ A = ((center (pCore 2 J)).map (pCore 2 J).subtype).map J.subtype := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n :=
    hnatural.1 ▸ hnatural.2.1
  exact local_non_two_pair h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    g hleft hright hnon

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
