module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalPairCore
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalPairBounds

/-!
# The quaternion pair core on the whole reduced layer

Apply the source 6.2.6 pair calculation to the actual whole reduced layer of
12.2.2(3d). The chosen module supplies the characteristic-two input, and the
natural-module premise supplies the order-sixteen geometry. The resulting
order-32 subgroup has actual quaternion factors, is normalized by the generated
pair, and has center equal to the literal intersection of the two layers.

The subsequent two-core and quotient identification remains with the common
local-analysis owner, qt-d-1222-recognition-local-analysis; no LocalAnalysis
witness is assumed here.
Source: Aschbacher--Smith, 6.2.6(2), printed p.682.
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Construct the source quaternion pair core for the original reduced layer. -/
theorem source_local_non_two_pair_quaternion_core
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
    let Q := localPairCore B A
    Nat.card (B ⊓ A : Subgroup G) = 2 ∧
      ⁅B ⊓ normalizer (A : Set G), A ⊓ normalizer (B : Set G)⁆ = B ⊓ A ∧
      Nat.card Q = 32 ∧ B ⊔ A ≤ normalizer (Q : Set G) ∧
      (center Q).map Q.subtype = B ⊓ A ∧
      Nonempty (QuaternionCentralProductData Q) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n :=
    hnatural.1 ▸ hnatural.2.1
  exact local_non_two_pair_quaternion_core h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    g hleft hright hnon

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
