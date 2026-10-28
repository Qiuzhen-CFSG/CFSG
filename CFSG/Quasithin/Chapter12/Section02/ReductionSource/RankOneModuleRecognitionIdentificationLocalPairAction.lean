module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalPairAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalPairCore

/-!
# Source application of the non-two-pair orthogonal action

Apply the Chapter 6 pair action to the whole reduced layer of the chosen
natural module. This retains the concrete conjugate layers, quaternion core,
normalizer action and central kernel, and identifies the actual quotient
image with S₃ from the source hypothesis that the layer join is not a
two-group.

Source: Aschbacher--Smith, 6.2.6(2), printed p.682.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The source non-two pair acts through the actual symmetric-three quotient. -/
theorem source_local_non_two_pair_outer_symmetricThree
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
    let Q := localPairCore B A
    ∃ (hn : J ≤ normalizer (Q : Set G)) (d : QuaternionCentralProductData Q),
      let f := seedOrthogonalAction J Q hn d
      f.ker.map J.subtype = Q ⊔ (J ⊓ centralizer (J : Set G)) ∧
      Nonempty (f.range ≃* Equiv.Perm (Fin 3)) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n :=
    hnatural.1 ▸ hnatural.2.1
  exact local_non_two_pair_outer_symmetricThree h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    g hleft hright hnon

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
