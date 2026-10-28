module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalPairFusion
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalPairAction

/-!
# Internal conjugacy for the original whole reduced layer

The chosen-module hypotheses supply E.6.1. The original natural layers in a
non-two pair, and their mutual normalizer hyperplanes, are conjugate by an
element of their own join. This supplies the internal-fusion premise in the
source kernel-removal argument; it is stronger than ambient conjugacy.

Source: Aschbacher--Smith, 6.2.6(2), printed p.682.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Internal conjugacy of the original two layers and their hyperplanes. -/
theorem source_local_non_two_pair_internal_conjugacy
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
    ∃ k ∈ B ⊔ A,
      (B ⊓ normalizer (A : Set G)).map (MulAut.conj k).toMonoidHom =
        A ⊓ normalizer (B : Set G) ∧
      B.map (MulAut.conj k).toMonoidHom = A := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n :=
    hnatural.1 ▸ hnatural.2.1
  exact local_non_two_pair_internal_conjugacy h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    g hleft hright hnon

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
