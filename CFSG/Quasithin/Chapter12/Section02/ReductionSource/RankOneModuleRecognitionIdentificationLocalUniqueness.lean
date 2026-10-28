module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalUniqueness
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalInitial

/-!
# Hyperplane uniqueness on the original Chapter 12 layer

The chosen module supplies the E.6.1 uniqueness and relative TI hypotheses
for [R₂(LT),L]. Thus the ambient centralizer rigidity and hyperplane uniqueness
of 6.2.5(6) hold for this literal layer. The same transport excludes trivial
actions of the two index-two normalizer intersections in source 6.2.6.

This discharges the hyperplane_unique field of the common LocalAnalysis
contract without assuming that record. The remaining fields stay with
qt-d-1222-recognition-local-analysis; final identification is assembled by
qt-d-1222-rankone-recognition-identification.

Source: Aschbacher--Smith, 6.1.10(1), 6.2.5(6), and 6.2.6, pp.670 and 681,
applied to the whole reduced layer in 12.2.2(3d), p.795.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- A subgroup of order at least eight detects the full ambient centralizer of
[R₂(LT),L], with the source uniqueness hypothesis discharged. -/
theorem source_local_large_subgroup_centralizer
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    {U : Subgroup G} (hUB : U ≤ commutatorLayer T L) (hU : 8 ≤ Nat.card U) :
    centralizer (U : Set G) = centralizer (commutatorLayer T L : Set G) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  exact local_large_subgroup_centralizer h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat) hUB hU

/-- The exact hyperplane_unique clause of the recognition local analysis. -/
theorem source_local_hyperplane_unique
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hcard : 8 ≤ Nat.card (commutatorLayer T L ⊓
      (commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    (commutatorLayer T L).map (MulAut.conj g).toMonoidHom = commutatorLayer T L := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  exact local_hyperplane_unique h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat) g hcard

/-- The first action exclusion in source 6.2.6 on the original conjugate pair. -/
theorem source_local_pair_normalizer_action_nontrivial
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
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
        ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom) = 2) :
    ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ⊓
      normalizer (commutatorLayer T L : Set G) ≤ centralizer (commutatorLayer T L : Set G) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  exact local_pair_normalizer_action_nontrivial h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat) g hleft hright

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
