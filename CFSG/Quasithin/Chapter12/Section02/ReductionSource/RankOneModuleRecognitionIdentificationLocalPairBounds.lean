module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalPairBounds
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalInitial

/-!
# The non-two pair kernel on the original reduced layer

This adapter discharges the chosen-module and characteristic-two inputs in
source 6.2.6, keeping the two conjugates and their literal normalizer
intersections in the ambient group. It proves the actual order-two action
kernel used by the extraspecial pair analysis.
Source: Aschbacher--Smith, 6.2.6, printed p.682, applied to the whole layer
from 12.2.2(3d).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
open Chapter6.Source Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Apply the source 6.2.6 kernel calculation to the chosen whole layer. -/
theorem source_local_pair_normalizer_kernel_card_two
    (D : ChosenModule T L V)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hright : ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom ⊓
      normalizer (commutatorLayer T L : Set G)).relIndex
        ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom) = 2)
    (hnon : ¬ IsPGroup 2 (commutatorLayer T L ⊔
      (commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Subgroup G)) :
    Nat.card ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom ⊓
      centralizer (commutatorLayer T L : Set G) : Subgroup G) = 2 := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n :=
    hnatural.1 ▸ hnatural.2.1
  exact local_pair_normalizer_kernel_card_two h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    g hright hnon

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
