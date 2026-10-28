module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryWeakClosure
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionNaturalContainedWeakClosureRanksGlobal

/-!
# The field-centralizer weak-closure bounds on the original layer

The proved global rank equality and the field-plane A₂ exclusion give
W₀(C_P(U),B) ≤ C_P(B), and the same bound for W₁ when n > 2.
The ambient Sylow may be the one chosen for U; no transport of the
original Chapter12 reduced module is needed.
Source: Aschbacher–Smith, 6.1.14(3), printed p.671.
-/

public section
open Subgroup
open CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V U : Subgroup G} {n : ℕ}

theorem source_field_fixedSpace_weak_closure
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (h611 : Chapter6.Source.Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Chapter6.Source.IsNaturalModule L (commutatorLayer T L) n)
    (hfield : IsInvolutoryFieldFixedSpace L (normalizer (L : Set G))
      (commutatorLayer T L) U n) (hUne : U ≠ ⊥)
    (P : Sylow 2 G)
    (hPB : (P : Subgroup G) ≤ normalizer (commutatorLayer T L : Set G))
    {i : ℕ} (hi : i + 2 ≤ n) :
    Chapter6.Source.W (commutatorLayer T L)
        ((P : Subgroup G) ⊓ centralizer (U : Set G)) i ≤
      (P : Subgroup G) ⊓ centralizer (commutatorLayer T L : Set G) := by
  let : IsElementaryAbelian 2 (commutatorLayer T L) := h611.layer_elementary
  have hE := source_natural_layer_hypothesisE61 D h h611 hnatural
  have hs := (source_natural_layer_rank_bounds D h h611 hnatural).2.2
  have hb := field_fixedSpace_weak_closure hnatural hE.normalizer_le hfield hUne hs
    ((P : Subgroup G) ⊓ centralizer (U : Set G)) (inf_le_left.trans hPB) inf_le_right hi
  exact hb.trans (inf_le_inf_right _ inf_le_left)
end CFSG.Quasithin.Chapter12.Section02.RankOneModule
