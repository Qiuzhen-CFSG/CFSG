module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalOneSidedAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalInitial

/-!
# The one-sided contrary configuration on the original Chapter 12 layer

The chosen module supplies E.6.1 and the central-line normalizer
factorization. Hence a noncommuting conjugate normalized by [R₂(LT),L]
gives an escaping field plane, its elementary centralizer closure, and
the exact central-plane intersection. The conjugate layer induces a
four-group on the literal quotient of that closure by the field plane.

These are the initial reductions of 6.2.7, not its final contradiction.
The component/action classification and the subsequent 6.2.8 graph
argument remain in the common-local-analysis assembly task.

Source: Aschbacher--Smith, 6.2.7, printed p.682, applied to the whole
reduced layer of 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The initial one-sided configuration, with the chosen module discharging
all earlier normalizer and local-action premises. -/
theorem source_local_one_sided_closure_geometry
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hBA : commutatorLayer T L ≤ normalizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    let B := commutatorLayer T L
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    let H := centralizer (U : Set G)
    let J := conjugateSpanBy B H
    let F := ⁅A, B⁆
    Nat.card U = 4 ∧ IsInvolutoryFieldFixedSpace L (normalizer (L : Set G)) B U n ∧
      IsElementaryAbelian 2 J ∧ J ≤ H.pCoreIn 2 ∧
      Nat.card F = 4 ∧ F = A ⊓ centralizer (B : Set G) ∧
      F ≤ J ∧ J ≤ normalizer (A : Set G) ∧
      ⁅A, J⁆ = F ∧ A ⊓ J = F := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  exact local_one_sided_closure_geometry h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    (source_central_line_normalizer_factorization D h.toHypothesis1221 h611 hnatural.2.2.2.1)
    g hBA hnon

/-- The four-group is the actual image on the original field-plane quotient. -/
theorem source_local_one_sided_image_four
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hBA : commutatorLayer T L ≤ normalizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    let B := commutatorLayer T L
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    let I := (A.subgroupOf (centralizer (U : Set G))).map (LocalFieldQuotientAction.action B U)
    Nat.card I = 4 ∧ IsElementaryAbelian 2 I := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  exact LocalFieldQuotientAction.layer_image_four h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    (source_central_line_normalizer_factorization D h.toHypothesis1221 h611 hnatural.2.2.2.1)
    g hBA hnon

/-- The centralizer closure has the exact source fixed index on the conjugate layer. -/
theorem source_local_one_sided_closure_action_index
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hBA : commutatorLayer T L ≤ normalizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G)) :
    let B := commutatorLayer T L
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    (centralizer (A : Set G)).relIndex (conjugateSpanBy B (centralizer (U : Set G))) = 4 := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  exact local_one_sided_closure_action_index h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    (source_central_line_normalizer_factorization D h.toHypothesis1221 h611 hnatural.2.2.2.1)
    g hBA hnon

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
