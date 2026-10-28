module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldTransvections
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalFieldReduced

/-!
# The moved-line branch on the original Chapter 12 quotient

A nontrivial intersection of the original fixed and commutator planes
makes the conjugate four-group act by transvections with one center.
The faithful image has trivial two-core, so genuine G.3 applies and
provides the canonical full linear blocks and their decomposition.
The chosen module discharges the earlier local and normalizer premises.
This is the recognition step of the moved-line branch; its cubic-action
contradiction remains to be proved.

Source: Aschbacher--Smith, 6.2.7, printed pp.682--683, applied to the
whole reduced layer of 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open BinaryTransvectionGroups
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The original moved line and conjugate image satisfy the genuine G.3
hypotheses and conclusions, retaining the actual quotient coordinates. -/
theorem source_local_one_sided_line_recognition
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hBA : commutatorLayer T L ≤ normalizer ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤ centralizer (commutatorLayer T L : Set G))
    (hmeet : (commutatorLayer T L ⊓ centralizer ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G)) ⊓
      ⁅(commutatorLayer T L).map (MulAut.conj g).toMonoidHom, commutatorLayer T L⁆ ≠ ⊥) :
    let B := commutatorLayer T L
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    letI := (source_local_one_sided_reduced_action D h h611 hnatural g hBA hnon).1.elementary
    let W := Additive (LocalFieldQuotientAction.space B U)
    let H := LocalFieldQuotientAction.Centralizer U
    let J := conjugateSpanBy B H
    let π := (LocalFieldQuotientAction.action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ (ρ : Representation (ZMod 2) (LocalFieldQuotientAction.action B U).range W)
      (c : BinaryConjugationSection H J U (ρ.comp π)),
      Function.Injective ρ ∧ IsOffender ρ I ∧ Nat.card I = 4 ∧
      LocalFieldQuotientAction.LineRecognition ρ I (c.imageSpace ⁅A,B⁆) ∧
      ∀ j : J, ∃ hj : (j : G) ∈ H, LocalFieldQuotientAction.projection U ⟨j, hj⟩ =
        ((c.coordinates j).toAdd.toMul : LocalFieldQuotientAction.Ambient U) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  exact LocalFieldQuotientAction.exists_line_recognition h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    (source_central_line_normalizer_factorization D h.toHypothesis1221 h611 hnatural.2.2.2.1)
    g hBA hnon hmeet

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
