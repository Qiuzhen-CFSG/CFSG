module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldReduced
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalInitial

/-!
# The reduced field-plane action on the original Chapter 12 layer

The chosen module supplies the earlier local and normalizer hypotheses.
For a noncommuting conjugate normalized by [R₂(LT),L], its fixed plane U
gives the literal elementary closure J in C_G(U). The section J/U is
reduced, its faithful action has trivial two-core, and the actual conjugate
image is an offender of order four. Its representation retains the
original quotient coordinates through a binary conjugation section.

These are inputs to the remaining component exclusions in 6.2.7.
Source: Aschbacher--Smith, 6.2.4(4) and 6.2.7, printed pp.680,682--683,
applied to the whole reduced layer in 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The original field-plane quotient is reduced and its actual action has
trivial two-core, with all earlier local-action premises discharged. -/
theorem source_local_one_sided_reduced_action
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
    IsPReduced 2 (LocalFieldQuotientAction.space B U) ∧
      pCore 2 (LocalFieldQuotientAction.action B U).range = ⊥ := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc, hfield, _⟩ := local_one_sided_field_plane h611 hnatural hE hfactor g hBA hnon
  exact ⟨LocalFieldQuotientAction.reduced_space h611 hnatural hE hfactor hfield hUc.ge,
    LocalFieldQuotientAction.action_range_core h611 hnatural hE hfactor hfield hUc.ge⟩

/-- The actual conjugate four-group is an offender on the faithful original
section, retaining the literal quotient coordinate of every closure element. -/
theorem source_local_one_sided_faithful_offender
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
    letI := (source_local_one_sided_reduced_action D h h611 hnatural g hBA hnon).1.elementary
    let H := LocalFieldQuotientAction.Centralizer U
    let J := conjugateSpanBy B H
    let π := (LocalFieldQuotientAction.action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ (ρ : Representation (ZMod 2) (LocalFieldQuotientAction.action B U).range
        (Additive (LocalFieldQuotientAction.space B U)))
      (c : Representation.BinaryConjugationSection H J U (ρ.comp π)),
      Function.Injective ρ ∧ Representation.BinaryOffender.IsOffender ρ I ∧
      Nat.card I = 4 ∧
      ∀ j : J, ∃ hj : (j : G) ∈ H, LocalFieldQuotientAction.projection U ⟨j, hj⟩ =
        ((c.coordinates j).toAdd.toMul : LocalFieldQuotientAction.Ambient U) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  exact LocalFieldQuotientAction.exists_faithful_offender h611 hnatural
    (source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat)
    (source_central_line_normalizer_factorization D h.toHypothesis1221 h611 hnatural.2.2.2.1)
    g hBA hnon

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
