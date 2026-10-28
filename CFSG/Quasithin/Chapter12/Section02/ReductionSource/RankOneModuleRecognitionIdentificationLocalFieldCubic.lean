module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFieldCubicAction
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalFieldReduced

/-!
# The field-plane cubic on the original Chapter 12 layer

For a noncommuting conjugate normalized by the whole reduced commutator
layer, source 6.2.4(5) identifies the actual plane-normalizer residual:
its two-core is its intersection with the plane centralizer, and its
quotient is cyclic of order three. The original faithful offender marking
extends to an actual cubic in that residual. This cubic fully moves the
original layer and has order three on the same marked quotient.

The marked noncentrality conclusion is the three-subgroups claim in the
second paragraph of 6.2.7. The component restrictions and remaining
exclusions of that lemma, and the subsequent graph escape, are separate
obligations; no LocalAnalysis premise is used here.

Source: Aschbacher--Smith, 6.2.4(5) and 6.2.7, printed pp.680,682,
applied to 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- Source 6.2.4(5) on the actual fixed plane of the Chapter12 conjugate
pair, with the literal residual, two-core, and centralizer. -/
theorem source_local_one_sided_field_residual
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
    let U := B ⊓ centralizer (B.map (MulAut.conj g).toMonoidHom : Set G)
    let K := fieldLocalResidual L U
    K.pCoreIn 2 = K ⊓ centralizer (U : Set G) ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Multiplicative (ZMod 3)) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc,hfield,_⟩ := local_one_sided_field_plane h611 hnatural hE hfactor g hBA hnon
  exact field_plane_residual_structure hnat hfield hUc

/-- The original faithful offender section extends to the actual cubic.
Its original quotient coordinates, order-three action, and noncentrality
claim from paragraph two of 6.2.7 are retained together. -/
theorem source_local_one_sided_cubic_action
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
    LocalFieldQuotientAction.CubicSection L B A U := by
  let B := commutatorLayer T L
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let H := LocalFieldQuotientAction.Centralizer U
  let J := conjugateSpanBy B H
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc,hfield,hJe,_,_,_,_,_,_,_⟩ :=
    local_one_sided_closure_geometry h611 hnatural hE hfactor g hBA hnon
  let := (source_local_one_sided_reduced_action D h h611 hnatural g hBA hnon).1.elementary
  let : IsElementaryAbelian 2 J := hJe
  obtain ⟨ρ,c,hfaith,hI,hIc,hmark⟩ := source_local_one_sided_faithful_offender D h h611 hnatural g hBA hnon
  obtain ⟨d,hd,ho,hBD,η,c',hcoords,hrestrict,horder⟩ :=
    field_plane_cubic_section_action hnat hfield hUc c
  unfold LocalFieldQuotientAction.CubicSection
  refine ⟨ρ,c,hfaith,hI,hIc,d,hd,ho,hBD,η,c',hcoords,hrestrict,horder,?_,?_⟩
  · exact local_one_sided_cubic_section_noncentral h611 hnatural hE hfactor g hBA hnon η c' d hd hBD
  · intro j
    rw [hcoords]
    exact hmark j

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
