module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalCubicSylow
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalFieldKernel

/-!
# The original cubic centralizes binary-three action components in Chapter12

The original whole reduced commutator layer supplies the field plane and
its centralizer Sylow, normalized by the actual plane-normalizer residual.
The compatible component lifts and Sylow intersections prove that the
previously constructed cubic commutes with every PSL₃(2) component of the
faithful action. Its quotient coordinates and the three-subgroups
noncentrality claim are retained in the same witnesses.

The moved-module arguments, the A5 and SL₃(4) exclusions, and the graph
escape remain obligations of the common local analysis.
Source: Aschbacher--Smith, 6.2.7, printed p.683, applied to12.2.2(3d), p.795.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The residual-invariant Sylow on the original noncommuting field plane. -/
theorem source_local_one_sided_field_sylow
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
    let H := centralizer (U : Set G)
    ∃ S : Sylow 2 H, B ≤ (S : Subgroup H).map H.subtype ∧
      fieldLocalResidual L U ≤ normalizer ((S : Subgroup H).map H.subtype : Set G) ∧
      normalizer ((S : Subgroup H).map H.subtype : Set G) ≤ normalizer (L : Set G) := by
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc,hfield,_⟩ := local_one_sided_field_plane h611 hnatural hE hfactor g hBA hnon
  exact local_field_residual_sylow h611 hnatural hE hfield hUc

/-- The same marked cubic and its noncentrality claim, now with proved
centralization of each actual PSL₃(2) action component. -/
theorem source_local_one_sided_cubic_binary_centralization
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
    LocalFieldQuotientAction.CubicBinarySection L B A U := by
  let B := commutatorLayer T L
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc,hfield,hout⟩ := local_one_sided_field_plane h611 hnatural hE hfactor g hBA hnon
  let := (source_local_one_sided_reduced_action D h h611 hnatural g hBA hnon).1.elementary
  obtain ⟨ρ,c,hfaith,hI,hIc,d,hd,ho,hBD,η,c',hcoords,hrestrict,horder,hclaim,hmark⟩ :=
    source_local_one_sided_cubic_action D h h611 hnatural g hBA hnon
  unfold LocalFieldQuotientAction.CubicBinarySection
  refine ⟨ρ,c,hfaith,hI,hIc,d,hd,ho,hBD,η,c',hcoords,hrestrict,horder,hclaim,hmark,?_⟩
  intro K hK ⟨e⟩
  exact LocalFieldQuotientAction.binary_component_cubic_commutes h611 hnatural hE hfactor
    (Chapter4.Section03.RankOneUniqueness.unique_sylow_join D h.toHypothesis1221).2.2
    hfield hUc hout K hK e ρ η hrestrict d hd (ho ▸ pow_orderOf_eq_one d)

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
