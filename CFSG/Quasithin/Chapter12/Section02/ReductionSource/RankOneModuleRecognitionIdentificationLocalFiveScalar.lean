module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFiveScalar
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalFiveCubic

/-!+# The original field-plane cubic is a nonidentity scalar

Keep the original natural moved-space marking and extend the same quotient
coordinates to the plane-normalizer residual. The checked cubic centralizes
an actual moved A5 component. Its whole moved space is natural SL2(4), so
the scalar commutant identifies the cubic with a field scalar. The source
three-subgroups claim, applied to the preimage of this same component,
excludes the identity scalar.

The literal cubic, quotient maps, offender Sylow, and fixed complement are
retained together. The outer two-action contradiction and subsequent graph
geometry remain necessary for LocalAnalysis.
Source: Aschbacher--Smith 6.2.7, printed p.684; the original Chapter12
application is 12.2.2(3d), printed p.795.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The original cubic acts on the actual natural moved component as a
nonidentity scalar of order three, in the original quotient coordinates. -/
theorem source_local_one_sided_cubic_scalar
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
    LocalFieldQuotientAction.CubicScalarSection L B A U := by
  let B := commutatorLayer T L
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let H := LocalFieldQuotientAction.Centralizer U
  let J := conjugateSpanBy B H
  let P := H ⊔ fieldLocalResidual L U
  let π := (LocalFieldQuotientAction.action B U).rangeRestrict
  let := (source_local_one_sided_reduced_action D h h611 hnatural g hBA hnon).1.elementary
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc,hfield,_⟩ := local_one_sided_field_plane h611 hnatural hE hfactor g hBA hnon
  let : IsElementaryAbelian 2 J :=
    local_plane_closure_elementary h611 hnatural hE hfactor inf_le_left hUc.ge
  obtain ⟨ρ,c,hfaith,hI,_,hIc,_,_,_,_,_,hmodels,_,hmark⟩ :=
    source_local_one_sided_plane_natural D h h611 hnatural g hBA hnon
  obtain ⟨d,hd,ho,hBD,η,c',hcoords,hrestrict,horder⟩ :=
    field_plane_cubic_section_action hnat hfield hUc c
  have hclaim := local_one_sided_cubic_section_noncentral
    h611 hnatural hE hfactor g hBA hnon η c' d hd hBD
  obtain ⟨K,hK,hKI,eK,hcomm⟩ := source_local_one_sided_five_cubic_commutes
    D h h611 hnatural g hBA hnon ρ η hrestrict d hd (ho ▸ pow_orderOf_eq_one d)
  obtain ⟨_,_,⟨F,hF,⟨a⟩⟩,hsyl,hcompl⟩ := hmodels K hK hKI
  have hIK : (A.subgroupOf H).map π ≤ K := by
    obtain ⟨S,hS⟩ := hsyl
    rw [hS]
    exact map_subtype_le _
  have hscalar := LocalFieldQuotientAction.section_natural_cubic_scalar
    (show H ≤ P from le_sup_left) (show A ≤ H from le_centralizer_iff.mpr inf_le_right)
    π (LocalFieldQuotientAction.action B U).rangeRestrict_surjective ρ c η c' hcoords hrestrict
    ⟨d,mem_sup_right hd⟩ (Subtype.ext (ho ▸ pow_orderOf_eq_one d)) K hIK hcomm hclaim F a
  unfold LocalFieldQuotientAction.CubicScalarSection
  refine ⟨ρ,c,hfaith,hI,hIc,d,hd,ho,hBD,η,c',hcoords,hrestrict,horder,hclaim,?_,
    K,hK,hKI,eK,hcomm,hsyl,hcompl,F,hF,a,hscalar⟩
  intro j
  rw [hcoords]
  exact hmark j

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
