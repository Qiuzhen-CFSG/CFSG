module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFiveSpace
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalLinearFourExclusion

/-!
# The natural A5 component of the original field-plane action

Apply the complete B.5 reduction to the original four-group offender. The
same offender is a Sylow subgroup of every component it moves. Two conjugate
Sylows generate A5, so its whole moved space has dimension at most four.
The natural quotient has dimension four, removing its central kernel.
The actual moved space therefore is the natural SL2(4) module and has the
component fixed space as a direct complement, in the original quotient.

This supplies the module identification in the last paragraph of 6.2.7.
The remaining Sylow-normalizer contradiction and graph escape are still
required; this module does not assert LocalAnalysis.
Source: Aschbacher--Smith 6.2.7, pp.683--684, applied to 12.2.2(3d), p.795.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterB.SourceInduction
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The original plane offender is a component Sylow, and each component
it moves has the full natural four-space with its actual fixed complement. -/
theorem source_local_one_sided_plane_natural
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
    LocalFieldQuotientAction.PlaneNaturalSection B A U := by
  let B := commutatorLayer T L
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let := (source_local_one_sided_reduced_action D h h611 hnatural g hBA hnon).1.elementary
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc,hfield,_⟩ := local_one_sided_field_plane h611 hnatural hE hfactor g hBA hnon
  exact LocalFieldQuotientAction.field_plane_natural h611 hnatural hE hfactor hfield hUc
    (source_local_one_sided_plane_alternating D h h611 hnatural g hBA hnon)

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
