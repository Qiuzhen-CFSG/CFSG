module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFiveNormalizer
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalFiveSpace

/-!
# The escaping A5 Sylow-normalizer residual in the original plane action

The actual moved A5 component lifts through the original centralizer action.
For every Sylow subgroup of that lift, the two-residual of its normalizer
escapes M. Its natural moved space has no Borel-fixed vectors, whereas field
geometry would force the original V/U into the component fixed space if
that residual lay in M. The nonzero original offender displacement excludes
this possibility. Quotient maps and ambient subgroup embeddings are retained.

This is the first paragraph of the final A5 contradiction in 6.2.7;
the remaining cubic/field-automorphism contradiction and 6.2.8--11 are still
required for LocalAnalysis.
Source: Aschbacher--Smith, 6.2.7, printed p.684, applied to 12.2.2(3d), p.795.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterB.SourceInduction
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The lifted moved component has an actual escaping Sylow-normalizer
residual, in the original Chapter12 subgroups and quotient coordinates. -/
theorem source_local_one_sided_five_normalizer_escape
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
    let H := LocalFieldQuotientAction.Centralizer U
    let π := (LocalFieldQuotientAction.action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∃ J : Subgroup (LocalFieldQuotientAction.action B U).range,
      IsComponent _ J ∧ ⁅J,I⁆ = J ∧ Nonempty (J ≃* alternatingGroup (Fin 5)) ∧
      ∃ K : Subgroup H, K.IsCComponent ∧ K.map π = J ∧
        (∃ e : (K ⧸ pCore 2 K) ≃* J, ∀ k : K,
          ((e (QuotientGroup.mk' (pCore 2 K) k) : J) :
            (LocalFieldQuotientAction.action B U).range) = π k) ∧
        ∀ S : Sylow 2 K, ¬ ((((pResidual 2 (normalizer (S : Set K))).map
          (normalizer (S : Set K)).subtype).map K.subtype).map H.subtype) ≤
            normalizer (L : Set G) := by
  let B := commutatorLayer T L
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let := (source_local_one_sided_reduced_action D h h611 hnatural g hBA hnon).1.elementary
  have hnat : IsNaturalModule L B n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc,hfield,hout⟩ := local_one_sided_field_plane h611 hnatural hE hfactor g hBA hnon
  exact LocalFieldQuotientAction.plane_natural_component_escape h611 hnatural hE hfactor
    (Chapter4.Section03.RankOneUniqueness.unique_sylow_join D h.toHypothesis1221).2.2
    hfield hUc hout (le_centralizer_iff.mpr inf_le_right)
    (source_local_one_sided_plane_natural D h h611 hnatural g hBA hnon)

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
