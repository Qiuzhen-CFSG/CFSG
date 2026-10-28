module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFiveNormal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalFiveNormalizer

/-!
# The normal lifted A5 component in the original plane action

The escaping A5 component is normal in the original field-plane centralizer,
and its embedded image is normal in the full field-plane normalizer. The
external cubic excludes two conjugate A5 components by the three-rank bound.
The existing action quotient marking and every Sylow-normalizer escape
are retained on this same component.

This supplies the relative normality used in the final A5 contradiction of
6.2.7. Cubic centralization, the field-automorphism contradiction and the
subsequent graph argument still remain for LocalAnalysis.
Source: Aschbacher--Smith, 6.2.4(6), 6.2.7, printed pp.680,684;
applied to the original 12.2.2(3d) layer, printed p.795.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
open CFSG.Quasithin.Chapter6.Source CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.ChapterB.SourceInduction
namespace CFSG.Quasithin.Chapter12.Section02.RankOneModule
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}

/-- The actual escaping component is normal in both original local overgroups;
its quotient map agrees with the original field-plane action. -/
theorem source_local_one_sided_five_normal
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
      ∃ K : Subgroup H, K.IsCComponent ∧ K.Normal ∧
        (K.map (inclusion (Subgroup.centralizer_le_normalizer (U : Set G)))).Normal ∧
        K.map π = J ∧
        (∃ e : (K ⧸ pCore 2 K) ≃* J, ∀ k : K,
          ((e (QuotientGroup.mk' (pCore 2 K) k) : J) :
            (LocalFieldQuotientAction.action B U).range) = π k) ∧
        ∀ S : Sylow 2 K, ¬ ((((pResidual 2 (normalizer (S : Set K))).map
          (normalizer (S : Set K)).subtype).map K.subtype).map H.subtype) ≤
            normalizer (L : Set G) := by
  obtain ⟨J,hJ,hJI,⟨eJ⟩,K,hK,hKJ,⟨eK,heK⟩,hescape⟩ :=
    source_local_one_sided_five_normalizer_escape D h h611 hnatural g hBA hnon
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc,hfield,_⟩ := local_one_sided_field_plane h611 hnatural hE hfactor g hBA hnon
  exact ⟨J,hJ,hJI,⟨eJ⟩,K,hK,
    local_field_five_component_normal h611 hnat hfield hUc K hK (eK.trans eJ),
    local_field_five_component_normalizer h611 hnat hfield hUc K hK (eK.trans eJ),
    hKJ,⟨eK,heK⟩,hescape⟩

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
