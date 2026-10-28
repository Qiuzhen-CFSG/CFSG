module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationLocalFiveCubic
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleRecognitionIdentificationLocalFiveNormal

/-!
# The cubic centralizes the original A5 action component

The escaping Sylow normalizer forces an outer two-actor on the lifted A5
quotient. Its two-action image is therefore Sylow in Aut(A5) = S5, whose
Sylow normalizer is a two-group. The original cubic normalizes this image
and hence centralizes the component quotient. The compatible quotient map
transfers this commutation to the original marked field-plane representation.

The cubic's scalar action and the field-involution contradiction remain
for the final A5 exclusion and LocalAnalysis.
Source: Aschbacher--Smith, final paragraph of 6.2.7, printed p.684;
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

/-- Every extension of the original quotient marking has a moved A5 component
centralized by the same plane-residual cubic. -/
theorem source_local_one_sided_five_cubic_commutes
    (D : ChosenModule T L V) (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (h611 : Hypothesis611 KnownSimple.IsKnownSimple T L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (hnatural : Conclusion6127 (T : Subgroup G) L
      (normalizer (L : Set G)) (wholeReduced T L) n)
    (g : G)
    (hBA : commutatorLayer T L ≤ normalizer
      ((commutatorLayer T L).map (MulAut.conj g).toMonoidHom : Set G))
    (hnon : ¬ (commutatorLayer T L).map (MulAut.conj g).toMonoidHom ≤
      centralizer (commutatorLayer T L : Set G))
    :
    let B := commutatorLayer T L
    let A := B.map (MulAut.conj g).toMonoidHom
    let U := B ⊓ centralizer (A : Set G)
    let H := LocalFieldQuotientAction.Centralizer U
    let π := (LocalFieldQuotientAction.action B U).rangeRestrict
    let I := (A.subgroupOf H).map π
    ∀ {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
      (ρ : Representation (ZMod 2) (LocalFieldQuotientAction.action B U).range W)
      (η : Representation (ZMod 2) (H ⊔ fieldLocalResidual L U : Subgroup G) W),
      (∀ k : H, η (inclusion le_sup_left k) = ρ (π k)) →
      ∀ (d : G) (hd : d ∈ fieldLocalResidual L U), d^3=1 →
    ∃ J : Subgroup (LocalFieldQuotientAction.action B U).range,
      IsComponent _ J ∧ ⁅J,I⁆ = J ∧ Nonempty (J ≃* alternatingGroup (Fin 5)) ∧
      ∀ j : J, Commute (η.asGroupHom ⟨d,mem_sup_right hd⟩) (ρ.asGroupHom j) := by
  dsimp only
  intro W _ _ ρ η hrestrict d hd hd3
  obtain ⟨J,hJ,hJI,⟨eJ⟩,K,hK,_,_,_,⟨eK,heK⟩,hescape⟩ :=
    source_local_one_sided_five_normal D h h611 hnatural g hBA hnon
  have hnat : IsNaturalModule L (commutatorLayer T L) n := hnatural.1 ▸ hnatural.2.1
  have hE := source_natural_layer_hypothesisE61 D h.toHypothesis1221 h611 hnat
  have hfactor := source_central_line_normalizer_factorization
    D h.toHypothesis1221 h611 hnatural.2.2.2.1
  obtain ⟨hUc,hfield,_⟩ := local_one_sided_field_plane h611 hnatural hE hfactor g hBA hnon
  exact ⟨J,hJ,hJI,⟨eJ⟩,LocalFieldQuotientAction.five_component_cubic_commutes
    h611 hnatural hE hfield hUc J eJ K hK eK heK hescape ρ η hrestrict d hd hd3⟩

/-- The same marked cubic and its noncentrality claim, now with proved
centralization of an actual moved A5 action component. -/
theorem source_local_one_sided_cubic_five_centralization
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
    LocalFieldQuotientAction.CubicFiveSection L B A U := by
  let B := commutatorLayer T L
  let A := B.map (MulAut.conj g).toMonoidHom
  let U := B ⊓ centralizer (A : Set G)
  let := (source_local_one_sided_reduced_action D h h611 hnatural g hBA hnon).1.elementary
  obtain ⟨ρ,c,hfaith,hI,hIc,d,hd,ho,hBD,η,c',hcoords,hrestrict,horder,hclaim,hmark⟩ :=
    source_local_one_sided_cubic_action D h h611 hnatural g hBA hnon
  unfold LocalFieldQuotientAction.CubicFiveSection
  refine ⟨ρ,c,hfaith,hI,hIc,d,hd,ho,hBD,η,c',hcoords,hrestrict,horder,hclaim,hmark,?_⟩
  exact source_local_one_sided_five_cubic_commutes D h h611 hnatural g hBA hnon
    ρ η hrestrict d hd (ho ▸ pow_orderOf_eq_one d)

end CFSG.Quasithin.Chapter12.Section02.RankOneModule
