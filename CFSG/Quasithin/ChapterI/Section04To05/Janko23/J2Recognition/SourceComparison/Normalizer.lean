module
public import Theory.SpecificGroups.AlternatingSix.TripleCoverComparison
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.ConcreteSystem
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.InvolutionGeometry.Applications
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J2Recognition.SourceLocal.System

/-!
# Comparing the actual source and target vertex normalizers

The source C_G(X) and the literal ATLAS centralizer are perfect triple
covers of A₆. Schur uniqueness, with its quotient map retained, compares
these covers. Their chosen involutions induce exceptional automorphisms
of A₆; the exceptional conjugacy theorem and uniqueness of perfect lifts
make the comparison intertwine those actual involutions. The internal
semidirect decompositions then give an isomorphism of the full normalizers.

The comparison retains the centralizer inclusion and sends the source
inverter to the ATLAS splitter. It also preserves the marked cubic
subgroup, because that subgroup is the center of the centralizer. The
last theorem applies the construction to the literal vertex groups in
the two uniqueness systems. Aligning the edge fixer and local A₅ remains
necessary to obtain a similarity; source pentagon contraction remains
independent. No unconditional J₂ recognition is asserted here.

Source: Aschbacher, *Sporadic Groups* (1994), 47.10, pp.266–267,
using the completed source 47.1–47.3 and GLS, volume 3, Theorem 5.2.3
and Proposition 5.2.7(a).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Janko23.J2Recognition.SourceComparison
open SourceLocal SourceLocal.PrimeNormalizers.ThreeLocal
open Sporadic.LeechRelated.J2
variable {G : Type*} [Group G] [Finite G] {D : Seed G}

/-- Retain natural six-point coordinates in the central-cover comparison. -/
theorem centralizers_over_coordinates (H : CentralizerCalculation D)
    (e1 : (C D ⧸ XC D) ≃* alternatingGroup (Fin 6))
    (e0 : RecognitionGeometry.VertexExtension.CentralQuotient ≃* alternatingGroup (Fin 6)) :
    ∃ (k : MulAut (alternatingGroup (Fin 6)))
      (e : C D ≃* RecognitionGeometry.VertexExtension.C),
      k ∈ AlternatingSix.ShadowLocal.natural ∧
      (∀ x, e0 (RecognitionGeometry.VertexExtension.centralQuotientMap (e x)) =
        k (e1 (QuotientGroup.mk' (XC D) x))) ∧
      (∀ x, e (CentralizerCalculation.centralizerAction H.inverter x) =
        RecognitionGeometry.VertexExtension.splitterAction (e x)) := by
  let := H.quasisimple
  let := RecognitionGeometry.VertexExtension.C_isQuasisimple ConcreteSystem.card_M
  let f : Covering (C D) (alternatingGroup (Fin 6)) :=
    { toMonoidHom := e1.toMonoidHom.comp (QuotientGroup.mk' (XC D))
      surjective := e1.surjective.comp (QuotientGroup.mk'_surjective _) }
  have hf : f.toMonoidHom.ker = XC D := by
    ext x
    change e1 (QuotientGroup.mk' _ x) = 1 ↔ x ∈ _
    rw [e1.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let α := H.alternatingQuotient.some.symm.trans e1
  have hα (x : C D) : f x = α (H.coverMap x) := by
    change e1 (QuotientGroup.mk' _ x) =
      e1 (H.alternatingQuotient.some.symm (H.alternatingQuotient.some (QuotientGroup.mk' _ x)))
    rw [MulEquiv.symm_apply_apply]
  let g : Covering RecognitionGeometry.VertexExtension.C (alternatingGroup (Fin 6)) :=
    { toMonoidHom := e0.toMonoidHom.comp RecognitionGeometry.VertexExtension.centralQuotientMap
      surjective := e0.surjective.comp (QuotientGroup.mk'_surjective _) }
  have hg : g.toMonoidHom.ker = RecognitionGeometry.VertexExtension.XC := by
    ext x
    change e0 (QuotientGroup.mk' _ x) = 1 ↔ x ∈ _
    rw [e0.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  let b := MulAut.congr α (H.quotientAction H.inverter)
  let c := RecognitionGeometry.VertexExtension.normalizerAlternatingAction e0 RecognitionGeometry.VertexExtension.splitterM
  apply AlternatingSix.TripleCoverComparison.equiv_intertwining_over_natural f g
    (by rw [hf]; exact CentralizerCalculation.card_XC)
    (by rw [hg]; exact RecognitionGeometry.VertexExtension.card_XC)
    (CentralizerCalculation.centralizerAction H.inverter) RecognitionGeometry.VertexExtension.splitterAction b c
  · change (MulAut.congr α) (H.quotientAction H.inverter) ^ 2 = 1
    rw [← map_pow, ← map_pow, ← H.inverter_order, pow_orderOf_eq_one, map_one, map_one]
  · change RecognitionGeometry.VertexExtension.normalizerAlternatingAction e0 RecognitionGeometry.VertexExtension.splitterM ^ 2 = 1
    rw [← map_pow, show RecognitionGeometry.VertexExtension.splitterM ^ 2 = 1 from
      Subtype.ext RecognitionGeometry.VertexExtension.splitter_square, map_one]
  · let : AlternatingSix.ShadowLocal.natural.Normal := normal_of_index_eq_two
      GLS3.Chapter5.naturalAlternatingAutomorphismSubgroup_index
    have hn := (mem_normalizer_iff.mp (show α ∈ normalizer
      (AlternatingSix.ShadowLocal.natural : Set (MulAut (alternatingGroup (Fin 6)))) from
      by rw [normalizer_eq_top]; trivial)) (H.quotientAction H.inverter)
    exact fun h => H.quotientAction_inverter_not_natural (hn.mpr h)
  · exact RecognitionGeometry.VertexExtension.splitterAction_not_natural e0
      (RecognitionGeometry.VertexExtension.C_isPerfect ConcreteSystem.card_M)
  · intro x
    rw [hα, hα]
    change α (H.coverMap (CentralizerCalculation.centralizerAction H.inverter x)) =
      α (H.quotientAction H.inverter (α.symm (α (H.coverMap x))))
    rw [α.symm_apply_apply, H.quotientAction_apply]
  · intro x
    exact (RecognitionGeometry.VertexExtension.normalizerAlternatingAction_apply e0 RecognitionGeometry.VertexExtension.splitterM x).symm

private noncomputable def complementEquiv (H : CentralizerCalculation D) :
    zpowers H.inverter ≃* RecognitionGeometry.VertexExtension.S :=
  (alternatingGroup.FiveLocalGeometry.CubicEdges.involutionZpowersEquiv
    H.inverter H.inverter_order).symm.trans
    (alternatingGroup.FiveLocalGeometry.CubicEdges.involutionZpowersEquiv
      RecognitionGeometry.VertexExtension.splitterM RecognitionGeometry.VertexExtension.orderOf_splitterM)

private theorem complementEquiv_generator (H : CentralizerCalculation D) :
    complementEquiv H ⟨H.inverter, mem_zpowers _⟩ =
      ⟨RecognitionGeometry.VertexExtension.splitterM, mem_zpowers _⟩ := by
  let u := alternatingGroup.FiveLocalGeometry.CubicEdges.involutionZpowersEquiv
    H.inverter H.inverter_order
  let v := alternatingGroup.FiveLocalGeometry.CubicEdges.involutionZpowersEquiv
    RecognitionGeometry.VertexExtension.splitterM RecognitionGeometry.VertexExtension.orderOf_splitterM
  have hu : u (Multiplicative.ofAdd 1) = ⟨H.inverter, mem_zpowers _⟩ :=
    Subtype.ext (alternatingGroup.FiveLocalGeometry.CubicEdges.involutionZpowersEquiv_generator _ _)
  change v (u.symm ⟨H.inverter, mem_zpowers _⟩) = _
  rw [← hu, u.symm_apply_apply]
  exact Subtype.ext
    (alternatingGroup.FiveLocalGeometry.CubicEdges.involutionZpowersEquiv_generator _ _)

private def sourceAction (H : CentralizerCalculation D) :
    zpowers H.inverter →* MulAut (C D) := CentralizerCalculation.centralizerAction.comp (zpowers H.inverter).subtype

private noncomputable def sourceSplitting (H : CentralizerCalculation D) :
    (C D) ⋊[sourceAction H] zpowers H.inverter ≃* M D := by
  let eC : CM D ≃* C D := subgroupOfEquivOfLe (C_le_M D)
  let α : zpowers H.inverter →* MulAut (CM D) :=
    (CM D).normalizerMonoidHom.comp
      (Subgroup.inclusion ((CM D).normalizer_eq_top ▸ le_top))
  let e : (CM D) ⋊[α] zpowers H.inverter ≃*
      (C D) ⋊[sourceAction H] zpowers H.inverter :=
    SemidirectProduct.congr eC (MulEquiv.refl _) (by intro s; ext c; rfl)
  exact e.symm.trans (SemidirectProduct.mulEquivSubgroup H.split)

/-- The full normalizer comparison retains its restriction to the actual centralizer. -/
theorem extend_centralizer_comparison (H : CentralizerCalculation D)
    (eC : C D ≃* RecognitionGeometry.VertexExtension.C)
    (heC : ∀ x, eC (CentralizerCalculation.centralizerAction H.inverter x) =
      RecognitionGeometry.VertexExtension.splitterAction (eC x)) :
    ∃ eM : M D ≃* RecognitionGeometry.M,
      (∀ x : C D, eM ⟨x, C_le_M D x.property⟩ = RecognitionGeometry.VertexExtension.centralInclusion (eC x)) ∧
      eM H.inverter = RecognitionGeometry.VertexExtension.splitterM := by
  classical
  let eS := complementEquiv H
  have hact (s : zpowers H.inverter) :
      (sourceAction H s).trans eC =
        eC.trans (RecognitionGeometry.VertexExtension.splitAction (eS s)) := by
    have hs := s.property
    rw [mem_zpowers_iff_mem_range_orderOf, H.inverter_order] at hs
    obtain ⟨i, hi, hs⟩ := Finset.mem_image.mp hs
    have hi' : i < 2 := Finset.mem_range.mp hi
    interval_cases i
    · have he : s = 1 := Subtype.ext (hs.symm.trans (pow_zero _))
      rw [he, map_one, map_one, map_one]
      rfl
    · have he : s = ⟨H.inverter, mem_zpowers _⟩ :=
        Subtype.ext (hs.symm.trans (pow_one _))
      rw [he, show eS ⟨H.inverter, mem_zpowers _⟩ =
        ⟨RecognitionGeometry.VertexExtension.splitterM, mem_zpowers _⟩ from complementEquiv_generator H]
      exact MulEquiv.ext heC
  let e := SemidirectProduct.congr eC eS hact
  let eM := (sourceSplitting H).symm.trans (e.trans RecognitionGeometry.VertexExtension.splitting)
  have hsource (x : C D) :
      sourceSplitting H (SemidirectProduct.inl x) = ⟨x, C_le_M D x.property⟩ := by
    apply Subtype.ext
    change (x : G) * 1 = (x : G)
    exact mul_one _
  have hsourceS : sourceSplitting H
      (SemidirectProduct.inr ⟨H.inverter, mem_zpowers _⟩) = H.inverter := by
    apply Subtype.ext
    change 1 * (H.inverter : G) = (H.inverter : G)
    exact one_mul _
  refine ⟨eM, ?_, ?_⟩
  · intro x
    rw [← hsource]
    change RecognitionGeometry.VertexExtension.splitting
      (e ((sourceSplitting H).symm (sourceSplitting H (SemidirectProduct.inl x)))) = _
    rw [MulEquiv.symm_apply_apply]
    change RecognitionGeometry.VertexExtension.splitting (SemidirectProduct.inl (eC x) *
      SemidirectProduct.inr (eS 1)) = _
    rw [map_one, map_one, mul_one, RecognitionGeometry.VertexExtension.splitting_inl]
  · rw [← hsourceS]
    change RecognitionGeometry.VertexExtension.splitting
      (e ((sourceSplitting H).symm (sourceSplitting H
        (SemidirectProduct.inr ⟨H.inverter, mem_zpowers _⟩)))) = _
    rw [MulEquiv.symm_apply_apply]
    change RecognitionGeometry.VertexExtension.splitting
      (SemidirectProduct.inl (eC 1) * SemidirectProduct.inr
        (eS ⟨H.inverter, mem_zpowers _⟩)) = _
    rw [map_one, map_one, one_mul, show eS ⟨H.inverter, mem_zpowers _⟩ =
      ⟨RecognitionGeometry.VertexExtension.splitterM, mem_zpowers _⟩ from complementEquiv_generator H,
      RecognitionGeometry.VertexExtension.splitting_inr]

/-- The full normalizer comparison with its centralizer restriction. -/
theorem normalizers_of_calculation (H : CentralizerCalculation D) :
    ∃ (eC : C D ≃* RecognitionGeometry.VertexExtension.C) (eM : M D ≃* RecognitionGeometry.M),
      (∀ x : C D, eM ⟨x, C_le_M D x.property⟩ = RecognitionGeometry.VertexExtension.centralInclusion (eC x)) ∧
      eM H.inverter = RecognitionGeometry.VertexExtension.splitterM := by
  obtain ⟨_, eC, _, _, heC⟩ := centralizers_over_coordinates H H.alternatingQuotient.some
    (RecognitionGeometry.VertexExtension.centralQuotientEquivAlt6 ConcreteSystem.card_M)
  obtain ⟨eM, he, ht⟩ := extend_centralizer_comparison H eC heC
  exact ⟨eC, eM, he, ht⟩

private theorem seed_preserved (H : CentralizerCalculation D)
    (eC : C D ≃* RecognitionGeometry.VertexExtension.C)
    (eM : M D ≃* RecognitionGeometry.M)
    (he : ∀ x : C D, eM ⟨x, C_le_M D x.property⟩ =
      RecognitionGeometry.VertexExtension.centralInclusion (eC x)) :
    ∀ m : M D, m ∈ XM D ↔ eM m ∈ RecognitionGeometry.VertexExtension.XM := by
  intro m
  constructor
  · intro hm
    let c : C D := ⟨m, X_le_C D hm⟩
    have hc : c ∈ center (C D) := by rw [H.center_eq]; exact hm
    have ht : eC c ∈ center RecognitionGeometry.VertexExtension.C :=
      (MulEquivClass.apply_mem_center_iff eC).mpr hc
    rw [RecognitionGeometry.VertexExtension.center_C_eq_XC ConcreteSystem.card_M] at ht
    have hm' : eM m = RecognitionGeometry.VertexExtension.centralInclusion (eC c) := he c
    rw [hm']
    exact ht
  · intro hm
    let d : RecognitionGeometry.VertexExtension.C :=
      ⟨eM m, RecognitionGeometry.VertexExtension.X_le_C hm⟩
    obtain ⟨c, hc⟩ := eC.surjective d
    have hz : c ∈ center (C D) := by
      apply (MulEquivClass.apply_mem_center_iff eC).mp
      change eC c ∈ center RecognitionGeometry.VertexExtension.C
      rw [hc, RecognitionGeometry.VertexExtension.center_C_eq_XC ConcreteSystem.card_M]
      exact hm
    have hmc : (⟨c, C_le_M D c.property⟩ : M D) = m := by
      apply eM.injective
      rw [he, hc]
      rfl
    rw [← hmc]
    rw [H.center_eq] at hz
    exact hz

/-- The normalizer extension retains the chosen six-point quotient coordinates. -/
theorem normalizers_over_coordinates (H : CentralizerCalculation D)
    (e1 : (C D ⧸ XC D) ≃* alternatingGroup (Fin 6))
    (e0 : RecognitionGeometry.VertexExtension.CentralQuotient ≃* alternatingGroup (Fin 6)) :
    ∃ (k : MulAut (alternatingGroup (Fin 6)))
      (eC : C D ≃* RecognitionGeometry.VertexExtension.C)
      (eM : M D ≃* RecognitionGeometry.M),
      k ∈ AlternatingSix.ShadowLocal.natural ∧
      (∀ x, e0 (RecognitionGeometry.VertexExtension.centralQuotientMap (eC x)) =
        k (e1 (QuotientGroup.mk' (XC D) x))) ∧
      (∀ x : C D, eM ⟨x, C_le_M D x.property⟩ =
        RecognitionGeometry.VertexExtension.centralInclusion (eC x)) ∧
      (∀ m : M D, m ∈ XM D ↔ eM m ∈ RecognitionGeometry.VertexExtension.XM) := by
  obtain ⟨k, eC, hk, hq, heC⟩ := centralizers_over_coordinates H e1 e0
  obtain ⟨eM, he, _⟩ := extend_centralizer_comparison H eC heC
  exact ⟨k, eC, eM, hk, hq, he, seed_preserved H eC eM he⟩

/-- An arbitrary source seed supplies a comparison of the full normalizers,
with the literal centralizer restriction and order-three subgroup retained. -/
theorem normalizer_comparison [IsSimpleGroup G] (D : Seed G) :
    ∃ (eC : C D ≃* RecognitionGeometry.VertexExtension.C)
      (eM : M D ≃* RecognitionGeometry.M),
      (∀ x : C D, eM ⟨x, C_le_M D x.property⟩ =
        RecognitionGeometry.VertexExtension.centralInclusion (eC x)) ∧
      (∀ m : M D, m ∈ XM D ↔ eM m ∈ RecognitionGeometry.VertexExtension.XM) := by
  obtain ⟨S, _, _⟩ := InvolutionGeometry.Applications.source_prime_local D
  obtain ⟨H⟩ := PrimeNormalizers.centralizerCalculation_of_selectedGeometry
    (InvolutionGeometry.card_eq D) S
  obtain ⟨eC, eM, he, _⟩ := normalizers_of_calculation H
  exact ⟨eC, eM, he, seed_preserved H eC eM he⟩

/-- Application to the actual uniqueness systems: the vertex-group map is
constructed, preserving X. Aligning its edge fixer with the local A₅ map is
still required for a similarity, independently of source pentagon contraction. -/
theorem vertex_comparison [IsSimpleGroup G] (D : Seed G) :
    ∃ e : (sourceSystem D).vertexGroup ≃* ConcreteSystem.system.vertexGroup,
      ∀ a : (sourceSystem D).vertexGroup, (a : G) ∈ D.X ↔ (e a : Carrier) ∈ RecognitionGeometry.X := by
  obtain ⟨_, eM, _, he⟩ := normalizer_comparison D
  have hsource : (sourceSystem D).vertexGroup = M D :=
    D.stabilizer_eq_normalizer D.base
  let e := (MulEquiv.subgroupCongr hsource).trans
    (eM.trans (MulEquiv.subgroupCongr ConcreteSystem.system_vertexGroup.symm))
  exact ⟨e, fun a => he (MulEquiv.subgroupCongr hsource a)⟩

end CFSG.Quasithin.Janko23.J2Recognition.SourceComparison
