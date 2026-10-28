module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualLinearThreeChief
public import CFSG.Quasithin.ChapterE.Section02.Structure.Original
public import Theory.GroupTheory.GeneralizedFitting.QuasisimpleTwoQuotient
public import Theory.GroupTheory.PResidual.FiniteImage

/-!
# The actual PSL₃(4) chief image

Every selected noncentral chief action has kernel O₂(H). The first
isomorphism theorem identifies its faithful image with H/O₂(H), so SQTK
descends through this genuine two-group kernel. The image of the original
two-residual is its actual PSL₃(4) quotient, and is both the two-residual
and the generalized Fitting subgroup of the chief image. Its quotient is
a two-group and the chief image has trivial two-core.

These are the source group markings for the small-ratio chief factor;
no irreducibility on the residual or representation classification is assumed.
Source: Aschbacher--Smith9.2.7 and B.6.8, printed pp.731--732 and114.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender NoncentralChiefRefinement
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterB ChapterD ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

theorem old_residual_linear_three_chief_image_structure
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (hK : (pResidual 2 H).IsCComponent)
    (hm : let hP := source_a5_hstar_minimal_parabolic D e m.sylow_not_normalizes_component hH
      ClassicalGroup.IsPSL (ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels.sourceImage
        (ChapterB.minimalParabolicMax (T.subtype hH.1.1.2) hP) (pResidual 2 H)) 3 4)
    [IsElementaryAbelian 2 ((conjugateSpan H D.fullModule).subgroupOf H)]
    (s : SeriesOn ((conjugateSpan H D.fullModule).subgroupOf H))
    (i : Fin s.series.length) (hi : ¬ s.Central i) :
    let σ := s.factorRepresentation i
    let Q := actionImage σ
    let K := (pResidual 2 H).map (actionHom σ)
    letI : K.Normal := Normal.map inferInstance (actionHom σ) σ.asGroupHom.rangeRestrict_surjective
    IsSQTK KnownSimple.IsKnownSimple Q ∧ ClassicalGroup.IsPSL K 3 4 ∧
      generalizedFitting Q = K ∧ pResidual 2 Q = K ∧ IsPGroup 2 (Q ⧸ K) ∧
        pCore 2 Q = ⊥ := by
  let σ := s.factorRepresentation i
  let := s.factorRepresentation_irreducible i
  let f := actionHom σ
  have hf : Function.Surjective f := σ.asGroupHom.rangeRestrict_surjective
  have hk : f.ker = pCore 2 H := (actionHom_ker_eq σ).trans
    (m.old_residual_linear_three_chief_kernel_eq_twoCore hH hlarge hK hm s i hi)
  let E : (H ⧸ pCore 2 H) ≃* actionImage σ :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hsq : IsSQTK KnownSimple.IsKnownSimple (actionImage σ) :=
    (IsSQTK.equiv E).mp (ChapterE.Structure.sqtk_two_quotient
      (Chapter3.sqtk_of_mem_H D.simpleQTKE hH.1.1.1) (pCore 2 H) pCore_isPGroup)
  let K := pResidual 2 H
  have hkK : (f.subgroupMap K).ker = pCore 2 K := by
    rw [ker_subgroupMap,hk]
    exact (pCore_subnormal_eq_comap 2 hK.subnormal).symm
  let Eₖ : (K ⧸ pCore 2 K) ≃* K.map f :=
    (QuotientGroup.quotientMulEquivOfEq hkK.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (f.subgroupMap K) (f.subgroupMap_surjective K))
  obtain ⟨F,hF,hfin,hcard,⟨eF⟩⟩ := m.old_residual_linear_three_quotient hH hlarge hK hm
  let E' := Eₖ.symm.trans eF
  have hmodel : ClassicalGroup.IsPSL (K.map f) 3 4 := ⟨F,hF,hfin,hcard,⟨E'⟩⟩
  let : IsQuasisimple (K.map f) := IsQuasisimple.of_mulEquiv E'.symm
  let : (K.map f).Normal := Normal.map inferInstance f hf
  have hr : pResidual 2 (actionImage σ) = K.map f :=
    (map_pResidual_of_surjective 2 f hf).symm
  have hquot : IsPGroup 2 (actionImage σ ⧸ K.map f) :=
    (pResidual_le_iff_isPGroup_quotient 2 _).mp hr.le
  exact ⟨hsq,hmodel,generalizedFitting_eq_of_quasisimple_two_quotient _ hquot
    (irreducible_image_twoCore_eq_bot σ),hr,hquot,irreducible_image_twoCore_eq_bot σ⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
