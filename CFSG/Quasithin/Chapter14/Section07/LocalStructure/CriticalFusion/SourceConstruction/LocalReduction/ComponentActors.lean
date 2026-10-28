module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentQuotients

/-!
# The quadratic action on a general component orbit

Every original C-component has a quasisimple two-core quotient. Its
Sylow conjugate span is normal and escapes the original normalizer, so
adjoining the point parabolic gives a literal member of the same local
family. The reduced quotient retains the exact intrinsic two-core kernel
and the orbit identity. The source edge then supplies a quadratic actor
faithful on the whole orbit, without assuming faithfulness on one factor.

The original full-point application selects an actual component using
14.7.29 and supplies this reduction. The F.9.18 component and module
classification remains to be proved for this action.

Source: Aschbacher–Smith, 14.7.30, printed p.1055, using 14.5.18–19,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The genuine reduced-local action for source 14.7.30. Quasisimplicity,
relative normality, generation and the actor on the whole Sylow orbit
are derived from the original local, rather than supplied as recognition data. -/
theorem local_component_reduced_quadratic_actor
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (K : Subgroup I) (hK : K.IsCComponent) :
    let N := conjugateSpanBy (K.map I.subtype) (T : Subgroup G)
    let J := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
    let KJ := (K.map I.subtype).subgroupOf J
    let q := QuotientGroup.mk' (pCore 2 J)
    let X := (N.subgroupOf J).map q
    J ≤ I ∧ J ∈ F.Hz L (normalizer (L : Set G)) ∧ KJ.IsCComponent ∧
      IsQuasisimple (KJ ⧸ pCore 2 KJ) ∧
      ((q.comp KJ.subtype).ker = pCore 2 KJ) ∧
      IsComponent (HStar J) (KJ.map q) ∧
      X = conjugateSpanBy (KJ.map q) (((T : Subgroup G).subgroupOf J).map q) ∧
      X.Normal ∧
      X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J).map q = ⊤ ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH J),
        let := hU
        ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
          quadraticRatio a.representation ≤ 2 ∧
          ∃ A : Subgroup J,
            A ≤ (F.Ri L 1).subgroupOf J ∧
            IsElementaryTwo (A.map q) ∧ IsQuadratic a.representation (A.map q) ∧
            fixedCodim a.representation (A.map q) ≤ 2 * rank (A.map q) ∧
            A.map q ⊓ centralizer (X : Set (HStar J)) = ⊥ := by
  let N := conjugateSpanBy (K.map I.subtype) (T : Subgroup G)
  let J := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  let KJ := (K.map I.subtype).subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let X := (N.subgroupOf J).map q
  obtain ⟨hNI,hJI,hJ⟩ := local_component_reduced_mem_Hz h structural I hI K hK
  have hNJ : N ≤ J := le_sup_left
  have hKI : ((K.map I.subtype).subgroupOf I).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hK
  have hKJle : K.map I.subtype ≤ J := (le_conjugateSpanBy _ _).trans le_sup_left
  have hKJ : KJ.IsCComponent := hKI.subgroupOf_of_le hKJle hJI
  have hNJn : (N.subgroupOf J).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNJ).mpr
      (hJI.trans ((normal_subgroupOf_iff_le_normalizer (hNJ.trans hJI)).mp hNI))
  let : X.Normal := hNJn.map q (QuotientGroup.mk'_surjective _)
  have horbit : X = conjugateSpanBy (KJ.map q) (((T : Subgroup G).subgroupOf J).map q) := by
    rw [←map_conjugateSpanBy]
    apply congrArg (map q)
    apply map_injective J.subtype_injective
    rw [map_subgroupOf_eq_of_le hNJ,map_conjugateSpanBy,
      map_subgroupOf_eq_of_le hKJle,map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hJ)]
  have hgen : X ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J).map q = ⊤ := by
    rw [←Subgroup.map_sup,←subgroupOf_sup hNJ (show F.Li L 1 ⊔ (T : Subgroup G) ≤ J from le_sup_right)]
    change (J.subgroupOf J).map q = ⊤
    rw [subgroupOf_self,←MonoidHom.range_eq_map,MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)]
  refine ⟨hJI,hJ,hKJ,local_component_twoCore_isQuasisimple h hab structural previous faithful J hJ KJ hKJ,
    ?_,local_component_star_isComponent h hab structural previous faithful J hJ KJ hKJ,
    horbit,inferInstance,hgen,?_⟩
  · rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hKJ.subnormal).symm
  · exact local_prime_supplement_quadratic_actor h hab structural previous J hJ X hgen

/-- At the original full point normalizer, an actual escaping component
has a quasisimple two-core quotient and a reduced local with the literal
quadratic section and actor faithful on the whole component orbit. -/
theorem original_exists_component_quadratic_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u}) :
    ∃ K : Subgroup F.H, K.IsCComponent ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      ¬ K.map F.H.subtype ≤ normalizer (L : Set G) ∧
      let N := conjugateSpanBy (K.map F.H.subtype) (T : Subgroup G)
      let J := N ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
      let q := QuotientGroup.mk' (pCore 2 J)
      let X := (N.subgroupOf J).map q
      J ≤ F.H ∧ J ∈ F.Hz L (normalizer (L : Set G)) ∧
        ∃ hU : IsElementaryAbelian 2 (F.UH J),
          let := hU
          ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
            quadraticRatio a.representation ≤ 2 ∧
            ∃ A : Subgroup J,
              A ≤ (F.Ri L 1).subgroupOf J ∧
              IsElementaryTwo (A.map q) ∧ IsQuadratic a.representation (A.map q) ∧
              fixedCodim a.representation (A.map q) ≤ 2 * rank (A.map q) ∧
              A.map q ⊓ centralizer (X : Set (HStar J)) = ⊥ := by
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  obtain ⟨K,hK,hq,hout⟩ :=
    local_exists_quasisimple_component d h hab structural previous faithful earlier F.H hH
  obtain ⟨hJH,hJ,_,_,_,_,_,_,_,ha⟩ :=
    local_component_reduced_quadratic_actor h hab structural previous faithful F.H hH K hK
  exact ⟨K,hK,hq,hout,hJH,hJ,ha⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
