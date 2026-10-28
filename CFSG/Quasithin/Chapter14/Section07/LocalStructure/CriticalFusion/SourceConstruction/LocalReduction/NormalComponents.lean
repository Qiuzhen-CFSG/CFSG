module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.BinaryPlaneContradiction
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ComponentUniqueness

/-!
# Normal component reductions for the remaining source classification

Source 14.7.32 makes the original Sylow orbit of each component a single
component. Consequently its reduced local K L₁ T has a quadratic actor
faithful on that component, with the original section and two-core kernel.
Apply the full F.9.18 recognition to this actual reduced local and transport
back to the intrinsic K/O₂(K). The original full-point application selects
a genuine component and retains its escape, normality and exact quotient.

This is the common reduction used in 14.7.36 and 14.7.40. It does not
identify the selected component with the whole residual, or exclude the
remaining sporadic and larger-field alternatives.
Source: Aschbacher–Smith, 14.7.30,32,36,40, printed pp.1055–1061,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.Components
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual single-component reduction after 14.7.32. Faithfulness is
on the same component image, obtained by proving that its Sylow orbit
collapses, rather than by restricting a faithful action arbitrarily. -/
theorem local_normal_component_quadratic_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent) :
    let J := K ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
    let KJ := K.subgroupOf J
    let q := QuotientGroup.mk' (pCore 2 J)
    J ≤ I ∧ J ∈ F.Hz L (normalizer (L : Set G)) ∧
      KJ.IsCComponent ∧ KJ.Normal ∧ IsQuasisimple (KJ ⧸ pCore 2 KJ) ∧
      ((q.comp KJ.subtype).ker = pCore 2 KJ) ∧
      IsComponent (HStar J) (KJ.map q) ∧ (KJ.map q).Normal ∧
      KJ.map q ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J).map q = ⊤ ∧
      ∃ hU : IsElementaryAbelian 2 (F.UH J),
        let := hU
        ∃ a : LocalQuotientAction J (F.UH J) (F.Vi 1),
          quadraticRatio a.representation ≤ 2 ∧
          ∃ A : Subgroup J,
            A ≤ (F.Ri L 1).subgroupOf J ∧
            IsElementaryTwo (A.map q) ∧ IsQuadratic a.representation (A.map q) ∧
            fixedCodim a.representation (A.map q) ≤ 2 * rank (A.map q) ∧
            A.map q ⊓ centralizer (KJ.map q : Set (HStar J)) = ⊥ := by
  let J := K ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  let KJ := K.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  have hn := local_cComponent_normal d h hab structural previous faithful earlier I K hI hKI hK
  have hJ := (local_component_sylow_normalized_and_mem_Hz d h hab structural previous
    faithful earlier I K hI hKI hK).2
  have hJI : J ≤ I := sup_le hKI
    (sup_le (F.Li_one_le_of_mem_Hz hI) (F.sylow_le_of_mem_Hz hI))
  have hKJle : K ≤ J := le_sup_left
  have hKJ : KJ.IsCComponent := hK.subgroupOf_of_le hKJle hJI
  let hnJ : KJ.Normal := (normal_subgroupOf_iff_le_normalizer hKJle).mpr
    (hJI.trans ((normal_subgroupOf_iff_le_normalizer hKI).mp hn))
  let : (KJ.map q).Normal := hnJ.map q (QuotientGroup.mk'_surjective _)
  have hg : KJ.map q ⊔ ((F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J).map q = ⊤ := by
    rw [←Subgroup.map_sup,
      ←subgroupOf_sup hKJle (show F.Li L 1 ⊔ (T : Subgroup G) ≤ J from le_sup_right),
      show K ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) = J from rfl,subgroupOf_self,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  refine ⟨hJI,hJ,hKJ,hnJ,
    local_component_twoCore_isQuasisimple h hab structural previous faithful J hJ KJ hKJ,
    ?_,local_component_star_isComponent h hab structural previous faithful J hJ KJ hKJ,
    inferInstance,hg,?_⟩
  · rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hKJ.subnormal).symm
  · exact local_prime_supplement_quadratic_actor h hab structural previous J hJ (KJ.map q) hg

/-- F.9.18(4) for every original local component, with its literal
intrinsic two-core quotient. The normality premise is discharged by 14.7.32. -/
theorem local_component_f918_models
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent) :
    Models.F918Models (K ⧸ pCore 2 K) := by
  let J := K ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  obtain ⟨_,hJ,hKJ,hn,_,_,_,_,_,_⟩ := local_normal_component_quadratic_reduction
    d h hab structural previous faithful earlier I K hI hKI hK
  let : (K.subgroupOf J).Normal := hn
  have hg : K.subgroupOf J ⊔ (F.Li L 1 ⊔ (T : Subgroup G)).subgroupOf J = ⊤ := by
    rw [←subgroupOf_sup (show K ≤ J from le_sup_left)
      (show F.Li L 1 ⊔ (T : Subgroup G) ≤ J from le_sup_right),
      show K ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) = J from rfl,subgroupOf_self]
  let e : K ≃* K.subgroupOf J := (subgroupOfEquivOfLe (show K ≤ J from le_sup_left)).symm
  exact SourceModels.f918Models_transport (QuotientGroup.congr _ _ e (pCore_map_iso 2 e))
    (local_reduced_normal_component_f918_models h hab structural previous faithful J hJ
      (K.subgroupOf J) hKJ hg)

/-- Every original component satisfies the Sylow-overgroup uniqueness
property, with the original Sylow normalization now proved. -/
theorem local_component_sylow_overgroup_unique
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent) :
    SylowOvergroupComponentUnique K :=
  local_sylow_invariant_component_unique h hab structural previous faithful I K hI hKI hK
    (local_component_sylow_normalized_and_mem_Hz d h hab structural previous faithful
      earlier I K hI hKI hK).1

/-- The original point normalizer has a normal escaping component with
the full source model catalogue and the literal reduced-local placement.
This does not identify it with O²(H). -/
theorem original_exists_normal_component_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u}) :
    ∃ K : Subgroup G, K ≤ F.H ∧ (K.subgroupOf F.H).IsCComponent ∧
      (K.subgroupOf F.H).Normal ∧ ¬ K ≤ normalizer (L : Set G) ∧
      (T : Subgroup G) ≤ normalizer (K : Set G) ∧
      K ⊔ (F.Li L 1 ⊔ (T : Subgroup G)) ∈ F.Hz L (normalizer (L : Set G)) ∧
      Models.F918Models (K ⧸ pCore 2 K) ∧ SylowOvergroupComponentUnique K := by
  have hH := F.H_mem_Hz (by decide) L _ (h.flag_escape F previous)
  obtain ⟨K,hK,_,hout⟩ := local_exists_quasisimple_component d h hab structural previous
    faithful earlier F.H hH
  have hK' : ((K.map F.H.subtype).subgroupOf F.H).IsCComponent := by
    simpa only [subgroupOf,comap_map_eq_self_of_injective F.H.subtype_injective] using hK
  have hnorm := local_component_sylow_normalized_and_mem_Hz d h hab structural previous
    faithful earlier F.H (K.map F.H.subtype) hH (map_subtype_le _) hK'
  exact ⟨K.map F.H.subtype,map_subtype_le _,hK',
    local_cComponent_normal d h hab structural previous faithful earlier F.H _ hH
      (map_subtype_le _) hK',hout,hnorm.1,hnorm.2,
    local_component_f918_models d h hab structural previous faithful earlier F.H _ hH
      (map_subtype_le _) hK',
    local_component_sylow_overgroup_unique d h hab structural previous faithful earlier F.H _
      hH (map_subtype_le _) hK'⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
