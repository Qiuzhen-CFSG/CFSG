module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt.Borel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ProjectiveNormalityAt
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.LargePrimeGeometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.UnitaryEight.Projective
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields.LinearThreeFour.Projective.QuadraticActor

/-!
# Projective exceptional components at the original group and Sylow

The actual projective-three model is made normal by the same-G,T normality
producer. Passing to the literal K L₁ T reduction retains the actual component
quotient and quadratic actor. The native PSL₃(4) and PSU₃(8) obstructions then
exclude both exceptional rows without a universal structural record.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
open Chapter13.Section08.Components Swapped Swapped.LinearTwo
open Chapter13.Section08.ComponentSieve.FieldComponents.ExceptionalFields
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- The actual normal-component reduction, with no later classification premise. -/
theorem normal_component_quadratic_reduction_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I K : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (hKI : K ≤ I) (hK : (K.subgroupOf I).IsCComponent)
    (hn : (K.subgroupOf I).Normal) :
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
  have hTN : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (F.sylow_le_of_mem_Hz hI).trans ((normal_subgroupOf_iff_le_normalizer hKI).mp hn)
  have hspan : conjugateSpanBy K (T : Subgroup G) = K :=
    le_antisymm (conjugateSpanBy_le le_rfl hTN) (le_conjugateSpanBy _ _)
  have hJ : J ∈ F.Hz L (normalizer (L : Set G)) := by
    have hh := (local_component_reduced_mem_Hz_at h structural I hI (K.subgroupOf I) hK).2.2
    simpa only [map_subgroupOf_eq_of_le hKI,hspan] using hh
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
    WholeResidualAssembly.GuardedSource.local_component_twoCore_isQuasisimple h hab structural previous faithful J hJ KJ hKJ,
    ?_,WholeResidualAssembly.GuardedSource.local_component_star_isComponent h hab structural previous faithful J hJ KJ hKJ,
    inferInstance,hg,?_⟩
  · rw [←MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact (pCore_subnormal_eq_comap 2 hKJ.subnormal).symm
  · exact WholeResidualAssembly.GuardedSource.local_prime_supplement_quadratic_actor h hab structural previous J hJ (KJ.map q) hg

private theorem normal_projective_exceptions
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) [C.Normal] (hC : C.IsCComponent) :
    (¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 4) ∧
      (¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 8) := by
  let K := C.map I.subtype
  have hK : (K.subgroupOf I).IsCComponent := by
    simpa only [K,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using hC
  let J := K ⊔ (F.Li L 1 ⊔ (T : Subgroup G))
  let KJ := K.subgroupOf J
  let q := QuotientGroup.mk' (pCore 2 J)
  let B := KJ.map q
  have hnK : (K.subgroupOf I).Normal := by
    simpa only [K,subgroupOf,comap_map_eq_self_of_injective I.subtype_injective] using
      (inferInstance : C.Normal)
  obtain ⟨_,hJ,hKJ,hn,_,_,_,hnB,_,hU,a,_,A,_,hA,hquad,hcod,hfaith⟩ :=
    normal_component_quadratic_reduction_at h hab structural previous faithful
      I K hI (map_subtype_le _) hK hnK
  let := hU
  let : B.Normal := hnB
  let ec : C ≃* KJ := (equivMapOfInjective C I.subtype I.subtype_injective).trans
    (subgroupOfEquivOfLe (show K ≤ J from le_sup_left)).symm
  let e : (C ⧸ pCore 2 C) ≃* B :=
    (QuotientGroup.congr _ _ ec (pCore_map_iso 2 ec)).trans
      (cComponentTwoCoreQuotientEquiv hKJ)
  have hs := WholeResidualAssembly.GuardedSource.local_star_sqtk h J hJ
  constructor
  · intro hm
    exact LinearThreeFour.Projective.no_quadratic_actor a.representation B (A.map q)
      hs (hm.of_mulEquiv e.symm) a.faithful hA hquad hcod hfaith
  · intro hm
    exact UnitaryEight.Projective.no_quadratic_actor a.representation B (A.map q)
      hs (hm.of_mulEquiv e.symm) a.faithful hA hquad hcod hfaith


theorem local_projective_exceptional_components_impossible_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) (hC : C.IsCComponent) :
    (¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 4) ∧
      (¬ ClassicalGroup.IsPSU (C ⧸ pCore 2 C) 3 8) := by
  constructor
  · intro hm
    have hm' := hm
    obtain ⟨E,_,_,hE,⟨e⟩⟩ := hm
    let := local_projective_linearThree_normal_at d h hab structural previous faithful earlier
      I hI C hC (by decide : 0 < 2) hE e
    exact (normal_projective_exceptions h hab structural previous faithful I hI C hC).1 hm'
  · intro hm
    have hm' := hm
    obtain ⟨E,_,_,J,hE,hconj,⟨e⟩⟩ := hm
    let := local_projective_unitaryThree_normal_at d h hab structural previous faithful earlier
      I hI C hC J (by decide : 0 < 3) hE hconj e
    exact (normal_projective_exceptions h hab structural previous faithful I hI C hC).2 hm'

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.ContainedProjectiveAt
