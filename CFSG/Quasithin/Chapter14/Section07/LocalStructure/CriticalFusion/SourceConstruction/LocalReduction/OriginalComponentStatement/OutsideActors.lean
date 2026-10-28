module
public import Theory.GroupTheory.GeneralizedFitting.Defs
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.SolvableNormalSup
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.PGroup.NormalSupplementKernel
public import Theory.GroupTheory.GeneralizedFitting.SylowLayerNormalizer
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.WholeResidualAssembly.At.Source.SolvableConclusion
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.AlternatingSevenSource.Coordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.ChiefDecomposition.Pairing.GroupReduction

/-!
# The actual outside point cubic and component action

In the reduced original local C L1 T, component normalization makes L1
normal. Its exact image modulo the local two-core is a normal cubic.
The ordinary component centralizes it. The source Fitting bound identifies
F(H*) with this cubic, while the solvable quotient by the component shows
that the component fills the layer. Thus F*(H*) is their commuting product.
The original seed commutator propagates to full movement of U_I/V1.

These statements use structural inputs at the original G,T and retain the
actual subgroup and quotient maps. They do not assume 14.7.47 or a module
model, and they do not select an inverter or a symmetric-three complement.
Source: Aschbacher--Smith 14.7.41--47, printed pp.1061--1064,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideActors
section
variable {G : Type*} [Group G] [Finite G]

private theorem fitting_product (K X S : Subgroup G) [K.Normal] [X.Normal]
    (hK : IsComponent G K) (hX : Nat.card X = 3) (hS : IsPGroup 2 S)
    (hgen : (K ⊔ X) ⊔ S = ⊤) (hfit : fittingSubgroup G = X) :
    generalizedFitting G = K ⊔ X := by
  let q := QuotientGroup.mk' K
  let Y := X.map q
  let R := S.map q
  let : IsCyclic X := isCyclic_of_prime_card hX
  let : Group.IsSolvable X := Group.isSolvable_of_comm (fun a b => mul_comm a b)
  let : Y.Normal := (inferInstance : X.Normal).map q (QuotientGroup.mk'_surjective _)
  let : Group.IsSolvable Y := Group.isSolvable_of_surjective (q.subgroupMap_surjective X)
  let : Group.IsNilpotent R := (hS.map q).isNilpotent
  have hg : Y ⊔ R = ⊤ := by
    have hh := congrArg (Subgroup.map q) hgen
    have hzero : K.map q = ⊥ := (map_eq_bot_iff K).mpr (by
      change K ≤ (QuotientGroup.mk' K).ker
      rw [QuotientGroup.ker_mk'])
    simpa only [Subgroup.map_sup,hzero,bot_sup_eq,map_top_of_surjective q
      (QuotientGroup.mk'_surjective _)] using hh
  let : Group.IsSolvable (G ⧸ K) := Group.isSolvable_of_normal_sup_eq_top Y R hg
  have hlayer : componentLayer G ≤ K := by
    apply sSup_le
    intro D hD
    let := hD.2
    exact le_of_isPerfect_of_solvable_quotient D K
  apply le_antisymm
  · exact sup_le (hfit.le.trans le_sup_right) (hlayer.trans le_sup_left)
  · exact sup_le (component_le_generalizedFitting G K hK)
      (hfit.symm.le.trans (fitting_le_generalizedFitting G))

end

open Representation Representation.BinaryOffender
open scoped IsMulCommutative
open Chapter12.Section08 CriticalFusion.Source
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter15.Section03.AbelianAmalgam
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

/-- In the actual reduced local, component normalization gives relative point normality. -/
theorem local_point_normal_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (I : Subgroup G) (_hI : I ∈ F.Hz L (normalizer (L : Set G))) (C : Subgroup I)
    (hgen : I = C.map I.subtype ⊔ F.Li L 1 ⊔ (T : Subgroup G))
    (hn : C.map I.subtype ≤ normalizer (F.Li L 1 : Set G)) :
    ((F.Li L 1).subgroupOf I).Normal := by
  apply normal_subgroupOf_of_le_normalizer
  rw [hgen]
  exact sup_le (sup_le hn (F.Li L 1).le_normalizer) (T_normalizes_L₁_at h structural)

/-- The actual component and point cubic form the generalized Fitting subgroup. -/
theorem local_structure_at
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (previous : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T)
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (I : Subgroup G) (hI : I ∈ F.Hz L (normalizer (L : Set G)))
    (C : Subgroup I) [C.Normal] (hC : C.IsCComponent)
    (hgen : I = C.map I.subtype ⊔ F.Li L 1 ⊔ (T : Subgroup G))
    (hn : C.map I.subtype ≤ normalizer (F.Li L 1 : Set G))
    (hz : center (C ⧸ pCore 2 C) = ⊥) :
    let q := QuotientGroup.mk' (pCore 2 I)
    let K := C.map q
    let X := ((F.Li L 1).subgroupOf I).map q
    ((F.Li L 1).subgroupOf I).Normal ∧ K.Normal ∧ X.Normal ∧
      IsComponent (HStar I) K ∧ Nat.card X = 3 ∧
      (∀ k : K, ∀ x : X, Commute (k : HStar I) (x : HStar I)) ∧
      Disjoint K X ∧ generalizedFitting (HStar I) = K ⊔ X ∧
      centralizer (K : Set (HStar I)) ⊓ centralizer (X : Set (HStar I)) ≤ X := by
  let q := QuotientGroup.mk' (pCore 2 I)
  let K := C.map q
  let A := (F.Li L 1).subgroupOf I
  let X := A.map q
  let S := (T : Subgroup G).subgroupOf I
  have hAn := local_point_normal_at h structural I hI C hgen hn
  let := hAn
  let : K.Normal := (inferInstance : C.Normal).map q (QuotientGroup.mk'_surjective _)
  let : X.Normal := (inferInstance : A.Normal).map q (QuotientGroup.mk'_surjective _)
  have hc : Nat.card X = 3 := WholeResidualAssembly.GuardedSource.local_point_star_card_of_normal
    h structural I (F.Li_one_le_of_mem_Hz hI) hAn
  have hX3 : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by simpa using hc)
  let : Group.IsNilpotent X := hX3.isNilpotent
  have hK := WholeResidualAssembly.GuardedSource.local_component_star_isComponent
    h hab structural previous faithful I hI C hC
  have hKX : K ≤ centralizer (X : Set (HStar I)) :=
    hK.le_centralizer_normal_solvable X
  have hcomm (k : K) (x : X) : Commute (k : HStar I) (x : HStar I) :=
    (hKX k.property x x.property).symm
  have hzK : center K = ⊥ := by
    apply bot_unique
    intro k hk
    have hh := (centerCongr (cComponentTwoCoreQuotientEquiv hC).symm ⟨k,hk⟩).property
    change (cComponentTwoCoreQuotientEquiv hC).symm k ∈ center (C ⧸ pCore 2 C) at hh
    rw [hz,mem_bot] at hh
    exact (cComponentTwoCoreQuotientEquiv hC).symm.map_eq_one_iff.mp hh
  have hdis : Disjoint K X := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro k hk
    have hh : (⟨k,hk.1⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (hcomm y ⟨k,hk.2⟩).eq
    rw [hzK,mem_bot] at hh
    exact congrArg Subtype.val hh
  have hXcore : X ≤ pCore 3 (HStar I) := le_sSup ⟨inferInstance,hX3⟩
  have hcoreX : pCore 3 (HStar I) = X := (eq_of_le_of_card_ge hXcore (by
    rw [hc]
    exact WholeResidualAssembly.GuardedSource.local_threeCore_card_le_three
      d h hab structural previous faithful earlier I hI)).symm
  have hfit : fittingSubgroup (HStar I) = X :=
    (WholeResidualAssembly.GuardedSource.local_fitting_eq_threeCore
      h hab structural previous faithful I hI).trans hcoreX
  have hgenI : C ⊔ A ⊔ S = ⊤ := by
    apply map_injective I.subtype_injective
    rw [Subgroup.map_sup,Subgroup.map_sup,map_subgroupOf_eq_of_le (F.Li_one_le_of_mem_Hz hI),
      map_subgroupOf_eq_of_le (F.sylow_le_of_mem_Hz hI),←hgen,
      ←MonoidHom.range_eq_map,range_subtype]
  have hgenQ : K ⊔ X ⊔ S.map q = ⊤ := by
    rw [←Subgroup.map_sup,←Subgroup.map_sup,hgenI,
      map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hS : IsPGroup 2 (S.map q) :=
    ((T.subtype (F.sylow_le_of_mem_Hz hI)).isPGroup'.map q)
  have hF := fitting_product K X (S.map q) hK hc hS hgenQ hfit
  refine ⟨hAn,inferInstance,inferInstance,hK,hc,hcomm,hdis,hF,?_⟩
  exact Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.ExternalModules.joint_centralizer_le_external
    K X hcomm hF hzK

/-- The normal original point cubic moves the entire literal local section. -/
theorem local_point_movement_at
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (I : Subgroup G) (hLI : F.Li L 1 ≤ I)
    (hn : ((F.Li L 1).subgroupOf I).Normal)
    [IsElementaryAbelian 2 (F.UH I)]
    (a : LocalQuotientAction I (F.UH I) (F.Vi 1)) :
    subspaceCommutator a.representation ⊤
      (((F.Li L 1).subgroupOf I).map (QuotientGroup.mk' (pCore 2 I))) = ⊤ := by
  have hm : ⁅F.UH I,F.Li L 1⁆ = F.UH I :=
    (conjugateSpanBy_eq_commutator_of_seed V I (F.Li L 1) (F.Li L 1)
      hLI ((normal_subgroupOf_iff_le_normalizer hLI).mp hn) le_rfl (seed_commutator h F)).symm
  rw [←subspaceCommutator_comp_map]
  apply (AlternatingSevenSource.localQuotientSection a).subspaceCommutator_eq_top_of_movement _ hLI
  rw [commutator_comm,hm,sup_eq_left.mpr a.kernel_le]


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.OutsideActors
