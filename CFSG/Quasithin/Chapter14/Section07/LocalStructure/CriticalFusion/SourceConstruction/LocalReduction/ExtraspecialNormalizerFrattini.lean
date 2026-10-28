module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialNormalizerKernel
public import Theory.SpecificGroups.HeisenbergPrime.TernaryOuterAction
public import Theory.SpecificGroups.GL2.ThreeQuaternionPullback
public import Theory.GroupTheory.RelativeSylowFrattini

public import Stellmacher.BaumannNormalizer

/-!
# The inner kernel in the extraspecial normalizer

The original residual action on its Heisenberg quotient induces a GL₂(3)
action. Its determinant-one preimage is the literal point centralizer.
Pulling back the normal quaternion subgroup gives K C R₁, retaining the
inner automorphisms in the kernel. Relative Frattini then gives
N_G(K) = K C N_{N_G(K)}(R₁); original 14.7.16(7) places the last
factor in N_G(L).

Source: Aschbacher–Smith 14.7.21(1), printed pp.1049–1050. This repairs
the outer-action normality step; it does not assert normality of C R₁,
a normal three-complement, or the final equality N_G(K) = H.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3}

omit [Finite G] in
private theorem point_center_action_iff
    (hn : normalizer (K F : Set G) ≤ normalizer (F.Li L 1 : Set G))
    (hP : (F.Li L 1).pCoreIn 2 = (K F).pCoreIn 2)
    (hZ : (F.Li L 1).subgroupOf (K F) =
      (center ((K F) ⧸ pCore 2 (K F))).comap (QuotientGroup.mk' (pCore 2 (K F))))
    (n : normalizer (K F : Set G)) :
    pCoreNormalizerAction 2 (F.Li L 1) (inclusion hn n) = 1 ↔
      ∀ z ∈ center ((K F) ⧸ pCore 2 (K F)), pCoreNormalizerAction 2 (K F) n z = z := by
  rw [pCoreNormalizerAction_eq_one_iff]
  let q := QuotientGroup.mk' (pCore 2 (K F))
  have hmemA (a : F.Li L 1) : q ⟨a,pointResidual_le F a.property⟩ ∈ center _ := by
    change (⟨a,pointResidual_le F a.property⟩ : K F) ∈ (center _).comap q
    rw [←hZ]
    exact a.property
  constructor
  · intro hh z hz
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (K F)) z
    have hk : (k : G) ∈ F.Li L 1 := by
      change k ∈ (F.Li L 1).subgroupOf (K F)
      rw [hZ]
      exact hz
    let a : F.Li L 1 := ⟨k,hk⟩
    rw [pCoreNormalizerAction_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    have hd : ((F.Li L 1).normalizerMonoidHom (inclusion hn n) a / a : G) ∈
        (K F).pCoreIn 2 := hP ▸ mem_map_of_mem (F.Li L 1).subtype (hh a)
    have he : ((K F).pCoreIn 2).subgroupOf (K F) = pCore 2 (K F) :=
      comap_map_eq_self_of_injective (K F).subtype_injective _
    exact he ▸ hd
  · intro hh a
    let k : K F := ⟨a,pointResidual_le F a.property⟩
    have he := hh (q k) (hmemA a)
    rw [pCoreNormalizerAction_mk] at he
    have hd := QuotientGroup.eq_iff_div_mem.mp he
    have hd' : ((K F).normalizerMonoidHom n k / k : G) ∈ (F.Li L 1).pCoreIn 2 :=
      hP.symm ▸ mem_map_of_mem (K F).subtype hd
    have he' : ((F.Li L 1).pCoreIn 2).subgroupOf (F.Li L 1) = pCore 2 (F.Li L 1) :=
      comap_map_eq_self_of_injective (F.Li L 1).subtype_injective _
    exact he' ▸ hd'

/-- The point centralizer is exactly the determinant-one preimage for the
marked outer action on the original residual. -/
theorem extraspecial_normalizer_point_outer_preimage
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : ((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3) :
    (normalizerPointCentralizer F L).subgroupOf (normalizer (K F : Set G)) =
      Matrix.GeneralLinearGroup.threeSpecialLinear.comap
        ((HeisenbergPrime.TernaryOuterAction.markedAction e).comp
          (pCoreNormalizerAction 2 (K F))) := by
  have hn := extraspecial_normalizer_normalizes_point h hab structural previous faithful ⟨e⟩
  have hP := (extraspecial_centralizer_core_reduction_no_small_intervals
    h hab structural previous faithful ⟨e⟩).1
  have hZ := extraspecial_point_eq_central_preimage h hab structural previous faithful ⟨e⟩
  ext n
  change (n : G) ∈ normalizerPointCentralizer F L ↔ _
  rw [mem_comap,MonoidHom.comp_apply,HeisenbergPrime.TernaryOuterAction.markedAction_mem_special_iff,
    ←point_center_action_iff hn hP hZ n]
  constructor
  · rintro ⟨_,⟨a,ha,he⟩⟩
    exact (show a = inclusion hn n from Subtype.ext he) ▸ ha
  · intro hh
    exact ⟨n.property,⟨inclusion hn n,hh,rfl⟩⟩

/-- The exact quaternion preimage in the original normalizer includes both K and C_K. -/
theorem extraspecial_normalizer_quaternion_preimage
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (e : ((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3) :
    (Matrix.GeneralLinearGroup.threeQuaternion.comap
      ((HeisenbergPrime.TernaryOuterAction.markedAction e).comp
        (pCoreNormalizerAction 2 (K F)))).map (normalizer (K F : Set G)).subtype =
      K F ⊔ normalizerResidualCentralizer F ⊔ F.Ri L 1 := by
  let N := normalizer (K F : Set G)
  let Y := normalizerPointCentralizer F L
  let a := pCoreNormalizerAction 2 (K F)
  let f := (HeisenbergPrime.TernaryOuterAction.markedAction e).comp a
  have hY := extraspecial_normalizer_point_outer_preimage h hab structural previous faithful e
  have hk : f.ker = (K F).subgroupOf N ⊔ a.ker := by
    rw [show f.ker = (HeisenbergPrime.TernaryOuterAction.markedAction e).ker.comap a from rfl,
      HeisenbergPrime.TernaryOuterAction.markedAction_ker,
      ←pCoreNormalizerAction_component_image,comap_map_eq]
  have hYN : Y ≤ N := inf_le_left
  obtain ⟨S,hS⟩ := extraspecial_normalizer_point_sylow h hab structural previous faithful ⟨e⟩
  let ey : Y ≃* Matrix.GeneralLinearGroup.threeSpecialLinear.comap f :=
    (subgroupOfEquivOfLe hYN).symm.trans (MulEquiv.subgroupCongr hY)
  let S' := S.mapSurjective (f := ey.toMonoidHom) ey.surjective
  have hD := Matrix.GeneralLinearGroup.quaternion_preimage_eq_sylow_sup_kernel f S'
  have hDm := congrArg (Subgroup.map N.subtype) hD
  have hSm : (((S' : Subgroup (Matrix.GeneralLinearGroup.threeSpecialLinear.comap f)).map
      (Matrix.GeneralLinearGroup.threeSpecialLinear.comap f).subtype).map N.subtype) = F.Ri L 1 := by
    change (((S : Subgroup Y).map ey.toMonoidHom).map _).map _ = _
    rw [map_map,map_map]
    exact hS
  rw [Subgroup.map_sup,hSm,hk,Subgroup.map_sup,map_subgroupOf_eq_of_le (K F).le_normalizer] at hDm
  simpa only [normalizerResidualCentralizer,sup_assoc,sup_comm,sup_left_comm] using hDm

/-- The corrected normal subgroup lies in the original point centralizer,
and R₁ is its Sylow two-subgroup. -/
theorem extraspecial_normalizer_inner_sylow
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let B := K F ⊔ normalizerResidualCentralizer F ⊔ F.Ri L 1
    (B.subgroupOf (normalizer (K F : Set G))).Normal ∧
      B ≤ normalizerPointCentralizer F L ∧ IsSylowIn 2 (F.Ri L 1) B := by
  obtain ⟨e⟩ := he
  let N := normalizer (K F : Set G)
  let f := (HeisenbergPrime.TernaryOuterAction.markedAction e).comp
    (pCoreNormalizerAction 2 (K F))
  let D := Matrix.GeneralLinearGroup.threeQuaternion.comap f
  have hd := extraspecial_normalizer_quaternion_preimage h hab structural previous faithful e
  have hn : ((D.map N.subtype).subgroupOf N).Normal := by
    rw [show (D.map N.subtype).subgroupOf N = D from
      comap_map_eq_self_of_injective N.subtype_injective D]
    infer_instance
  have hle : D.map N.subtype ≤ normalizerPointCentralizer F L := by
    have hm := map_mono (f := N.subtype)
      (comap_mono (f := f) Matrix.GeneralLinearGroup.threeQuaternion_le_specialLinear)
    rw [←extraspecial_normalizer_point_outer_preimage h hab structural previous faithful e,
      map_subgroupOf_eq_of_le (show normalizerPointCentralizer F L ≤ N from inf_le_left)] at hm
    exact hm
  rw [hd] at hn hle
  exact ⟨hn,hle,(extraspecial_normalizer_point_sylow h hab structural previous faithful ⟨e⟩).restrict
    le_sup_right hle⟩

/-- Frattini factorization in the original normalizer with the full inner kernel retained. -/
theorem extraspecial_normalizer_inner_frattini
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    K F ⊔ normalizerResidualCentralizer F ⊔
      (normalizer (K F : Set G) ⊓ normalizer (F.Ri L 1 : Set G)) =
        normalizer (K F : Set G) := by
  let N := normalizer (K F : Set G)
  let B := K F ⊔ normalizerResidualCentralizer F ⊔ F.Ri L 1
  obtain ⟨hn,hBY,hs⟩ := extraspecial_normalizer_inner_sylow h hab structural previous faithful he
  have hBN : B ≤ N := hBY.trans inf_le_left
  have hNB : N ≤ normalizer (B : Set G) := (normal_subgroupOf_iff_le_normalizer hBN).mp hn
  obtain ⟨S,hS⟩ := hs
  have hgen := relative_sylow_frattini B N hBN hNB S
  rw [hS] at hgen
  have hR : F.Ri L 1 ≤ N ⊓ normalizer (F.Ri L 1 : Set G) :=
    le_inf (le_sup_right.trans hBN) (F.Ri L 1).le_normalizer
  change (K F ⊔ normalizerResidualCentralizer F ⊔ F.Ri L 1) ⊔ _ = N at hgen
  rwa [sup_assoc (K F ⊔ normalizerResidualCentralizer F),sup_eq_right.mpr hR] at hgen

/-- The normalizer factor in the repaired Frattini product is controlled by
original 14.7.16(7), via the characteristic Baumann subgroup of R₁. -/
theorem extraspecial_normalizer_inner_frattini_source
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    let N := normalizer (K F : Set G)
    let M₁ := N ⊓ normalizer (F.Ri L 1 : Set G)
    K F ⊔ normalizerResidualCentralizer F ⊔ M₁ = N ∧
      M₁ ≤ normalizer (L : Set G) := by
  refine ⟨extraspecial_normalizer_inner_frattini h hab structural previous faithful he,?_⟩
  exact inf_le_right.trans ((Stellmacher.normalizer_le_normalizer_baumann _).trans
    (extraspecial_baumann_normalizer d h hab structural previous earlier he))

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
