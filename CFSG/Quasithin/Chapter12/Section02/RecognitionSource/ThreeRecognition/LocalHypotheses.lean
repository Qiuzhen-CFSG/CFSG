module

public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRecognition.LocalCoordinates
public import Theory.SpecificGroups.BinaryLinear.AffineThree.Fixed
public import Theory.GroupTheory.Amalgam.LocalStructure

/-!
# The actual I.4.6 hypotheses in the dimension-three source

The split marking chooses an original involution in V. The computed affine
centralizer supplies its extraspecial two-core of order 32, the literal S₃
quotient, a cubic Sylow subgroup with the required fixed line, and quaternion
nonnormality inside that centralizer. The generalized Fitting comparison and
original module fusion put these facts into precisely the I.4.6 conventions.

All local hypotheses are proved from the chosen module, no escape, and the
split linear configuration. No recognition or local-structure premise remains.
Source: Aschbacher–Smith 12.2.27(2) and I.4.6, printed pp.807,417.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRecognition
open Extraspecial32
namespace LocalTransport
open BinaryLinear.Affine.ThreeLocal
variable {K : Type*} [Group K]

private theorem map_centralizer (D : Subgroup H) (e : H ≃* K) :
    (centralizer (D : Set H)).map e.toMonoidHom =
      centralizer (D.map e.toMonoidHom : Set K) := by
  ext x
  constructor
  · rintro ⟨u,hu,rfl⟩ v ⟨w,hw,rfl⟩
    change e w * e u = e u * e w
    simpa only [← map_mul] using congrArg e (hu w hw)
  · intro hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hx (e y) ⟨y,hy,rfl⟩

noncomputable def modelSylow (e : H ≃* K) : Sylow 3 K :=
  cubicSylow.mapSurjective (f := e.toMonoidHom)
    (by simpa only [MulEquiv.coe_toMonoidHom] using e.surjective)

theorem fixed_eq (e : H ≃* K) :
    pCore 2 K ⊓ centralizer (modelSylow e : Set K) = zpowers (e point) := by
  have h := congrArg (fun D : Subgroup H => D.map e.toMonoidHom) cubic_fixed
  rw [map_inf _ _ _ e.injective,pCore_map_iso] at h
  change pCore 2 K ⊓ (centralizer
    ((cubicSylow : Subgroup H) : Set H)).map e.toMonoidHom = _ at h
  rw [map_centralizer,MonoidHom.map_zpowers] at h
  exact h

theorem quaternion_nonnormal (e : H ≃* K)
    (R : Subgroup (pCore 2 K)) (hR : Nonempty (R ≃* QuaternionGroup 2)) :
    ¬ (R.map (pCore 2 K).subtype).Normal := by
  let eQ := LocalCoreTransport.coreEquiv 2 e
  let S := R.map eQ.symm.toMonoidHom
  have hS : Nonempty (S ≃* QuaternionGroup 2) :=
    ⟨(eQ.symm.subgroupMap R).symm.trans hR.some⟩
  have hn := BinaryLinear.Affine.ThreeLocal.quaternion_nonnormal S hS
  have he : (S.map (pCore 2 H).subtype).map e.toMonoidHom =
      R.map (pCore 2 K).subtype := by
    change ((R.map eQ.symm.toMonoidHom).map _).map _ = _
    rw [map_map,map_map]
    congr 1
    apply MonoidHom.ext
    intro x
    exact congrArg Subtype.val (eQ.apply_symm_apply x)
  intro hnormal
  apply hn
  apply (MulEquiv.normal_map_iff (f := e)).mp
  exact he.symm ▸ hnormal

end LocalTransport

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}

theorem local_hypotheses (D : ChosenModule T L V) (hnone : NoEscape L V)
    (C : SplitLinearConfiguration L V 3) :
    ∃ v : G, v ∈ V ∧ Nonempty (Hypotheses v) ∧ QuaternionSubgroupsNonnormal v := by
  obtain ⟨v,hv,hv1,E,hpoint⟩ := C.exists_standard_point_centralizer hnone
  let e := E.symm
  have hp : e BinaryLinear.Affine.ThreeLocal.point = distinguished v := by
    apply E.injective
    rw [E.apply_symm_apply]
    apply Subtype.ext
    exact BinaryLinear.Affine.ThreeLocal.point_marking.trans hpoint.symm
  have hF : Core v = pCore 2 (Centralizer v) := C.point_generalizedFitting_eq_pCore hnone hv hv1
  let eQ : Core v ≃* pCore 2 BinaryLinear.Affine.ThreeLocal.H :=
    (MulEquiv.subgroupCongr hF).trans (LocalCoreTransport.coreEquiv 2 e).symm
  have hz : orderOf v = 2 := by
    let := D.elementary
    exact orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) v hv) hv1
  have hfixed : Core v ⊓ centralizer (LocalTransport.modelSylow e : Set (Centralizer v)) =
      zpowers (distinguished v) := by
    rw [hF, ← hp]
    exact LocalTransport.fixed_eq e
  have hfused : ∃ g : G, g * v * g⁻¹ ∈ coreInG v ∧ g * v * g⁻¹ ≠ v := by
    obtain ⟨g,_,hg,hne⟩ := C.point_fused_in_generalizedFitting D hnone hv hv1
    exact ⟨g,hg,hne⟩
  refine ⟨v,hv,?_,?_⟩
  · refine ⟨⟨hz,
      IsExtraspecial.of_mulEquiv eQ.symm BinaryLinear.Affine.ThreeLocal.core_extraspecial,
      (Nat.card_congr eQ.toEquiv).trans BinaryLinear.Affine.ThreeLocal.core_card,
      ?_, LocalTransport.modelSylow e, hfixed, hfused⟩⟩
    exact ⟨(QuotientGroup.quotientMulEquivOfEq hF).trans
      ((LocalCoreTransport.quotientEquiv 2 e).symm.trans BinaryLinear.Affine.ThreeLocal.quotientEquiv)⟩
  · change ∀ R : Subgroup (Core v), Nonempty (R ≃* QuaternionGroup 2) →
      ¬ (R.map (Core v).subtype).Normal
    rw [hF]
    exact LocalTransport.quaternion_nonnormal e

end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ThreeRecognition
