module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.LocalControl.OriginalSource.NaturalPointMS
public import CFSG.Quasithin.ChapterC.Section01.NaturalPointControl.ChiefBound
public import CFSG.Quasithin.ChapterB.Section02.DoubledOvergroupPointBaumann
public import Theory.GroupTheory.CubicFactorSylowPlacement

/-!
# The natural-point MS core cannot be doubled

The original natural point gives an index-seven centralizer and hence a Sylow
subgroup of the component fixing that point. If the MS commutator core were
doubled natural, its point-radical Thompson subgroup would centralize the whole
core. It would then centralize the original natural submodule and lie in the
ambient two-core, contrary to MS3. Thus the actual whole core is natural.

Cubic movement on that core is at most one layer. Coprime additivity gives at
most two layers on the intrinsic two-core of any subgroup embedded in the
component: one in the ambient kernel and one in its SL₃(2) image. Every action
and kernel is the displayed natural marking and actual subgroup inclusion.
The original covered-row consumer is Nonsolvable.ComponentLinearShort.

Source: Aschbacher--Smith C.1.37, printed pp.141--143, and 13.4.10(2), p.908.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.NaturalPointControl
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
open NoncentralChiefRefinement NoncentralChiefRefinement.CubicComparison
universe u
variable {G : Type u} [Group G] [Finite G] {V : Subgroup G} [V.Normal]
  [IsElementaryAbelian 2 V]
namespace NaturalAction
variable (d : NaturalAction V)

theorem not_doubled_core {κ : GroupClass.{u}} {K R : Subgroup G}
    (h : BinaryMS.Input κ K R) (hR : R = d.P.pCoreIn 2)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group) :
    ¬ HasSectionModel K (msQ K R) ⊥ (linearThreeActor e)
      (BinaryLinearThree.W.prod BinaryLinearThree.W) := by
  intro hm
  have hQ : msQ K R = BinaryMS.commutatorCore K := by
    rw [msQ,h.sup_eq_top]
    rw [show (⊤ : Subgroup G).pCoreIn 2 = pCore 2 G from pCore_map_iso 2 topEquiv]
  rw [hQ] at hm
  let Q := BinaryMS.commutatorCore K
  let := h.component_normal
  let : Q.Normal := by
    dsimp [Q, BinaryMS.commutatorCore]
    infer_instance
  obtain ⟨_,_,_,hn,eq,heq⟩ := hm
  let := hn
  let f : Q ≃* Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector) :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf Q).symm).trans eq)
  let : IsElementaryAbelian 2 (Multiplicative (BinaryLinearThree.Vector × BinaryLinearThree.Vector)) :=
    Representation.BinaryGroupAction.elementary
  let : IsElementaryAbelian 2 Q := IsElementaryAbelian.of_injective f.toMonoidHom f.injective
  have hf (k : K) (v : Q) : (f (MulAut.conjNormal k.val v)).toAdd =
      (BinaryLinearThree.W.prod BinaryLinearThree.W) (linearThreeActor e k) (f v).toAdd :=
    heq k v (MulAut.conjNormal k.val v) rfl
  have hVQ : V ≤ Q := (d.module_le_center_core h).trans (map_subtype_le _)
  let v : V := d.coordinates.symm (Multiplicative.ofAdd flagPoint.val)
  let w : Q := ⟨v.val,hVQ v.property⟩
  have hw : w ≠ 1 := by
    intro hw
    have hv : v = 1 := Subtype.ext (congrArg (fun x : Q => (x : G)) hw)
    have hz := congrArg d.coordinates hv
    change d.coordinates (d.coordinates.symm (Multiplicative.ofAdd flagPoint.val)) = _ at hz
    rw [d.coordinates.apply_symm_apply,map_one] at hz
    exact flagPoint.property (congrArg Multiplicative.toAdd hz)
  have hP : centralizer ({w.val} : Set G) = d.P := by
    ext g
    change g ∈ centralizer ({v.val} : Set G) ↔ d.q g ∈ pointParabolicSL
    rw [←Fano.stabilizer_flagPoint_SL]
    change _ ↔ d.q g • flagPoint = flagPoint
    rw [Subtype.ext_iff]
    change _ ↔ BinaryLinearThree.W (d.q g) flagPoint.val = flagPoint.val
    have hv : (d.coordinates v).toAdd = flagPoint.val := d.coordinates.apply_symm_apply _
    have ha : (d.coordinates (MulAut.conjNormal g v)).toAdd =
        BinaryLinearThree.W (d.q g) (d.coordinates v).toAdd := d.action g v
    rw [←hv,←ha,Multiplicative.toAdd.injective.eq_iff,d.coordinates.injective.eq_iff,
      Subtype.ext_iff]
    change _ ↔ g * v.val * g⁻¹ = v.val
    rw [mul_inv_eq_iff_eq_mul,mem_centralizer_singleton_iff]
  have honto : Function.Surjective (d.q.comp K.subtype) := by
    rw [←h.residual_eq]
    exact d.residual_surjective
  have hi : Odd ((K ⊓ d.P).relIndex K) := by
    rw [inf_relIndex_left]
    change Odd ((pointParabolicSL.comap (d.q.comp K.subtype)).index)
    rw [pointParabolicSL.index_comap_of_surjective honto]
    have hc := pointParabolicSL.index_mul_card
    rw [card_pointParabolicSL,card_SL] at hc
    have hi : pointParabolicSL.index = 7 := by omega
    rw [hi]
    decide
  obtain ⟨S,hS⟩ := exists_sylow_map_le_of_odd_relIndex (K ⊓ d.P) K inf_le_left hi
  have honto' : Function.Surjective (linearThreeActor e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hb := ChapterB.doubled_overgroup_point_thompson K Q (linearThreeActor e)
    honto' f hf w hw S (by rw [hP]; exact hS.trans inf_le_right)
  rw [hP,←hR] at hb
  apply h.thompson_not_le_core
  apply hb.trans
  rw [←d.kernel, d.kernel_centralizer]
  exact centralizer_le hVQ

omit [Finite G] in
private theorem natural_section_card {K D : Subgroup G}
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (hm : HasSectionModel K D ⊥ (linearThreeActor e) BinaryLinearThree.W) :
    Nat.card D = 8 := by
  obtain ⟨_,_,_,hn,f,_⟩ := hm
  let := hn
  let q : D ≃* Multiplicative BinaryLinearThree.Vector :=
    QuotientGroup.quotientBot.symm.trans
      ((QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf D).symm).trans f)
  rw [Nat.card_congr q.toEquiv]
  change Nat.card (Fin 3 → ZMod 2) = 8
  simp

/-- The original point radical eliminates the doubled whole-core alternative. -/
theorem natural_core_of_msInput {κ : GroupClass.{u}}
    (h : BinaryMS.Input κ d.LJ d.BJ) :
    ∃ e : (d.LJ ⧸ pCore 2 d.LJ) ≃* BinaryLinearThree.Group,
      HasSectionModel d.LJ (msQ d.LJ d.BJ) ⊥ (linearThreeActor e) BinaryLinearThree.W := by
  obtain ⟨e,hm⟩ := Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.LocalControl.OriginalSource.natural_or_double_of_msInput d h
  let : IsElementaryAbelian 2 (V.subgroupOf d.J) := IsElementaryAbelian.subgroupOf d.module_le_J
  exact ⟨e,hm.resolve_right (d.inMSGroup.not_doubled_core h (d.PJ_core_of_msInput h).symm e)⟩

/-- Cubics of the component move at most one layer on the actual ambient core
when the whole commutator core is natural. -/
theorem core_length_le_one {κ : GroupClass.{u}} {K R : Subgroup G}
    (h : BinaryMS.Input κ K R)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e) BinaryLinearThree.W)
    (A : Subgroup G) (hA : IsPGroup 3 A) (hAK : A ≤ K) :
    conjugationCubicLength A (pCore 2 G) ≤ 1 := by
  let := h.component_normal
  let Q := BinaryMS.commutatorCore K
  have hQ : Q ≤ pCore 2 G := commutator_le_left _ _
  have heQ : msQ K R = Q := by
    rw [msQ,h.sup_eq_top]
    rw [show (⊤ : Subgroup G).pCoreIn 2 = pCore 2 G from pCore_map_iso 2 topEquiv]
  have hc : Nat.card Q = 8 := heQ ▸ natural_section_card e hm
  have hn := length_le_log_card A Q
  rw [hc] at hn
  norm_num at hn
  rw [←length_eq_of_commutator_le A (pCore 2 G) Q hA pCore_isPGroup hQ
    le_normalizer_of_normal le_normalizer_of_normal (commutator_mono le_rfl hAK)]
  exact hn

private theorem two_subgroup_card_le_eight (P : Subgroup Matrix.PSL3Two.SL)
    (hp : IsPGroup 2 P) : Nat.card P ≤ 8 := by
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hc : Nat.card (S : Subgroup Matrix.PSL3Two.SL) = 8 := by
    rw [S.card_eq_multiplicity, Matrix.PSL3Two.card_SL]
    decide +kernel
  exact (Nat.card_le_card_of_injective (inclusion hS) (inclusion_injective _)).trans_eq hc

include d in
omit [IsElementaryAbelian 2 V] in
/-- On the intrinsic two-core of every actual embedded subgroup of K,
cubics move at most two layers. The second layer is the image in SL₃(2). -/
theorem embedded_core_length_le_two {κ : GroupClass.{u}} {K R : Subgroup G}
    (h : BinaryMS.Input κ K R)
    (e : (K ⧸ pCore 2 K) ≃* BinaryLinearThree.Group)
    (hm : HasSectionModel K (msQ K R) ⊥ (linearThreeActor e) BinaryLinearThree.W)
    {H : Type*} [Group H] [Finite H] (f : H →* G) (hf : Function.Injective f)
    (hfK : f.range ≤ K) (A : Subgroup H) (hpA : IsPGroup 3 A) :
    conjugationCubicLength A (pCore 2 H) ≤ 2 := by
  let N : Subgroup H := (pCore 2 G).comap f
  have hpN : IsPGroup 2 N := pCore_isPGroup.comap_of_injective f hf
  have hNU : N ≤ pCore 2 H := le_sSup ⟨inferInstance, hpN⟩
  have hN : conjugationCubicLength A N ≤ 1 := by
    rw [←length_map_injective f hf]
    exact (conjugationCubicLength_mono (A.map f) (map_comap_le _ _)).trans
      (core_length_le_one h e hm (A.map f) (hpA.map f) ((map_le_range _ _).trans hfK))
  let φ : pCore 2 H →* Matrix.PSL3Two.SL := (d.q.comp f).comp (pCore 2 H).subtype
  have hk : φ.ker = N.subgroupOf (pCore 2 H) := by
    ext x
    change d.q (f x) = 1 ↔ f x ∈ pCore 2 G
    rw [←d.kernel]
    rfl
  have hφ : IsPGroup 2 φ.range :=
    pCore_isPGroup.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have hquot : Nat.card (pCore 2 H ⧸ N.subgroupOf (pCore 2 H)) ≤ 8 := by
    rw [←hk,Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    exact two_subgroup_card_le_eight φ.range hφ
  have hsection := (section_length_le_log_card A (pCore 2 H) N hpA pCore_isPGroup hNU
    le_normalizer_of_normal le_normalizer_of_normal).trans (Nat.log_mono_right hquot)
  norm_num at hsection
  unfold sectionCubicLength at hsection
  omega

end NaturalAction
end CFSG.Quasithin.ChapterC.NaturalPointControl
