module
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.ResidualAlgebra
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingFullCentralizerSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingSylowSource
public import CFSG.Quasithin.Chapter2.Section04.SmallBlocks.AlternatingMarkedSylowSource
/-!
# The residual factors in the original single A5 centralizer

The canonical action of the actual two-core identifies the order-72 orthogonal
quotient. Its factor-preserving index-two preimage gives the commuting SL2(3)
factors of the two-perfect residual. The residual has odd image of order nine
and joins the original Sylow subgroup in a normal subgroup whose intersection
with the ambient Sylow is exactly the original Sylow. These are the literal
subgroups used by the generalized Thompson transfer argument.

Source: Aschbacher–Smith, 2.4.29, printed p.546.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2
variable {G : Type*} [Group G] [Finite G]

structure AlternatingResidualSetup (M S : Subgroup G) (T : Sylow 2 G) where
  data : QuaternionCentralProductData (pCore 2 M)
  factors : QuaternionResidualCentralProduct (pCore 2 M) data
  selfcentralizing : centralizer (pCore 2 M : Set M) ≤ pCore 2 M
  maximal_card : Nat.card M=2304
  core_le_sylow : M.pCoreIn 2 ≤ S
  sylow_card : Nat.card S=128
  sylow_le : S≤(T:Subgroup G)
  ambient_le : (T:Subgroup G)≤M

namespace AlternatingResidualSetup
variable {M S : Subgroup G} {T : Sylow 2 G} (c : AlternatingResidualSetup M S T)
noncomputable def action : M →* BinaryFourPlus.Wreath := c.data.normalWreathAction (pCore 2 M)
noncomputable def intrinsicSylow : Sylow 2 M := T.subtype c.ambient_le
noncomputable def residual (_c : AlternatingResidualSetup M S T) : Subgroup G := (pResidual 2 M).map M.subtype
noncomputable def transferSubgroup : Subgroup G := c.residual ⊔ S

include c
omit [Finite G] in
@[simp] theorem transferSubgroup_def :
    c.transferSubgroup = (pResidual 2 M).map M.subtype ⊔ S := by
  rfl

@[simp] theorem action_def :
    c.action = c.data.quotientWreathAction.comp MulAut.conjNormal := by
  apply MonoidHom.ext
  intro x
  rfl

omit [Finite G] in
@[simp] theorem intrinsicSylow_coe :
    (c.intrinsicSylow : Subgroup M) = (T : Subgroup G).subgroupOf M := by
  ext x
  rfl

theorem action_ker : c.action.ker=pCore 2 M :=
  c.data.normalWreathAction_ker _ c.selfcentralizing

theorem action_surjective : Function.Surjective c.action :=
  c.data.normalWreathAction_surjective _ c.selfcentralizing c.maximal_card

theorem quotient_residual_card : Nat.card (pResidual 2 BinaryFourPlus.Wreath)=9 :=
  c.data.residual_wreath_card _ c.factors c.action c.action_surjective c.action_ker

theorem residual_inf_sylow_le : c.residual ⊓ (T:Subgroup G)≤S := by
  rintro x ⟨⟨x,hx,rfl⟩,hxt⟩
  exact c.core_le_sylow (mem_map_of_mem M.subtype
    (c.data.residual_inf_two_subgroup_le _ c.factors
      ((T:Subgroup G).subgroupOf M) (T.isPGroup'.comap_subtype) ⟨hx,hxt⟩))

theorem transfer_subgroup_normalized : M≤normalizer (c.transferSubgroup:Set G) := by
  let Si := S.subgroupOf M
  have hSM : S≤M := c.sylow_le.trans c.ambient_le
  have hQS : pCore 2 M≤Si := by
    intro q hq
    exact c.core_le_sylow (mem_map_of_mem M.subtype hq)
  have hcS : Nat.card Si=128 :=
    (Nat.card_congr (subgroupOfEquivOfLe hSM).toEquiv).trans c.sylow_card
  have hSi : IsPGroup 2 Si := (T.isPGroup'.to_le c.sylow_le).comap_subtype
  let F := pResidual 2 M ⊔ Si
  have hF : F.Normal := c.data.residual_join_normal _ c.factors Si hSi hQS hcS c.maximal_card
  have he : F.map M.subtype=c.transferSubgroup := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hSM]
    rfl
  rw [←he]
  have hh := F.le_normalizer_map M.subtype
  rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  exact hh

theorem transfer_subgroup_inf_sylow : c.transferSubgroup ⊓ (T:Subgroup G)=S := by
  let Si := S.subgroupOf M
  have hSM : S≤M := c.sylow_le.trans c.ambient_le
  have hQS : pCore 2 M≤Si := by
    intro q hq
    exact c.core_le_sylow (mem_map_of_mem M.subtype hq)
  have hh := c.data.residual_join_inf_two_subgroup _ c.factors Si
    ((T:Subgroup G).subgroupOf M) T.isPGroup'.comap_subtype hQS
    (subgroupOf_mono M c.sylow_le)
  have he : (pResidual 2 M ⊔ Si).map M.subtype=c.transferSubgroup := by
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hSM]
    rfl
  have hm := congrArg (map M.subtype) hh
  rwa [map_inf _ _ M.subtype M.subtype_injective,he,
    map_subgroupOf_eq_of_le c.ambient_le,map_subgroupOf_eq_of_le hSM] at hm
end AlternatingResidualSetup

variable {M : Subgroup G}
theorem MinimalBlockSetup.single_alternating_residual_factors
    (d : MinimalBlockSetup M) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T:Subgroup G)≤M)
    (hu : ∀N:Subgroup G, IsMaximalTwoLocal N→(T:Subgroup G)≤N→N=M)
    (hST : (d.S:Subgroup d.H).map d.H.subtype<(T:Subgroup G))
    (hsingle : d.L0=d.block)
    (hA : ChapterC.IsAlternatingBlock (d.block.map d.H.subtype) 5)
    (hD : (T:Subgroup G) ⊓ centralizer (d.block.map d.H.subtype:Set G)=⊥) :
    Nonempty (AlternatingResidualSetup M ((d.S:Subgroup d.H).map d.H.subtype) T) := by
  let B := M ⊓ d.block.map d.H.subtype
  let K := (pResidual 2 B).map B.subtype
  let P := K.pCoreIn 2
  let Q := pCore 2 M
  have hc := (d.single_alternating_maximal_core_of_centralizer_bot
    hG T hM hTM hu hST hsingle hA hD).1
  change M.pCoreIn 2=P at hc
  obtain ⟨hp⟩ := d.single_alternating_borel_core_quaternion hG T hST hsingle hA
  let e : Q≃*P := (Q.equivMapOfInjective M.subtype M.subtype_injective).trans
    (MulEquiv.subgroupCongr hc)
  let hq := hp.map e.symm
  have hself : centralizer (Q:Set M)≤Q := by
    intro x hx
    have hh : (x:G)∈M ⊓ centralizer (M.pCoreIn 2:Set G) := by
      refine ⟨x.property,?_⟩
      rintro y ⟨a,ha,rfl⟩
      exact congrArg Subtype.val (hx a ha)
    obtain ⟨a,ha,hea⟩ := (Chapter1.mem_He_iff.mpr (hG.evenCharacteristic T M hM hTM)) hh
    exact (M.subtype_injective hea) ▸ ha
  have hcM : Nat.card M=2304 := d.single_alternating_maximal_card_of_centralizer_bot
    hG T hM hTM hu hST hsingle hA hD
  obtain ⟨r⟩ := Subgroup.QuaternionCentralProductData.quaternion_residual_central_product_of_wreath
    (hq.normalWreathAction Q) Q hq rfl hself
    (hq.normalWreathAction_surjective Q hself hcM) (hq.normalWreathAction_ker Q hself)
  have hcS : Nat.card ((d.S:Subgroup d.H).map d.H.subtype)=128 := by
    let Di := centralizer (d.block:Set d.H)
    obtain ⟨eS,_⟩ := d.single_alternating_marked_sylow_model hG T hM hTM hu hST hsingle hA
    have hDi : Nat.card Di=1 := by
      have he := d.single_alternating_centralizer_factor_map hG T hM hTM hu hST hsingle hA
      rw [hD] at he
      rw [←card_map_of_injective (K:=Di) (f:=d.H.subtype) d.H.subtype_injective,he]
      simp
    rw [card_map_of_injective (f:=d.H.subtype) d.H.subtype_injective,Nat.card_congr eS.toEquiv,
      Nat.card_prod,SymmetricFourWreath.card_P,hDi,mul_one]
  exact ⟨⟨hq,r,hself,hcM,hc.symm ▸ (d.single_borel_core_placement hsingle).1,hcS,hST.le,hTM⟩⟩
end CFSG.Quasithin.Chapter2
