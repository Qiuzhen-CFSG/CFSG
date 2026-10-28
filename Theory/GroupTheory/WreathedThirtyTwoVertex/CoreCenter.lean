module
public import Theory.GroupTheory.WreathedThirtyTwoVertex.SourceCore
public import Theory.GroupTheory.NormalNonabelianSixteenCenter

/-!
# The center of order four in the nonabelian wreathed vertex

The quaternion–cyclic model identifies the core center with C₄. ABG embeds
that center in the actual Sylow center, and the independent normal-sixteen
center theorem makes it central in the whole vertex. Self-centralization of
the core gives the reverse inclusion, so these are exactly the ambient center.

Source: Aschbacher–Smith F.1.12(I)(8), the order-96 nonabelian endpoint.
-/

public section
noncomputable section
open Subgroup
namespace WreathedVertex
variable {G:Type*} [Group G] [Finite G]

def modelCenterEquiv : center QuaternionCyclic.Model≃*C4 :=
  (MulEquiv.subgroupCongr QuaternionCyclic.center_eq_cyclic).trans
    (MonoidHom.ofInjective QuaternionCyclic.cyclicEmbedding_injective).symm

theorem core_center_central (Q:Subgroup G) [Q.Normal] (hQ:IsPGroup 2 Q)
    (hc:centralizer (Q:Set G)≤Q) (hna:¬IsMulCommutative Q) (h3:3∣Nat.card G)
    (S:Sylow 2 G) (eS:S≃*W) : (center Q).map Q.subtype≤center G := by
  obtain ⟨eQ⟩:=core_equiv Q hQ hc hna h3 S eS
  have hQS:Q≤S:=hQ.le_sylow_of_normal S
  let K:Subgroup S:=Q.subgroupOf S
  let eK:K≃*Q:=subgroupOfEquivOfLe hQS
  have hnK:¬IsMulCommutative K := by
    intro hh
    apply hna
    exact IsMulCommutative.of_comm (fun a b=>eK.symm.injective (by
      rw [map_mul,map_mul];exact hh.is_comm.comm _ _))
  have hS:ABG.IsWreathedOfHeight S 2:=
    ABG.wreathed_equiv eS.symm ABG.RegularWreathHeightTwo.isWreathedOfHeight
  obtain ⟨P⟩:=ABG.Wreathed.nonempty_presentation hS
  have hQcard:Nat.card Q=16:=(Nat.card_congr eQ.toEquiv).trans QuaternionCyclic.card_model
  have hzglobal:=NormalNonabelianSixteen.sylow_center_le_center Q hQcard hna hc S
  rintro z ⟨a,ha,rfl⟩
  let ak:K:=eK.symm a
  have hak:ak∈center K := (centerCongr eK.symm ⟨a,ha⟩).property
  have ham:(ak:S)∈center S := P.nonabelian_center_le K hnK ⟨ak,hak,rfl⟩
  exact hzglobal ⟨(ak:S),ham,rfl⟩

theorem center_eq_core_center (Q:Subgroup G) [Q.Normal] (hQ:IsPGroup 2 Q)
    (hc:centralizer (Q:Set G)≤Q) (hna:¬IsMulCommutative Q) (h3:3∣Nat.card G)
    (S:Sylow 2 G) (eS:S≃*W) : center G=(center Q).map Q.subtype := by
  apply le_antisymm _ (core_center_central Q hQ hc hna h3 S eS)
  intro g hg
  have hq:g∈Q:=hc (center_le_centralizer (Q:Set G) hg)
  refine ⟨⟨g,hq⟩,?_,rfl⟩
  exact mem_center_iff.mpr (fun a=>Subtype.ext (mem_center_iff.mp hg a))

theorem center_card_four (Q:Subgroup G) [Q.Normal] (hQ:IsPGroup 2 Q)
    (hc:centralizer (Q:Set G)≤Q) (hna:¬IsMulCommutative Q) (h3:3∣Nat.card G)
    (S:Sylow 2 G) (eS:S≃*W) : Nat.card (center G)=4 := by
  obtain ⟨eQ⟩:=core_equiv Q hQ hc hna h3 S eS
  rw [center_eq_core_center Q hQ hc hna h3 S eS,card_map_of_injective Q.subtype_injective,
    Nat.card_congr ((centerCongr eQ).trans modelCenterEquiv).toEquiv]
  simp
end WreathedVertex
