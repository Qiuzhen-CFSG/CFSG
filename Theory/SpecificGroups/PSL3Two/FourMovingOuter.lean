module
public import Theory.SpecificGroups.PSL3Two.InvolutionResidual
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.Kernels.SylowModels
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Mathlib.GroupTheory.IndexNormal

/-!
# Inner actors fixing a cubic four-group point

In PSL₃(2), the centralizer of an involution is a two-group. An elementary
four-group containing that involution lies in a common dihedral Sylow group,
where it has index two. Thus the involution centralizer normalizes the four.
An ambient actor fixing the involution while moving the four to a noncommuting
conjugate cannot induce an inner automorphism of the component.

Source application: Aschbacher–Smith 2.4.34, printed p.548, the original outer
actor on both components of the paired group.
-/

public noncomputable section
open Subgroup
namespace Matrix.PSL3Two
variable {K : Type*} [Group K] [Finite K]

/-- An involution centralizer preserves each elementary four containing it. -/
theorem centralizer_normalizes_four
    (e : K ≃* PSL) (U : Subgroup K) [IsElementaryAbelian 2 U]
    (hU : Nat.card U = 4) (z : K) (hz : z ∈ U) (ho : orderOf z = 2) :
    centralizer ({z} : Set K) ≤ normalizer (U : Set K) := by
  let : CommGroup U := IsMulCommutative.instCommGroup
  have hp : IsPGroup 2 (centralizer ({z} : Set K)) :=
    (InvolutionResidual.centralizer_two (e z) ((e.orderOf_eq z).trans ho)).of_equiv
      (Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e z).symm
  obtain ⟨S,hS⟩ := hp.exists_le_sylow
  have hUC : U ≤ centralizer ({z} : Set K) := by
    intro u hu
    apply mem_centralizer_singleton_iff.mpr
    exact congrArg Subtype.val (mul_comm (⟨u,hu⟩ : U) ⟨z,hz⟩)
  have hUS : U ≤ (S : Subgroup K) := hUC.trans hS
  let Q := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨eQ⟩ := Matrix.PSL3Four.FixedResidualKernels.psl3Two_sylow_dihedral Q
  let eS : S ≃* DihedralGroup 4 :=
    ((S : Subgroup K).equivMapOfInjective e.toMonoidHom e.injective).trans eQ
  have hcardS : Nat.card S = 8 := by rw [Nat.card_congr eS.toEquiv,DihedralGroup.nat_card]
  have hidx : (U.subgroupOf (S : Subgroup K)).index = 2 := by
    have hc := (U.subgroupOf (S : Subgroup K)).card_mul_index
    rw [Nat.card_congr (subgroupOfEquivOfLe hUS).toEquiv,hU,hcardS] at hc
    omega
  have hnormal := normal_of_index_eq_two hidx
  exact hS.trans ((normal_subgroupOf_iff_le_normalizer hUS).mp hnormal)


variable {G : Type*} [Group G] [Finite G]

/-- A four-group mover fixing its marked involution induces an outer action. -/
theorem moving_four_not_inner
    (K U : Subgroup G) (e : K ≃* PSL) (hUK : U ≤ K)
    [IsElementaryAbelian 2 U] (hU : Nat.card U = 4)
    (z x : G) (hz : z ∈ U) (ho : orderOf z = 2)
    (hx : x ∈ normalizer (K : Set G)) (hfix : x ∈ centralizer ({z} : Set G))
    (hmove : ¬ U.map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U : Set G)) :
    K.normalizerMonoidHom ⟨x,hx⟩ ∉ MulAut.innerSubgroup K := by
  let α := K.normalizerMonoidHom ⟨x,hx⟩
  let W := U.subgroupOf K
  let zK : K := ⟨z,hUK hz⟩
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hUK
  have hW : Nat.card W = 4 := (Nat.card_congr (subgroupOfEquivOfLe hUK).toEquiv).trans hU
  have hzK : orderOf zK = 2 := (Subgroup.orderOf_coe zK).symm.trans ho
  have hαz : α zK = zK := by
    apply Subtype.ext
    change x*z*x⁻¹=z
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hfix)
  rintro ⟨k,hk⟩
  change MulAut.conj k = α at hk
  have hkz : k ∈ centralizer ({zK} : Set K) := by
    rw [←hk] at hαz
    exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hαz)
  have hn : k ∈ normalizer (W : Set K) := centralizer_normalizes_four e W hW zK hz hzK hkz
  apply hmove
  rintro v ⟨u,hu,rfl⟩
  have huK : (⟨u,hUK hu⟩ : K) ∈ W := hu
  have hmem : (MulAut.conj k⁻¹) (⟨u,hUK hu⟩ : K) ∈ W :=
    ((normalizer (W : Set K)).inv_mem hn _).mp huK
  have he : (MulAut.conj k⁻¹) = K.normalizerMonoidHom ⟨x⁻¹,
      (normalizer (K : Set G)).inv_mem hx⟩ := by
    change MulAut.conj k⁻¹ = K.normalizerMonoidHom ((⟨x,hx⟩ : normalizer (K : Set G))⁻¹)
    rw [map_inv,map_inv]
    exact congrArg Inv.inv hk
  rw [he] at hmem
  have hUmem : x⁻¹*u*x ∈ U := by
    change x⁻¹*u*(x⁻¹)⁻¹ ∈ U at hmem
    simpa only [inv_inv] using hmem
  let : CommGroup U := IsMulCommutative.instCommGroup
  intro w hw
  change w * (x⁻¹*u*(x⁻¹)⁻¹) = (x⁻¹*u*(x⁻¹)⁻¹) * w
  rw [inv_inv]
  exact congrArg Subtype.val (mul_comm (⟨w,hw⟩ : U) ⟨_,hUmem⟩)

end Matrix.PSL3Two
