module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.Hyperplanes
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.PlaneCubic
public import Theory.GroupAction.ElementConjugacyOrbit
public import Mathlib.GroupTheory.Perm.Sign

/-!
# Order of the actual elementary-plane normalizer

Normalizer fusion gives an orbit of fifteen points. Its stabilizer contains
the source Sylow128 and a genuine cubic, so has order divisible by384.
It is contained in the original involution centralizer of order1152.
The faithful polarity action embeds the normalizer quotient into S6;
these exact divisibilities force orders5760 and360 respectively.
Source: Aschbacher, Sporadic Groups (1994),45.6, printed p.244.
-/

@[expose] public noncomputable section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree
variable {G:Type*} [Group G] [Finite G] {z:G}
namespace RootPair
variable (P:RootPair z)

private theorem plane_orbit_card (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) :
    Nat.card ((normalizer (V:Set G)).elementOrbit z)=15 := by
  classical
  let K:=normalizer (V:Set G)
  have hzV:z∈V := P.E_le_plane h V hV P.z_mem_E
  have hz1:z≠1 := by intro he; have hh:=h.involution; simp [he] at hh
  let e:K.elementOrbit z≃{x:V // x≠1} := {
    toFun := fun x=>⟨⟨x,(elementOrbit_subset le_rfl hzV x.property)⟩,by
      intro he
      have ho := elementOrbit_orderOf x.property
      rw [congrArg Subtype.val he,h.involution] at ho
      simp at ho⟩
    invFun := fun x=>⟨x.val,P.plane_nonidentity_transitive h V hV z x.val hzV x.val.property hz1
      (fun he=>x.property (Subtype.ext he))⟩
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl }
  rw [Nat.card_congr e]
  let := Fintype.ofFinite V
  have hV' : Fintype.card V=16 := by simpa only [Nat.card_eq_fintype_card] using hV.2.2
  rw [Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype_compl,hV']

theorem plane_normalizer_card (h:IsType z) (V:Subgroup G)
    (hV:V≤P.T ∧ IsElementaryAbelian 2 V ∧ Nat.card V=16) :
    Nat.card (normalizer (V:Set G))=5760 ∧ Nat.card (NormalizerAction.Star V)=360 := by
  let K:=normalizer (V:Set G)
  let C:=K⊓centralizer z
  have hTC:P.T≤C := le_inf ((P.T_le_N h).trans (P.plane_normalized_by_N h V hV)) P.T_le_centralizer
  have h128 : 128∣Nat.card C := by simpa only [P.T_card h] using card_dvd_of_le hTC
  obtain ⟨a,ha,ha3⟩:=P.exists_cubic_plane_stabilizer h V hV
  have haC:a∈C := ⟨ha.2,ha.1⟩
  have h3 : 3∣Nat.card C := by
    have he : orderOf (⟨a,haC⟩:C)=3 := (orderOf_injective C.subtype C.subtype_injective (⟨a,haC⟩:C)).symm.trans ha3
    exact he ▸ orderOf_dvd_natCard (⟨a,haC⟩:C)
  have h384 : 384∣Nat.card C := (show Nat.Coprime 128 3 by decide).mul_dvd_of_dvd_of_dvd h128 h3
  have h1152 : Nat.card C∣1152 := by
    have hd:=card_dvd_of_le (show C≤centralizer z from inf_le_right)
    simpa [h.centralizer_card] using hd
  have hzK:z∈K := V.le_normalizer (P.E_le_plane h V hV P.z_mem_E)
  have hOrbit : 15*Nat.card C=Nat.card K := by
    have hh:=elementOrbit_card K z hzK
    rw [P.plane_orbit_card h V hV] at hh
    exact hh
  have hker : Nat.card (NormalizerAction.C V)=16 := by
    change Nat.card ((Subgroup.centralizer (V:Set G)).subgroupOf K)=16
    rw [P.plane_centralizer h V hV,Nat.card_congr (subgroupOfEquivOfLe V.le_normalizer).toEquiv,hV.2.2]
  have hK : Nat.card K=Nat.card (NormalizerAction.Star V)*16 := by
    have hh:=card_eq_card_quotient_mul_card_subgroup (NormalizerAction.C V)
    rw [hker] at hh
    exact hh
  obtain ⟨φ,hφ⟩:=P.exists_injective_plane_six_action h V hV
  have h720 : Nat.card (NormalizerAction.Star V)∣720 := by
    have hd:=card_dvd_of_injective φ hφ
    simpa [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin,Nat.factorial] using hd
  have hKdvd : Nat.card K∣11520 := by
    rw [hK]
    exact Nat.mul_dvd_mul h720 (dvd_refl 16)
  have hC768 : Nat.card C∣768 := by
    apply Nat.dvd_of_mul_dvd_mul_left (by decide : 0<15)
    rw [hOrbit]
    exact hKdvd
  have hc : Nat.card C=384 := Nat.dvd_antisymm
    (by simpa using Nat.dvd_gcd hC768 h1152) h384
  rw [hc] at hOrbit
  constructor
  · exact hOrbit.symm
  · omega
end RootPair
end Theory.GroupTheory.Recognition.UnitaryFourThree
