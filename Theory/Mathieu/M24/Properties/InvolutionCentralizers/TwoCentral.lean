module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Coverage
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoA.Quotient
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.CentralInvolutions
public import Theory.GroupTheory.CharacteristicCentralizerSylow
public import Theory.GroupTheory.DoubleCoverCentralizer.Basic

/-!
# The two-central involution class and centralizer order of M₂₄

The checked Sylow center has a unique nonidentity element, enumeration
row 106. Its certified fusion word conjugates it to the actual 2A
representative. Sylow conjugacy therefore places every two-central
involution in 2A, and the established centralizer calculation gives 21504.
No coverage or class-selection premise remains.

Source: GLS3 Table 5.3e; Aschbacher–Smith 14.7.68(2), printed p.1071.
-/

public section
open Subgroup Theory.GroupTheory.DoubleCoverCentralizer
namespace Sporadic.Mathieu.M24InvolutionCentralizers
open M24LocalGeometry.SylowNormalizer

private theorem element106_isConj_twoA :
    IsConj involution2A (OrderEnumeration.element 106).val := by
  have fusion (i : Fin 1024) (hi : i ≠ 0)
      (hsq : OrderEnumeration.point i
        (OrderEnumeration.point i (FusionData.badPoint i)) = FusionData.badPoint i) :
      IsConj (FusionData.base (FusionData.tag i)) (OrderEnumeration.element i).val := by
    let g := FusionData.evaluate (FusionData.word i)
    have he : g * FusionData.base (FusionData.tag i) =
        (OrderEnumeration.element i).val * g := by
      apply Subtype.ext
      apply Equiv.ext
      intro x
      change g.val ((FusionData.base (FusionData.tag i)).val x) =
        (OrderEnumeration.element i).val.val (g.val x)
      rw [FusionData.base_apply, FusionData.evaluate_apply, FusionData.evaluate_apply,
        OrderEnumeration.element_apply]
      exact FusionData.fusion_check i hi hsq x
    exact isConj_iff.mpr ⟨g, (mul_inv_eq_iff_eq_mul).mpr he⟩
  have ht : FusionData.tag 106 = true := by decide +kernel
  have hsq : OrderEnumeration.point 106
      (OrderEnumeration.point 106 (FusionData.badPoint 106)) = FusionData.badPoint 106 := by
    decide +kernel
  simpa only [ht, FusionData.base, ↓reduceIte] using fusion 106 (by decide) hsq

/-- The two-central mark selects the actual 2A conjugacy class. -/
theorem isConj_twoA_of_twoCentral (x : M24) (hx : orderOf x = 2)
    (hc : TwoCentral x) : IsConj involution2A x := by
  obtain ⟨P, hp, hc⟩ := hc
  have hind : ¬ 2 ∣ candidate.index := by
    have hc := candidate.card_mul_index
    rw [candidate_card, m24_order] at hc
    have he : candidate.index = 239085 := by omega
    rw [he]
    decide
  let S : Sylow 2 M24 := (IsPGroup.of_card (p := 2) (n := 10) candidate_card).toSylow hind
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M24 P S
  have hP : ((g • P : Sylow 2 M24) : Subgroup M24) = candidate :=
    congrArg (fun Q : Sylow 2 M24 => (Q : Subgroup M24)) hg
  let eP : P ≃* candidate :=
    (P.equivSMul g).trans (MulEquiv.subgroupCongr hP)
  have hyc : eP ⟨x, hp⟩ ∈ center candidate := by
    apply mem_center_iff.mpr
    intro t
    obtain ⟨s, rfl⟩ := eP.surjective t
    rw [← eP.map_mul, ← eP.map_mul, mem_center_iff.mp hc s]
  have hyo : orderOf (eP ⟨x, hp⟩) = 2 := by
    rw [eP.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hx
  have hy := central_involution_eq_element106 _ hyc hyo
  have he : (MulAut.conj g) x = (OrderEnumeration.element 106).val :=
    congrArg Subtype.val hy
  exact element106_isConj_twoA.trans (isConj_iff.mpr ⟨g, he⟩).symm

/-- The full centralizer of a two-central M₂₄ involution has order 21504. -/
theorem card_centralizer_of_twoCentral (x : M24) (hx : orderOf x = 2)
    (hc : TwoCentral x) : Nat.card (centralizer ({x} : Set M24)) = 21504 := by
  rw [← card_centralizer_eq_of_isConj _ _ (isConj_twoA_of_twoCentral x hx hc)]
  exact TwoA.centralizer_card

end Sporadic.Mathieu.M24InvolutionCentralizers
