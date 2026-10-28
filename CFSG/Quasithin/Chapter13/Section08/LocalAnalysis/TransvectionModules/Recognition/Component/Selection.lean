module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Recognition.Action
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Basic
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Basic

/-!
# A component moved by the nonsolvable transvection closure

If the literal normal closure of t in H/O₂(H) is nonsolvable, it contains
an ambient C-component not centralized by t. Otherwise every conjugate of
t would centralize each such component, making one contained in the normal
closure abelian. The component lifts across O₂(H), a solvable kernel, to
a genuine subgroup K ≤ H with relative C-component membership.

This proves nontriviality of [K*,⟨t⟩]. The stronger identity K*=[K*,⟨t⟩]
and the natural-module recognition are separate obligations: no component
normalization is inferred from noncentrality. No use is made of 13.8.13.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, the first
paragraph of the proof of 13.8.5, printed p.947 (PDF p.964).
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component

private theorem exists_noncentral_in_normalClosure {A : Type*} [Group A] [Finite A]
    (t : A) (hns : ¬ Group.IsSolvable (normalClosure ({t} : Set A))) :
    ∃ C : Subgroup A, C ≤ normalClosure ({t} : Set A) ∧ C.IsCComponent ∧
      t ∉ centralizer (C : Set A) := by
  let N := normalClosure ({t} : Set A)
  obtain ⟨D, hD⟩ := exists_isCComponent_of_not_isSolvable hns
  let C := D.map N.subtype
  have hC : C.IsCComponent := hD.map_subtype (inferInstance : N.Normal).isSubnormal
  have hCN : C ≤ N := map_subtype_le D
  by_contra! hall
  have hNC : N ≤ centralizer (C : Set A) := by
    apply (closure_le (centralizer (C : Set A))).mpr
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    have hat : a = t := Set.mem_singleton_iff.mp ha
    subst a
    obtain ⟨g, rfl⟩ := isConj_iff.mp hax
    intro c hc
    let E := C.map (MulAut.conj g⁻¹).toMonoidHom
    have hEN : E ≤ N := by
      rintro _ ⟨y, hy, rfl⟩
      exact (inferInstance : N.Normal).conj_mem y (hCN hy) g⁻¹
    have hE := hall E hEN (hC.map_equiv (MulAut.conj g⁻¹))
    have he := hE _ (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hc)
    change (g⁻¹ * c * (g⁻¹)⁻¹) * t = t * (g⁻¹ * c * (g⁻¹)⁻¹) at he
    simpa only [MulAut.conj_apply, inv_inv, mul_assoc, mul_inv_cancel_left,
      inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel_right, mul_inv_cancel,
      mul_one] using
      congrArg (fun z => g * z * g⁻¹) he
  have hc : IsMulCommutative C := le_centralizer_iff_isMulCommutative.mp (hCN.trans hNC)
  let := hc
  exact hC.not_isSolvable (Group.isSolvable_of_comm fun x y : C => mul_comm' x y)

/-- A genuine C-component of H with nontrivial t-commutator in the literal star quotient. -/
theorem exists_noncentral_component {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (t : Source.Hstar H)
    (hns : ¬ Group.IsSolvable (normalClosure ({t} : Set (Source.Hstar H)))) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      Source.starImage H K ≤ normalClosure ({t} : Set (Source.Hstar H)) ∧
      ⁅Source.starImage H K, zpowers t⁆ ≠ ⊥ := by
  obtain ⟨C, hCN, hC, ht⟩ := exists_noncentral_in_normalClosure t hns
  let := pCore_isNilpotent (p := 2) (G := H)
  obtain ⟨D, hD, he⟩ := hC.exists_map_quotient_eq (pCore 2 H)
  have hsub : (D.map H.subtype).subgroupOf H = D :=
    comap_map_eq_self_of_injective H.subtype_injective D
  have hstar : Source.starImage H (D.map H.subtype) = C := by
    unfold Source.starImage
    rw [hsub, he]
  refine ⟨D.map H.subtype, map_subtype_le D, hsub.symm ▸ hD,
    hstar.symm ▸ hCN, ?_⟩
  rw [hstar]
  intro hcomm
  exact ht ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm))
    (mem_zpowers t))

end CFSG.Quasithin.Chapter13.Section08.TransvectionRecognition.Component

end
