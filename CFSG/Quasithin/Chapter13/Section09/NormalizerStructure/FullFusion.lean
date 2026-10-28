module
public import CFSG.Quasithin.Chapter13.Section09.NormalizerStructure.CoreSpan
public import CFSG.Quasithin.Chapter13.Section09.NormalizerStructure.Fusion

/-!
# The original local fusion pattern with its unresolved label ordering

The swap fuses with z and the two ambient classes restrict to three
local classes each. The two candidate four-point classes have opposite
fusion, retained as an explicit unordered choice. This proves the
source fusion content needed by alignment without the false printed
claim that multiplication by z preserves Delta5.

Source: Aschbacher–Smith 13.9.9, printed pp.972–973.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath SymmetricFourWreath.InvolutionClasses
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

theorem local_fusion_flags {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    ∃b:Bool,∀j:Fin 6,
      (m.fusionFlags j=true ↔ j=0 ∨ j=5 ∨ j=(if b then 4 else 2)) := by
  have h0:m.fusionFlags 0=true := by
    simp only [fusionFlags,decide_eq_true_eq]
    exact IsConj.refl _
  have h1:m.fusionFlags 1=false := by
    simp only [fusionFlags,decide_eq_false_iff_not]
    exact fun h=>m.not_isConj_t_z h.symm
  have h3:m.fusionFlags 3=false := by
    simp only [fusionFlags,decide_eq_false_iff_not]
    intro h
    exact m.not_isConj_t_z ((m.double_transposition_fused_t (hG.evenCharacteristic d.T)
      (m.centralizer_growth hG).1).trans h.symm)
  have h5:m.fusionFlags 5=true := by
    simp only [fusionFlags,decide_eq_true_eq]
    exact m.swap_fused_z hG
  rcases m.normalizerOrbit_fusion_alternatives hG with h|h
  · refine ⟨false,?_⟩
    intro j
    have hj:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5:=by omega
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all
  · refine ⟨true,?_⟩
    intro j
    have hj:j=0 ∨ j=1 ∨ j=2 ∨ j=3 ∨ j=4 ∨ j=5:=by omega
    rcases hj with rfl|rfl|rfl|rfl|rfl|rfl <;> simp_all

theorem local_involution_fusion_alternatives {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    ∃b:Bool,∀x:G,x∈d.M→
      (IsConj m.z x ↔ x∈m.localInvolutionClass 0 ∨ x∈m.localInvolutionClass 5 ∨
        x∈m.localInvolutionClass (if b then 4 else 2)) ∧
      (IsConj m.t x ↔ x∈m.localInvolutionClass 1 ∨ x∈m.localInvolutionClass 3 ∨
        x∈m.localInvolutionClass (if b then 2 else 4)) := by
  obtain ⟨b,hb⟩:=m.local_fusion_flags hG
  refine ⟨b,?_⟩
  intro x hx
  have hc (j:Fin 6) (hj:x∈m.localInvolutionClass j) :
      IsConj m.z x ↔ m.fusionFlags j=true := by
    have hlocal:=m.isConj_of_mem_localInvolutionClass j x hj
    simp only [fusionFlags,decide_eq_true_eq]
    exact ⟨fun h=>h.trans hlocal.symm,fun h=>h.trans hlocal⟩
  have ho (j:Fin 6) (hj:x∈m.localInvolutionClass j) : orderOf x=2 := by
    obtain ⟨g,hg⟩:=isConj_iff.mp (m.isConj_of_mem_localInvolutionClass j x hj)
    rw [←hg]
    exact ((MulAut.conj g).orderOf_eq _).trans
      ((orderOf_injective m.embedding m.embedding_injective _).trans (representative_order j))
  have hzin : IsConj m.z x→∃j:Fin 6,x∈m.localInvolutionClass j := by
    intro h
    have hox:orderOf x=2 := by
      obtain ⟨g,hg⟩:=isConj_iff.mp h
      rw [←hg]
      exact ((MulAut.conj g).orderOf_eq _).trans m.z_order
    obtain ⟨j,hj,_⟩:=m.local_involution_classes x hx hox
    exact ⟨j,hj⟩
  have htin : IsConj m.t x→∃j:Fin 6,x∈m.localInvolutionClass j := by
    intro h
    have hox:orderOf x=2 := by
      obtain ⟨g,hg⟩:=isConj_iff.mp h
      rw [←hg]
      exact ((MulAut.conj g).orderOf_eq _).trans m.t_order
    obtain ⟨j,hj,_⟩:=m.local_involution_classes x hx hox
    exact ⟨j,hj⟩
  constructor
  · constructor
    · intro h
      obtain ⟨j,hj⟩:=hzin h
      rcases (hb j).mp ((hc j hj).mp h) with rfl|rfl|he
      · exact Or.inl hj
      · exact Or.inr (Or.inl hj)
      · exact Or.inr (Or.inr (he ▸ hj))
    · rintro (h|h|h)
      · exact (hc 0 h).mpr ((hb 0).mpr (Or.inl rfl))
      · exact (hc 5 h).mpr ((hb 5).mpr (Or.inr (Or.inl rfl)))
      · exact (hc _ h).mpr ((hb _).mpr (Or.inr (Or.inr rfl)))
  · constructor
    · intro h
      obtain ⟨j,hj⟩:=htin h
      have hn:¬(j=0 ∨ j=5 ∨ j=(if b then 4 else 2)):=fun he=>
        m.not_isConj_t_z (h.trans ((hc j hj).mpr ((hb j).mpr he)).symm)
      have he:j=1 ∨ j=3 ∨ j=(if b then 2 else 4) := by cases b <;> simp_all <;> omega
      rcases he with rfl|rfl|he
      · exact Or.inl hj
      · exact Or.inr (Or.inl hj)
      · exact Or.inr (Or.inr (he ▸ hj))
    · intro h
      have hex:∃j:Fin 6,x∈m.localInvolutionClass j ∧ (j=1 ∨ j=3 ∨ j=(if b then 2 else 4)) := by
        rcases h with h|h|h
        · exact ⟨1,h,Or.inl rfl⟩
        · exact ⟨3,h,Or.inr (Or.inl rfl)⟩
        · exact ⟨_,h,Or.inr (Or.inr rfl)⟩
      obtain ⟨j,hj,hjv⟩:=hex
      apply (m.original_two_involution_classes hG x (ho j hj)).resolve_left
      intro hzx
      have hzj:=(hb j).mp ((hc j hj).mp hzx)
      cases b <;> dsimp at hjv hzj <;> omega

end CFSG.Quasithin.Chapter13.Section09.Marking


namespace CFSG.Quasithin.Chapter13.Section09
open Subgroup
variable {G:Type*} [Group G] [Finite G]

/-- The original-input fusion and core-span consumer. -/
theorem source13_9_9_fusion {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G)
    (d:Configuration G) (m:Marking d) :
    IsConj m.z m.s ∧ Subgroup.closure {x:G | x∈m.core ∧ IsConj m.t x}=m.B⊓m.core ∧
      ∃b:Bool,∀x:G,x∈d.M→
        (IsConj m.z x ↔ x∈m.localInvolutionClass 0 ∨ x∈m.localInvolutionClass 5 ∨
          x∈m.localInvolutionClass (if b then 4 else 2)) ∧
        (IsConj m.t x ↔ x∈m.localInvolutionClass 1 ∨ x∈m.localInvolutionClass 3 ∨
          x∈m.localInvolutionClass (if b then 2 else 4)) :=
  ⟨m.swap_fused_z hG,m.core_t_class_closure hG,m.local_involution_fusion_alternatives hG⟩

end CFSG.Quasithin.Chapter13.Section09
