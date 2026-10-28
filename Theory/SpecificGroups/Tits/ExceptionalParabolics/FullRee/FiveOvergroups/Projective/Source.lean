module

public import Theory.SpecificGroups.Tits.MinimumIndex.CandidateOrders.Max4.Checked
public import Theory.SpecificGroups.Tits.Atlas1600OrderData
import Mathlib.Tactic.FinCases

/-! The original two max4 SLP generators match the native packed Schreier generators exactly. The source embedding and closure retain the original Atlas1600Group carrier. -/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace Tits.Max4Projective
open MinimumIndexCandidates OrderCertificate.Max4

def sourceEmbedding : Atlas1600Group →* Equiv.Perm (Fin 1600) := atlas1600Subgroup.subtype
theorem sourceEmbedding_injective : Function.Injective sourceEmbedding := Subtype.val_injective

def sourceGen : Fin 4 → Atlas1600Group :=
  ![max4Generators.1,max4Generators.2,max4Generators.1⁻¹,max4Generators.2⁻¹]
private def program {G : Type*} [Group G] (a b:G) : G × G :=
  let w0 := a*b
  let w1 := b*w0
  let w2 := w1*a
  let w3 := w2⁻¹
  let w4 := a*w1
  let w5 := w3*w4
  let w6 := w5*w5
  let w7 := w0*b
  let w8 := w0*w7
  let w9 := w0*w8
  let w10 := w9^3
  (w6,w10)
private theorem generator0 : L0Gen 0 = sourceEmbedding (sourceGen 0) := by
  have h : L0Gen 0=(program Atlas1600OrderCertificate.L0G0 Atlas1600OrderCertificate.L0G1).1 := by
    apply Equiv.ext
    apply Atlas1600OrderCertificate.allFin
    decide +kernel
  rw [h,program,Atlas1600OrderCertificate.L0G0_eq_atlas,Atlas1600OrderCertificate.L0G1_eq_atlas]
  rfl
private theorem generator1 : L0Gen 1 = sourceEmbedding (sourceGen 1) := by
  have h : L0Gen 1=(program Atlas1600OrderCertificate.L0G0 Atlas1600OrderCertificate.L0G1).2 := by
    apply Equiv.ext
    apply Atlas1600OrderCertificate.allFin
    decide +kernel
  rw [h,program,Atlas1600OrderCertificate.L0G0_eq_atlas,Atlas1600OrderCertificate.L0G1_eq_atlas]
  rfl

theorem sourceGen_spec (i:Fin 4) : L0Gen i=sourceEmbedding (sourceGen i) := by
  fin_cases i
  · exact generator0
  · exact generator1
  · exact congrArg Inv.inv generator0
  · exact congrArg Inv.inv generator1

theorem sourceGen_mem (i:Fin 4) : sourceGen i∈max4 := by
  have h0 : max4Generators.1∈max4 := subset_closure (by simp)
  have h1 : max4Generators.2∈max4 := subset_closure (by simp)
  fin_cases i
  · exact h0
  · exact h1
  · exact max4.inv_mem h0
  · exact max4.inv_mem h1

theorem sourceGen_closure : closure (Set.range sourceGen)=max4 := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨i,rfl⟩
    exact sourceGen_mem i
  · rw [max4]
    apply (closure_le _).mpr
    rintro x (hx|hx)
    · subst x; exact subset_closure ⟨0,rfl⟩
    · have he : x=max4Generators.2 := hx
      subst x;exact subset_closure ⟨1,rfl⟩

theorem packed0_ne_one : L0Gen 0≠1 := by
  intro he
  have h := congrArg (fun g:Equiv.Perm (Fin 1600) => g 0) he
  have hn : L0Gen 0 0≠0 := by decide +kernel
  exact hn h
end Tits.Max4Projective
