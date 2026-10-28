module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.NormalForms.Recognition
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.OrbitKernels.Actions
/-!
# Normality of the concrete triality four-group

The loop generators centralize the four-group `K`. Even standard automorphisms
centralize it, and each odd standard-automorphism family exchanges the other
two nonidentity elements. Thus every generator of the actual permutation group
`N` normalizes `K`. No collection hypothesis is used.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.3(2), printed pp. 60–61.
Products act by left composition, reversing the source's right-action words.
-/

public section
open Atlas.Fischer Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin

private theorem normalizes_K_of_generators (g : Equiv.Perm Triple)
    (h : ∀ k ∈ ({k1,k2,k3} : Set N), ∃ l ∈ K, g * k.val = l.val * g) :
    g ∈ Subgroup.normalizer ((K.map N.subtype : Subgroup (Equiv.Perm Triple)) : Set _) := by
  apply Subgroup.mem_normalizer_fintype
  rintro _ ⟨k,hk,rfl⟩
  have hh (k : N) (hk : k ∈ ({k1,k2,k3} : Set N)) :
      g * k.val * g⁻¹ ∈ K.map N.subtype := by
    obtain ⟨l,hl,he⟩ := h k hk
    refine ⟨l,hl,?_⟩
    change l.val = g * k.val * g⁻¹
    rw [he, mul_assoc, mul_inv_cancel, mul_one]
  rcases (mem_K_iff k).mp hk with rfl | rfl | rfl | rfl
  · change g * 1 * g⁻¹ ∈ K.map N.subtype
    simp only [mul_one, mul_inv_cancel, Subgroup.one_mem]
  · exact hh k1 (by simp)
  · exact hh k2 (by simp)
  · exact hh k3 (by simp)

private theorem psi_loop_normalizes_K (d : ParkerLoop) :
    psi1 d ∈ Subgroup.normalizer (K.map N.subtype : Set _) ∧
    psi2 d ∈ Subgroup.normalizer (K.map N.subtype : Set _) ∧
    psi3 d ∈ Subgroup.normalizer (K.map N.subtype : Set _) := by
  have h13 : k1 * k3 = k2 := by
    rw [← k1_mul_k2, ← mul_assoc, ← pow_two, k1_sq, one_mul]
  have h31 : Commute (psi3N d) k1 := by
    apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psi3 d (k1.val (a,b,c)) = k1.val (psi3 d (a,b,c))
    simp [k1_apply]
  have h33 : Commute (psi3N d) k3 := by
    apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psi3 d (k3.val (a,b,c)) = k3.val (psi3 d (a,b,c))
    simp [k3_apply]
  have h (p : N) (h1 : Commute p k1) (h3 : Commute p k3) :
      p.val ∈ Subgroup.normalizer (K.map N.subtype : Set _) := by
    apply normalizes_K_of_generators
    rintro k (rfl | rfl | rfl)
    · exact ⟨k1, (mem_K_iff _).mpr (by simp), congrArg Subtype.val h1.eq⟩
    · refine ⟨k2, (mem_K_iff _).mpr (by simp), ?_⟩
      have he : p * k2 = k2 * p := by rw [← h13]; exact (h1.mul_right h3).eq
      exact congrArg Subtype.val he
    · exact ⟨k3, (mem_K_iff _).mpr (by simp), congrArg Subtype.val h3.eq⟩
  exact ⟨h _ (psi1N_commutes_k1 d) (psi1N_commutes_k3 d),
    h _ (psi2N_commutes_k1 d) (psi2N_commutes_k3 d),h _ h31 h33⟩

private theorem psi_aut_normalizes_K (α : ParkerStandardGroup) :
    psiAut1 α.val ∈ Subgroup.normalizer (K.map N.subtype : Set _) ∧
    psiAut2 α.val ∈ Subgroup.normalizer (K.map N.subtype : Set _) ∧
    psiAut3 α.val ∈ Subgroup.normalizer (K.map N.subtype : Set _) := by
  have hk1 : k1 ∈ K := (mem_K_iff _).mpr (by simp)
  have hk2 : k2 ∈ K := (mem_K_iff _).mpr (by simp)
  have hk3 : k3 ∈ K := (mem_K_iff _).mpr (by simp)
  by_cases ha : α.val parkerOmega = parkerOmega
  · have he : diagonal α.val ∈ Subgroup.normalizer (K.map N.subtype : Set _) := by
      apply normalizes_K_of_generators
      rintro k (rfl | rfl | rfl)
      · refine ⟨k1,hk1,?_⟩
        ext ⟨a,b,c⟩ : 1
        simp [diagonal,k1_apply,ha]
      · refine ⟨k2,hk2,?_⟩
        ext ⟨a,b,c⟩ : 1
        simp [diagonal,k2_apply,ha]
      · refine ⟨k3,hk3,?_⟩
        ext ⟨a,b,c⟩ : 1
        simp [diagonal,k3_apply,ha]
    simpa only [psiAut1,psiAut2,psiAut3,if_pos ha] using And.intro he (And.intro he he)
  · have ho := parkerStandard_omega_odd α ha
    refine ⟨?_,?_,?_⟩
    · apply normalizes_K_of_generators
      rintro k (rfl | rfl | rfl)
      · exact ⟨k1,hk1,congrArg Subtype.val (psiAut1N_commutes_k1 α).eq⟩
      · refine ⟨k3,hk3,?_⟩
        ext ⟨a,b,c⟩ : 1
        simp only [psiAut1, if_neg ha, Equiv.Perm.mul_apply]
        simp [diagonal,flip1,k2_apply,k3_apply,ho,
          ← signZero_inverseZero, ← signZero_optionMap]
      · refine ⟨k2,hk2,?_⟩
        ext ⟨a,b,c⟩ : 1
        simp only [psiAut1, if_neg ha, Equiv.Perm.mul_apply]
        simp [diagonal,flip1,k2_apply,k3_apply,ho,
          ← signZero_inverseZero, ← signZero_optionMap]
    · apply normalizes_K_of_generators
      rintro k (rfl | rfl | rfl)
      · refine ⟨k3,hk3,?_⟩
        ext ⟨a,b,c⟩ : 1
        simp only [psiAut2, if_neg ha, Equiv.Perm.mul_apply]
        simp [diagonal,flip2,k1_apply,k3_apply,ho,
          ← signZero_inverseZero, ← signZero_optionMap]
      · refine ⟨k2,hk2,?_⟩
        ext ⟨a,b,c⟩ : 1
        simp only [psiAut2, if_neg ha, Equiv.Perm.mul_apply]
        simp [diagonal,flip2,k2_apply,ho,
          ← signZero_inverseZero, ← signZero_optionMap]
      · refine ⟨k1,hk1,?_⟩
        ext ⟨a,b,c⟩ : 1
        simp only [psiAut2, if_neg ha, Equiv.Perm.mul_apply]
        simp [diagonal,flip2,k1_apply,k3_apply,ho,
          ← signZero_inverseZero, ← signZero_optionMap]
    · apply normalizes_K_of_generators
      rintro k (rfl | rfl | rfl)
      · refine ⟨k2,hk2,?_⟩
        ext ⟨a,b,c⟩ : 1
        simp only [psiAut3, if_neg ha, Equiv.Perm.mul_apply]
        simp [diagonal,flip3,k1_apply,k2_apply,ho,
          ← signZero_inverseZero, ← signZero_optionMap]
      · refine ⟨k1,hk1,?_⟩
        ext ⟨a,b,c⟩ : 1
        simp only [psiAut3, if_neg ha, Equiv.Perm.mul_apply]
        simp [diagonal,flip3,k1_apply,k2_apply,ho,
          ← signZero_inverseZero, ← signZero_optionMap]
      · refine ⟨k3,hk3,?_⟩
        ext ⟨a,b,c⟩ : 1
        simp only [psiAut3, if_neg ha, Equiv.Perm.mul_apply]
        simp [diagonal,flip3,k3_apply,ho,
          ← signZero_inverseZero, ← signZero_optionMap]

theorem K_normal : K.Normal := by
  have hn : N ≤ Subgroup.normalizer (K.map N.subtype : Set _) := by
    apply (Subgroup.closure_le _).mpr
    rintro g (((⟨d,rfl⟩ | ⟨d,rfl⟩) | ⟨d,rfl⟩) | ⟨α,hα,hg⟩)
    · exact (psi_loop_normalizes_K d).1
    · exact (psi_loop_normalizes_K d).2.1
    · exact (psi_loop_normalizes_K d).2.2
    · rcases hg with rfl | rfl | rfl
      · exact (psi_aut_normalizes_K ⟨α,hα⟩).1
      · exact (psi_aut_normalizes_K ⟨α,hα⟩).2.1
      · exact (psi_aut_normalizes_K ⟨α,hα⟩).2.2
  constructor
  intro k hk g
  have hc := (Subgroup.mem_normalizer_iff.mp (hn g.prop) k.val).mp ⟨k,hk,rfl⟩
  obtain ⟨l,hl,he⟩ := hc
  exact (show l = g * k * g⁻¹ from Subtype.ext he) ▸ hl
end Sporadic.Monster.Construction.TrialitySpin
