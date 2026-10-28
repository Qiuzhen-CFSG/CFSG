module
public import Theory.SpecificGroups.Monster.Construction.NMonomial.ZeroAction.Coefficients
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.NormalForms

/-!
# The triality group needed by the zero-summand cubic argument

The concrete sign subgroup `Z` is normal: each loop generator centralizes its
three named involutions, and each standard automorphism permutes them.
Normal forms then identify `NPlus` with its centralizer, proving normality in
`N`. Finally the existing three-coset calculation and the explicit odd
standard-automorphism formulas show that `N1` together with any one marked
second-family cocode generator generates `N`.

These are statements about the existing permutation group, before quotienting
by `K`. They supply the normality and generation hypotheses of the monomial
argument; they assert no cubic invariance.

Source: Aschbacher, *Sporadic Groups*, Section 14, printed pp. 58--62,
and 9.8(2), 29.9, printed pp. 38 and 157--158. Products use left composition.
-/

@[expose] public section
open Atlas.Codes Atlas.Fischer
open Sporadic.Monster.Construction
open LocalC ShortFamilies TrialitySpin
noncomputable section
namespace Sporadic.Monster.Construction.NMonomial.ZeroAction.CubicInvariance

private def signSet : Set (Equiv.Perm Triple) := {z1,z2,z3}

private theorem normalizes_signSet (g : Equiv.Perm Triple)
    (h : ∀ z ∈ signSet, ∃ t ∈ signSet, g * z = t * g) :
    g ∈ Subgroup.normalizer signSet := by
  apply Subgroup.mem_normalizer_fintype
  intro z hz
  obtain ⟨t,ht,he⟩ := h z hz
  simpa only [he, mul_assoc, mul_inv_cancel, mul_one] using ht

private theorem loop_centralizes_signs (d : ParkerLoop) :
    (∀ z ∈ signSet, psi1 d * z = z * psi1 d) ∧
    (∀ z ∈ signSet, psi2 d * z = z * psi2 d) ∧
    (∀ z ∈ signSet, psi3 d * z = z * psi3 d) := by
  refine ⟨?_,?_,?_⟩ <;> rintro z (rfl | rfl | rfl) <;>
    ext ⟨a,b,c⟩ : 1 <;> simp [Equiv.Perm.mul_apply]

private theorem aut_normalizes_signs (α : ParkerStandardGroup) :
    psiAut1 α.val ∈ Subgroup.normalizer signSet ∧
    psiAut2 α.val ∈ Subgroup.normalizer signSet ∧
    psiAut3 α.val ∈ Subgroup.normalizer signSet := by
  by_cases ha : α.val parkerOmega = parkerOmega
  · have hd : TrialitySpin.diagonal α.val ∈ Subgroup.normalizer signSet := by
      apply normalizes_signSet
      rintro z (rfl | rfl | rfl)
      · refine ⟨z1, by simp [signSet], ?_⟩
        ext ⟨a,b,c⟩ : 1
        simp [Equiv.Perm.mul_apply, TrialitySpin.diagonal]
      · refine ⟨z2, by simp [signSet], ?_⟩
        ext ⟨a,b,c⟩ : 1
        simp [Equiv.Perm.mul_apply, TrialitySpin.diagonal]
      · refine ⟨z3, by simp [signSet], ?_⟩
        ext ⟨a,b,c⟩ : 1
        simp [Equiv.Perm.mul_apply, TrialitySpin.diagonal]
    simpa only [psiAut1,psiAut2,psiAut3,if_pos ha] using ⟨hd,hd,hd⟩
  · refine ⟨?_,?_,?_⟩
    · apply normalizes_signSet
      rintro z (rfl | rfl | rfl)
      · refine ⟨z1, by simp [signSet], ?_⟩
        ext ⟨a,b,c⟩ : 1
        simp [psiAut1,ha,Equiv.Perm.mul_apply,TrialitySpin.diagonal,flip1]
      · refine ⟨z3, by simp [signSet], ?_⟩
        ext ⟨a,b,c⟩ : 1
        simp [psiAut1,ha,Equiv.Perm.mul_apply,TrialitySpin.diagonal,flip1]
      · refine ⟨z2, by simp [signSet], ?_⟩
        ext ⟨a,b,c⟩ : 1
        simp [psiAut1,ha,Equiv.Perm.mul_apply,TrialitySpin.diagonal,flip1]
    · apply normalizes_signSet
      rintro z (rfl | rfl | rfl)
      · refine ⟨z3, by simp [signSet], ?_⟩
        ext ⟨a,b,c⟩ : 1
        simp [psiAut2,ha,Equiv.Perm.mul_apply,TrialitySpin.diagonal,flip2]
      · refine ⟨z2, by simp [signSet], ?_⟩
        ext ⟨a,b,c⟩ : 1
        simp [psiAut2,ha,Equiv.Perm.mul_apply,TrialitySpin.diagonal,flip2]
      · refine ⟨z1, by simp [signSet], ?_⟩
        ext ⟨a,b,c⟩ : 1
        simp [psiAut2,ha,Equiv.Perm.mul_apply,TrialitySpin.diagonal,flip2]
    · apply normalizes_signSet
      rintro z (rfl | rfl | rfl)
      · refine ⟨z2, by simp [signSet], ?_⟩
        ext ⟨a,b,c⟩ : 1
        simp [psiAut3,ha,Equiv.Perm.mul_apply,TrialitySpin.diagonal,flip3]
      · refine ⟨z1, by simp [signSet], ?_⟩
        ext ⟨a,b,c⟩ : 1
        simp [psiAut3,ha,Equiv.Perm.mul_apply,TrialitySpin.diagonal,flip3]
      · refine ⟨z3, by simp [signSet], ?_⟩
        ext ⟨a,b,c⟩ : 1
        simp [psiAut3,ha,Equiv.Perm.mul_apply,TrialitySpin.diagonal,flip3]

theorem signGroup_normal : Z.Normal := by
  have hn : N ≤ Subgroup.normalizer signSet := by
    apply (Subgroup.closure_le _).mpr
    rintro g (((⟨d,rfl⟩ | ⟨d,rfl⟩) | ⟨d,rfl⟩) | ⟨α,hα,hg⟩)
    · exact normalizes_signSet _ (fun z hz => ⟨z,hz,(loop_centralizes_signs d).1 z hz⟩)
    · exact normalizes_signSet _ (fun z hz => ⟨z,hz,(loop_centralizes_signs d).2.1 z hz⟩)
    · exact normalizes_signSet _ (fun z hz => ⟨z,hz,(loop_centralizes_signs d).2.2 z hz⟩)
    · rcases hg with rfl | rfl | rfl
      · exact (aut_normalizes_signs ⟨α,hα⟩).1
      · exact (aut_normalizes_signs ⟨α,hα⟩).2.1
      · exact (aut_normalizes_signs ⟨α,hα⟩).2.2
  have hm : Z.map N.subtype = Subgroup.closure signSet := by
    rw [Z, MonoidHom.map_closure]
    congr 1
    simp [Set.image_insert_eq,Set.image_singleton,signSet,z1N,z2N,z3N,psi1N,psi2N,psi3N,z1,z2,z3]
  constructor
  intro z hz g
  have hg := Subgroup.normalizer_le_normalizer_closure signSet (hn g.prop)
  rw [← hm] at hg
  obtain ⟨t,ht,he⟩ := (Subgroup.mem_normalizer_iff.mp hg z.val).mp ⟨z,hz,rfl⟩
  exact (show t = g * z * g⁻¹ from Subtype.ext he) ▸ ht

private theorem aut1_commutes_z2_iff (α : ParkerStandardGroup) :
    Commute (psiAut1N α) z2N ↔ α.val parkerOmega = parkerOmega := by
  constructor
  · intro h
    by_contra ha
    have hh := congrArg (fun g : N => g.val (axis2 loopOne)) h.eq
    have hfix : α.val loopOne = loopOne := α.prop.2.1 0
    have he : loopOne = parkerSign 1 loopOne := by
      change psiAut1 α.val (z2 (axis2 loopOne)) = z2 (psiAut1 α.val (axis2 loopOne)) at hh
      have hh' := congrArg (fun t : Triple => t.2.2) hh
      simpa [psiAut1,ha,axis2,TrialitySpin.diagonal,flip1,hfix] using hh'
    exact parkerSign_one_ne loopOne he.symm
  · intro ha
    apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psiAut1 α.val (z2 (a,b,c)) = z2 (psiAut1 α.val (a,b,c))
    simp [psiAut1,ha,TrialitySpin.diagonal]

theorem nPlus_eq_centralizer_signGroup : NPlus = Subgroup.centralizer (Z : Set N) := by
  rw [Z, Subgroup.centralizer_closure]
  apply le_antisymm
  · have hc (g : N) (hg : ∀ z ∈ signSet, g.val * z = z * g.val) :
        g ∈ Subgroup.centralizer ({z1N,z2N,z3N} : Set N) := by
      rintro z (rfl | rfl | rfl)
      · exact Subtype.ext (hg z1 (by simp [signSet])).symm
      · exact Subtype.ext (hg z2 (by simp [signSet])).symm
      · exact Subtype.ext (hg z3 (by simp [signSet])).symm
    apply (Subgroup.closure_le _).mpr
    rintro g (⟨d,hg | hg | hg⟩ | ⟨α,hα,ha,hg⟩)
    · exact hc g (hg ▸ (loop_centralizes_signs d).1)
    · exact hc g (hg ▸ (loop_centralizes_signs d).2.1)
    · exact hc g (hg ▸ (loop_centralizes_signs d).2.2)
    · apply hc
      rintro z (rfl | rfl | rfl)
      all_goals rw [hg]
      all_goals ext ⟨a,b,c⟩ : 1
      all_goals simp [Equiv.Perm.mul_apply,TrialitySpin.diagonal,
        signZero_optionMap ⟨α,hα⟩]
  · intro g hg
    have hg1 : g ∈ N1 := Subgroup.mem_centralizer_singleton_iff.mpr (hg z1N (by simp)).symm
    obtain ⟨⟨d,e,α⟩,h⟩ := normalForm_surjective ⟨g,hg1⟩
    have hval : (normalForm d e α).val = g := congrArg Subtype.val h
    rw [← hval]
    apply (normalForm_mem_NPlus_iff d e α).mpr
    apply (aut1_commutes_z2_iff α).mp
    have h2 := (hg z2N (by simp)).symm
    rw [← hval] at h2
    have hl1 : Commute (psi1N d) z2N :=
      Subtype.ext ((loop_centralizes_signs d).1 z2 (by simp [signSet]))
    have hl2 : Commute (psi2N e) z2N :=
      Subtype.ext ((loop_centralizes_signs e).2.1 z2 (by simp [signSet]))
    change Commute (psiAut1N α) z2N
    change psiAut1N α * psi2N e * psi1N d * z2N =
      z2N * (psiAut1N α * psi2N e * psi1N d) at h2
    rw [mul_assoc _ (psi1N d), hl1.eq, ← mul_assoc, mul_assoc _ (psi2N e), hl2.eq] at h2
    exact mul_right_cancel (mul_right_cancel (by simpa only [mul_assoc] using h2))

theorem nPlus_normal : NPlus.Normal := by
  let : Z.Normal := signGroup_normal
  rw [nPlus_eq_centralizer_signGroup]
  infer_instance

def sigma (w : Omega) : N := psiAut2N (parkerCocodeStandard (Submodule.Quotient.mk (pointWord w)))

theorem n1_sup_aut2 (α : ParkerStandardGroup) (hα : α.val parkerOmega ≠ parkerOmega) :
    N1 ⊔ Subgroup.zpowers (psiAut2N α) = ⊤ := by
  let c : N := (psiAut1N α)⁻¹ * psiAut2N α
  have hc : c.val = cycle := by
    change (psiAut1 α.val)⁻¹ * psiAut2 α.val = cycle
    apply inv_mul_eq_of_eq_mul
    simp only [psiAut1,psiAut2,if_neg hα]
    rfl
  have hc_mem : c ∈ N1 ⊔ Subgroup.zpowers (psiAut2N α) :=
    (N1 ⊔ Subgroup.zpowers (psiAut2N α)).mul_mem
      ((N1 ⊔ Subgroup.zpowers (psiAut2N α)).inv_mem ((show N1 ≤ N1 ⊔ Subgroup.zpowers (psiAut2N α) from le_sup_left) (psiAut1N_mem_N1 α)))
      ((show Subgroup.zpowers (psiAut2N α) ≤ N1 ⊔ Subgroup.zpowers (psiAut2N α) from le_sup_right) (Subgroup.mem_zpowers (psiAut2N α)))
  apply top_unique
  intro g _
  obtain ⟨h,hh,i,hi⟩ := exists_collectionSubgroup_cycle g
  have he : g = h * c ^ i.val := by
    apply Subtype.ext
    simpa only [Subgroup.coe_mul,Subgroup.coe_pow,hc] using hi
  rw [he]
  exact (N1 ⊔ Subgroup.zpowers (psiAut2N α)).mul_mem
    ((show N1 ≤ N1 ⊔ Subgroup.zpowers (psiAut2N α) from le_sup_left) (collectionSubgroup_le_N1 hh))
    ((N1 ⊔ Subgroup.zpowers (psiAut2N α)).pow_mem hc_mem _)

theorem n1_sup_sigma (w : Omega) : N1 ⊔ Subgroup.zpowers (sigma w) = ⊤ :=
  n1_sup_aut2 _ (pointStandard_odd w)

end Sporadic.Monster.Construction.NMonomial.ZeroAction.CubicInvariance
