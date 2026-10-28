module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.OrbitKernels.Actions
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.OrbitKernels.Axis2Kernels.Coordinates

/-!
# The two axis-2 orbit kernels

For the actual Parker-triple permutations in `NPlus`, the pointwise kernels
on the `k1` and `k3` orbits of axis 2 are the two specified three-generator
subgroups. The coordinate calculation restricts a normal-form word to these
generators; the converse follows because each generator fixes every orbit.

The common proof retains an explicit sign parameter: `k1` translates the
loop coordinate by Ω, whereas `k3` translates it by −Ω. The only presentation
premises are those already recorded in `OrbitPresentation`; no representation
or additional kernel premise is used.

Source: Aschbacher, *Sporadic Groups*, Lemma 27.3(5–6), printed p. 146.
-/

@[expose] public section

open Atlas.Fischer Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin

private theorem omega_translate_twice (s : ParkerBit) (b : ParkerLoop) :
    parkerLoopMultiply (parkerLoopMultiply b (parkerSign s parkerOmega))
      (parkerSign s parkerOmega) = b := by
  simp only [parkerLoopMultiply_sign_right, parkerLoopMultiply_sign_left,
    parkerSign_add, CharTwo.add_self_eq_zero, parkerSign_zero]
  exact Option.some.inj (rightOmega_rightOmega (some b))

/-- Permutations fixing each two-point orbit form a subgroup. -/
private def signedAxis2Fixer (s : ParkerBit) : Subgroup N where
  carrier := {g | ∀ b : ParkerLoop, g.val (axis2 b) = axis2 b ∨
    g.val (axis2 b) = axis2 (parkerLoopMultiply b (parkerSign s parkerOmega))}
  one_mem' := fun _ => Or.inl rfl
  mul_mem' := by
    intro g h hg hh b
    change g.val (h.val (axis2 b)) = axis2 b ∨
      g.val (h.val (axis2 b)) = axis2 (parkerLoopMultiply b (parkerSign s parkerOmega))
    rcases hh b with hb | hb
    · rw [hb]; exact hg b
    · rw [hb]
      rcases hg (parkerLoopMultiply b (parkerSign s parkerOmega)) with hg' | hg'
      · exact Or.inr hg'
      · exact Or.inl (by simpa only [omega_translate_twice] using hg')
  inv_mem' := by
    intro g hg b
    change g.val.symm (axis2 b) = axis2 b ∨ _
    rcases hg b with hb | hb
    · left
      exact g.val.symm_apply_eq.mpr hb.symm
    · right
      apply g.val.symm_apply_eq.mpr
      symm
      rcases hg (parkerLoopMultiply b (parkerSign s parkerOmega)) with he | he
      · exact he.trans (g.val.injective (hb.trans he.symm)).symm
      · simpa only [omega_translate_twice] using he

private def signedAxis2Kernel (s : ParkerBit) : Subgroup N :=
  Subgroup.closure {psi1N (parkerSign s parkerOmega), psi2N loopPi, psi2N parkerOmega}

private theorem signedAxis2Kernel_le_fixer (s : ParkerBit) :
    signedAxis2Kernel s ≤ signedAxis2Fixer s := by
  apply (Subgroup.closure_le _).mpr
  rintro g (rfl | rfl | rfl) b
  · right
    change psi1 (parkerSign s parkerOmega) (axis2 b) = _
    rw [psi1_axis2, parkerLoopMultiply_sign_left,
      parkerLoopMultiply_sign_right, parkerOmega_commutes]
  · left
    change z2 (axis2 b) = axis2 b
    simp [axis2]
  · left
    change psi2 parkerOmega (axis2 b) = axis2 b
    rw [psi2_axis2]
    apply congrArg axis2
    unfold loopSandwich
    rw [loopInverse_omega]
    exact Option.some.inj (omega_sandwich (some b))

private theorem psi1N_one_axis2 : psi1N loopOne = 1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psi1 loopOne (a,b,c) = (a,b,c)
  simp

private theorem psi2N_one_axis2 : psi2N loopOne = 1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psi2 loopOne (a,b,c) = (a,b,c)
  simp

private theorem psiAut1N_one_axis2 : psiAut1N 1 = 1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  simp [psiAut1N, psiAut1, diagonal]

private theorem psi2N_signOmega_axis2 :
    psi2N (parkerSign 1 parkerOmega) = psi2N loopPi * psi2N parkerOmega := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psi2 (parkerSign 1 parkerOmega) (a,b,c) = z2 (psi2 parkerOmega (a,b,c))
  simp [rightSignOmega_eq]

private theorem psi2N_radical_mem (s : ParkerBit) (e : ParkerLoop)
    (he : e.1 = 0 ∨ e.1 = golayOne) : psi2N e ∈ signedAxis2Kernel s := by
  have hbit : ∀ t : ParkerBit, t = 0 ∨ t = 1 := by decide
  rcases e with ⟨a,t⟩
  rcases he with ha | ha <;> dsimp only at ha <;> subst a
  · rcases hbit t with rfl | rfl
    · exact psi2N_one_axis2 ▸ (signedAxis2Kernel s).one_mem
    · apply Subgroup.subset_closure; exact Or.inr (Or.inl rfl)
  · rcases hbit t with rfl | rfl
    · apply Subgroup.subset_closure; exact Or.inr (Or.inr rfl)
    · change psi2N (parkerSign 1 parkerOmega) ∈ _
      rw [psi2N_signOmega_axis2]
      exact (signedAxis2Kernel s).mul_mem
        (Subgroup.subset_closure (Or.inr (Or.inl rfl)))
        (Subgroup.subset_closure (Or.inr (Or.inr rfl)))

private theorem signedAxis2Fixer_iff (H : OrbitPresentation) (s : ParkerBit)
    (g : N) (hg : g ∈ NPlus) : g ∈ signedAxis2Fixer s ↔ g ∈ signedAxis2Kernel s := by
  constructor
  · intro h
    obtain ⟨⟨d,e,α⟩, hw⟩ := H.normalForm_bijective.surjective ⟨g,NPlus_le_N1 hg⟩
    have hval : (normalForm d e α).val = g := congrArg Subtype.val hw
    have heven := (H.normalForm_mem_NPlus d e α).mp (hval.symm ▸ hg)
    have hc : ∀ b : ParkerLoop,
        α.val (loopSandwich e (parkerLoopMultiply d b)) = b ∨
        α.val (loopSandwich e (parkerLoopMultiply d b)) =
          parkerLoopMultiply b (parkerSign s parkerOmega) := by
      intro b
      have hb := h b
      rw [← hval, normalForm_axis2_even d e α heven] at hb
      exact hb.imp (fun he => axis2_injective he) (fun he => axis2_injective he)
    obtain ⟨hd,he,rfl⟩ := axis2_normalForm_coordinates s d e α heven hc
    rw [← hval]
    change psiAut1N 1 * psi2N e * psi1N d ∈ signedAxis2Kernel s
    rw [psiAut1N_one_axis2, one_mul]
    apply (signedAxis2Kernel s).mul_mem (psi2N_radical_mem s e he)
    rcases hd with rfl | rfl
    · rw [psi1N_one_axis2]; exact (signedAxis2Kernel s).one_mem
    · exact Subgroup.subset_closure (Or.inl rfl)
  · exact fun h => signedAxis2Kernel_le_fixer s h

/-- Aschbacher 27.3(5): the kernel on the `k1` orbits of axis 2. -/
theorem fixesAxis2K1Orbits_iff_mem_axis2K1Kernel (H : OrbitPresentation)
    (g : N) (hg : g ∈ NPlus) : FixesAxis2K1Orbits g ↔ g ∈ axis2K1Kernel := by
  have h := signedAxis2Fixer_iff H 0 g hg
  change (∀ b : ParkerLoop, g.val (axis2 b) = axis2 b ∨
    g.val (axis2 b) = axis2 (parkerLoopMultiply b (parkerSign 0 parkerOmega))) ↔
      g ∈ signedAxis2Kernel 0 at h
  simpa only [signedAxis2Kernel, parkerSign_zero, axis2K1Kernel,
    FixesAxis2K1Orbits, k1_axis2] using h

/-- Aschbacher 27.3(6): the kernel on the distinct `k3` orbits of axis 2. -/
theorem fixesAxis2K3Orbits_iff_mem_axis2K3Kernel (H : OrbitPresentation)
    (g : N) (hg : g ∈ NPlus) : FixesAxis2K3Orbits g ↔ g ∈ axis2K3Kernel := by
  have h := signedAxis2Fixer_iff H 1 g hg
  change (∀ b : ParkerLoop, g.val (axis2 b) = axis2 b ∨
    g.val (axis2 b) = axis2 (parkerLoopMultiply b (parkerSign 1 parkerOmega))) ↔
      g ∈ signedAxis2Kernel 1 at h
  simpa only [signedAxis2Kernel, axis2K3Kernel, FixesAxis2K3Orbits, k3_axis2] using h

end Sporadic.Monster.Construction.TrialitySpin
