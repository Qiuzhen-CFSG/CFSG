module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.OrbitKernels.Actions

/-!
# The kernel on the union of Parker axes

Under the three premises of `OrbitPresentation`, the pointwise kernel of the
`N1` action on the two-point `k1` orbits of `A2 ∪ A3` is exactly `J`, and
`Q1 ⊓ J = K1`.

An element fixing every orbit cannot exchange the axes, so its normal-form
standard automorphism is even. The axis-2 code action is the identity modulo
the all-ones line. Faithfulness of the actual Golay coordinate group on this
quotient makes the induced code action trivial. The two axes then force both
loop parameters onto the all-ones line, where their sandwich actions are
trivial. Keeping the opposite omega signs on axes 2 and 3 leaves precisely
four concrete permutations: the identity, the two generators of `J`, and
`k1`. The axis-1 Golay projection excludes the two generators from `Q1`.

These are conditional orbit calculations. The unconditional presentation and
the real monomial representation remain separate results.

Source: Aschbacher, *Sporadic Groups*, Lemmas 14.4 and 14.6, printed pp. 61–63.
Products of permutations use Lean's left-composition convention.
-/

public section

open Atlas.Fischer Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin

@[simp] private theorem multiply_code (x y : ParkerLoop) :
    (parkerLoopMultiply x y).1 = x.1 + y.1 := rfl

private theorem axis2_ne_axis3 (b c : ParkerLoop) : axis2 b ≠ axis3 c := by
  intro h
  have := congrArg (fun t : Triple => t.2.1) h
  contradiction

private theorem kernel_even (d e : ParkerLoop) (α : ParkerStandardGroup)
    (h : FixesK1Orbits (normalForm d e α).val) : α.val parkerOmega = parkerOmega := by
  by_contra ho
  have hh := h (axis2 loopOne) (Or.inl ⟨_,rfl⟩)
  rw [normalForm_axis2_odd d e α ho, k1_axis2] at hh
  rcases hh with hh | hh <;> exact axis2_ne_axis3 _ _ hh.symm

private theorem kernel_axes (d e : ParkerLoop) (α : ParkerStandardGroup)
    (h : FixesK1Orbits (normalForm d e α).val) :
    (∀ b, α.val (loopSandwich e (parkerLoopMultiply d b)) = b ∨
      α.val (loopSandwich e (parkerLoopMultiply d b)) = parkerLoopMultiply b parkerOmega) ∧
    (∀ b, α.val (parkerLoopMultiply e (parkerLoopMultiply b d)) = b ∨
      α.val (parkerLoopMultiply e (parkerLoopMultiply b d)) =
        parkerLoopMultiply b (parkerSign 1 parkerOmega)) := by
  have heven := kernel_even d e α h
  constructor
  · intro b
    have hh := h (axis2 b) (Or.inl ⟨_,rfl⟩)
    rw [normalForm_axis2_even d e α heven, k1_axis2] at hh
    exact hh.imp (fun h => axis2_injective h) (fun h => axis2_injective h)
  · intro b
    have hh := h (axis3 b) (Or.inr ⟨_,rfl⟩)
    rw [normalForm_axis3_even d e α heven, k1_axis3] at hh
    exact hh.imp (fun h => axis3_injective h) (fun h => axis3_injective h)

private theorem kernel_code (d e : ParkerLoop) (α : ParkerStandardGroup)
    (h : FixesK1Orbits (normalForm d e α).val) :
    parkerStandardProjection α = 1 ∧
      (d.1 = 0 ∨ d.1 = golayOne) ∧ (e.1 = 0 ∨ e.1 = golayOne) := by
  obtain ⟨h2,h3⟩ := kernel_axes d e α h
  let f := parkerCodeEquiv (parkerStandardProjection α)
  have hc (a : golay) : ∃ t : Bit, f (d.1+a) = a+t • golayOne := by
    rcases h2 (a,0) with hb | hb
    · refine ⟨0,?_⟩
      simpa only [parkerStandardProjection_spec, loopSandwich_code, multiply_code, Prod.fst, zero_smul,
        add_zero] using congrArg Prod.fst hb
    · refine ⟨1,?_⟩
      simpa only [parkerStandardProjection_spec, loopSandwich_code, multiply_code, Prod.fst, parkerOmega, one_smul]
        using congrArg Prod.fst hb
  obtain ⟨t,ht⟩ := hc 0
  simp only [add_zero, zero_add] at ht
  have hproj : parkerStandardProjection α = 1 := by
    apply parkerCodeEquiv_faithful_mod_golayOne
    intro a
    obtain ⟨u,hu⟩ := hc a
    refine ⟨u+t,?_⟩
    rw [map_add, ht] at hu
    rw [parkerCodeEquiv_one, add_smul]
    change f a = _
    calc
      f a = (t • golayOne + f a) + t • golayOne := by
        rw [add_comm (t • golayOne), add_assoc, parkerGolay_add_self, add_zero]
      _ = _ := by rw [hu]; abel
  have hd : d.1 = 0 ∨ d.1 = golayOne := by
    rcases h2 loopOne with hb | hb
    · left
      have := congrArg Prod.fst hb
      simpa [parkerStandardProjection_spec, hproj, loopOne, loopSandwich_code, multiply_code, parkerOmega]
        using this
    · right
      have := congrArg Prod.fst hb
      simpa [parkerStandardProjection_spec, hproj, loopOne, loopSandwich_code, multiply_code, parkerOmega,
        parkerLoopMultiply_one_left] using this
  have hed : e.1 + d.1 = 0 ∨ e.1 + d.1 = golayOne := by
    rcases h3 loopOne with hb | hb
    · left
      have := congrArg Prod.fst hb
      simpa [parkerStandardProjection_spec, hproj, loopOne, multiply_code, parkerOmega, parkerSign,
        parkerLoopMultiply_one_left] using this
    · right
      have := congrArg Prod.fst hb
      simpa [parkerStandardProjection_spec, hproj, loopOne, multiply_code, parkerOmega, parkerSign,
        parkerLoopMultiply_one_left] using this
  refine ⟨hproj,hd,?_⟩
  rcases hd with hd | hd
  · simpa [hd] using hed
  · rw [hd] at hed
    rcases hed with he | he
    · right
      calc
        e.1 = (e.1+golayOne)+golayOne := by simp [add_assoc, parkerGolay_add_self]
        _ = golayOne := by rw [he,zero_add]
    · left
      exact add_right_cancel (he.trans (zero_add golayOne).symm)

private theorem central_cases (d : ParkerLoop) (hd : d.1 = 0 ∨ d.1 = golayOne) :
    (∃ t : ParkerBit, d = parkerSign t loopOne) ∨
    (∃ t : ParkerBit, d = parkerSign t parkerOmega) := by
  rcases hd with hd | hd
  · exact Or.inl ⟨d.2, Prod.ext hd (by simp [parkerSign,loopOne])⟩
  · exact Or.inr ⟨d.2, Prod.ext hd (by simp [parkerSign,parkerOmega])⟩

private theorem sandwich_sign_arg (t : ParkerBit) (d b : ParkerLoop) :
    loopSandwich (parkerSign t d) b = loopSandwich d b := by
  simp only [loopSandwich,loopInverse_sign,parkerLoopMultiply_sign_left,
    parkerLoopMultiply_sign_right,parkerSign_add,CharTwo.add_self_eq_zero,parkerSign_zero]

private theorem central_sandwich (d b : ParkerLoop) (hd : d.1 = 0 ∨ d.1 = golayOne) :
    loopSandwich d b = b := by
  rcases central_cases d hd with ⟨t,rfl⟩ | ⟨t,rfl⟩
  · rw [sandwich_sign_arg]
    rw [loopSandwich,loopInverse_one]
    simp only [loopOne,parkerLoopMultiply_one_left,parkerLoopMultiply_one_right]
  · rw [sandwich_sign_arg]
    exact Option.some.inj (omega_sandwich (some b))

private theorem even_fixes_central (α : ParkerStandardGroup)
    (heven : α.val parkerOmega = parkerOmega) (d : ParkerLoop)
    (hd : d.1 = 0 ∨ d.1 = golayOne) : α.val d = d := by
  rcases central_cases d hd with ⟨t,rfl⟩ | ⟨t,rfl⟩
  · rw [parkerStandard_preserves_sign,show α.val loopOne = loopOne from α.prop.2.1 0]
  · rw [parkerStandard_preserves_sign,heven]

private theorem kernel_automorphism (d e : ParkerLoop) (α : ParkerStandardGroup)
    (h : FixesK1Orbits (normalForm d e α).val) :
    α = 1 ∧ (d = loopOne ∨ d = parkerOmega) := by
  obtain ⟨hproj,hd,he⟩ := kernel_code d e α h
  obtain ⟨h2,_⟩ := kernel_axes d e α h
  have heven := kernel_even d e α h
  have hd' : d = loopOne ∨ d = parkerOmega := by
    have hh := h2 loopOne
    simpa only [loopOne,parkerLoopMultiply_one_left,parkerLoopMultiply_one_right,
      central_sandwich e d he,even_fixes_central α heven d hd] using hh
  refine ⟨?_,hd'⟩
  apply Subtype.ext
  apply Equiv.ext
  intro b
  change α.val b = b
  have hcode (x : ParkerLoop) : (α.val x).1 = x.1 := by
    rw [parkerStandardProjection_spec,hproj,parkerCodeEquiv_one]
  have hh := h2 b
  rw [central_sandwich e _ he,α.prop.1,even_fixes_central α heven d hd] at hh
  rcases hd' with rfl | rfl
  · simp only [loopOne,parkerLoopMultiply_one_left] at hh
    rcases hh with hh | hh
    · exact hh
    · have hc := congrArg Prod.fst hh
      rw [hcode,multiply_code] at hc
      exact False.elim (golayOne_ne_zero (add_left_cancel ((add_zero b.1).trans hc).symm))
  · rcases hh with hh | hh
    · have hc := congrArg Prod.fst hh
      rw [multiply_code,hcode] at hc
      exact False.elim (golayOne_ne_zero (add_right_cancel (hc.trans (zero_add b.1).symm)))
    · apply (loopLeft parkerOmega).injective
      exact hh.trans (parkerOmega_commutes b).symm

private abbrev unionJ2 : N := psi2N (parkerSign 1 parkerOmega)
private abbrev unionJ3 : N := psi3N parkerOmega

private theorem unionJ2_apply (a b c : LoopZero) :
    unionJ2.val (a,b,c) =
      (rightZero (parkerSign 1 parkerOmega) a,b,rightZero (parkerSign 1 parkerOmega) c) := by
  change psi2 (parkerSign 1 parkerOmega) (a,b,c) = _
  simp

private theorem unionJ3_apply (a b c : LoopZero) :
    unionJ3.val (a,b,c) = (rightZero parkerOmega a,rightZero parkerOmega b,c) := by
  change psi3 parkerOmega (a,b,c) = _
  simp

private theorem unionJ2_sq : unionJ2 * unionJ2 = 1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change unionJ2.val (unionJ2.val (a,b,c)) = (a,b,c)
  simp only [unionJ2_apply,rightSignOmega_rightSignOmega]

private theorem unionJ3_sq : unionJ3 * unionJ3 = 1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change unionJ3.val (unionJ3.val (a,b,c)) = (a,b,c)
  simp only [unionJ3_apply,rightOmega_rightOmega]

private theorem unionJ_commute : unionJ3 * unionJ2 = k1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change unionJ3.val (unionJ2.val (a,b,c)) = k1.val (a,b,c)
  simp [unionJ2_apply,unionJ3_apply,k1_apply]

private theorem unionJ_four (g : N) :
    g ∈ J ↔ g = 1 ∨ g = unionJ2 ∨ g = unionJ3 ∨ g = k1 := by
  have h23 : unionJ2 * unionJ3 = k1 := rfl
  have h2k : unionJ2*k1 = unionJ3 := by rw [← h23,← mul_assoc,unionJ2_sq,one_mul]
  have h3k : unionJ3*k1 = unionJ2 := by
    rw [← unionJ_commute,← mul_assoc,unionJ3_sq,one_mul]
  have hk2 : k1*unionJ2 = unionJ3 := by
    rw [← unionJ_commute,mul_assoc,unionJ2_sq,mul_one]
  have hk3 : k1*unionJ3 = unionJ2 := by rw [← h23,mul_assoc,unionJ3_sq,mul_one]
  have hkk : k1*k1 = 1 := by simpa only [pow_two] using k1_sq
  have h2 : unionJ2 ∈ J := Subgroup.subset_closure (by simp)
  have h3 : unionJ3 ∈ J := Subgroup.subset_closure (by simp)
  have hk : k1 ∈ J := J.mul_mem h2 h3
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => rcases hx with rfl | rfl <;> simp
    | one => simp
    | mul x y hx hy ihx ihy =>
      rcases ihx with rfl | rfl | rfl | rfl <;>
        rcases ihy with rfl | rfl | rfl | rfl <;>
        simp [unionJ2_sq,unionJ3_sq,h23,unionJ_commute,h2k,h3k,hk2,hk3,hkk]
    | inv x hx ihx =>
      have h2i : unionJ2⁻¹ = unionJ2 := inv_eq_of_mul_eq_one_left unionJ2_sq
      have h3i : unionJ3⁻¹ = unionJ3 := inv_eq_of_mul_eq_one_left unionJ3_sq
      have hki : k1⁻¹ = k1 := inv_eq_of_mul_eq_one_left hkk
      rcases ihx with rfl | rfl | rfl | rfl <;> simp [h2i,h3i,hki]
  · rintro (rfl | rfl | rfl | rfl)
    · exact J.one_mem
    · exact h2
    · exact h3
    · exact hk

private theorem normalForm_trivial_aut (d e : ParkerLoop) :
    (normalForm d e 1).val = psi2N e * psi1N d := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psiAut1 (1 : ParkerStandardGroup).val (psi2 e (psi1 d (a,b,c))) =
    psi2 e (psi1 d (a,b,c))
  simp [psiAut1,diagonal]

private theorem normalForm_central_four :
    (normalForm loopOne loopOne 1).val = 1 ∧
    (normalForm loopOne (parkerSign 1 parkerOmega) 1).val = unionJ2 ∧
    (normalForm parkerOmega parkerOmega 1).val = unionJ3 ∧
    (normalForm parkerOmega loopPi 1).val = k1 := by
  have h1 : psi1N loopOne = 1 := by
    apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psi1 loopOne (a,b,c) = (a,b,c)
    simp
  have h2 : psi2N loopOne = 1 := by
    apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psi2 loopOne (a,b,c) = (a,b,c)
    simp
  simp only [normalForm_trivial_aut,h1,h2,mul_one,true_and]
  constructor
  · apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psi2 parkerOmega (psi1 parkerOmega (a,b,c)) = unionJ3.val (a,b,c)
    simp [unionJ3_apply]
  · apply Subtype.ext
    ext ⟨a,b,c⟩ : 1
    change psi2 loopPi (psi1 parkerOmega (a,b,c)) = k1.val (a,b,c)
    simp [k1_apply]

private theorem kernel_normalForm_mem_J (d e : ParkerLoop) (α : ParkerStandardGroup)
    (h : FixesK1Orbits (normalForm d e α).val) : (normalForm d e α).val ∈ J := by
  obtain ⟨ha,hd⟩ := kernel_automorphism d e α h
  subst α
  have he := (kernel_axes d e 1 h).2 loopOne
  change parkerLoopMultiply e (parkerLoopMultiply loopOne d) = loopOne ∨
    parkerLoopMultiply e (parkerLoopMultiply loopOne d) =
      parkerLoopMultiply loopOne (parkerSign 1 parkerOmega) at he
  simp only [loopOne,parkerLoopMultiply_one_left] at he
  rcases hd with rfl | rfl
  · simp only [loopOne,parkerLoopMultiply_one_right] at he
    rcases he with he | he
    · change e = loopOne at he
      rw [he,normalForm_central_four.1]; exact J.one_mem
    · rw [he,normalForm_central_four.2.1]
      exact Subgroup.subset_closure (by simp)
  · rcases he with he | he
    · have he' : e = parkerOmega := by
        apply (loopRight parkerOmega).injective
        exact he.trans parkerOmega_square.symm
      rw [he',normalForm_central_four.2.2.1]
      exact Subgroup.subset_closure (by simp)
    · have he' : e = loopPi := by
        apply (loopRight parkerOmega).injective
        exact he.trans (loopPi_mul parkerOmega).symm
      rw [he',normalForm_central_four.2.2.2]
      exact K1_le_J (Subgroup.mem_zpowers k1)

/-- The pointwise kernel on the two-point `k1` orbits of axes 2 and 3. -/
theorem fixesK1Orbits_iff_mem_J (H : OrbitPresentation) (g : N) (hg : g ∈ N1) :
    FixesK1Orbits g ↔ g ∈ J := by
  constructor
  · intro h
    obtain ⟨⟨d,e,α⟩,hw⟩ := H.normalForm_bijective.surjective ⟨g,hg⟩
    have hv : (normalForm d e α).val = g := congrArg Subtype.val hw
    subst g
    exact kernel_normalForm_mem_J d e α h
  · intro hgJ
    rcases (unionJ_four g).mp hgJ with rfl | rfl | rfl | rfl
    · intro x _; exact Or.inl rfl
    · rintro x (⟨b,rfl⟩ | ⟨b,rfl⟩)
      · left; simp [unionJ2_apply,axis2]
      · right; simp [unionJ2_apply,k1_apply,axis3]
    · rintro x (⟨b,rfl⟩ | ⟨b,rfl⟩)
      · right; simp [unionJ3_apply,k1_apply,axis2]
      · left; simp [unionJ3_apply,axis3]
    · intro x _; exact Or.inr rfl

private theorem not_Q1_of_axis1_one (H : OrbitPresentation) (g : N) (hg : g ∈ N1)
    (d : ParkerLoop) (hd : g.val (axis1 loopOne) = axis1 d) (hc : d.1 ≠ 0) :
    g ∉ Q1 := by
  intro hQ
  obtain ⟨c,hc',hc0⟩ := (mem_Q1_iff_axis1_code H g hg).mp hQ loopOne
  have he : d = c := axis1_injective (hd.symm.trans hc')
  exact hc ((congrArg Prod.fst he).trans hc0)

/-- Exactly the `k1` subgroup of `Q1` is killed by the union orbit action. -/
theorem Q1_inf_J (H : OrbitPresentation) : Q1 ⊓ J = K1 := by
  have h2 : unionJ2 ∉ Q1 := by
    apply not_Q1_of_axis1_one H unionJ2 (psi2N_mem_N1 _) (parkerSign 1 parkerOmega)
    · change psi2 (parkerSign 1 parkerOmega) (axis1 loopOne) = _
      rw [psi2_axis1]
      exact congrArg axis1 (parkerLoopMultiply_one_left _)
    · exact golayOne_ne_zero
  have h3 : unionJ3 ∉ Q1 := by
    apply not_Q1_of_axis1_one H unionJ3 (psi3N_mem_N1 _) parkerOmega
    · change psi3 parkerOmega (axis1 loopOne) = _
      rw [psi3_axis1]
      exact congrArg axis1 (parkerLoopMultiply_one_right _)
    · exact golayOne_ne_zero
  have hk : k1 ∈ Q1 := by
    apply (mem_Q1_iff_axis1_code H k1
      (J_le_N1 (K1_le_J (Subgroup.mem_zpowers k1)))).mpr
    intro b
    refine ⟨parkerSign 1 b,?_,rfl⟩
    simp [axis1,k1_apply]
  apply le_antisymm
  · intro g hg
    rcases (unionJ_four g).mp hg.2 with rfl | rfl | rfl | rfl
    · exact K1.one_mem
    · exact False.elim (h2 hg.1)
    · exact False.elim (h3 hg.1)
    · exact Subgroup.mem_zpowers k1
  · exact le_inf (Subgroup.zpowers_le.mpr hk) K1_le_J

end Sporadic.Monster.Construction.TrialitySpin
