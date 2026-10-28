module

public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.BasicSubgroups
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.Structure.CocodeActions

/-!
# Conditional axis actions for Parker triality

Normal-form words act on axis 1 through the affine Golay action
`b ↦ α(b + e)`. On axes 2 and 3, even automorphisms preserve each axis
and odd automorphisms exchange them. Centrality and nuclearity of the
all-ones loop element give commutation with `k1`, and with `k3` on `NPlus`.

`OrbitPresentation` records exactly three independent presentation premises:
normal-form bijectivity and the normal-form tests for `Q1` and `NPlus`.
No axis or orbit-kernel conclusion is assumed. Under these premises we prove
axis preservation, commutation, and the characterization of `Q1` by its action
on the actual Golay projection of axis 1. The three remaining pointwise orbit
kernel predicates and the two proposed axis-2 kernel subgroups are defined
here for independent kernel calculations.

Source: Aschbacher, *Sporadic Groups*, Lemma 14.4 and the proof of Lemma 14.6,
printed pp. 61–63; Lemma 27.3, printed p. 146. All actions are permutations of
Parker triples. In particular the `k1` and `k3` orbit relations on axis 2 use
multiplication by `parkerOmega` and by its negative, respectively.
-/

@[expose] public section

open Atlas.Fischer Atlas.Codes
noncomputable section
namespace Sporadic.Monster.Construction.TrialitySpin

/-- The three presentation premises used by the orbit calculations. -/
structure OrbitPresentation : Prop where
  normalForm_bijective : Function.Bijective
    (fun p : ParkerLoop × ParkerLoop × ParkerStandardGroup => normalForm p.1 p.2.1 p.2.2)
  normalForm_mem_Q1 : ∀ d e α, (normalForm d e α).val ∈ Q1 ↔
    e.1 = 0 ∧ parkerStandardProjection α = 1
  normalForm_mem_NPlus : ∀ d e α, (normalForm d e α).val ∈ NPlus ↔
    α.val parkerOmega = parkerOmega

theorem NPlus_le_N1 : NPlus ≤ N1 := by
  apply (Subgroup.closure_le _).mpr
  rintro g (⟨d, hg | hg | hg⟩ | ⟨e, he, heven, hg⟩)
  · exact (Subtype.ext hg : g = psi1N d) ▸ psi1N_mem_N1 d
  · exact (Subtype.ext hg : g = psi2N d) ▸ psi2N_mem_N1 d
  · exact (Subtype.ext hg : g = psi3N d) ▸ psi3N_mem_N1 d
  · have h : g = psiAut1N ⟨e,he⟩ := by
      apply Subtype.ext
      simpa [psiAut1N, psiAut1, heven] using hg
    rw [h]
    exact psiAut1N_mem_N1 _

@[simp] theorem axis1_injective : Function.Injective axis1 := by
  intro x y h
  exact Option.some.inj (congrArg Prod.fst h)
@[simp] theorem axis2_injective : Function.Injective axis2 := by
  intro x y h
  exact Option.some.inj (congrArg (fun t : Triple => t.2.1) h)
@[simp] theorem axis3_injective : Function.Injective axis3 := by
  intro x y h
  exact Option.some.inj (congrArg (fun t : Triple => t.2.2) h)

def loopSandwich (d b : ParkerLoop) : ParkerLoop :=
  parkerLoopMultiply (parkerLoopMultiply (loopInverse d) b) (loopInverse d)

@[simp] theorem loopSandwich_code (d b : ParkerLoop) : (loopSandwich d b).1 = b.1 := by
  change (d.1 + b.1) + d.1 = b.1
  rw [add_comm d.1 b.1, add_assoc, parkerGolay_add_self, add_zero]

theorem loopSandwich_sign (d b : ParkerLoop) :
    loopSandwich d b = parkerSign (golayHalfOverlap d.1 b.1 + golayQuarterWeight d.1) b := by
  unfold loopSandwich
  rw [parkerLoopMultiply_commutator (loopInverse d) b, parkerLoopMultiply_sign_left]
  have h : parkerLoopMultiply (parkerLoopMultiply b (loopInverse d)) (loopInverse d) =
      parkerSign (golayQuarterWeight d.1) b := by
    conv_lhs => arg 2; rw [loopInverse]
    rw [parkerLoopMultiply_sign_right]
    congr 1
    simpa only [loopInverse_inverse] using loopInverse_mul_right (loopInverse d) b
  rw [h, parkerSign_add]
  rfl

@[simp] theorem psi1_axis1 (d b : ParkerLoop) :
    psi1 d (axis1 b) = axis1 (loopSandwich d b) := rfl
@[simp] theorem psi2_axis2 (d b : ParkerLoop) :
    psi2 d (axis2 b) = axis2 (loopSandwich d b) := rfl
@[simp] theorem psi2_axis3 (d b : ParkerLoop) :
    psi2 d (axis3 b) = axis3 (parkerLoopMultiply d b) := rfl
@[simp] theorem psi3_axis2 (d b : ParkerLoop) :
    psi3 d (axis2 b) = axis2 (parkerLoopMultiply b d) := rfl
@[simp] theorem psi3_axis3 (d b : ParkerLoop) :
    psi3 d (axis3 b) = axis3 (loopSandwich d b) := rfl

theorem psiAut1_axis1 (α : ParkerStandardGroup) (b : ParkerLoop) :
    psiAut1 α.val (axis1 b) = axis1 (α.val
      (if α.val parkerOmega = parkerOmega then b else loopInverse b)) := by
  by_cases h : α.val parkerOmega = parkerOmega <;>
    simp [psiAut1, h, axis1, diagonal, flip1]

theorem psiAut1_axis2_even (α : ParkerStandardGroup)
    (h : α.val parkerOmega = parkerOmega) (b : ParkerLoop) :
    psiAut1 α.val (axis2 b) = axis2 (α.val b) := by
  simp [psiAut1, h, axis2, diagonal]
theorem psiAut1_axis3_even (α : ParkerStandardGroup)
    (h : α.val parkerOmega = parkerOmega) (b : ParkerLoop) :
    psiAut1 α.val (axis3 b) = axis3 (α.val b) := by
  simp [psiAut1, h, axis3, diagonal]
theorem psiAut1_axis2_odd (α : ParkerStandardGroup)
    (h : α.val parkerOmega ≠ parkerOmega) (b : ParkerLoop) :
    psiAut1 α.val (axis2 b) = axis3 (α.val (loopInverse b)) := by
  simp [psiAut1, h, axis2, axis3, diagonal, flip1]
theorem psiAut1_axis3_odd (α : ParkerStandardGroup)
    (h : α.val parkerOmega ≠ parkerOmega) (b : ParkerLoop) :
    psiAut1 α.val (axis3 b) = axis2 (α.val (loopInverse b)) := by
  simp [psiAut1, h, axis2, axis3, diagonal, flip1]

theorem normalForm_apply (d e : ParkerLoop) (α : ParkerStandardGroup) (x : Triple) :
    (normalForm d e α).val.val x = psiAut1 α.val (psi2 e (psi1 d x)) := rfl

theorem normalForm_axis1 (d e : ParkerLoop) (α : ParkerStandardGroup) (b : ParkerLoop) :
    (normalForm d e α).val.val (axis1 b) = axis1 (α.val
      (if α.val parkerOmega = parkerOmega then parkerLoopMultiply (loopSandwich d b) e
        else loopInverse (parkerLoopMultiply (loopSandwich d b) e))) := by
  rw [normalForm_apply, psi1_axis1, psi2_axis1, psiAut1_axis1]

theorem normalForm_axis2_even (d e : ParkerLoop) (α : ParkerStandardGroup)
    (h : α.val parkerOmega = parkerOmega) (b : ParkerLoop) :
    (normalForm d e α).val.val (axis2 b) =
      axis2 (α.val (loopSandwich e (parkerLoopMultiply d b))) := by
  rw [normalForm_apply, psi1_axis2, psi2_axis2, psiAut1_axis2_even α h]
theorem normalForm_axis3_even (d e : ParkerLoop) (α : ParkerStandardGroup)
    (h : α.val parkerOmega = parkerOmega) (b : ParkerLoop) :
    (normalForm d e α).val.val (axis3 b) =
      axis3 (α.val (parkerLoopMultiply e (parkerLoopMultiply b d))) := by
  rw [normalForm_apply, psi1_axis3, psi2_axis3, psiAut1_axis3_even α h]
theorem normalForm_axis2_odd (d e : ParkerLoop) (α : ParkerStandardGroup)
    (h : α.val parkerOmega ≠ parkerOmega) (b : ParkerLoop) :
    (normalForm d e α).val.val (axis2 b) =
      axis3 (α.val (loopInverse (loopSandwich e (parkerLoopMultiply d b)))) := by
  rw [normalForm_apply, psi1_axis2, psi2_axis2, psiAut1_axis2_odd α h]
theorem normalForm_axis3_odd (d e : ParkerLoop) (α : ParkerStandardGroup)
    (h : α.val parkerOmega ≠ parkerOmega) (b : ParkerLoop) :
    (normalForm d e α).val.val (axis3 b) =
      axis2 (α.val (loopInverse (parkerLoopMultiply e (parkerLoopMultiply b d)))) := by
  rw [normalForm_apply, psi1_axis3, psi2_axis3, psiAut1_axis3_odd α h]

theorem N1_preserves_A (H : OrbitPresentation) (g : N) (hg : g ∈ N1) :
    Set.MapsTo g.val A A := by
  obtain ⟨⟨d,e,α⟩, hw⟩ := H.normalForm_bijective.surjective ⟨g,hg⟩
  have hval : (normalForm d e α).val = g := congrArg Subtype.val hw
  subst g
  rintro x (⟨b,rfl⟩ | ⟨b,rfl⟩)
  · by_cases h : α.val parkerOmega = parkerOmega
    · rw [normalForm_axis2_even d e α h]; exact Or.inl ⟨_,rfl⟩
    · rw [normalForm_axis2_odd d e α h]; exact Or.inr ⟨_,rfl⟩
  · by_cases h : α.val parkerOmega = parkerOmega
    · rw [normalForm_axis3_even d e α h]; exact Or.inr ⟨_,rfl⟩
    · rw [normalForm_axis3_odd d e α h]; exact Or.inl ⟨_,rfl⟩

theorem NPlus_preserves_axes (H : OrbitPresentation) (g : N) (hg : g ∈ NPlus) :
    Set.MapsTo g.val A2 A2 ∧ Set.MapsTo g.val A3 A3 := by
  obtain ⟨⟨d,e,α⟩, hw⟩ := H.normalForm_bijective.surjective ⟨g,NPlus_le_N1 hg⟩
  have hval : (normalForm d e α).val = g := congrArg Subtype.val hw
  have heven := (H.normalForm_mem_NPlus d e α).mp (hval.symm ▸ hg)
  subst g
  constructor
  · rintro _ ⟨b,rfl⟩; rw [normalForm_axis2_even d e α heven]; exact ⟨_,rfl⟩
  · rintro _ ⟨b,rfl⟩; rw [normalForm_axis3_even d e α heven]; exact ⟨_,rfl⟩

theorem normalForm_axis1_code (d e : ParkerLoop) (α : ParkerStandardGroup) (b : ParkerLoop) :
    ∃ c : ParkerLoop, (normalForm d e α).val.val (axis1 b) = axis1 c ∧
      c.1 = parkerCodeEquiv (parkerStandardProjection α) (b.1 + e.1) := by
  rw [normalForm_axis1]
  refine ⟨_,rfl,?_⟩
  rw [parkerStandardProjection_spec]
  congr 1
  split_ifs <;> change (loopSandwich d b).1 + e.1 = b.1 + e.1 <;>
    rw [loopSandwich_code]

theorem mem_Q1_iff_axis1_code (H : OrbitPresentation) (g : N) (hg : g ∈ N1) :
    g ∈ Q1 ↔ ∀ b : ParkerLoop, ∃ c : ParkerLoop,
      g.val (axis1 b) = axis1 c ∧ c.1 = b.1 := by
  obtain ⟨⟨d,e,α⟩, hw⟩ := H.normalForm_bijective.surjective ⟨g,hg⟩
  have hval : (normalForm d e α).val = g := congrArg Subtype.val hw
  subst g
  rw [H.normalForm_mem_Q1]
  constructor
  · rintro ⟨he,hα⟩ b
    obtain ⟨c,hc,hcode⟩ := normalForm_axis1_code d e α b
    exact ⟨c,hc,by simpa [he,hα] using hcode⟩
  · intro h
    have hcode (b : ParkerLoop) :
        parkerCodeEquiv (parkerStandardProjection α) (b.1 + e.1) = b.1 := by
      obtain ⟨c,hc,hc'⟩ := normalForm_axis1_code d e α b
      obtain ⟨c',hc2,hc2'⟩ := h b
      have hcc := axis1_injective (hc.symm.trans hc2)
      exact hc'.symm.trans (hcc ▸ hc2')
    have he : e.1 = 0 := by
      apply (parkerCodeEquiv (parkerStandardProjection α)).injective
      simpa [loopOne] using hcode loopOne
    refine ⟨he,parkerCodeEquiv_faithful _ 1 ?_⟩
    intro a
    simpa [he] using hcode (a,0)

@[simp] theorem rightOmega_leftZero (d : ParkerLoop) (a : LoopZero) :
    rightZero parkerOmega (leftZero d a) = leftZero d (rightZero parkerOmega a) := by
  cases a with
  | none => rfl
  | some a => exact congrArg some (parkerOmega_associates_right d a)

@[simp] theorem rightOmega_rightZero (d : ParkerLoop) (a : LoopZero) :
    rightZero parkerOmega (rightZero d a) = rightZero d (rightZero parkerOmega a) := by
  cases a with
  | none => rfl
  | some a =>
    apply congrArg some
    change parkerLoopMultiply (parkerLoopMultiply a d) parkerOmega =
      parkerLoopMultiply (parkerLoopMultiply a parkerOmega) d
    rw [parkerOmega_associates_right, parkerOmega_associates_middle,
      parkerOmega_commutes d]

@[simp] theorem loopInverse_mul_omega (b : ParkerLoop) :
    loopInverse (parkerLoopMultiply b parkerOmega) =
      parkerLoopMultiply (loopInverse b) parkerOmega := by
  apply (loopRight (parkerLoopMultiply b parkerOmega)).injective
  change parkerLoopMultiply (loopInverse (parkerLoopMultiply b parkerOmega))
      (parkerLoopMultiply b parkerOmega) =
    parkerLoopMultiply (parkerLoopMultiply (loopInverse b) parkerOmega)
      (parkerLoopMultiply b parkerOmega)
  rw [loopInverse_mul, ← parkerOmega_associates_right,
    parkerOmega_associates_middle, parkerOmega_commutes b,
    ← parkerOmega_associates_right, loopInverse_mul]
  change (0,0) = parkerLoopMultiply (parkerLoopMultiply (0,0) parkerOmega) parkerOmega
  rw [parkerLoopMultiply_one_left, parkerOmega_square]

@[simp] theorem inverseZero_rightOmega (a : LoopZero) :
    inverseZero (rightZero parkerOmega a) = rightZero parkerOmega (inverseZero a) := by
  cases a with
  | none => rfl
  | some a => simp

@[simp] theorem optionMap_rightZero (α : ParkerStandardGroup) (d : ParkerLoop) (a : LoopZero) :
    (rightZero d a).map α.val = rightZero (α.val d) (a.map α.val) := by
  cases a with
  | none => rfl
  | some a => exact congrArg some (α.prop.1 a d)

theorem parkerStandard_omega_odd (α : ParkerStandardGroup)
    (h : α.val parkerOmega ≠ parkerOmega) :
    α.val parkerOmega = parkerSign 1 parkerOmega := by
  have hb : ∀ t : ParkerBit, t = 0 ∨ t = 1 := by decide
  rcases hb (α.val parkerOmega).2 with he | he
  · exact False.elim (h (by rw [parkerStandard_omega, he, parkerSign_zero]))
  · rw [parkerStandard_omega, he]

theorem psi1N_commutes_k1 (d : ParkerLoop) : Commute (psi1N d) k1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psi1 d (k1.val (a,b,c)) = k1.val (psi1 d (a,b,c))
  simp [k1_apply]

theorem psi2N_commutes_k1 (d : ParkerLoop) : Commute (psi2N d) k1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psi2 d (k1.val (a,b,c)) = k1.val (psi2 d (a,b,c))
  simp [k1_apply]

theorem psiAut1N_commutes_k1 (α : ParkerStandardGroup) : Commute (psiAut1N α) k1 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psiAut1 α.val (k1.val (a,b,c)) = k1.val (psiAut1 α.val (a,b,c))
  by_cases h : α.val parkerOmega = parkerOmega
  · simp [psiAut1, h, diagonal, k1_apply]
  · have ho := parkerStandard_omega_odd α h
    simp only [psiAut1, if_neg h]
    simp [diagonal, flip1, k1_apply, ho,
      ← signZero_inverseZero, ← signZero_optionMap]

theorem N1_commutes_k1 (H : OrbitPresentation) (g : N) (hg : g ∈ N1) :
    Commute g k1 := by
  obtain ⟨⟨d,e,α⟩, hw⟩ := H.normalForm_bijective.surjective ⟨g,hg⟩
  have hval : (normalForm d e α).val = g := congrArg Subtype.val hw
  rw [← hval]
  exact ((psiAut1N_commutes_k1 α).mul_left (psi2N_commutes_k1 e)).mul_left
    (psi1N_commutes_k1 d)

/-- Fixing each individual two-point `k1` orbit of the union of axes. -/
def FixesK1Orbits (g : N) : Prop :=
  ∀ x ∈ A, g.val x = x ∨ g.val x = k1.val x

/-- Fixing each individual `k1` orbit of axis 2. -/
def FixesAxis2K1Orbits (g : N) : Prop :=
  ∀ b : ParkerLoop, g.val (axis2 b) = axis2 b ∨
    g.val (axis2 b) = k1.val (axis2 b)

/-- Fixing each individual `k3` orbit of axis 2, with the opposite omega sign. -/
def FixesAxis2K3Orbits (g : N) : Prop :=
  ∀ b : ParkerLoop, g.val (axis2 b) = axis2 b ∨
    g.val (axis2 b) = k3.val (axis2 b)

/-- The proposed kernel in Aschbacher 27.3(5); its equality with the pointwise
orbit kernel is a theorem obligation. -/
def axis2K1Kernel : Subgroup N :=
  Subgroup.closure {psi1N parkerOmega, psi2N loopPi, psi2N parkerOmega}

/-- The proposed kernel in Aschbacher 27.3(6), using the other orbit relation. -/
def axis2K3Kernel : Subgroup N :=
  Subgroup.closure {psi1N (parkerSign 1 parkerOmega), psi2N loopPi, psi2N parkerOmega}

theorem k3_axis2 (b : ParkerLoop) :
    k3.val (axis2 b) = axis2 (parkerLoopMultiply b (parkerSign 1 parkerOmega)) := by
  simp [axis2,k3_apply]

theorem N1_mem_A_iff (H : OrbitPresentation) (g : N) (hg : g ∈ N1) (x : Triple) :
    g.val x ∈ A ↔ x ∈ A := by
  constructor
  · intro hx
    have h := N1_preserves_A H g⁻¹ (N1.inv_mem hg) hx
    simpa using h
  · exact fun hx => N1_preserves_A H g hg hx

theorem NPlus_mem_axes_iff (H : OrbitPresentation) (g : N) (hg : g ∈ NPlus)
    (x : Triple) : (g.val x ∈ A2 ↔ x ∈ A2) ∧ (g.val x ∈ A3 ↔ x ∈ A3) := by
  have hp := NPlus_preserves_axes H g hg
  have hi := NPlus_preserves_axes H g⁻¹ (NPlus.inv_mem hg)
  constructor
  · exact ⟨fun hx => by simpa using hi.1 hx, fun hx => hp.1 hx⟩
  · exact ⟨fun hx => by simpa using hi.2 hx, fun hx => hp.2 hx⟩

theorem psi1N_commutes_k3 (d : ParkerLoop) : Commute (psi1N d) k3 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psi1 d (k3.val (a,b,c)) = k3.val (psi1 d (a,b,c))
  simp [k3_apply]

theorem psi2N_commutes_k3 (d : ParkerLoop) : Commute (psi2N d) k3 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psi2 d (k3.val (a,b,c)) = k3.val (psi2 d (a,b,c))
  simp [k3_apply]

theorem psiAut1N_commutes_k3_even (α : ParkerStandardGroup)
    (h : α.val parkerOmega = parkerOmega) : Commute (psiAut1N α) k3 := by
  apply Subtype.ext
  ext ⟨a,b,c⟩ : 1
  change psiAut1 α.val (k3.val (a,b,c)) = k3.val (psiAut1 α.val (a,b,c))
  simp [psiAut1, h, diagonal, k3_apply]

theorem NPlus_commutes_k3 (H : OrbitPresentation) (g : N) (hg : g ∈ NPlus) :
    Commute g k3 := by
  obtain ⟨⟨d,e,α⟩, hw⟩ := H.normalForm_bijective.surjective ⟨g,NPlus_le_N1 hg⟩
  have hval : (normalForm d e α).val = g := congrArg Subtype.val hw
  have heven := (H.normalForm_mem_NPlus d e α).mp (hval.symm ▸ hg)
  rw [← hval]
  exact ((psiAut1N_commutes_k3_even α heven).mul_left (psi2N_commutes_k3 e)).mul_left
    (psi1N_commutes_k3 d)

end Sporadic.Monster.Construction.TrialitySpin
