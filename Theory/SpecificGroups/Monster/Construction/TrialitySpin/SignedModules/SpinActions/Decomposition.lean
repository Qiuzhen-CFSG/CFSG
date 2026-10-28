module
public import Theory.SpecificGroups.Monster.Construction.TrialitySpin.SignedModules.Spin

/-!
# Restriction of the Parker spin space to its two axes

The disjoint union of the actual second and third axes commutes with their
`k1` orbit quotients. Restriction therefore identifies anti-invariant functions
on the union with the product of the two signed spaces. Splitting the finite
sum proves that the normalized bilinear form becomes the sum of the two forms.

Source: Aschbacher, *Sporadic Groups*, pp. 146–147, following Lemma 27.3.
-/

@[expose] public section
open Atlas.Fischer Atlas.Codes
open Sporadic.Monster.Construction.TrialitySpin
open SignedModules
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Sporadic.Monster.Construction.TrialitySpin.SpinActions
variable {X Y : Type*}
def sumPairing (p : Pairing X) (q : Pairing Y) : Pairing (X ⊕ Y) where
  flip := Equiv.sumCongr p.flip q.flip
  involutive := by
    rintro (x | y)
    · exact congrArg Sum.inl (p.involutive x)
    · exact congrArg Sum.inr (q.involutive y)

def sumOrbitEquiv (p : Pairing X) (q : Pairing Y) :
    (sumPairing p q).Orbit ≃ p.Orbit ⊕ q.Orbit where
  toFun := Quotient.lift (Sum.elim (fun x => Sum.inl (p.orbit x))
    (fun y => Sum.inr (q.orbit y))) (by
      intro a b h
      rcases h with rfl | rfl
      · rfl
      · cases b <;> simp [sumPairing])
  invFun := Sum.elim
    (Quotient.map Sum.inl (by
      intro x y h
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl))
    (Quotient.map Sum.inr (by
      intro x y h
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl))
  left_inv := by
    intro a
    induction a using Quotient.inductionOn with
    | h a => cases a <;> rfl
  right_inv := by
    rintro (a | b)
    · induction a using Quotient.inductionOn with | h a => rfl
    · induction b using Quotient.inductionOn with | h b => rfl

def sumSigns (s : SignedSet X) (t : SignedSet Y) : SignedSet (X ⊕ Y) where
  toPairing := sumPairing s.toPairing t.toPairing
  fixedPointFree := by
    rintro (x | y) h
    · exact s.fixedPointFree x (Sum.inl.inj h)
    · exact t.fixedPointFree y (Sum.inr.inj h)

def sumSpaceEquiv (s : SignedSet X) (t : SignedSet Y) :
    (sumSigns s t).Space ≃ₗ[ℝ] s.Space × t.Space where
  toFun v := (⟨fun x => v.val (Sum.inl x), fun x => v.property (Sum.inl x)⟩,
    ⟨fun y => v.val (Sum.inr y), fun y => v.property (Sum.inr y)⟩)
  invFun v := ⟨Sum.elim v.1.val v.2.val, by
    rintro (x | y)
    · exact v.1.property x
    · exact v.2.property y⟩
  left_inv v := by apply Subtype.ext; funext a; cases a <;> rfl
  right_inv v := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem sumSpaceEquiv_isometry (s : SignedSet X) (t : SignedSet Y)
    [Fintype X] [Fintype Y] (v w : (sumSigns s t).Space) :
    s.form (sumSpaceEquiv s t v).1 (sumSpaceEquiv s t w).1 +
      t.form (sumSpaceEquiv s t v).2 (sumSpaceEquiv s t w).2 =
      (sumSigns s t).form v w := by
  change (1 / 2 : ℝ) * (∑ x, v.val (Sum.inl x) * w.val (Sum.inl x)) +
    (1 / 2 : ℝ) * (∑ y, v.val (Sum.inr y) * w.val (Sum.inr y)) =
    (1 / 2 : ℝ) * (∑ a, v.val a * w.val a)
  rw [Fintype.sum_sum_type, mul_add]

def axisUnion : A2 ⊕ A3 ≃ A := (Equiv.Set.union axes_disjoint).symm

theorem axisUnion_pairing (a : A2 ⊕ A3) :
    axisUnion ((sumPairing secondAxisDomain.pairing thirdAxisDomain.pairing).flip a) =
      bothAxesDomain.pairing.flip (axisUnion a) := by
  cases a <;> rfl

def spinOrbitUnion : secondAxisDomain.pairing.Orbit ⊕ thirdAxisDomain.pairing.Orbit ≃
    bothAxesDomain.pairing.Orbit :=
  (sumOrbitEquiv secondAxisDomain.pairing thirdAxisDomain.pairing).symm.trans
    ((sumPairing secondAxisDomain.pairing thirdAxisDomain.pairing).transport
      bothAxesDomain.pairing axisUnion axisUnion_pairing)

theorem spinOrbitUnion_sign (a : secondAxisDomain.pairing.Orbit ⊕
    thirdAxisDomain.pairing.Orbit) :
    spinOrbitUnion ((sumSigns secondAxisDomain.signedOrbits
      thirdAxisDomain.signedOrbits).flip a) =
      bothAxesDomain.signedOrbits.flip (spinOrbitUnion a) := by
  cases a with
  | inl a => induction a using Quotient.inductionOn with | h a => rfl
  | inr a => induction a using Quotient.inductionOn with | h a => rfl

/-- Restriction of a function on the two-axis orbit set to each of its axes. -/
def spinRestriction : SpinSpace ≃ₗ[ℝ] B1A2 × B1A3 :=
  ((sumSigns secondAxisDomain.signedOrbits thirdAxisDomain.signedOrbits).transport
    bothAxesDomain.signedOrbits spinOrbitUnion spinOrbitUnion_sign).symm.trans
    (sumSpaceEquiv secondAxisDomain.signedOrbits thirdAxisDomain.signedOrbits)

@[simp] theorem spinRestriction_second (v : SpinSpace) (b : ParkerLoop) :
    (spinRestriction v).1.val (secondAxisDomain.pairing.orbit (axis2Equiv b)) =
      v.val (bothAxesDomain.pairing.orbit ⟨axis2 b, Or.inl ⟨b, rfl⟩⟩) := rfl

@[simp] theorem spinRestriction_third (v : SpinSpace) (b : ParkerLoop) :
    (spinRestriction v).2.val (thirdAxisDomain.pairing.orbit (axis3Equiv b)) =
      v.val (bothAxesDomain.pairing.orbit ⟨axis3 b, Or.inr ⟨b, rfl⟩⟩) := rfl

theorem spinRestriction_isometry (v w : SpinSpace) :
    secondAxisDomain.form (spinRestriction v).1 (spinRestriction w).1 +
      thirdAxisDomain.form (spinRestriction v).2 (spinRestriction w).2 =
      bothAxesDomain.form v w := by
  let s := sumSigns secondAxisDomain.signedOrbits thirdAxisDomain.signedOrbits
  let e := s.transport bothAxesDomain.signedOrbits spinOrbitUnion spinOrbitUnion_sign
  change secondAxisDomain.signedOrbits.form (sumSpaceEquiv _ _ (e.symm v)).1
      (sumSpaceEquiv _ _ (e.symm w)).1 +
    thirdAxisDomain.signedOrbits.form (sumSpaceEquiv _ _ (e.symm v)).2
      (sumSpaceEquiv _ _ (e.symm w)).2 = _
  rw [sumSpaceEquiv_isometry]
  have h := s.transport_isometry bothAxesDomain.signedOrbits spinOrbitUnion
    spinOrbitUnion_sign (e.symm v) (e.symm w)
  change bothAxesDomain.form (e (e.symm v)) (e (e.symm w)) = _ at h
  simpa only [e.apply_symm_apply] using h.symm
end Sporadic.Monster.Construction.TrialitySpin.SpinActions
