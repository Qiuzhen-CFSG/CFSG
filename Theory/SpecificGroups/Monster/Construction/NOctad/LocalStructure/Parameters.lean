module
public import Theory.SpecificGroups.Monster.Construction.NOctad.LocalStructure.Action

/-!
# Source octad parameters under the three local generators

These are the literal parameters in the right sides of 29.12. Standard
automorphisms transport the code and the even subset by the same coordinate
permutation. The first loop family changes the sign by epsilon_J(d) plus
the half-intersection parity. The second translates J by the intersection
of the two Golay words and adds its prescribed half-intersection sign.

Golay self-orthogonality proves that the translated subset is even.
The binary weight identity proves the half-weight parity identity used
in the source's conjugation calculation. All three transformations commute
with changing the loop sign and complementing the subset. This module
establishes parameter validity and compatibility; the corresponding
conjugation identities are separate obligations.

Source: Aschbacher, *Sporadic Groups*, Lemma 29.12 and its proof,
printed p. 160 (PDF p. 86, left page).
-/

@[expose] public section
noncomputable section
namespace Sporadic.Monster.Construction.NOctad.LocalStructure
open LocalC LocalC.ShortFamilies TrialitySpin
open Atlas.Codes Atlas.Fischer Atlas.Lattices
attribute [local instance] Classical.propDecidable

@[ext] theorem parameters_ext {p q : OctadParameters} (hc : p.c = q.c) (hJ : p.J = q.J) : p = q := by
  cases p
  cases q
  simp_all

/-- The source parameter on the right of 29.12(1); its action formula requires even `α`. -/
def standardParameters (α : ParkerStandardGroup) (p : OctadParameters) : OctadParameters where
  c := α.val p.c
  J := coordinatePermutation (parkerStandardProjection α).val p.J
  octad := by
    rw [parkerStandardProjection_spec]
    exact (coordinatePermutation_weight _ _).trans p.octad
  supported := by
    intro i hi
    rw [parkerStandardProjection_spec]
    exact p.supported ((parkerStandardProjection α).val.symm i) hi
  even := by
    rw [coordinatePermutation_weight]
    exact p.even

/-- The epsilon and half-intersection sign in 29.12(2). -/
def psi1Parameters (d : ParkerLoop) (p : OctadParameters) : OctadParameters :=
  p.sign (binaryDot p.J d.1.val + golayHalfOverlap p.c.1 d.1)

private theorem intersection_weight (a b : BinaryWord) :
    hammingNorm (a * b) = overlap a b := by
  simp only [hammingNorm, overlap, Pi.mul_apply, mul_ne_zero_iff]

/-- The translated subset in 29.12(3) is again even. -/
theorem translatedSubset_even (p : OctadParameters) (e : ParkerLoop) :
    Even (hammingNorm (p.J + p.c.1.val * e.1.val)) := by
  have hw := binary_weight_add p.J (p.c.1.val * e.1.val)
  rw [intersection_weight] at hw
  have hc := golay_overlap_two_dvd p.c.1 e.1
  have hJ := even_iff_two_dvd.mp p.even
  apply even_iff_two_dvd.mpr
  omega

/-- The half-intersection sign and symmetric-difference subset in 29.12(3). -/
def psi2Parameters (e : ParkerLoop) (p : OctadParameters) : OctadParameters where
  c := parkerSign (golayHalfOverlap e.1 p.c.1) p.c
  J := p.J + p.c.1.val * e.1.val
  octad := p.octad
  supported := by
    intro i hi hc
    change p.c.1.val i = 0 at hc
    have hj : p.J i = 0 := by
      by_contra hj
      exact p.supported i hj hc
    exact hi (by simp [hj, hc])
  even := translatedSubset_even p e

/-- The parity calculation stated explicitly in the proof of 29.12(3). -/
theorem translatedSubset_half_weight (p : OctadParameters) (e : ParkerLoop) :
    ((hammingNorm (psi2Parameters e p).J / 2 : ℕ) : ParkerBit) =
      ((hammingNorm p.J / 2 : ℕ) : ParkerBit) + golayHalfOverlap p.c.1 e.1 + binaryDot p.J e.1.val := by
  have ho : overlap p.J (p.c.1.val * e.1.val) = overlap p.J e.1.val := by
    unfold overlap
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.mul_apply, mul_ne_zero_iff]
    exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, p.supported i h.1, h.2⟩⟩
  have hw := binary_weight_add p.J (p.c.1.val * e.1.val)
  rw [intersection_weight, ho] at hw
  have hJ := even_iff_two_dvd.mp p.even
  have hc := golay_overlap_two_dvd p.c.1 e.1
  have hn : hammingNorm (psi2Parameters e p).J / 2 + overlap p.J e.1.val =
      hammingNorm p.J / 2 + overlap p.c.1.val e.1.val / 2 := by
    change hammingNorm (p.J + p.c.1.val * e.1.val) / 2 + _ = _
    omega
  have hh := congrArg (fun n : ℕ => (n : ParkerBit)) hn
  simp only [Nat.cast_add] at hh
  have hz : ∀ x : ParkerBit, x + x = 0 := by decide
  rw [binaryDot_overlap]
  exact by
    simpa only [golayHalfOverlap, add_assoc, hz, add_zero] using
      congrArg (fun x : ParkerBit => x + (overlap p.J e.1.val : ParkerBit)) hh

@[simp] theorem standardParameters_sign (α : ParkerStandardGroup) (p : OctadParameters) (s : ParkerBit) :
    standardParameters α (p.sign s) = (standardParameters α p).sign s := by
  apply parameters_ext
  · exact parkerStandard_preserves_sign α s p.c
  · rfl

@[simp] theorem psi1Parameters_sign (d : ParkerLoop) (p : OctadParameters) (s : ParkerBit) :
    psi1Parameters d (p.sign s) = (psi1Parameters d p).sign s := by
  apply parameters_ext
  · change parkerSign _ (parkerSign s p.c) = parkerSign s (parkerSign _ p.c)
    rw [parkerSign_add, parkerSign_add, add_comm]
    rfl
  · rfl

@[simp] theorem psi2Parameters_sign (e : ParkerLoop) (p : OctadParameters) (s : ParkerBit) :
    psi2Parameters e (p.sign s) = (psi2Parameters e p).sign s := by
  apply parameters_ext
  · change parkerSign _ (parkerSign s p.c) = parkerSign s (parkerSign _ p.c)
    rw [parkerSign_add, parkerSign_add, add_comm]
    rfl
  · rfl

@[simp] theorem standardParameters_complement (α : ParkerStandardGroup) (p : OctadParameters) :
    standardParameters α p.complement = (standardParameters α p).complement := by
  apply parameters_ext
  · rfl
  · change coordinatePermutation _ (p.J + p.c.1.val) = _ + (α.val p.c).1.val
    rw [parkerStandardProjection_spec]
    rfl

@[simp] theorem psi1Parameters_complement (d : ParkerLoop) (p : OctadParameters) :
    psi1Parameters d p.complement = (psi1Parameters d p).complement := by
  apply parameters_ext
  · change parkerSign (binaryDot (p.J + p.c.1.val) d.1.val + _) p.c = _
    rw [map_add, LinearMap.add_apply, golay_selfOrthogonal d.1.prop _ p.c.1.prop, add_zero]
    rfl
  · rfl

@[simp] theorem psi2Parameters_complement (e : ParkerLoop) (p : OctadParameters) :
    psi2Parameters e p.complement = (psi2Parameters e p).complement := by
  apply parameters_ext
  · rfl
  · change (p.J + p.c.1.val) + p.c.1.val * e.1.val =
      (p.J + p.c.1.val * e.1.val) + p.c.1.val
    abel

end Sporadic.Monster.Construction.NOctad.LocalStructure
