module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Image.Containment.Generation
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddSixComparison.Image.Root

/-!
# Commutator containment for the odd unitary exterior action

The signed plane Levi and all first-direction root lifts act through the
commutator of the original full minus-six orthogonal group. The proof uses
their established membership in the derived subgroup of the actual SU₄.

Signed unitary elimination proves that the concrete Levi and plane radical
normally generate SU₄. Their commutator membership therefore proves
perfectness and puts the entire exterior image in the orthogonal commutator,
including at fixed-field order three. This module is an input to `Image`,
so it does not import the projective image assembly.

Source: GLS3 §2.7; Aschbacher–Smith A.2.17, printed pp.38–39.
-/

public noncomputable section
namespace ClassicalOrthogonal.Minus.OddSixComparison
open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary

variable {p n : ℕ} [Fact p.Prime] [NeZero n]
variable {F : Type} [Field F] [Finite F]
variable (R : ExteriorRealization F (Extension p n) (unitaryForm p n))
variable (C : SignedCoordinates R)

/-- Membership in the actual SU commutator transports through the original
exterior action into the original full orthogonal commutator. -/
theorem ExteriorRealization.action_mem_commutator_of_mem
    (g : (unitaryForm p n).specialSubgroup)
    (hg : g ∈ commutator (unitaryForm p n).specialSubgroup) :
    R.action g ∈ commutator (FullOrthogonal F) := by
  have hm := map_derivedSeries_le_derivedSeries R.action 1
  rw [derivedSeries_one, derivedSeries_one] at hm
  exact hm ⟨g, hg, rfl⟩

/-- Literal application of extension-field Levi perfectness. -/
theorem ExteriorRealization.levi_action_mem_commutator (hp : p ≠ 2)
    (A : SpecialLinearGroup (Fin 2) (Extension p n)) :
    R.action (Image.Containment.levi (Extension p n) (conjugation p n)
      (conjugation_involutive p n) A) ∈ commutator (FullOrthogonal F) :=
  R.action_mem_commutator_of_mem _ (Image.Containment.levi_mem_commutator hp A)

/-- The published first-direction lift is exactly one of the derived signed
plane-radical elements; this retains its literal matrix and coordinate signs. -/
theorem Image.rootLift_mem_commutator (hp : p ≠ 2) (v : Space F 2) :
    Image.rootLift R C v ∈ commutator (unitaryForm p n).specialSubgroup := by
  let t : Extension p n := 2 * C.root + 1
  let b := t * R.coefficient (v.1 1).1
  let c := t⁻¹ * R.coefficient (v.1 1).2
  have hb : conjugation p n b = -b := by
    change (unitaryForm p n).conj (t * R.coefficient (v.1 1).1) = -b
    rw [map_mul, Image.conjugation_skew, C.coefficient_fixed]
    exact neg_mul _ _
  have hc : conjugation p n c = -c := by
    change (unitaryForm p n).conj (t⁻¹ * R.coefficient (v.1 1).2) = -c
    rw [map_mul, map_inv₀, Image.conjugation_skew, C.coefficient_fixed]
    rw [inv_neg, neg_mul]
  have he : Image.rootLift R C v = Image.Containment.upper (Extension p n)
      (conjugation p n) (conjugation_involutive p n)
      (-Image.normCoordinate R C v) b c hb hc := by
    apply Subtype.ext
    apply Units.ext
    change Image.rootMatrix R C v = Image.Containment.upperMatrix _ _ _ _ _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Image.rootMatrix, Image.Containment.upperMatrix, b, c, t]
    rfl
  rw [he]
  exact Image.Containment.upper_mem_commutator hp _ _ _ hb hc

/-- Every published signed first-direction exterior lift is in the full
orthogonal commutator, including at q = 3. -/
theorem ExteriorRealization.rootLift_action_mem_commutator (hp : p ≠ 2)
    (v : Space F 2) :
    R.action (Image.rootLift R C v) ∈ commutator (FullOrthogonal F) :=
  R.action_mem_commutator_of_mem _ (Image.rootLift_mem_commutator R C hp v)

include R C in
/-- The same containment with precisely the literal Siegel element consumed by
projective image assembly. -/
theorem ExteriorRealization.direction_siegel_mem_commutator (hp : p ≠ 2)
    (v : Space F 2)
    (hv : (quadraticForm F 3).polarBilin (Image.direction F) v = 0) :
    siegelElement (quadraticForm F 3) (Image.direction F) v
      (Image.direction_singular F) hv ∈ commutator (FullOrthogonal F) := by
  rw [← Image.rootLift_action R C v hv]
  exact R.rootLift_action_mem_commutator C hp v

/-- Conditional containment from normal generation of the two concrete unitary
matrix families defined in `Containment.Generators`. -/
theorem ExteriorRealization.action_mem_commutator_of_normal_generation
    (hp : p ≠ 2) (hgen : Image.Containment.elementaryNormal p n = ⊤)
    (g : (unitaryForm p n).specialSubgroup) :
    R.action g ∈ commutator (FullOrthogonal F) := by
  let := Image.Containment.su_isPerfect_of_normal_generation p n hp hgen
  apply R.action_mem_commutator_of_mem
  rw [Group.IsPerfect.commutator_eq_top]
  exact Subgroup.mem_top g

/-- The actual odd SU₄ exterior action lies in the commutator of the original
full minus-six orthogonal group, including at q = 3. Signed unitary elimination
discharges normal generation; no additional perfectness or simplicity premise
is needed. -/
theorem ExteriorRealization.action_mem_commutator (hp : p ≠ 2)
    (g : (unitaryForm p n).specialSubgroup) :
    R.action g ∈ commutator (FullOrthogonal F) :=
  R.action_mem_commutator_of_normal_generation hp
    (Image.Containment.elementaryNormal_eq_top p n hp) g

end ClassicalOrthogonal.Minus.OddSixComparison
