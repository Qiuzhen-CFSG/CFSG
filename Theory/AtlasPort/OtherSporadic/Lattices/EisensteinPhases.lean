/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/EisensteinPhases.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.EisensteinCongruence

/-!
# Eisenstein Phases

Code phases preserve the integral congruence lattice. Residue and sum calculations certify the phase action.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/EisensteinPhases.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for the source coordinate computations.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra

/-- The three integral Eisenstein phases with the fixed ternary marking. -/
def eisensteinPhase (a : ZMod 3) : Eisenstein := eisensteinOmega ^ a.val

/-- Integral correction after subtracting one and dividing by theta. -/
def eisensteinPhaseCorrection (a : ZMod 3) : Eisenstein :=
  if a = 0 then 0 else if a = 1 then 1 + eisensteinOmega else eisensteinOmega

@[simp] theorem eisensteinPhase_zero : eisensteinPhase 0 = 1 := by decide +kernel

theorem eisensteinPhase_add (a b : ZMod 3) :
    eisensteinPhase (a+b) = eisensteinPhase a * eisensteinPhase b := by
  revert a b; decide +kernel

theorem eisensteinPhase_neg_mul (a : ZMod 3) :
    eisensteinPhase (-a) * eisensteinPhase a = 1 := by
  rw [← eisensteinPhase_add, neg_add_cancel, eisensteinPhase_zero]

theorem eisensteinPhase_injective : Function.Injective eisensteinPhase := by
  intro a b h
  have hh : ∀ a b : ZMod 3, eisensteinPhase a = eisensteinPhase b → a = b := by
    decide +kernel
  exact hh a b h

theorem eisensteinPhase_correction (a : ZMod 3) :
    eisensteinPhase a = 1 + eisensteinTheta * eisensteinPhaseCorrection a := by
  revert a; decide +kernel

@[simp] theorem eisensteinPhase_residue (a : ZMod 3) :
    eisensteinResidue (eisensteinPhase a) = 1 := by
  revert a; decide +kernel

@[simp] theorem eisensteinPhaseCorrection_residue (a : ZMod 3) :
    eisensteinResidue (eisensteinPhaseCorrection a) = -a := by
  revert a; decide +kernel

/-- A bounded check on the 729 code parameters: the two integral coefficients
of the correction sum are divisible by three. This is code arithmetic, not
a permutation-group certificate. -/
private theorem eisensteinPhaseCorrection_sum_check :
    ∀ p : TernaryParameters,
      let s := ∑ i, eisensteinPhaseCorrection (ternaryEncoder p i)
      s = 3 * (⟨s.re / 3, s.im / 3⟩ : Eisenstein) := by
  decide +kernel

/-- For every actual ternary Golay word, the total correction is a multiple of three. -/
theorem eisensteinPhaseCorrection_sum_dvd (t : ternaryGolay) :
    (3 : Eisenstein) ∣ ∑ i, eisensteinPhaseCorrection (t.val i) := by
  obtain ⟨p, hp⟩ := t.property
  refine ⟨⟨(∑ i, eisensteinPhaseCorrection (t.val i)).re / 3,
    (∑ i, eisensteinPhaseCorrection (t.val i)).im / 3⟩, ?_⟩
  rw [← hp]
  exact eisensteinPhaseCorrection_sum_check p

/-- Orthogonality of code residues supplies the second theta in the sum correction. -/
theorem eisensteinPhaseCorrection_dot_dvd
    (t : ternaryGolay) (u : EisensteinCoordinates)
    (hu : eisensteinWordResidue u ∈ ternaryGolay) :
    eisensteinTheta ∣ ∑ i, eisensteinPhaseCorrection (t.val i) * u i := by
  apply (eisensteinResidue_eq_zero _).mp
  simp only [map_sum, map_mul, eisensteinPhaseCorrection_residue, neg_mul,
    Finset.sum_neg_distrib, neg_eq_zero]
  have h := ternaryGolay_selfOrthogonal hu t.val t.property
  exact h

/-- Diagonal ternary phases in the marked twelve Eisenstein coordinates. -/
def eisensteinDiagonal (t : TernaryWord) (z : EisensteinCoordinates) : EisensteinCoordinates :=
  fun i => eisensteinPhase (t i) * z i

@[simp] theorem eisensteinDiagonal_zero (z : EisensteinCoordinates) :
    eisensteinDiagonal 0 z = z := by
  funext i
  simp [eisensteinDiagonal]

theorem eisensteinDiagonal_add (s t : TernaryWord) (z : EisensteinCoordinates) :
    eisensteinDiagonal (s+t) z = eisensteinDiagonal s (eisensteinDiagonal t z) := by
  funext i
  simp [eisensteinDiagonal, eisensteinPhase_add, mul_assoc]

/-- Every code phase preserves all three defining congruences of the actual lattice. -/
theorem eisensteinDiagonal_mem (t : ternaryGolay)
    {z : EisensteinCoordinates} (hz : z ∈ eisensteinLeechModule) :
    eisensteinDiagonal t.val z ∈ eisensteinLeechModule := by
  obtain ⟨m, u, hu, hc, hd⟩ := hz
  let k : EisensteinCoordinates := fun i => eisensteinPhaseCorrection (t.val i)
  let v : EisensteinCoordinates := fun i => eisensteinPhase (t.val i) * u i + m * k i
  obtain ⟨b, hb⟩ := eisensteinPhaseCorrection_sum_dvd t
  obtain ⟨c, he⟩ := eisensteinPhaseCorrection_dot_dvd t u hc
  refine ⟨m, v, ?_, ?_, ?_⟩
  · intro i
    dsimp [eisensteinDiagonal, v, k]
    rw [hu i, eisensteinPhase_correction]
    ring
  · have hh := ternaryGolay.sub_mem hc (ternaryGolay.smul_mem (eisensteinResidue m) t.property)
    convert hh using 1
    funext i
    simp [eisensteinWordResidue, v, k, sub_eq_add_neg]
  · have hsum : (∑ i, eisensteinDiagonal t.val z i) + 3*m =
        ((∑ i, z i) + 3*m) + (3*eisensteinTheta) * (m*b-c) := by
      have hdiff : (∑ i, eisensteinDiagonal t.val z i) =
          (∑ i, z i) + eisensteinTheta *
            (m * (∑ i, k i) + eisensteinTheta * ∑ i, k i * u i) := by
        simp only [mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        dsimp [eisensteinDiagonal, k]
        rw [hu i, eisensteinPhase_correction]
        ring
      rw [hdiff]
      change (∑ i, z i) + eisensteinTheta *
        (m * (∑ i, eisensteinPhaseCorrection (t.val i)) +
          eisensteinTheta * ∑ i, eisensteinPhaseCorrection (t.val i) * u i) + 3*m = _
      rw [hb, he]
      linear_combination (eisensteinTheta * c) * eisensteinTheta_sq
    rw [hsum]
    exact dvd_add hd (dvd_mul_right (3*eisensteinTheta) (m*b-c))

/-- The diagonal code phases preserve the lattice in both directions. -/
theorem eisensteinDiagonal_lattice_iff (t : ternaryGolay) (z : EisensteinCoordinates) :
    z ∈ eisensteinLeechModule ↔ eisensteinDiagonal t.val z ∈ eisensteinLeechModule := by
  constructor
  · exact eisensteinDiagonal_mem t
  · intro hz
    have h := eisensteinDiagonal_mem (-t) hz
    rw [← eisensteinDiagonal_add] at h
    change eisensteinDiagonal (-t.val + t.val) z ∈ eisensteinLeechModule at h
    simpa only [neg_add_cancel, eisensteinDiagonal_zero] using h

/-- Diagonal phases act by actual Eisenstein-linear coordinate automorphisms. -/
def eisensteinDiagonalEquiv (t : TernaryWord) :
    EisensteinCoordinates ≃ₗ[Eisenstein] EisensteinCoordinates where
  toFun := eisensteinDiagonal t
  invFun := eisensteinDiagonal (-t)
  left_inv z := by rw [← eisensteinDiagonal_add, neg_add_cancel, eisensteinDiagonal_zero]
  right_inv z := by rw [← eisensteinDiagonal_add, add_neg_cancel, eisensteinDiagonal_zero]
  map_add' z w := by funext i; simp [eisensteinDiagonal, mul_add]
  map_smul' a z := by funext i; simp [eisensteinDiagonal, mul_left_comm]

/-- The additive ternary code maps into the diagonal coordinate automorphisms. -/
def eisensteinDiagonalHom :
    Multiplicative ternaryGolay →* (EisensteinCoordinates ≃ₗ[Eisenstein] EisensteinCoordinates) where
  toFun t := eisensteinDiagonalEquiv t.toAdd.val
  map_one' := by
    apply LinearEquiv.ext
    exact eisensteinDiagonal_zero
  map_mul' s t := by
    apply LinearEquiv.ext
    exact eisensteinDiagonal_add s.toAdd.val t.toAdd.val

/-- Distinct codewords give distinct actual diagonal coordinate automorphisms. -/
theorem eisensteinDiagonalHom_injective : Function.Injective eisensteinDiagonalHom := by
  intro s t h
  change s.toAdd = t.toAdd
  apply Subtype.ext
  funext i
  apply eisensteinPhase_injective
  have he := congrArg (fun f : EisensteinCoordinates ≃ₗ[Eisenstein] EisensteinCoordinates =>
    f (fun _ => 1) i) h
  simpa only [eisensteinDiagonalHom, eisensteinDiagonalEquiv, eisensteinDiagonal,
    MonoidHom.coe_mk, OneHom.coe_mk, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, mul_one] using he

end Atlas.Lattices
