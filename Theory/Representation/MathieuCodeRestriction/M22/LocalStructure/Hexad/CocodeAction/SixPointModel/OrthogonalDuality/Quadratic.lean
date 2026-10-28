module
public import Theory.Representation.MathieuCodeRestriction.M22.LocalStructure.Hexad.CocodeAction.SixPointModel.OrthogonalDuality.DeletedDuality
public import Theory.AtlasPort.OtherSporadic.Codes.BinaryWeight
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# The half-weight quadratic form on an octad

Binary weight addition supplies the quadratic identity on even words, with
coordinate dot product as polar form. For an octad, constants have quadratic
value zero and belong to the polar radical, so this form descends to the
natural section. Its value on the marked pair is one. Only the constant
line is divided out; no quadratic form is descended through the pair line.

Source: Aschbacher--Smith, H.15.2(2), printed pp.398--399. The weight identities
are from the checked ATLAS port `Codes.BinaryWeight`, whose original attribution
and license are retained in that imported module.
-/
@[expose] public section
open scoped BigOperators
namespace MathieuCode.Hexad.CocodeAction.SixPointModel.OrthogonalDuality
noncomputable section
open BinaryPermutation

private lemma binary_scalar_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  revert c
  decide +kernel

section General
variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω]

/-- Half the weight of an even binary word, reduced modulo two. -/
def halfWeight (v : core Ω) : ZMod 2 := (hammingNorm v.val / 2 : ℕ)

omit [DecidableEq Ω] in
lemma halfWeight_add (v w : core Ω) :
    halfWeight Ω (v + w) = halfWeight Ω v + halfWeight Ω w +
      ∑ i, v.val i * w.val i := by
  have hv := (Atlas.Codes.even_weight_iff v.val).mpr v.property
  have hw := (Atlas.Codes.even_weight_iff w.val).mpr w.property
  have hz := (Atlas.Codes.even_weight_iff (v + w).val).mpr (v + w).property
  have he := Atlas.Codes.binary_weight_add v.val w.val
  have hh : hammingNorm (v + w).val / 2 + Atlas.Codes.overlap v.val w.val =
      hammingNorm v.val / 2 + hammingNorm w.val / 2 := by
    obtain ⟨a, ha⟩ := hv
    obtain ⟨b, hb⟩ := hw
    obtain ⟨c, hc⟩ := hz
    change hammingNorm (v + w).val + 2 * Atlas.Codes.overlap v.val w.val = _ at he
    omega
  have hh' := congrArg (fun n : ℕ => (n : ZMod 2)) hh
  push_cast at hh'
  rw [← Atlas.Codes.binaryDot_overlap] at hh'
  change halfWeight Ω (v + w) + (∑ i, v.val i * w.val i) =
    halfWeight Ω v + halfWeight Ω w at hh'
  calc
    _ = (halfWeight Ω (v + w) + (∑ i, v.val i * w.val i)) +
        (∑ i, v.val i * w.val i) := by simp [add_assoc]
    _ = _ := by rw [hh']

/-- The dot product restricted to even words. -/
def evenDot : core Ω →ₗ[ZMod 2] core Ω →ₗ[ZMod 2] ZMod 2 :=
  (fullCorePairing Ω).domRestrict (core Ω)

/-- The canonical quadratic form on the even binary permutation module. -/
def evenQuadratic : QuadraticForm (ZMod 2) (core Ω) :=
  QuadraticMap.mk (halfWeight Ω) (fun c v => by
    rcases binary_scalar_cases c with rfl | rfl <;> simp [halfWeight]) ⟨evenDot Ω, halfWeight_add Ω⟩

lemma evenQuadratic_apply (v : core Ω) :
    evenQuadratic Ω v = (hammingNorm v.val / 2 : ℕ) := rfl

lemma evenQuadratic_polar (v w : core Ω) :
    (evenQuadratic Ω).polarBilin v w = ∑ i, v.val i * w.val i := by
  change halfWeight Ω (v + w) - halfWeight Ω v - halfWeight Ω w = _
  rw [halfWeight_add]
  abel

lemma evenQuadratic_invariant (g : Equiv.Perm Ω) (v : core Ω) :
    evenQuadratic Ω (BinaryPermutation.coreRepresentation Ω g v) = evenQuadratic Ω v := by
  apply congrArg (fun n : ℕ => ((n / 2 : ℕ) : ZMod 2))
  simp only [Atlas.Codes.hammingNorm_eq_sum, BinaryPermutation.coreRepresentation_apply, representation_apply]
  exact Equiv.sum_comp g.symm (fun i => if v.val i = 0 then 0 else 1)
end General

lemma octad_constants_quadratic_radical :
    (coreToNatural O.val).ker ≤ (evenQuadratic O.val).radical := by
  intro v hv
  have he : (constants O.val).mkQ v.val = 0 := congrArg Subtype.val hv
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp ((Submodule.Quotient.mk_eq_zero _).mp he)
  constructor
  · change ((hammingNorm v.val / 2 : ℕ) : ZMod 2) = 0
    rw [← hc]
    rcases binary_scalar_cases c with rfl | rfl
    · simp
    · simp only [one_smul]
      have h : hammingNorm (allOne O.val) = 8 := by decide +kernel
      rw [h]
      rfl
  · apply LinearMap.ext
    intro w
    rw [evenQuadratic_polar]
    rw [← hc]
    simp only [Pi.smul_apply, allOne, smul_eq_mul, mul_one, ← Finset.mul_sum]
    rw [show ∑ i, w.val i = 0 from w.property, mul_zero]
    rfl

/-- The genuine octad quadratic form on the natural section. -/
def octadQuadratic : QuadraticForm (ZMod 2) (natural O.val) :=
  ((evenQuadratic O.val).lift (coreToNatural O.val).ker octad_constants_quadratic_radical).comp
    ((coreToNatural O.val).quotKerEquivOfSurjective coreToNatural_surjective).symm.toLinearMap


lemma octadQuadratic_apply_core (v : core O.val) :
    octadQuadratic (coreToNatural O.val v) = (hammingNorm v.val / 2 : ℕ) := by
  simp [octadQuadratic, evenQuadratic_apply]

lemma octadQuadratic_polar (v w : natural O.val) :
    octadQuadratic.polarBilin v w = naturalPairing O.val v w := by
  obtain ⟨a, rfl⟩ := coreToNatural_surjective v
  obtain ⟨b, rfl⟩ := coreToNatural_surjective w
  rw [naturalPairing_apply_core]
  change octadQuadratic (coreToNatural O.val a + coreToNatural O.val b) -
    octadQuadratic (coreToNatural O.val a) - octadQuadratic (coreToNatural O.val b) = _
  rw [← map_add, octadQuadratic_apply_core, octadQuadratic_apply_core, octadQuadratic_apply_core]
  exact evenQuadratic_polar O.val a b

lemma octadQuadratic_invariant (g : Equiv.Perm O.val) (v : natural O.val) :
    octadQuadratic (naturalRepresentation O.val g v) = octadQuadratic v := by
  obtain ⟨a, rfl⟩ := coreToNatural_surjective v
  rw [← coreToNatural_equivariant, octadQuadratic_apply_core, octadQuadratic_apply_core]
  exact evenQuadratic_invariant O.val g a

lemma octadQuadratic_pair : octadQuadratic (coreToNatural O.val pairWord) = 1 := by
  rw [octadQuadratic_apply_core]
  have h : hammingNorm pairWord.val = 2 := by decide +kernel
  rw [h]
  rfl

/-- In particular the octad quadratic form cannot descend through the pair line. -/
lemma no_quadratic_descent_through_pair
    (q : natural O.val → ZMod 2)
    (hq : ∀ v, q (v + coreToNatural O.val pairWord) = q v) : q ≠ octadQuadratic := by
  intro he
  have h := hq 0
  rw [he, zero_add, octadQuadratic_pair, QuadraticMap.map_zero] at h
  exact one_ne_zero h


end
end MathieuCode.Hexad.CocodeAction.SixPointModel.OrthogonalDuality
