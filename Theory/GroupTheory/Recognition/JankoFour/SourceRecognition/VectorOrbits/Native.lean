module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.VectorOrbits.Certificates
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Native vector orbits and the unique invariant square form

Induction along the checked parent forest constructs an element of the actual
triple cover sending each vector's root to that vector. Generator invariance
of the labels proves orbit separation. Quadratic additivity on two explicit
triples forces the roots 4 and 7 to be singular; a nonzero invariant form
must take value one on the remaining nonzero orbit. Thus the square form is
unique, with two singular vector orbits.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), the module calculation in (4.2), p.597,
DOI 10.1007/BF01232280. This does not identify the orbit stabilizers.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.VectorOrbits
open Sporadic.Mathieu M22TripleCover
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

noncomputable def label (v : BinarySpace) : Word := (treeRow (decodeEquiv.symm v)).root

@[simp] theorem label_decode (n : Word) : label (decode n) = (treeRow n).root := by
  change (treeRow (decodeEquiv.symm (decodeEquiv n))).root = _
  rw [Equiv.symm_apply_apply]

def generator (b : Bool) : M22TripleCover := if b then coreGeneratorB else coreGeneratorA

theorem generator_decode (b : Bool) (n : Word) :
    binaryRepresentation (generator b) (decode n) = vector (next b n) := by
  rw [next, vector_packedAction]
  cases b <;> simp only [generator, Bool.false_eq_true, if_false, if_true,
    columnMap_generatorA, columnMap_generatorB, decode]

theorem generator_label (b : Bool) (v : BinarySpace) :
    label (binaryRepresentation (generator b) v) = label v := by
  obtain ⟨n, rfl⟩ := decode_bijective.surjective v
  rw [generator_decode]
  change label (decode ⟨next b n, next_lt b n⟩) = _
  rw [label_decode, label_decode]
  exact next_root b n

theorem label_invariant (g : M22TripleCover) (v : BinarySpace) :
    label (binaryRepresentation g v) = label v := by
  let K : Subgroup M22TripleCover := {
    carrier := {g | ∀ v, label (binaryRepresentation g v) = label v}
    one_mem' := by intro v; rw [map_one]; rfl
    mul_mem' := by
      intro a b ha hb v
      rw [map_mul, Module.End.mul_apply]
      exact (ha (binaryRepresentation b v)).trans (hb v)
    inv_mem' := by
      intro g hg v
      have he := hg (binaryRepresentation g⁻¹ v)
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at he
      exact he.symm }
  have ht : (⊤ : Subgroup M22TripleCover) ≤ K := by
    rw [← coreGenerators_closure_eq_top]
    apply (Subgroup.closure_le _).mpr
    rintro g (rfl | rfl)
    · exact generator_label false
    · exact generator_label true
  exact ht (Subgroup.mem_top g) v

theorem orbit_transport (n : Word) : ∃ g : M22TripleCover,
    binaryRepresentation g (decode (treeRow n).root) = decode n := by
  suffices hh : ∀ d, ∀ n : Word, (treeRow n).depth = d → ∃ g : M22TripleCover,
      binaryRepresentation g (decode (treeRow n).root) = decode n from hh _ n rfl
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro n hn
    by_cases hz : (treeRow n).depth = 0
    · refine ⟨1, ?_⟩
      rw [map_one]
      change decode (treeRow n).root = decode n
      rw [← tree_roots n hz]
    · obtain ⟨hd, hc, he⟩ := tree_descent n hz
      obtain ⟨g, hg⟩ := ih _ (by simpa [hn] using hd) (treeRow n).parent rfl
      refine ⟨generator (treeRow n).useB * g, ?_⟩
      rw [map_mul, Module.End.mul_apply, ← hc, hg, generator_decode, he]
      rfl

theorem orbit_iff_label (v w : BinarySpace) :
    (∃ g : M22TripleCover, binaryRepresentation g v = w) ↔ label v = label w := by
  constructor
  · rintro ⟨g, rfl⟩
    exact (label_invariant g v).symm
  · obtain ⟨a, rfl⟩ := decode_bijective.surjective v
    obtain ⟨b, rfl⟩ := decode_bijective.surjective w
    simp only [label_decode]
    intro hab
    obtain ⟨ga, ha⟩ := orbit_transport a
    obtain ⟨gb, hb⟩ := orbit_transport b
    have hi : binaryRepresentation ga⁻¹ (decode a) = decode (treeRow a).root := by
      rw [← ha, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    refine ⟨gb * ga⁻¹, ?_⟩
    rw [map_mul, Module.End.mul_apply, hi, hab, hb]

variable (q : QuadraticForm (ZMod 2) BinarySpace)
    (hq : ∀ g v, q (binaryRepresentation g v) = q v)
include hq

theorem invariant_value (n : Word) : q (decode n) = q (decode (treeRow n).root) := by
  obtain ⟨g, hg⟩ := orbit_transport n
  rw [← hg, hq]

/-- The two source singular orbits are forced by quadratic additivity. -/
theorem quadratic_singular_roots : q (decode 4) = 0 ∧ q (decode 7) = 0 := by
  have h2 : q (decode 2) = q (decode 1) := invariant_value q hq 2
  have h3 : q (decode 3) = q (decode 1) := invariant_value q hq 3
  have h5 : q (decode 5) = q (decode 1) := invariant_value q hq 5
  have h6 : q (decode 6) = q (decode 4) := invariant_value q hq 6
  have h12 : q (decode 12) = q (decode 1) := invariant_value q hq 12
  have h13 : q (decode 13) = q (decode 1) := invariant_value q hq 13
  have h14 : q (decode 14) = q (decode 4) := invariant_value q hq 14
  have h15 : q (decode 15) = q (decode 1) := invariant_value q hq 15
  have ha := q.map_add_add_add_map (vector 1) (vector 2) (vector 4)
  simp only [← vector_xor] at ha
  change q (decode 7) + (q (decode 1) + q (decode 2) + q (decode 4)) =
    q (decode 3) + q (decode 6) + q (decode 5) at ha
  rw [h2, h3, h6, h5] at ha
  have h7 : q (decode 7) = 0 := by linear_combination ha
  have hb := q.map_add_add_add_map (vector 1) (vector 2) (vector 12)
  simp only [← vector_xor] at hb
  change q (decode 15) + (q (decode 1) + q (decode 2) + q (decode 12)) =
    q (decode 3) + q (decode 14) + q (decode 13) at hb
  rw [h15, h2, h12, h3, h14, h13] at hb
  have hbinary : ∀ a b : ZMod 2, a + (a + a + a) = a + b + a → b = 0 := by decide
  exact ⟨hbinary _ _ hb, h7⟩

/-- Every nonzero invariant quadratic form has the same two singular orbits. -/
theorem quadratic_value (hne : q ≠ 0) (n : Word) :
    q (decode n) = if (treeRow n).root = 1 then 1 else 0 := by
  obtain ⟨h4, h7⟩ := quadratic_singular_roots q hq
  have h0 : q (decode 0) = 0 := by
    change q (vector 0) = 0
    rw [vector_zero, map_zero]
  have h1 : q (decode 1) = 1 := by
    have hbinary : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    apply (hbinary _).resolve_left
    intro hz
    apply hne
    ext v
    obtain ⟨n, rfl⟩ := decode_bijective.surjective v
    rw [invariant_value q hq]
    rcases root_cases n with he | he | he | he <;> rw [he]
    · exact h0
    · exact hz
    · exact h4
    · exact h7
  rw [invariant_value q hq]
  rcases root_cases n with he | he | he | he <;> rw [he] <;>
    norm_num [h0, h1, h4, h7] <;> decide

/-- The native triple-cover action has a unique nonzero invariant binary
quadratic form. This preserves square geometry under the module comparison. -/
theorem invariant_quadratic_unique (hne : q ≠ 0)
    (q' : QuadraticForm (ZMod 2) BinarySpace)
    (hq' : ∀ g v, q' (binaryRepresentation g v) = q' v) (hne' : q' ≠ 0) : q = q' := by
  ext v
  obtain ⟨n,rfl⟩ := decode_bijective.surjective v
  rw [quadratic_value q hq hne, quadratic_value q' hq' hne']

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.VectorOrbits
end
