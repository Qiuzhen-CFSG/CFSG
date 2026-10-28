module
public import Theory.Representation.BinaryPermutation.SixPairsQuadratic
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# The cosets of a six-letter pair stabilizer

The alternating group on six letters acts transitively on unordered pairs.
The orbit map therefore identifies the left cosets of a pair stabilizer
with the fifteen pairs for every coordinate homomorphism whose image
contains the alternating group. We prove its formula on cosets and its
equivariance, retaining the literal subgroup and coordinate homomorphism.

This is the orbit-stabilizer step in the alternative-section argument for
Aschbacher–Smith 13.8.21(2), printed p.956 (PDF p.973).
-/

@[expose] public section
namespace BinaryPermutation.SixPairsQuadratic

/-- The pair fixed pointwise by the two marked double transpositions. -/
def basePair : Pair := ⟨{4,5}, by decide⟩

private def pairTransport (i j : Fin 6) : Equiv.Perm (Fin 6) :=
  let t := Equiv.swap 4 i
  let u := Equiv.swap (t 5) j * t
  if Equiv.Perm.sign u = 1 then u else u * Equiv.swap 0 1

set_option maxRecDepth 4000 in
set_option maxHeartbeats 1000000 in
private theorem pairTransport_check : ∀ i j : Fin 6, ∀ hij : i ≠ j,
    Equiv.Perm.sign (pairTransport i j) = 1 ∧
      pairPerm (pairTransport i j) basePair = ⟨{i,j}, by simp [hij]⟩ := by
  decide +kernel

/-- The alternating group is transitive on the fifteen coordinate pairs. -/
theorem exists_even_pair_transport (s t : Pair) :
    ∃ g : alternatingGroup (Fin 6), pairPerm g.val s = t := by
  have hb (s : Pair) : ∃ g : alternatingGroup (Fin 6), pairPerm g.val basePair = s := by
    obtain ⟨i,j,hij,hs⟩ := Finset.card_eq_two.mp s.property
    refine ⟨⟨pairTransport i j, (pairTransport_check i j hij).1⟩, ?_⟩
    exact (pairTransport_check i j hij).2.trans (Subtype.ext hs.symm)
  obtain ⟨g,hg⟩ := hb s
  obtain ⟨h,hh⟩ := hb t
  refine ⟨h * g⁻¹, ?_⟩
  change pairHom (h.val * g.val⁻¹) s = t
  rw [map_mul, Equiv.Perm.mul_apply, map_inv]
  change pairPerm h.val ((pairPerm g.val).symm s) = t
  rw [← hg, Equiv.symm_apply_apply, hh]

variable {A : Type*} [Group A]

/-- The orbit map is bijective on the actual left cosets of a pair stabilizer. -/
noncomputable def pairCosets (f : A →* Equiv.Perm (Fin 6))
    (hf : ∀ g : alternatingGroup (Fin 6), ∃ a, f a = g.val)
    (P : Subgroup A) (s : Pair)
    (hP : ∀ a, a ∈ P ↔ pairPerm (f a) s = s) : (A ⧸ P) ≃ Pair := by
  letI : MulAction A Pair := MulAction.compHom Pair (pairHom.comp f)
  have he : P = MulAction.stabilizer A s := by ext a; exact hP a
  refine (Subgroup.quotientEquivOfEq he).trans (Equiv.ofBijective
    (MulAction.ofQuotientStabilizer A s) ⟨MulAction.injective_ofQuotientStabilizer A s, ?_⟩)
  intro t
  obtain ⟨g,hg⟩ := exists_even_pair_transport s t
  obtain ⟨a,ha⟩ := hf g
  refine ⟨QuotientGroup.mk a, ?_⟩
  change pairPerm (f a) s = t
  rw [ha, hg]

/-- The coset equivalence is the specified coordinate orbit map. -/
theorem pairCosets_mk (f : A →* Equiv.Perm (Fin 6))
    (hf : ∀ g : alternatingGroup (Fin 6), ∃ a, f a = g.val)
    (P : Subgroup A) (s : Pair)
    (hP : ∀ a, a ∈ P ↔ pairPerm (f a) s = s) (a : A) :
    pairCosets f hf P s hP (QuotientGroup.mk a) = pairPerm (f a) s := rfl

/-- The actual left coset action agrees with permutation of coordinate pairs. -/
theorem pairCosets_equivariant (f : A →* Equiv.Perm (Fin 6))
    (hf : ∀ g : alternatingGroup (Fin 6), ∃ a, f a = g.val)
    (P : Subgroup A) (s : Pair)
    (hP : ∀ a, a ∈ P ↔ pairPerm (f a) s = s) (a : A) (q : A ⧸ P) :
    pairCosets f hf P s hP (a • q) = pairPerm (f a) (pairCosets f hf P s hP q) := by
  induction q using Quotient.inductionOn' with | h b =>
    change pairPerm (f (a * b)) s = pairPerm (f a) (pairPerm (f b) s)
    change pairHom (f (a * b)) s = (pairHom (f a) * pairHom (f b)) s
    rw [f.map_mul, pairHom.map_mul]

end BinaryPermutation.SixPairsQuadratic
