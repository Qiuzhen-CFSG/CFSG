module

public import Theory.SpecificGroups.Janko4.Model
public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The ATLAS local subgroup used to count the concrete J₄ model

The source is the ATLAS straight-line program `J4G1-max1W1`:
https://brauer.maths.qmul.ac.uk/Atlas/spor/J4/words/J4G1-max1W1 .
Its bytes, retrieved 2026-10-03, have SHA-256
`fbad445106c5b19c1227f776cd4f007b3a80d516d5a30263d062627ac09eb275`.
`max1Program` transcribes its fourteen register instructions, and the two
projection lemmas verify their expansion as group words.

The downloaded program's first output is `(ab)⁻¹ a (ab)`. The summary at
https://brauer.maths.qmul.ac.uk/Atlas/v3/subgroup/J4G1-max1W1 incorrectly
prints `ab` in its Words field. We use the actual program. Its second output
is `(ab³)⁻¹ (ababab²)⁸ (ab³)`.

We construct the source generators in the existing matrix carrier from their
square/fourth-power identities and prove that they generate that carrier.
The program then defines a specific subgroup of that same carrier. The ATLAS
identifies it as `2^11:M24`, of order 501397585920 and index 173067389;
**neither identification nor count is asserted here**. Subsequent certificates
must prove the subgroup order, coset coverage, and distinctness in the matrices.
-/

@[expose] public section
namespace Janko4.Cardinality

/-- The first generator, using only its square identity. -/
def sourceA (hA : matrixA * matrixA = 1) : Model :=
  generator ⟨matrixA, matrixA, hA, hA⟩ (Or.inl rfl)

/-- The second generator, using only its fourth-power identity. -/
def sourceB (hB : matrixB ^ 4 = 1) : Model :=
  generator ⟨matrixB, matrixB ^ 3,
    by simpa only [← pow_succ'] using hB,
    by simpa only [← pow_succ] using hB⟩ (Or.inr rfl)

@[simp] theorem toMatrix_sourceA (hA : matrixA * matrixA = 1) :
    toMatrix (sourceA hA) = matrixA := rfl

@[simp] theorem toMatrix_sourceB (hB : matrixB ^ 4 = 1) :
    toMatrix (sourceB hB) = matrixB := rfl

theorem sourceA_mul_self (hA : matrixA * matrixA = 1) :
    sourceA hA * sourceA hA = 1 := by
  apply toMatrix_injective
  simpa only [map_mul, map_one, toMatrix_sourceA] using hA

theorem sourceB_pow_four (hB : matrixB ^ 4 = 1) :
    sourceB hB ^ 4 = 1 := by
  apply toMatrix_injective
  simpa only [map_pow, map_one, toMatrix_sourceB] using hB

/-- The generator family used by the coset certificate. -/
def sourceGenerators (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) : Bool → Model
  | false => sourceA hA
  | true => sourceB hB

theorem sourceGenerators_generate (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Subgroup.closure (Set.range (sourceGenerators hA hB)) = ⊤ := by
  apply Subgroup.map_injective toAmbient_injective
  rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map]
  rw [show toAmbient.range = matrixGroup from Subgroup.range_subtype matrixGroup]
  change Subgroup.closure (toAmbient '' Set.range (sourceGenerators hA hB)) = matrixGroup
  congr 1
  ext g
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro hg
    rcases hg with ha | hb
    · refine ⟨sourceA hA, ⟨false, rfl⟩, ?_⟩
      exact Units.ext ha.symm
    · refine ⟨sourceB hB, ⟨true, rfl⟩, ?_⟩
      exact Units.ext hb.symm

/-- Literal execution of the ATLAS maximal-subgroup straight-line program. -/
def max1Program {G : Type*} [Group G] (a b : G) : G × G :=
  let r3 := a * b
  let r4 := r3 * b
  let r5 := r3 * r4
  let r6 := r3 * r5
  let r5 := r6 * r6
  let r6 := r5 * r5
  let r5 := r6 * r6
  let r6 := r4 * b
  let r7 := r6⁻¹
  let r8 := r7 * r5
  let out2 := r8 * r6
  let r4 := r3⁻¹
  let r5 := r4 * a
  let out1 := r5 * r3
  (out1, out2)

/-- The first output of the downloaded program is a conjugate of `a`. -/
theorem max1Program_fst {G : Type*} [Group G] (a b : G) :
    (max1Program a b).1 = (a * b)⁻¹ * a * (a * b) := rfl

/-- The second output, expanded as a group word. -/
theorem max1Program_snd {G : Type*} [Group G] (a b : G) :
    (max1Program a b).2 =
      (a * b ^ 3)⁻¹ * (a * b * a * b * a * b ^ 2) ^ 8 * (a * b ^ 3) := by
  simp only [max1Program, pow_succ, pow_zero, one_mul, mul_assoc]

/-- The concrete subgroup singled out by the ATLAS maximal-subgroup program.
Its identification and index are separate proof obligations. -/
def max1Subgroup (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) : Subgroup Model :=
  let p := max1Program (sourceA hA) (sourceB hB)
  Subgroup.closure {p.1, p.2}

end Janko4.Cardinality
