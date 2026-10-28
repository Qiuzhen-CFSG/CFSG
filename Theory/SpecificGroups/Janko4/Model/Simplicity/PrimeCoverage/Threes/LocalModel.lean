module

public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Reduction

/-!
# Concrete local words for order-three coverage

`threeLocalProgram` executes the ATLAS program `J4G1-max10W1`, whose source is
https://brauer.maths.qmul.ac.uk/Atlas/spor/J4/words/J4G1-max10W1 . The program
is labelled `U3(3)` in the ATLAS; no recognition or order assertion is assumed.
The source authors are R. A. Wilson, S. J. Nickerson and J. N. Bray.

An untrusted enumeration in the binary matrices suggests that the words
`01011111` and `011011101111` in the program outputs generate a subgroup of
order 27. Their commutator and the first word are proposed representatives of
the local cyclic classes. This module only defines the words. Subgroup order,
local coverage, and fusion to the designated J4 representative are separate
certificate obligations.
-/

@[expose] public section

namespace Janko4.Simplicity

/-- Literal execution of the eighteen instructions in `J4G1-max10W1`. -/
def threeLocalProgram {G : Type*} [Group G] (a b : G) : G × G :=
  let r3 := a * b
  let r4 := r3 ^ 3
  let r5 := r4 * b
  let r4 := b * a
  let out2 := r5 ^ 4
  let r5 := r3 ^ 16
  let r6 := r5⁻¹
  let r5 := r4 ^ 24
  let r7 := r6 * r5
  let r6 := r7⁻¹
  let r5 := r6 * out2
  let out2 := r5 * r7
  let r5 := r4 ^ 8
  let r6 := r3 * r5
  let r7 := r3 ^ 18
  let r5 := r6 * r7
  let r6 := r5⁻¹
  let r7 := r6 * a
  let out1 := r7 * r5
  (out1, out2)

/-- The first proposed generator, with digit zero denoting program output one. -/
def threeLocalU (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) : Model :=
  let p := threeLocalProgram (a hA) (b hB)
  word p.1 p.2 "ababbbbb"

/-- The second proposed generator, the digit word `011011101111`. -/
def threeLocalV (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) : Model :=
  let p := threeLocalProgram (a hA) (b hB)
  word p.1 p.2 "abbabbbabbbb"

/-- The proposed central generator, using the commutator convention
`[u,v] = u⁻¹ v⁻¹ u v`. -/
def threeLocalZ (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) : Model :=
  let u := threeLocalU hA hB
  let v := threeLocalV hA hB
  u⁻¹ * v⁻¹ * u * v

/-- The concrete proposed Sylow three-subgroup, without an asserted order. -/
def threeLocalSubgroup (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Subgroup Model :=
  Subgroup.closure {threeLocalU hA hB, threeLocalV hA hB}

/-- The two proposed local representatives: noncentral and central. -/
def threeLocalRepresentative (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    Fin 2 → Model :=
  ![threeLocalU hA hB, threeLocalZ hA hB]

/-- The 27 proposed normal forms `u^i v^j z^k`. Their distinctness and
exhaustiveness are certificate obligations. -/
def threeLocalNormalForm (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (t : Fin 3 × Fin 3 × Fin 3) : Model :=
  threeLocalU hA hB ^ t.1.val * threeLocalV hA hB ^ t.2.1.val *
    threeLocalZ hA hB ^ t.2.2.val

theorem threeLocalU_mem (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    threeLocalU hA hB ∈ threeLocalSubgroup hA hB :=
  Subgroup.subset_closure (by simp)

theorem threeLocalV_mem (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    threeLocalV hA hB ∈ threeLocalSubgroup hA hB :=
  Subgroup.subset_closure (by simp)

theorem threeLocalZ_mem (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1) :
    threeLocalZ hA hB ∈ threeLocalSubgroup hA hB := by
  let H := threeLocalSubgroup hA hB
  exact H.mul_mem
    (H.mul_mem (H.mul_mem (H.inv_mem (threeLocalU_mem hA hB))
      (H.inv_mem (threeLocalV_mem hA hB))) (threeLocalU_mem hA hB))
    (threeLocalV_mem hA hB)

theorem threeLocalNormalForm_mem
    (hA : matrixA * matrixA = 1) (hB : matrixB ^ 4 = 1)
    (t : Fin 3 × Fin 3 × Fin 3) :
    threeLocalNormalForm hA hB t ∈ threeLocalSubgroup hA hB := by
  let H := threeLocalSubgroup hA hB
  exact H.mul_mem
    (H.mul_mem (H.pow_mem (threeLocalU_mem hA hB) _) (H.pow_mem (threeLocalV_mem hA hB) _))
    (H.pow_mem (threeLocalZ_mem hA hB) _)

end Janko4.Simplicity
