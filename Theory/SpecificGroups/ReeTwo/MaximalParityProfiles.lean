module

public import Theory.SpecificGroups.ReeTwo.MaximalCharacters
public import Theory.GroupTheory.PGroup.PowerFiberAutomorphisms

/-!
# Two small power-count stabilizers for the Ree two parity kernels

The two binary vector spaces below have ranks four and three. Their specified
profiles are pairs of proposed counts of solutions to x² = 1 and x⁴ = 1 in
Frattini cosets. Every automorphism preserving either profile has square one.
This is checked by reconstructing a homomorphism from its basis images and
exhausting the finite lists of possible images.

The predicates `ParityFrattiniModel` and `TwistedParityFrattiniModel` specify
the remaining link to the groups: a surjective quotient map with precisely the
Frattini kernel and exactly these power counts. This module proves the small
stabilizer calculation, not those model predicates.

Coordinate conventions: the rank-four basis lifts are rootOne², root 0,
root 1, root 2; the rank-three basis lifts are rootOne * root 0, root 1,
root 2. Root indices here are shifted by three from Shinoda (1975), (2.3),
pp. 81–82; rootOne denotes Shinoda root 1. These conventions specify the
profiles needed by the separate coordinate computations.
-/

namespace ReeTwo.SylowModel
/-- The proposed rank-four Frattini quotient of the parity kernel. -/
public abbrev ParityQuotient := Multiplicative (Fin 4 → ZMod 2)
/-- The proposed rank-three Frattini quotient of the twisted parity kernel. -/
public abbrev TwistedParityQuotient := Multiplicative (Fin 3 → ZMod 2)

/-- Proposed square/fourth-power solution counts in the sixteen parity cosets. -/
@[expose] public def parityProfile (x : ParityQuotient) : ℕ × ℕ :=
  ([ (48,128), (32,128), (32,128), (0,0), (0,128), (0,0), (0,128), (0,0),
     (0,128), (0,128), (0,128), (0,0), (0,128), (0,0), (32,128), (0,0) ] : List (ℕ × ℕ)).getD
    ((x.toAdd 0).val + 2 * (x.toAdd 1).val + 4 * (x.toAdd 2).val + 8 * (x.toAdd 3).val) (0,0)

/-- Proposed square/fourth-power solution counts in the eight twisted parity cosets. -/
@[expose] public def twistedParityProfile (x : TwistedParityQuotient) : ℕ × ℕ :=
  ([ (48,128), (0,0), (0,256), (0,0), (0,128), (0,0), (32,256), (0,0) ] : List (ℕ × ℕ)).getD
    ((x.toAdd 0).val + 2 * (x.toAdd 1).val + 4 * (x.toAdd 2).val) (0,0)

private def basisVector (n : ℕ) (i : Fin n) : Multiplicative (Fin n → ZMod 2) :=
  Multiplicative.ofAdd (fun j => if j = i then 1 else 0)
private def word4 (a b c d : ParityQuotient) (x : ParityQuotient) : ParityQuotient :=
  a ^ (x.toAdd 0).val * b ^ (x.toAdd 1).val * c ^ (x.toAdd 2).val * d ^ (x.toAdd 3).val
private def word3 (a b c : TwistedParityQuotient) (x : TwistedParityQuotient) : TwistedParityQuotient :=
  a ^ (x.toAdd 0).val * b ^ (x.toAdd 1).val * c ^ (x.toAdd 2).val

set_option synthInstance.maxSize 4096
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000
private theorem certificate4 :
    ∀ a : ParityQuotient, parityProfile a = (32,128) →
    ∀ b : ParityQuotient, parityProfile b = (32,128) →
    ∀ c : ParityQuotient, parityProfile c = (0,128) →
    ∀ d : ParityQuotient, parityProfile d = (0,128) →
    (∀ x, parityProfile (word4 a b c d x) = parityProfile x) →
    ∀ x, word4 a b c d (word4 a b c d x) = x := by decide +kernel

private theorem certificate3 :
    ∀ a : TwistedParityQuotient, twistedParityProfile a = (0,0) →
    ∀ b : TwistedParityQuotient, twistedParityProfile b = (0,256) →
    ∀ c : TwistedParityQuotient, twistedParityProfile c = (0,128) →
    (∀ x, twistedParityProfile (word3 a b c x) = twistedParityProfile x) →
    ∀ x, word3 a b c (word3 a b c x) = x := by decide +kernel

private theorem word4_hom (f : ParityQuotient →* ParityQuotient) (x : ParityQuotient) :
    word4 (f (basisVector 4 0)) (f (basisVector 4 1)) (f (basisVector 4 2))
      (f (basisVector 4 3)) x = f x := by
  have hn : word4 (basisVector 4 0) (basisVector 4 1) (basisVector 4 2) (basisVector 4 3) x = x :=
    (by decide +kernel : ∀ x, word4 (basisVector 4 0) (basisVector 4 1)
      (basisVector 4 2) (basisVector 4 3) x = x) x
  simpa only [word4, map_mul, map_pow] using congrArg f hn

private theorem word3_hom (f : TwistedParityQuotient →* TwistedParityQuotient) (x : TwistedParityQuotient) :
    word3 (f (basisVector 3 0)) (f (basisVector 3 1)) (f (basisVector 3 2)) x = f x := by
  have hn : word3 (basisVector 3 0) (basisVector 3 1) (basisVector 3 2) x = x :=
    (by decide +kernel : ∀ x, word3 (basisVector 3 0) (basisVector 3 1) (basisVector 3 2) x = x) x
  simpa only [word3, map_mul, map_pow] using congrArg f hn

/-- The stabilizer of the rank-four profile has exponent dividing two. -/
public theorem parityProfile_aut_square (f : MulAut ParityQuotient)
    (h : ∀ x, parityProfile (f x) = parityProfile x) : f ^ 2 = 1 := by
  have hc := certificate4 (f (basisVector 4 0)) (h _) (f (basisVector 4 1)) (h _)
    (f (basisVector 4 2)) (h _) (f (basisVector 4 3)) (h _)
  have hw := word4_hom f.toMonoidHom
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hw
  have hh := hc (by intro x; rw [hw]; exact h x)
  apply MulEquiv.ext
  intro x
  change f (f x) = x
  simpa only [hw] using hh x

/-- The stabilizer of the rank-three profile has exponent dividing two. -/
public theorem twistedParityProfile_aut_square (f : MulAut TwistedParityQuotient)
    (h : ∀ x, twistedParityProfile (f x) = twistedParityProfile x) : f ^ 2 = 1 := by
  have hc := certificate3 (f (basisVector 3 0)) (h _) (f (basisVector 3 1)) (h _)
    (f (basisVector 3 2)) (h _)
  have hw := word3_hom f.toMonoidHom
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hw
  have hh := hc (by intro x; rw [hw]; exact h x)
  apply MulEquiv.ext
  intro x
  change f (f x) = x
  simpa only [hw] using hh x
/-- A coordinate realization of the parity Frattini quotient with its power counts. -/
@[expose] public def ParityFrattiniModel : Prop :=
  ∃ π : (maximalCharacter 1 0 0).ker →* ParityQuotient,
    Function.Surjective π ∧ π.ker = frattini (maximalCharacter 1 0 0).ker ∧
    ∀ v, (π.powerFiberCard v 2, π.powerFiberCard v 4) = parityProfile v

/-- A coordinate realization of the twisted parity Frattini quotient with its power counts. -/
@[expose] public def TwistedParityFrattiniModel : Prop :=
  ∃ π : (maximalCharacter 1 1 0).ker →* TwistedParityQuotient,
    Function.Surjective π ∧ π.ker = frattini (maximalCharacter 1 1 0).ker ∧
    ∀ v, (π.powerFiberCard v 2, π.powerFiberCard v 4) = twistedParityProfile v

end ReeTwo.SylowModel
