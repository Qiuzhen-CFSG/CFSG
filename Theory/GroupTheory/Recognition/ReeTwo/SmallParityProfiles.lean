module

public import Theory.GroupTheory.Recognition.ReeTwo.SmallParityRepresentatives
public import Theory.GroupTheory.PGroup.InvariantFiberCoordinates

/-!
# Intrinsic profiles for the small Ree two parity candidates

The fourteen candidates have proposed binary Frattini models of ranks four
(eight candidates) and three (six candidates). Three counts in each coset
record element orders and centralizer sizes; candidate 458 also uses the
centralizer size of the square. The finite stabilizer calculations below are
kernel-checked and show that every profile symmetry has fourth power one.

The model predicates retain the separate obligations of constructing the
quotient map, proving its Frattini kernel, and verifying the actual counts.
No automorphism order from an external computation is used as a theorem.
Source: the root model of Shinoda (1975), (2.3), pp. 81–82, as verified in
`ReeTwo.Sylow`; generator positions refer to `SmallParityRepresentatives`.

The rank-four rows have diagnostic labels 68,70,71,73,194,199,457,471,
with basis lifts at generator positions (counted from one)
[1,2,3,6], [1,2,3,4], [1,2,3,5], [1,2,3,5],
[1,2,3,5], [1,2,3,5], [1,2,5,6], [1,2,4,5].
The rank-three rows have labels 76,209,458,459,460,478,
with basis positions [1,2,4], [1,2,4], [1,2,4], [1,2,5], [1,2,4], [1,2,4].
Cosets are indexed by the binary digits in this basis order, least significant first.
-/

namespace ReeTwo.SylowModel

public abbrev SmallParityFourQuotient := Multiplicative (Fin 4 → ZMod 2)
public abbrev SmallParityThreeQuotient := Multiplicative (Fin 3 → ZMod 2)

/-- Indices in the original fourteen-candidate family. -/
@[expose] public def smallParityFourIndex : Fin 8 → Fin 14 :=
  ![0, 1, 2, 3, 5, 6, 8, 12]

/-- The three intrinsic tests for each rank-4 row. -/
@[expose] public def smallParityFourTests (i : Fin 8) : Fin 3 → ℕ × ℕ × ℕ :=
  (![![(1, 512, 0), (4, 32, 0), (4, 64, 0)], ![(2, 128, 0), (4, 32, 0), (4, 64, 0)], ![(4, 32, 0), (4, 64, 0), (4, 128, 0)], ![(4, 32, 0), (4, 64, 0), (4, 128, 0)], ![(2, 128, 0), (4, 64, 0), (4, 64, 0)], ![(2, 64, 0), (4, 64, 0), (4, 128, 0)], ![(2, 64, 0), (2, 128, 0), (4, 32, 0)], ![(1, 128, 0), (4, 32, 0), (4, 64, 0)]]) i

/-- Proposed test counts in the binary cosets. -/
@[expose] public def smallParityFourProfile (i : Fin 8)
    (x : SmallParityFourQuotient) : ℕ × ℕ × ℕ :=
  ((![([(1, 0, 0), (0, 0, 32), (0, 0, 32), (0, 0, 32), (0, 32, 0), (0, 0, 0), (0, 0, 32), (0, 0, 32), (0, 0, 16), (0, 32, 0), (0, 0, 32), (0, 0, 32), (0, 32, 0), (0, 0, 0), (0, 0, 32), (0, 0, 32)] : List (ℕ × ℕ × ℕ)), ([(8, 0, 0), (0, 16, 16), (0, 0, 0), (0, 0, 0), (0, 32, 0), (0, 0, 16), (0, 0, 0), (0, 0, 0), (16, 0, 0), (0, 16, 16), (0, 0, 0), (0, 0, 0), (0, 32, 0), (0, 0, 16), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)), ([(0, 0, 8), (0, 16, 16), (0, 32, 0), (0, 32, 0), (16, 0, 0), (32, 0, 0), (0, 0, 0), (0, 0, 0), (0, 8, 0), (0, 0, 24), (0, 32, 0), (0, 32, 0), (32, 0, 0), (16, 16, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)), ([(0, 0, 8), (0, 0, 24), (0, 32, 0), (0, 32, 0), (32, 0, 0), (32, 0, 0), (0, 0, 0), (0, 0, 0), (0, 8, 0), (0, 16, 16), (0, 32, 0), (0, 32, 0), (16, 0, 0), (16, 16, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)), ([(12, 0, 0), (0, 0, 0), (0, 16, 16), (0, 16, 16), (0, 8, 8), (0, 16, 16), (0, 16, 16), (0, 16, 16), (16, 0, 0), (0, 0, 0), (0, 16, 16), (0, 16, 16), (0, 8, 8), (0, 16, 16), (0, 16, 16), (0, 16, 16)] : List (ℕ × ℕ × ℕ)), ([(0, 0, 8), (0, 16, 0), (0, 0, 0), (0, 0, 0), (16, 0, 0), (0, 16, 0), (0, 0, 0), (0, 0, 0), (8, 8, 0), (0, 0, 16), (0, 0, 0), (0, 0, 0), (16, 0, 0), (0, 16, 0), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)), ([(0, 7, 0), (0, 0, 0), (0, 0, 8), (0, 0, 8), (8, 0, 0), (0, 0, 0), (0, 0, 8), (0, 0, 8), (0, 8, 0), (0, 0, 0), (0, 0, 8), (0, 0, 8), (8, 0, 0), (0, 0, 0), (0, 0, 8), (0, 0, 8)] : List (ℕ × ℕ × ℕ)), ([(1, 0, 0), (0, 8, 0), (0, 0, 0), (0, 0, 0), (0, 4, 0), (0, 0, 8), (0, 0, 0), (0, 0, 0), (0, 0, 4), (0, 8, 0), (0, 0, 0), (0, 0, 0), (0, 4, 0), (0, 0, 8), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ))]) i).getD
    ((x.toAdd 0).val + 2 * (x.toAdd 1).val + 4 * (x.toAdd 2).val + 8 * (x.toAdd 3).val) (0, 0, 0)

/-- Indices in the original fourteen-candidate family. -/
@[expose] public def smallParityThreeIndex : Fin 6 → Fin 14 :=
  ![4, 7, 9, 10, 11, 13]

/-- The three intrinsic tests for each rank-3 row. -/
@[expose] public def smallParityThreeTests (i : Fin 6) : Fin 3 → ℕ × ℕ × ℕ :=
  (![![(2, 64, 0), (4, 64, 0), (4, 64, 0)], ![(4, 32, 0), (4, 64, 0), (4, 64, 0)], ![(2, 128, 128), (4, 32, 64), (4, 32, 64)], ![(1, 128, 0), (4, 32, 0), (4, 32, 0)], ![(1, 128, 0), (4, 32, 0), (4, 32, 0)], ![(4, 32, 0), (4, 64, 0), (4, 64, 0)]]) i

/-- Proposed test counts in the binary cosets. -/
@[expose] public def smallParityThreeProfile (i : Fin 6)
    (x : SmallParityThreeQuotient) : ℕ × ℕ × ℕ :=
  ((![([(8, 8, 8), (0, 0, 0), (0, 0, 0), (0, 32, 32), (32, 0, 0), (0, 0, 0), (0, 0, 0), (0, 16, 16)] : List (ℕ × ℕ × ℕ)), ([(0, 4, 4), (0, 0, 0), (0, 0, 0), (16, 0, 0), (8, 0, 0), (0, 0, 0), (0, 0, 0), (0, 16, 16)] : List (ℕ × ℕ × ℕ)), ([(3, 0, 0), (0, 0, 0), (0, 16, 16), (0, 16, 16), (4, 0, 0), (0, 0, 0), (0, 16, 16), (0, 16, 16)] : List (ℕ × ℕ × ℕ)), ([(1, 0, 0), (0, 16, 16), (0, 0, 0), (0, 0, 0), (0, 8, 8), (0, 16, 16), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)), ([(1, 0, 0), (0, 16, 16), (0, 0, 0), (0, 0, 0), (0, 8, 8), (0, 16, 16), (0, 0, 0), (0, 0, 0)] : List (ℕ × ℕ × ℕ)), ([(0, 2, 2), (0, 0, 0), (0, 0, 0), (0, 8, 8), (4, 0, 0), (0, 0, 0), (0, 0, 0), (8, 0, 0)] : List (ℕ × ℕ × ℕ))]) i).getD
    ((x.toAdd 0).val + 2 * (x.toAdd 1).val + 4 * (x.toAdd 2).val) (0, 0, 0)

private def basisVector (n : ℕ) (i : Fin n) : Multiplicative (Fin n → ZMod 2) :=
  Multiplicative.ofAdd (fun j => if j = i then 1 else 0)

private def word4 (a b c d : SmallParityFourQuotient) (x : SmallParityFourQuotient) :
    SmallParityFourQuotient :=
  a ^ (x.toAdd 0).val * b ^ (x.toAdd 1).val * c ^ (x.toAdd 2).val * d ^ (x.toAdd 3).val

private def word3 (a b c : SmallParityThreeQuotient) (x : SmallParityThreeQuotient) :
    SmallParityThreeQuotient :=
  a ^ (x.toAdd 0).val * b ^ (x.toAdd 1).val * c ^ (x.toAdd 2).val

set_option synthInstance.maxSize 4096
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

private theorem certificate4 : ∀ i : Fin 8,
    ∀ a : SmallParityFourQuotient, smallParityFourProfile i a = smallParityFourProfile i (basisVector 4 0) →
    ∀ b : SmallParityFourQuotient, smallParityFourProfile i b = smallParityFourProfile i (basisVector 4 1) →
    ∀ c : SmallParityFourQuotient, smallParityFourProfile i c = smallParityFourProfile i (basisVector 4 2) →
    ∀ d : SmallParityFourQuotient, smallParityFourProfile i d = smallParityFourProfile i (basisVector 4 3) →
    (∀ x, smallParityFourProfile i (word4 a b c d x) = smallParityFourProfile i x) →
    ∀ x, word4 a b c d (word4 a b c d (word4 a b c d (word4 a b c d x))) = x := by decide +kernel

private theorem word4_hom (f : SmallParityFourQuotient →* SmallParityFourQuotient) (x : SmallParityFourQuotient) :
    word4 (f (basisVector 4 0)) (f (basisVector 4 1)) (f (basisVector 4 2)) (f (basisVector 4 3)) x = f x := by
  have hn : word4 (basisVector 4 0) (basisVector 4 1) (basisVector 4 2) (basisVector 4 3) x = x :=
    (by decide +kernel : ∀ x, word4 (basisVector 4 0) (basisVector 4 1) (basisVector 4 2) (basisVector 4 3) x = x) x
  simpa only [word4, map_mul, map_pow] using congrArg f hn

/-- Every automorphism preserving a rank-4 profile has fourth power one. -/
public theorem smallParityFourProfile_aut_fourth (i : Fin 8) (f : MulAut SmallParityFourQuotient)
    (h : ∀ x, smallParityFourProfile i (f x) = smallParityFourProfile i x) : f ^ 4 = 1 := by
  have hc := certificate4 i (f (basisVector 4 0)) (h _) (f (basisVector 4 1)) (h _) (f (basisVector 4 2)) (h _) (f (basisVector 4 3)) (h _)
  have hw := word4_hom f.toMonoidHom
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hw
  have hh := hc (by intro x; rw [hw]; exact h x)
  apply MulEquiv.ext
  intro x
  change f (f (f (f x))) = x
  simpa only [hw] using hh x

/-- Realization of a rank-4 profile on the exact specified subgroup. -/
@[expose] public def SmallParityFourFrattiniModel (i : Fin 8) : Prop :=
  ∃ π : smallParityTwoCandidate (smallParityFourIndex i) →* SmallParityFourQuotient,
    Function.Surjective π ∧ π.ker = frattini (smallParityTwoCandidate (smallParityFourIndex i)) ∧
    ∀ v, (π.predicateFiberCard (MulAut.orderCentralizerTest (smallParityFourTests i 0)) v,
      π.predicateFiberCard (MulAut.orderCentralizerTest (smallParityFourTests i 1)) v,
      π.predicateFiberCard (MulAut.orderCentralizerTest (smallParityFourTests i 2)) v) =
      smallParityFourProfile i v

private theorem certificate3 : ∀ i : Fin 6,
    ∀ a : SmallParityThreeQuotient, smallParityThreeProfile i a = smallParityThreeProfile i (basisVector 3 0) →
    ∀ b : SmallParityThreeQuotient, smallParityThreeProfile i b = smallParityThreeProfile i (basisVector 3 1) →
    ∀ c : SmallParityThreeQuotient, smallParityThreeProfile i c = smallParityThreeProfile i (basisVector 3 2) →
    (∀ x, smallParityThreeProfile i (word3 a b c x) = smallParityThreeProfile i x) →
    ∀ x, word3 a b c (word3 a b c (word3 a b c (word3 a b c x))) = x := by decide +kernel

private theorem word3_hom (f : SmallParityThreeQuotient →* SmallParityThreeQuotient) (x : SmallParityThreeQuotient) :
    word3 (f (basisVector 3 0)) (f (basisVector 3 1)) (f (basisVector 3 2)) x = f x := by
  have hn : word3 (basisVector 3 0) (basisVector 3 1) (basisVector 3 2) x = x :=
    (by decide +kernel : ∀ x, word3 (basisVector 3 0) (basisVector 3 1) (basisVector 3 2) x = x) x
  simpa only [word3, map_mul, map_pow] using congrArg f hn

/-- Every automorphism preserving a rank-3 profile has fourth power one. -/
public theorem smallParityThreeProfile_aut_fourth (i : Fin 6) (f : MulAut SmallParityThreeQuotient)
    (h : ∀ x, smallParityThreeProfile i (f x) = smallParityThreeProfile i x) : f ^ 4 = 1 := by
  have hc := certificate3 i (f (basisVector 3 0)) (h _) (f (basisVector 3 1)) (h _) (f (basisVector 3 2)) (h _)
  have hw := word3_hom f.toMonoidHom
  simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hw
  have hh := hc (by intro x; rw [hw]; exact h x)
  apply MulEquiv.ext
  intro x
  change f (f (f (f x))) = x
  simpa only [hw] using hh x

/-- Realization of a rank-3 profile on the exact specified subgroup. -/
@[expose] public def SmallParityThreeFrattiniModel (i : Fin 6) : Prop :=
  ∃ π : smallParityTwoCandidate (smallParityThreeIndex i) →* SmallParityThreeQuotient,
    Function.Surjective π ∧ π.ker = frattini (smallParityTwoCandidate (smallParityThreeIndex i)) ∧
    ∀ v, (π.predicateFiberCard (MulAut.orderCentralizerTest (smallParityThreeTests i 0)) v,
      π.predicateFiberCard (MulAut.orderCentralizerTest (smallParityThreeTests i 1)) v,
      π.predicateFiberCard (MulAut.orderCentralizerTest (smallParityThreeTests i 2)) v) =
      smallParityThreeProfile i v

end ReeTwo.SylowModel
