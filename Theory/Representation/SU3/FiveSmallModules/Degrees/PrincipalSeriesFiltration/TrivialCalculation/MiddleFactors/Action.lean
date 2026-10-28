module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.PrincipalSeriesFiltration.TrivialCalculation.MiddleFactors.Basis

/-!
# Checked generator matrices in the adapted coordinates

The two packed products C A = P C certify the function-action convention
v(i) ↦ v(p(i)). The diagonal blocks are exactly the published matrices of
degrees 104 and 20. The vanishing blocks certify preservation of the initial
segments of dimensions 1, 105 and 125. Every identity extends to arbitrary
characteristic-two fields through the prime-field homomorphism.

These checks do not identify the permutation table with the canonical cosets:
that geometric realization remains a separate proof obligation.
Source motivation: Guralnick–Malle, Classification of 2F-modules I,
Proposition 4.3; Aschbacher–Smith K.2, printed p.453.
-/

@[expose] public section

namespace Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors
open Thompson.BinaryMatrix
open scoped BigOperators Matrix

theorem permutationImages_lt : ∀ (j : Fin 2) (i : Fin 126),
    (permutationImages j)[i.val]! < 126 := by decide +kernel

def image (j : Fin 2) (i : Fin 126) : Fin 126 :=
  ⟨(permutationImages j)[i.val]!, permutationImages_lt j i⟩

theorem packed_basis_action : ∀ (j : Fin 2) (i : Fin 126),
    rowProduct basisRows[i.val]! (actorRows j) 126 =
      basisRows[(permutationImages j)[i.val]!]! := by decide +kernel

theorem basis_mul_actor (j : Fin 2) :
    basisMatrix * actorMatrix j = fun x y => basisMatrix (image j x) y := by
  ext x y
  have h := congrArg (fun r => bit r y.val) (packed_basis_action j x)
  rw [bit_rowProduct] at h
  rw [← Fin.sum_univ_eq_sum_range] at h
  exact h

def cut : Fin 3 → ℕ := ![1, 105, 125]

private theorem packed_upper : ∀ (j : Fin 2) (m : Fin 3) (i : Fin 126),
    cut m ≤ i.val → (actorRows j)[i.val]! % 2 ^ cut m = 0 := by decide +kernel

theorem actor_upper (j : Fin 2) (m : Fin 3) (x y : Fin 126)
    (hx : cut m ≤ x.val) (hy : y.val < cut m) : actorMatrix j x y = 0 := by
  have h := congrArg (fun n => n.testBit y.val) (packed_upper j m x hx)
  simp only [Nat.testBit_mod_two_pow, hy, decide_true, Bool.true_and, Nat.zero_testBit] at h
  simp [actorMatrix, decode, bit, h]

def lowerIndex (i : Fin 104) : Fin 126 := ⟨i.val + 1, by omega⟩
def upperIndex (i : Fin 20) : Fin 126 := ⟨i.val + 105, by omega⟩

private theorem packed_lower_block : ∀ (j : Fin 2) (i : Fin 104),
    (factorRows104 j)[i.val]! = (actorRows j)[i.val + 1]! >>> 1 % 2 ^ 104 := by
  decide +kernel

private theorem packed_upper_block : ∀ (j : Fin 2) (i : Fin 20),
    (factorRows20 j)[i.val]! = (actorRows j)[i.val + 105]! >>> 105 % 2 ^ 20 := by
  decide +kernel

theorem factor104_eq_block (j : Fin 2) (x y : Fin 104) :
    factor104 j x y = actorMatrix j (lowerIndex x) (lowerIndex y) := by
  change bit (factorRows104 j)[x.val]! y.val = bit (actorRows j)[x.val + 1]! (y.val + 1)
  rw [packed_lower_block]
  simp only [bit, Nat.testBit_mod_two_pow, y.isLt, decide_true, Bool.true_and,
    Nat.testBit_shiftRight, Nat.add_comm]

theorem factor20_eq_block (j : Fin 2) (x y : Fin 20) :
    factor20 j x y = actorMatrix j (upperIndex x) (upperIndex y) := by
  change bit (factorRows20 j)[x.val]! y.val = bit (actorRows j)[x.val + 105]! (y.val + 105)
  rw [packed_upper_block]
  simp only [bit, Nat.testBit_mod_two_pow, y.isLt, decide_true, Bool.true_and,
    Nat.testBit_shiftRight, Nat.add_comm]

attribute [local irreducible] basisMatrix coordinateMatrix actorMatrix factor104 factor20

variable (K : Type*) [Field K] [CharP K 2]

theorem cast_basis_mul_actor (j : Fin 2) :
    CycleCertificate.castMatrix K basisMatrix * CycleCertificate.castMatrix K (actorMatrix j) =
      fun x y => CycleCertificate.castMatrix K basisMatrix (image j x) y := by
  rw [← map_mul]
  ext x y
  change (ZMod.castHom (dvd_refl 2) K) ((basisMatrix * actorMatrix j) x y) =
    (ZMod.castHom (dvd_refl 2) K) (basisMatrix (image j x) y)
  exact congrArg (ZMod.castHom (dvd_refl 2) K) (congrFun (congrFun (basis_mul_actor j) x) y)

/-- The table action agrees with the checked generator matrices over K. -/
theorem basisCoordinates_action (j : Fin 2) (v : Fin 126 → K) :
    basisCoordinates K (fun x => v (image j x)) =
      (CycleCertificate.castMatrix K (actorMatrix j)).mulVec (basisCoordinates K v) := by
  apply (basisCoordinates K).symm.injective
  rw [LinearEquiv.symm_apply_apply, basisCoordinates_symm_apply, Matrix.mulVec_mulVec,
    cast_basis_mul_actor]
  funext x
  change v (image j x) = (basisCoordinates K).symm (basisCoordinates K v) (image j x)
  rw [LinearEquiv.symm_apply_apply]

theorem cast_actor_upper (j : Fin 2) (m : Fin 3) (x y : Fin 126)
    (hx : cut m ≤ x.val) (hy : y.val < cut m) :
    CycleCertificate.castMatrix K (actorMatrix j) x y = 0 := by
  change (ZMod.castHom (dvd_refl 2) K) (actorMatrix j x y) = 0
  rw [actor_upper j m x y hx hy, map_zero]

theorem cast_factor104_eq_block (j : Fin 2) (x y : Fin 104) :
    CycleCertificate.castMatrix K (factor104 j) x y =
      CycleCertificate.castMatrix K (actorMatrix j) (lowerIndex x) (lowerIndex y) :=
  congrArg (ZMod.castHom (dvd_refl 2) K) (factor104_eq_block j x y)

theorem cast_factor20_eq_block (j : Fin 2) (x y : Fin 20) :
    CycleCertificate.castMatrix K (factor20 j) x y =
      CycleCertificate.castMatrix K (actorMatrix j) (upperIndex x) (upperIndex y) :=
  congrArg (ZMod.castHom (dvd_refl 2) K) (factor20_eq_block j x y)

end Representation.SU3.FiveSmallModules.Degrees.TrivialCalculation.MiddleFactors
