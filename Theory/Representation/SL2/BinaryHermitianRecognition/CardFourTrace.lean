module

public import Theory.Representation.SL2.BinaryHermitianRecognition.HighestWeight
public import Theory.Representation.EndFieldFrobenius
public import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# The Schur field of the binary weight-three SL₂(4) module

The two Frobenius factors have character `trace(g)^3`. Over a field of four
elements its square is itself. The actual Schur-field traces span that field,
so an irreducible binary action with this highest weight has Schur degree one.
This excludes a spurious eight-dimensional case without any degree bound.

The comparison retains the actual scalar-extension intertwiner. It is the
field-four specialization of the Schur-field descent in GLS3, §2.8.8.
-/

public section
open scoped MatrixGroups MonoidAlgebra TensorProduct
open Representation Representation.SL2
namespace Representation.SL2.BinaryHermitian

/-- The pair with Frobenius exponents zero and one has cubic trace. -/
theorem pair_character_one_zero {K L : Type*} [Field K] [Field L] [CharP L 2] [PerfectRing L 2]
    (e : K →+* L) (g : SL(2,K)) :
    (BinaryHermitian.pair e 1 0).character g = (e (g.val 0 0 + g.val 1 1)) ^ 3 := by
  classical
  rw [Representation.character, LinearMap.trace_eq_matrix_trace L (Matrix.stdBasis L (Fin 2) (Fin 2))]
  simp [Matrix.trace, LinearMap.toMatrix_apply, Matrix.stdBasis, BinaryHermitian.pair_apply,
    Fin.sum_univ_two, Fintype.sum_prod_type, Matrix.mul_apply]
  have hsq (a b : L) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
    simpa using add_pow_char_pow a b 2 1
  conv_rhs => rw [pow_succ, hsq]
  ring

/-- Over the field of four elements the pair character is binary-valued. -/
theorem pair_character_sq_of_card_four {K L : Type*} [Field K] [Finite K] [Field L] [CharP L 2] [PerfectRing L 2]
    (e : K →+* L) (hc : Nat.card K = 4) (g : SL(2,K)) :
    ((BinaryHermitian.pair e 1 0).character g) ^ 2 =
      (BinaryHermitian.pair e 1 0).character g := by
  have h4 (x : K) : x ^ 4 = x := by
    let := Fintype.ofFinite K
    simpa only [Fintype.card_eq_nat_card, hc] using FiniteField.pow_card x
  have h6 (x : K) : (x ^ 3) ^ 2 = x ^ 3 := by
    calc
      (x ^ 3) ^ 2 = x ^ 4 * x ^ 2 := by ring
      _ = x ^ 3 := by rw [h4]; ring
  rw [pair_character_one_zero, ← map_pow, ← map_pow, h6]

variable {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) SL(2,K) V) [ρ.IsIrreducible]

/-- Weight three over a field of four elements forces the actual Schur field
to have degree one over the binary prime field. No dimension bound is assumed. -/
theorem schur_degree_one_of_highestWeight_three
    (hc : Nat.card K = 4)
    (e : K →+* AlgebraicClosure (Module.End (ZMod 2)[SL(2,K)] ρ.asModule))
    (h : Nonempty ((extendScalars (AlgebraicClosure
      (Module.End (ZMod 2)[SL(2,K)] ρ.asModule)) ρ.endFieldRep).Equiv
        (highestWeightSpan e 3).toRepresentation)) :
    Module.finrank (ZMod 2) (Module.End (ZMod 2)[SL(2,K)] ρ.asModule) = 1 := by
  let E := Module.End (ZMod 2)[SL(2,K)] ρ.asModule
  let F := AlgebraicClosure E
  let : CharP F 2 := charP_of_injective_ringHom e.injective 2
  obtain ⟨u⟩ := BinaryHermitian.pair_equiv_highestWeightSpan e 1 0
    (by simpa using hc) (by decide)
  have hχ (g : SL(2,K)) : (BinaryHermitian.pair e 1 0).character g =
      algebraMap E F (ρ.endFieldRep.character g) := by
    rw [congrFun (Representation.char_iso u) g]
    change (highestWeightSpan e 3).toRepresentation.character g = _
    rw [← congrFun (Representation.char_iso h.some) g]
    exact LinearMap.trace_baseChange (ρ.endFieldRep g) F
  apply Nat.dvd_one.mp
  apply (endFieldRep_trace_frobenius_iff 2 ρ 1).mp
  intro g
  change ρ.endFieldRep.character g ^ 2 = ρ.endFieldRep.character g
  apply (algebraMap E F).injective
  rw [map_pow, ← hχ]
  simpa using pair_character_sq_of_card_four e hc g

end Representation.SL2.BinaryHermitian
