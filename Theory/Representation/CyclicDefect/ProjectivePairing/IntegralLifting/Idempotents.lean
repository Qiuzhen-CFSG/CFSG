module

public import Theory.RingTheory.AdicIdempotentLift
public import Theory.Representation.CyclicDefect.ProjectivePairing.IntegralLifting.Contracts
public import Mathlib.LinearAlgebra.Matrix.StdBasis

/-!
# Lifting finite group-algebra matrix idempotents

For a finite group `G`, a surjective coefficient map `f : R → k`, and
`R` complete for `ker f`, every idempotent matrix over `k[G]` lifts to an
idempotent matrix over `R[G]`. The reduction is the literal ring map
`(MonoidAlgebra.mapRingHom G f).mapMatrix`.

The standard group-algebra matrix basis identifies its kernel with
`(ker f) A` and transfers coefficient completeness to the matrix algebra.
The complete-algebra correction theorem then supplies the lift. Applied to
`CompleteCoefficientRing`, this discharges `MatrixIdempotentsLift` without
any additional lifting premise. The construction of the coefficient ring
and the realization of the resulting projective summand remain separate.

Source: Feit, *The Representation Theory of Finite Groups*, I.12.3--4,
and its application to projective modules in I.13 and I.17.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.ProjectivePairing.IntegralLifting
open AdicIdempotentLift Module
variable {R k G : Type*} [CommRing R] [Field k] [Group G] [Fintype G]

omit [Group G] [Fintype G] in
private lemma matrix_basis_repr (n : ℕ)
    (x : Matrix (Fin n) (Fin n) (MonoidAlgebra R G)) (i j : Fin n) (g : G) :
    ((MonoidAlgebra.basis G R).matrix (Fin n) (Fin n)).repr x (i, j, g) =
      (x i j).coeff g := by
  rfl

private lemma matrix_mem_smul_ker (f : R →+* k) (n : ℕ)
    (x : Matrix (Fin n) (Fin n) (MonoidAlgebra R G)) :
    x ∈ RingHom.ker f • (⊤ : Submodule R (Matrix (Fin n) (Fin n) (MonoidAlgebra R G))) ↔
      (MonoidAlgebra.mapRingHom G f).mapMatrix x = 0 := by
  rw [mem_smul_top_iff ((MonoidAlgebra.basis G R).matrix (Fin n) (Fin n))]
  constructor
  · intro hx
    ext i j g
    simpa [matrix_basis_repr, RingHom.mem_ker] using hx (i, j, g)
  · intro hx ⟨i, j, g⟩
    have h := congrArg (fun z : Matrix (Fin n) (Fin n) (MonoidAlgebra k G) =>
      (z i j).coeff g) hx
    simpa [matrix_basis_repr, RingHom.mem_ker] using h

/-- Finite group-algebra matrices lift idempotents over an adically complete coefficient ring. -/
theorem matrixIdempotentsLift_of_complete (f : R →+* k) (hf : Function.Surjective f)
    [IsAdicComplete (RingHom.ker f) R] : MatrixIdempotentsLift f G := by
  rw [matrixIdempotentsLift_iff]
  intro n e he
  let b := (MonoidAlgebra.basis G R).matrix (Fin n) (Fin n)
  let : IsAdicComplete (RingHom.ker f)
      (Matrix (Fin n) (Fin n) (MonoidAlgebra R G)) := complete_of_basis _ b
  have hsurj : Function.Surjective (MonoidAlgebra.mapRingHom G f) :=
    MonoidAlgebra.map_surjective f.toAddMonoidHom hf
  choose a ha using fun i j => hsurj (e i j)
  let x : Matrix (Fin n) (Fin n) (MonoidAlgebra R G) := a
  have hmap : (MonoidAlgebra.mapRingHom G f).mapMatrix x = e := funext fun i => funext (ha i)
  have herr : x * x - x ∈ RingHom.ker f •
      (⊤ : Submodule R (Matrix (Fin n) (Fin n) (MonoidAlgebra R G))) := by
    rw [matrix_mem_smul_ker, map_sub, map_mul, hmap, he.eq, sub_self]
  obtain ⟨p, hp, hpx⟩ := exists_idempotent (RingHom.ker f) x herr
  refine ⟨p, hp, ?_⟩
  have h := (matrix_mem_smul_ker f n (p - x)).mp hpx
  rw [map_sub, hmap, sub_eq_zero] at h
  exact h

/-- The complete coefficient system supplies the actual matrix-idempotent lifting contract. -/
theorem CompleteCoefficientRing.matrixIdempotentsLift {m : ℕ} {L : CyclicRootLift k m}
    (C : CompleteCoefficientRing L) : MatrixIdempotentsLift C.residue G := by
  let : IsAdicComplete (RingHom.ker C.residue) C.Coeff := by
    rw [C.residue_ker]
    infer_instance
  exact matrixIdempotentsLift_of_complete C.residue C.residue_surjective

end Representation.CyclicDefect.ProjectivePairing.IntegralLifting
