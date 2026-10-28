module

public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.FactorMatrices.F0
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.FactorMatrices.F1
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.FactorMatrices.F2
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.FactorMatrices.F3
public import Theory.Representation.Mathieu.M23DegreeSpectrum.InducedHeads.CocodeFiltration.FactorMatrices.F4
import Mathlib.Tactic.FinCases

/-!
# Simplicity of the five M23 cocode quotient matrix pairs

A rank-one operator and full row and column orbit bases certify that each
literal pair generates the entire binary matrix algebra. The subalgebra of
operators preserving a common invariant subspace is consequently the whole
algebra, so that subspace is zero or the whole space.

These certificates discharge `SimpleMatrices` in `filtration_of_certificates`;
the independent native generator comparison remains with that consumer.
The degrees are 120, 11, 44, 11, 44, with separate certificates for every pair.
The finite identities are checked by the kernel, with no character-table,
absolute-irreducibility, or degree-catalogue premise.

Source application: Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, M23 paragraph, journal p.366 / manuscript p.16.
This explicit filtration is an independently sufficient computation, rather
than a statement of that paragraph. See `FactorMatrices/source/README.md`.
-/

@[expose] public section
open Matrix
namespace Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration

/-- The two literal matrices in each diagonal block generate all matrices. -/
theorem fullFactorAlgebra (t : Factor)
    (Q : Subalgebra (ZMod 2)
      (Matrix (Fin (degree t)) (Fin (degree t)) (ZMod 2)))
    (hA : ∀ j : Fin 2, factorMatrix t j ∈ Q) : Q = ⊤ := by
  fin_cases t
  · exact FactorMatrices.F0.full Q hA
  · exact FactorMatrices.F1.full Q hA
  · exact FactorMatrices.F2.full Q hA
  · exact FactorMatrices.F3.full Q hA
  · exact FactorMatrices.F4.full Q hA

private theorem simple_of_full {n : ℕ} (A : Fin 2 → Matrix (Fin n) (Fin n) (ZMod 2))
    (hfull : ∀ Q : Subalgebra (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)),
      (∀ j, A j ∈ Q) → Q = ⊤)
    (S : Submodule (ZMod 2) (Fin n → ZMod 2))
    (hS : ∀ j v, v ∈ S → (A j).mulVec v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  classical
  let Q : Subalgebra (ZMod 2) (Matrix (Fin n) (Fin n) (ZMod 2)) := {
    carrier := {M | ∀ v, v ∈ S → M.mulVec v ∈ S}
    zero_mem' := by intro v _; simp
    one_mem' := by intro v hv; simpa using hv
    add_mem' := by
      intro M N hM hN v hv
      simpa only [add_mulVec] using S.add_mem (hM v hv) (hN v hv)
    mul_mem' := by
      intro M N hM hN v hv
      rw [← mulVec_mulVec]
      exact hM _ (hN v hv)
    algebraMap_mem' := by
      intro c v hv
      simpa only [Algebra.algebraMap_eq_smul_one, smul_mulVec, one_mulVec]
        using S.smul_mem c hv }
  have hQ : Q = ⊤ := hfull Q hS
  by_cases hb : S = ⊥
  · exact Or.inl hb
  right
  obtain ⟨v, hv, hv0⟩ := S.ne_bot_iff.mp hb
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    apply hv0
    ext i
    exact not_ne_iff.mp (not_exists.mp h i)
  apply top_unique
  intro w _
  let M : Matrix (Fin n) (Fin n) (ZMod 2) :=
    fun x y => if y = i then w x * (v i)⁻¹ else 0
  have hM : M ∈ Q := by rw [hQ]; trivial
  have he : M.mulVec v = w := by
    ext x
    simp [M, mulVec, dotProduct, ite_mul, mul_assoc, hi]
  rw [← he]
  exact hM v hv

/-- Every binary common invariant subspace of each factor pair is zero or whole. -/
theorem simpleMatrices : SimpleMatrices := by
  intro t S hS
  exact simple_of_full (factorMatrix t) (fullFactorAlgebra t) S hS

end Representation.MathieuSmall.M23DegreeSpectrum.InducedHeads.CocodeFiltration
