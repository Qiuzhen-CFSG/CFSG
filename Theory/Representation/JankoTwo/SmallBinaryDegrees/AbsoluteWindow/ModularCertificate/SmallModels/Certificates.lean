module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Construction
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels.Parameters

/-!
# Consumer of the two numerical Hall--Janko matrix certificates

A parameter certificate asserts the five literal relations, full matrix-algebra
span, and one nonbinary word trace for specified code matrices. The numerical
certificate producers must prove all three clauses. This module constructs
actual actions from those clauses, using presentation descent, and proves
irreducibility and inequivalence for the two coefficient embeddings.

These are conditional consumer theorems, not completed ATLAS model certificates.
Source: the J2G1-f4r6aB0 and J2G1-f4r14aB0 data and the J2G1-P2 presentation;
see ../Source.md and source/README.md.
-/

@[expose] public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
open Sporadic.LeechRelated.J2 G2FourModule.Embedding.InnerRealization Arithmetic
universe v

def ParameterCertificate {n : ℕ} (A B : CodeMatrix n) (w : List Bool) (c : Fin 4) : Prop :=
  ∀ (F : Type v) [Field F] [CharP F 2] (t : F), t ^ 2 = t + 1 →
    MatrixRelations (evalMatrix t A) (evalMatrix t B) ∧
    Algebra.adjoin F ({evalMatrix t A, evalMatrix t B} :
      Set (Matrix (Fin n) (Fin n) F)) = ⊤ ∧
    (wordValue (evalMatrix t A) (evalMatrix t B) w).trace = coefficient t c

/-- Frobenius transports the entire descended action, on the original carrier.
The two relation proofs can be supplied independently by the same certificate. -/
theorem matrixAction_frobenius {n : ℕ} {F : Type*} [Field F] [CharP F 2]
    (hp : Function.Injective Presentation.toCarrier) (A B : CodeMatrix n) (t : F)
    (hr : MatrixRelations (evalMatrix t A) (evalMatrix t B))
    (hr' : MatrixRelations (evalMatrix (t ^ 2) A) (evalMatrix (t ^ 2) B))
    (g : Carrier) :
    matrixAction hp (evalMatrix (t ^ 2) A) (evalMatrix (t ^ 2) B) hr' g =
      (matrixAction hp (evalMatrix t A) (evalMatrix t B) hr g).map (frobenius F 2) := by
  let f : Matrix (Fin n) (Fin n) F →+* Matrix (Fin n) (Fin n) F :=
    RingHom.mapMatrix (frobenius F 2)
  have he : matrixAction hp (evalMatrix (t ^ 2) A) (evalMatrix (t ^ 2) B) hr' =
      f.toMonoidHom.comp (matrixAction hp (evalMatrix t A) (evalMatrix t B) hr) := by
    apply MonoidHom.eq_of_eqOn_dense GeneratorPair.closure_pair_eq_top
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · simp only [MonoidHom.comp_apply, matrixAction_a]
      exact eval_frobenius t A
    · rw [Set.mem_singleton_iff] at hx
      subst x
      simp only [MonoidHom.comp_apply, matrixAction_b]
      exact eval_frobenius t B
  exact DFunLike.congr_fun he g

theorem exists_pair_of_certificate {n : ℕ} [NeZero n]
    (hp : Function.Injective Presentation.toCarrier)
    (A B : CodeMatrix n) (w : List Bool) (c : Fin 4) (hc : c = 2 ∨ c = 3)
    (hcert : ParameterCertificate.{v} A B w c)
    (F : Type v) [Field F] [IsAlgClosed F] [CharP F 2] :
    ∃ ρ σ : Representation F Carrier (Fin n → F),
      IsIrreducible ρ ∧ IsIrreducible σ ∧ IsEmpty (ρ.Equiv σ) := by
  obtain ⟨t, ht⟩ := exists_parameter (F := F)
  obtain ⟨hr, hd, htr⟩ := hcert F t ht
  obtain ⟨hr', hd', htr'⟩ := hcert F (t ^ 2) (square_parameter t ht)
  refine ⟨action hp _ _ hr, action hp _ _ hr', action_irreducible hp _ _ hr hd,
    action_irreducible hp _ _ hr' hd', ⟨?_⟩⟩
  intro e
  have he := congrFun (Representation.char_iso e) (wordValue GeneratorPair.a GeneratorPair.b w)
  rw [character_word, character_word, htr, htr'] at he
  exact coefficient_ne_square t ht c hc he

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.ModularCertificate.SmallModels
