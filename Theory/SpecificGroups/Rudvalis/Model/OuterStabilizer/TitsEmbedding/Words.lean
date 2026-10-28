module

public import Theory.SpecificGroups.Rudvalis.Model.PrimitiveCertificates
public import Theory.SpecificGroups.Tits.Presentation
public import Theory.GroupTheory.WordSubgroup
import Mathlib.Tactic.FinCases

/-!
# Candidate Parrott generators in the Rudvalis point stabilizer

These ten explicit words in `PrimitiveData.s` and `PrimitiveData.t` lie in
Rudvalis's stabilizer of 0. The first is nonidentity. The separate relator
certificate must establish all 37 relations before these words can induce
a homomorphism from the Tits group; no group identification is asserted here.

The words were found by an untrusted GAP isomorphism search between the
Parrott permutation image and the derived subgroup of `⟨s,t⟩`. Multiplication
uses the inverse point-action convention of `Model.PermutationData`, so word
order is preserved. Sources: the ATLAS data cited there; Parrott (1972), §5,
p.683, as transcribed in `refs/original/n-group-global/parrott-tits-presentation.md`;
and GLS3 Table 5.3r, printed p.279. Discovery data are in the adjacent `source/`.
-/

namespace Rudvalis.OuterStabilizer.TitsEmbedding
open Theory.GroupTheory

/-- The two certified stabilizer words and their inverses. -/
@[expose] public def letter : Fin 4 → Model
  | 0 => PrimitiveData.s
  | 1 => PrimitiveData.t
  | 2 => PrimitiveData.s⁻¹
  | 3 => PrimitiveData.t⁻¹

/-- Word witnesses for the ten generators, in Parrott's original ordering. -/
@[expose] public def word : Tits.ParrottGenerator → List (Fin 4)
  | .r1 => [3, 2, 3, 2, 1, 0, 3, 2, 1, 0, 3, 2, 1, 1, 2, 2, 1, 1, 1, 0]
  | .r8 => [2, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 2, 3, 2, 3, 0, 1, 2, 2, 2, 2, 3, 2, 2, 2, 2, 2, 2, 2, 1, 0, 1, 1, 2, 2, 1, 2, 2, 1, 2]
  | .s1 => [3, 3, 2, 3, 2, 3, 2, 3, 2, 1, 1, 1, 2, 2, 3, 2, 2, 3, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 3, 0, 1, 0, 1, 1, 2, 2, 1, 0, 0, 0, 0]
  | .s2 => [2, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 2, 3, 2, 3, 0, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 3, 0, 1, 0, 1, 1, 1, 1, 2, 3, 2, 2, 1, 0, 0, 3, 0, 3, 2, 3, 2, 3, 2, 3]
  | .s3 => [2, 1, 1, 0, 1, 2, 3, 2, 3, 2, 1, 0, 0, 1, 0, 0, 3, 3, 2, 3, 2, 2, 3, 2, 3, 2, 3, 3, 2, 2, 3, 0]
  | .s4 => [1, 2, 3, 2, 3, 0, 1, 2, 2, 2, 3, 0, 1, 1, 1, 0, 3, 2, 2, 3, 3, 3, 0, 1, 1, 2, 3, 0, 1, 2, 3, 2]
  | .s5 => [0, 3, 0, 0, 1, 2, 2, 3, 2, 1, 2, 2, 2, 1, 2, 2, 2, 1, 1, 2, 2, 3, 2, 2, 3, 2, 3, 2, 3, 3, 2, 2, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0, 1, 1]
  | .s6 => [2, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 2, 3, 2, 3, 0, 1, 2, 2, 2, 1, 2, 2, 3, 2, 2, 3, 0, 1, 0, 0, 1, 0, 1, 1, 0, 0, 3, 2, 1, 0, 1, 2, 2]
  | .s7 => [3, 3, 2, 3, 2, 3, 2, 3, 2, 1, 2, 1, 0, 0, 1, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 1, 2, 2, 3, 2, 2, 3, 0, 1, 0, 1, 0, 1, 1, 2, 3, 2, 2, 1, 1, 0, 1, 2, 2, 2, 2, 1, 0, 1, 1, 1, 1, 0]
  | .s8 => [1, 1, 2, 2, 3, 2, 2, 3, 0, 1, 0, 1, 0, 3, 0, 0, 0, 3, 3, 0, 1, 0, 0, 0, 3, 2, 3, 3, 3, 3, 2, 2, 2, 2]

/-- Concrete candidate images in the actual Rudvalis carrier. -/
@[expose] public def assignment (i : Tits.ParrottGenerator) : Model :=
  evalWord letter (word i)

private theorem letter_mem (i : Fin 4) :
    letter i ∈ MulAction.stabilizer Model (0 : Fin 4060) := by
  have hs : PrimitiveData.s ∈ MulAction.stabilizer Model (0 : Fin 4060) :=
    PrimitiveData.s_fix
  have ht : PrimitiveData.t ∈ MulAction.stabilizer Model (0 : Fin 4060) :=
    PrimitiveData.t_fix
  fin_cases i
  · exact hs
  · exact ht
  · exact (MulAction.stabilizer Model (0 : Fin 4060)).inv_mem hs
  · exact (MulAction.stabilizer Model (0 : Fin 4060)).inv_mem ht

/-- Every candidate generator fixes the distinguished point. -/
public theorem assignment_mem_stabilizer (i : Tits.ParrottGenerator) :
    assignment i ∈ MulAction.stabilizer Model (0 : Fin 4060) := by
  change evalWord letter (word i) ∈ _
  generalize word i = w
  induction w with
  | nil => exact (MulAction.stabilizer Model (0 : Fin 4060)).one_mem
  | cons j w ih => exact (MulAction.stabilizer Model (0 : Fin 4060)).mul_mem (letter_mem j) ih

/-- The realization cannot induce the trivial homomorphism. -/
public theorem assignment_r1_ne_one : assignment .r1 ≠ 1 := by
  have hn : assignment .r1 • (1 : Fin 4060) ≠ (1 : Fin 4060) := by decide +kernel
  intro he
  apply hn
  rw [he, one_smul]

end Rudvalis.OuterStabilizer.TitsEmbedding
