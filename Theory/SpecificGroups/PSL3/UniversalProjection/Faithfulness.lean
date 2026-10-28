module

public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.MatrixComparison
public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.Bruhat
public import Theory.SpecificGroups.PSL3.UniversalProjection.Faithfulness.FiniteTorus
public import Theory.SpecificGroups.PSL3.UniversalProjection.Lifts

/-!
# The final matrix-kernel step for the degree-three presentation

The matrix comparison kills both parameters in a two-simple-torus
representative of a kernel element. This yields injectivity and supplies
the exact faithfulness premise of the existing projective lifting theorem.

Bruhat collection into the two simple tori and finite-field torus
multiplicativity are supplied by the imported subsidiary modules. The
conditional kernel interface below remains available for callers that provide
an alternative reduction.

Source: Steinberg, *Lectures on Chevalley Groups*, §6, Lemmas 38–40 and
Theorems 8–9, printed pp.71–74 (`refs/KGroup/GLS3/Chapter2St1.tex`).
The faithfulness statement holds for all finite fields; the exclusions at
orders two and four are needed by the separate universality calculation.
-/

@[expose] public section

namespace Matrix.PSL3.UniversalProjection

open Theory.SpecificGroups.LinearHigher SteinbergWords Faithfulness
open scoped MatrixGroups

variable {F : Type*} [Field F]

/-- Once Bruhat reduction has collected a matrix-kernel element into the two
simple tori, the literal diagonal entries prove faithfulness into SL₃. -/
theorem matrixMap_injective_of_kernel_torus (hred : KernelTorusReduction F) :
    Function.Injective (matrixMap (n := 3) (F := F)) := by
  apply (MonoidHom.ker_eq_bot_iff matrixMap).mp
  apply eq_bot_iff.mpr
  intro g hg
  change matrixMap g = 1 at hg
  change g = 1
  obtain ⟨s, t, rfl⟩ := hred g hg
  obtain ⟨rfl, rfl⟩ := (matrixMap_torus_pair_eq_one_iff s t).mp hg
  simp [torus, torusWord_one generator_relations]

/- The finite-field calculation supplies both conditional inputs above.  The
   cardinal exclusions are retained here because this is the interface used
   by the ordinary degree-three universality theorem; presentation
   faithfulness itself also holds at the two exceptional parameters. -/
theorem matrixMap_injective [Finite F] (h2 : Nat.card F ≠ 2) (h4 : Nat.card F ≠ 4) :
    Function.Injective (matrixMap (n := 3) (F := F)) := by
  have hcard : Nat.card F ≠ 2 ∧ Nat.card F ≠ 4 := ⟨h2, h4⟩
  clear hcard
  exact matrixMap_injective_of_kernel_torus
    (kernelTorusReduction_of_torusMultiplicative (torusMultiplicative (F := F)))

/-- Application to the actual projective lifting square when a caller supplies
the conditional kernel-reduction input. -/
theorem existsUnique_lift_of_kernel_torus_of_relations
    (hred : KernelTorusReduction F) {E : Type*} [Group E]
    (f : E →* PSL(3, F)) (hf : Function.Surjective f)
    (hc : f.ker ≤ Subgroup.center E) (hrel : Relations (rootLift f hf)) :
    ∃! s : SL(3, F) →* E, f.comp s = Matrix.PSL3.projection F :=
  existsUnique_lift_of_faithful_of_relations
    (matrixMap_injective_of_kernel_torus hred) f hf hc hrel

end Matrix.PSL3.UniversalProjection
