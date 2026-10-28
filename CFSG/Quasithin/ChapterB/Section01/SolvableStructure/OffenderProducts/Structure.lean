module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.OffenderProducts
public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.ThreeConjugates.StructureInput

/-!+# The concrete factor consequences in the B.1.12 input

The natural factor witness and ratio one now supply every remaining field of
`ThreeConjugates.SolvableFFStructure`. The offender product uses the literal
inclusion-images of Sylow subgroups, and the stable product uses the original
definition of stability. This constructs the structure consumed by the
cyclic-three argument without assuming either classification conclusion.

The source-theorem owner must still construct the factor witness and prove
ratio one from the solvable FF hypotheses; this module asserts no existence
result for those inputs.

Source: Aschbacher–Smith, B.1.8(3)–(5), printed p. 70 (PDF p. 81), as used
in B.1.12, printed p. 73 (PDF p. 84).
-/

public section

open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.SolvableFFFactors

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
  (d : SolvableFFFactors ρ)

/-- Assemble the exact B.1.8 consequence record consumed by B.1.12 from the
concrete factors and ratio one. No offender-classification premise remains. -/
def toSolvableFFStructure (hfaith : Function.Injective ρ) (hq : quadraticRatio ρ = 1) :
    ThreeConjugates.SolvableFFStructure ρ where
  toSolvableFFFactors := d
  ratio_one := hq
  best_rank_eq A hA :=
    ((isBestOffender_iff_of_not_strong ρ (not_strong_of_ratio_eq_one hq) A).mp hA).2
  offender_product A := by
    rw [d.isBestOffender_iff_sylowProduct hfaith hq A]
    constructor
    · intro hA
      have hne := hA.ne_bot d
      obtain ⟨B, hB, _, he⟩ := hA
      refine ⟨hne, B, fun i => ?_, he⟩
      rcases hB i with h | ⟨S, h⟩
      · exact Or.inl h
      · exact Or.inr ⟨S, h.symm⟩
    · rintro ⟨hne, B, hB, he⟩
      refine ⟨B, fun i => ?_, ?_, he⟩
      · rcases hB i with h | ⟨S, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨S, h.symm⟩
      · by_contra hn
        push Not at hn
        apply hne
        rw [he]
        simp only [hn, iSup_bot]
  stable_product P hP :=
    ⟨d.stableFactorSet P, d.stable_generatedBy_eq hfaith hq hP⟩

end CFSG.Quasithin.ChapterB.SolvableFFFactors
