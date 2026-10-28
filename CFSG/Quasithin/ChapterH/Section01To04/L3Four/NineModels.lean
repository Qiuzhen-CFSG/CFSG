module

public import CFSG.Quasithin.ChapterH.Section01To04.L3Four.Source

/-!
# The two absolute models in binary dimension nine

The exhaustive five-word list and its exact Schur degrees show that dimension
nine is equivalent to the two equal natural/dual words. Both directions keep
the actual extension equivalence, and the source application uses the literal
cover of F*(M). Identifying these words with the published descended Hermitian
tensor requires a further equivalence; this module does not replace that step
by a dimension comparison.

Source: Aschbacher–Smith H.4.7, printed p.382 of refs/quasithin.pdf.
-/

public section

set_option backward.isDefEq.respectTransparency false
open scoped MatrixGroups TensorProduct
open Representation Representation.SL3.BinaryDefiningFactors Theory.GroupTheory
open CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
  (SchurField SplittingField)
namespace CFSG.Quasithin.ChapterH.Section01To04.L3Four
variable {F V : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) SL(3,F) V) [IsIrreducible ρ]

theorem nine_iff_natural_pair_model (hcard : Nat.card F = 4)
    (hcenter : Subgroup.center SL(3,F) ≤ ρ.ker) (hact : ∃ g, ρ g ≠ 1) :
    Module.finrank (ZMod 2) V = 9 ↔
      ∃ ι : F →+* SplittingField ρ,
        Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
          (wordRep ι [.natural,.natural])) ∨
        Nonempty ((extendScalars (SplittingField ρ) ρ.endFieldRep).Equiv
          (wordRep ι [.dual,.dual])) := by
  constructor
  · intro hd9
    obtain ⟨ι,b,c,hbc,he,_,hd⟩ := exists_nontrivial_binary_pair_model ρ hcard hcenter hact
    rcases hbc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨ι,Or.inl he⟩
    · exact ⟨ι,Or.inr he⟩
    all_goals norm_num [wordDegree, Factor.dimension, hd9,
      show Factor.trivial ≠ Factor.adjoint by decide,
      show Factor.adjoint ≠ Factor.trivial by decide] at hd
  · rintro ⟨ι, he | he⟩
    all_goals
      have hs := pair_schurDegree ρ hcard ι _ _ he
      obtain ⟨e⟩ := he
      rw [finrank_eq_schurDegree_mul 2 ρ (SplittingField ρ),
        e.toLinearEquiv.finrank_eq, finrank_wordSpace, hs]
      norm_num [wordDegree, Factor.dimension]

variable {M : Type*} [Group M]

theorem source_nine_iff_natural_pair_model (hcard : Nat.card F = 4)
    (e : PSL(3,F) ≃* generalizedFitting M) (σ : Representation (ZMod 2) M V)
    [IsIrreducible (σ.comp (generalizedFitting M).subtype)] (hσ : Function.Injective σ) :
    Module.finrank (ZMod 2) V = 9 ↔
      ∃ ι : F →+* SplittingField (coverRep e σ),
        Nonempty ((extendScalars (SplittingField (coverRep e σ)) (coverRep e σ).endFieldRep).Equiv
          (wordRep ι [.natural,.natural])) ∨
        Nonempty ((extendScalars (SplittingField (coverRep e σ)) (coverRep e σ).endFieldRep).Equiv
          (wordRep ι [.dual,.dual])) :=
  nine_iff_natural_pair_model (coverRep e σ) hcard
    (le_of_eq (coverRep_ker e σ hσ).symm) (coverRep_nontrivial e σ hσ)

end CFSG.Quasithin.ChapterH.Section01To04.L3Four
