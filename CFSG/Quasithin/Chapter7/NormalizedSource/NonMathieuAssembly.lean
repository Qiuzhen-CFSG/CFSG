module

public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuAssemblyInputs
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuAssemblyPSL2

/-!
# Conditional assembly of the surviving marked orthogonal action

Split the exact source families on the unchanged representation. The unitary,
Suzuki and Hermitian exclusions remove their respective rows; the proved PSL₂
dispatch returns the marked orthogonal model with exponent greater than one.
The family sieve and exclusions remain explicit source obligations.

Source: Aschbacher--Smith,3.2.9,7.0.1 and12.2.2, printed pp.582--583,695,795.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuAssembly

variable {A E : Type*} [Group A] [Finite A] [AddCommGroup E] [Module (ZMod 2) E]
  [FiniteDimensional (ZMod 2) E] {ρ : Representation (ZMod 2) A E} {Q : Subgroup A}

/-- Conditional source assembly with the PSL₂ comparison discharged.
The family sieve and the other source exclusions remain explicit. -/
theorem orthogonal_of_families (hs : ChapterK.RankOne.SourceHypotheses ρ Q)
    (hnon : ¬ IsFFModule (normalizerRepresentation (ρ.comp Q.subtype)))
    (hfamilies : SourceFamilies hs)
    (hunitary : ∀ s : ℕ, 2 ≤ s →
      ClassicalGroup.IsPSU (Q ⧸ center Q) 3 (2 ^ s) → False)
    (hsuzuki : ∀ m : ℕ, 1 ≤ m →
      Nonempty ((Q ⧸ center Q) ≃* SuzukiMatrixGroup m) → False)
    (hhermitian : HermitianRow hs → False) : OrthogonalMinusAlternative ρ Q := by
  rcases hfamilies with ⟨r, hr, hq⟩ | ⟨s, hs, hq⟩ | ⟨m, hm, hq⟩ | hh
  · exact orthogonal_of_psl2 hs hnon hr hq
  · exact (hunitary s hs hq).elim
  · exact (hsuzuki m hm hq).elim
  · exact (hhermitian hh).elim

end CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuAssembly
