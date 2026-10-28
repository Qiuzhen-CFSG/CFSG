module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.MarkedA312
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.MarkedNonternary
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.SourceOddThreeExtension

/-!
# The actual marked embedding in the canonical radical normalizer

The full known-simple catalogue and the nonternary exclusions leave a signed
odd-ternary model for the original containing quotient image. The signed
extension theorem constructs the elementary kernel and SL₂ quotient on the
original residual image, including the projective and central-cover cases.
This discharges the marked A.3.12 premise used by characteristic-normalizer
control, before any case-ten parameter or Sylow-kernel deductions are used.

Source: Aschbacher–Smith, A.3.12 and the proof of 1.3.8, printed pp.47–48, 513.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A.3.12 for every original escaping characteristic-normalizer pair. -/
theorem markedA312Input_knownSimple (p : ℕ) (L : Subgroup G) (T : Sylow 2 G) :
    MarkedA312Input p L T := by
  intro C K h
  obtain ⟨_, q, hq, ho, unitary, hm⟩ := h.containing_model_signed_oddThree
  exact Embedding.FiveCase.SourceData.odd_ternary_embedding hq ho h unitary hm

end CFSG.Quasithin.Chapter1.RadicalNormalizers
