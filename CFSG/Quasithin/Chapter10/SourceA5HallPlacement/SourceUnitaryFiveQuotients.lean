module

public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.SourceOddQuotientControl
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.Flag.Sylow

/-!
# The PSU₅(4) row of the original odd-normalizer quotient condition

The literal projective unitary flag group is a Sylow two-subgroup. Its
Frattini quotient has two invariant sections of order sixteen, distinguished
by the span of involution images. Their automorphism actions give two normal
kernels with solvable intersection and quotient orders avoiding 25.

Changing the Hermitian form and transporting Sylow subgroups supplies the
intrinsic row for every group marked as PSU₅(4). The final adapter removes
this row from the exact original odd-normalizer source condition, retaining
only its independent PSU₄ family.

Source: Aschbacher--Smith 4.4.10--11, printed p.621, and the unitary-five
matrix flag in F.1.12(7), printed pp.263--264.
-/

public section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.UnitaryFive
namespace CFSG.Quasithin.Chapter10
universe u

/-- The intrinsic PSU₅(4) Sylow automorphism quotient condition, with no
additional coordinate, flag, normalizer or automorphism premise. -/
theorem source_psu5_four_sylow_quotients
    {S : Type u} [Group S] [Finite S] (hS : ClassicalGroup.IsPSU S 5 4) :
    ∃ P : Sylow 2 S, HasSolvableQuotientPair 25 (MulAut P) := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hS
  let : CharP F 2 := charP_two_of_card_sixteen hcard
  obtain ⟨f⟩ := projective_equiv_identity_four J hcard hconj
  let P : Sylow 2 S := Classical.choice inferInstance
  exact ⟨P, Flag.sylow_solvableQuotientPair_four
    (HermitianForm.IdentityGram.identityGram J) hcard hconj rfl (e.trans f) P⟩

/-- Only the binary PSU₄ family remains in the exact unitary condition used
by the original odd-normalizer, full-Hall and generation-bound consumers. -/
theorem source_oddUnitarySylowQuotients_of_psu4
    (hfour : ∀ (S : Type u) [Group S] [Finite S], IsSimpleGroup S →
      ∀ f : ℕ, 3 ≤ f → ClassicalGroup.IsPSU S 4 (2 ^ f) →
        ∃ P : Sylow 2 S, HasSolvableQuotientPair 25 (MulAut P)) :
    SourceOddUnitarySylowQuotients.{u} := by
  intro S _ _ hS hm
  rcases hm with ⟨f, hf, hm⟩ | hm
  · exact hfour S hS f hf hm
  · exact source_psu5_four_sylow_quotients hm

end CFSG.Quasithin.Chapter10
