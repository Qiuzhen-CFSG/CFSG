module

public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.SourceUnitaryFiveQuotients
public import Theory.SpecificGroups.ClassicalUnitary.FourSylowStructure.Transport

/-!
# The PSU₄ family and the complete original unitary Sylow quotient condition

For PSU₄(2ᶠ), f ≥ 3, the characteristic self-centralizing elementary
subgroup of a Sylow two-subgroup has the norm-plane root action. Restriction
has a two-group kernel, and the additive root normalizer is solvable.
Transport through the actual Hermitian form and projective marking therefore
makes the whole Sylow automorphism group solvable.

The two trivial quotients supply the required quotient pair. Combining this
with the proved PSU₅(4) flag calculation discharges the complete intrinsic
unitary condition in the original odd-normalizer argument.

Source: Aschbacher--Smith 4.4.10--11, printed p.621, and the unitary-four
Sylow structure in F.1.11--12, printed pp.262--264.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
namespace CFSG.Quasithin.Chapter10
universe u

/-- The actual Sylow automorphism group is solvable for the binary PSU₄
family remaining in the original odd-normalizer source condition. -/
theorem source_psu4_binary_sylow_automorphisms
    {S : Type u} [Group S] [Finite S] {f : ℕ} (hf : 3 ≤ f)
    (hS : ClassicalGroup.IsPSU S 4 (2 ^ f)) :
    ∃ P : Sylow 2 S, Group.IsSolvable (MulAut P) := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hS
  let P : Sylow 2 S := Classical.choice inferInstance
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let j : P ≃* Q := P.equivMapOfInjective e.toMonoidHom e.injective
  let : Group.IsSolvable (MulAut Q) :=
    FourSylowStructure.projective_sylow_mulAut_isSolvable F J (n := f) (by omega) hcard hconj Q
  exact ⟨P, Group.isSolvable_of_surjective
    (f := (MulAut.congr j.symm).toMonoidHom) (MulAut.congr j.symm).surjective⟩

/-- Solvability supplies the two trivial quotient actions, whose orders
are both one, on the literal Sylow automorphism group. -/
theorem source_psu4_binary_sylow_quotients
    {S : Type u} [Group S] [Finite S] {f : ℕ} (hf : 3 ≤ f)
    (hS : ClassicalGroup.IsPSU S 4 (2 ^ f)) :
    ∃ P : Sylow 2 S, HasSolvableQuotientPair 25 (MulAut P) := by
  obtain ⟨P, hP⟩ := source_psu4_binary_sylow_automorphisms hf hS
  let : Group.IsSolvable (MulAut P) := hP
  refine ⟨P, ⊤, ⊤, inferInstance, inferInstance, inferInstance, ?_, ?_⟩ <;>
    simp only [index_top] <;> norm_num

/-- Both genuine unitary families in the original source condition have
the required Sylow quotient actions, with no additional model premise. -/
theorem source_oddUnitarySylowQuotients : SourceOddUnitarySylowQuotients.{u} := by
  apply source_oddUnitarySylowQuotients_of_psu4
  intro S _ _ _ f hf hS
  exact source_psu4_binary_sylow_quotients hf hS

end CFSG.Quasithin.Chapter10
