module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.DegreeThree.Covers
public import Theory.SpecificGroups.Classical.DegreeThreeSmallSylow
public import Theory.GroupTheory.DihedralEightSections

/-!
# Degree-three source component parameters and actual models

Restricting the ambient Sylow subgroup and passing through the literal
component central quotient preserves its order bound. The classical order
calculation fixes the source prime modulo eight. The scalar-cover theorem
then identifies the original component with the actual special or projective
matrix group over that same field and Hermitian form.

These are the numerical and covering steps of F.6.18(10)--(11), pp.309--310.
The catalogue selection and linear/unitary sign remain the Sylow-shape step;
no local subgroup or graph-automorphism conclusion is assumed here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly
variable {G H F : Type*} [Group G] [Finite G] [Group H] [Finite H]
    [Field F] [Finite F] {K : Subgroup G}

/-- The linear source component has the exact prime congruence and one of
the two actual scalar-cover models. -/
theorem component_linear_three_small_sylow_models
    (hK : IsComponent G K) (T : Sylow 2 G) (hT : Nat.card T ≤ 64)
    {p : ℕ} (_hp : p.Prime) (hcard : Nat.card F = p) (hsign : p % 4 = 1)
    (eK : K ⧸ center K ≃* PSL(3,F)) :
    p % 8 = 5 ∧ (Nonempty (K ≃* SL(3,F)) ∨ Nonempty (K ≃* PSL(3,F))) := by
  let P : Sylow 2 PSL(3,F) := default
  have hP : Nat.card P ≤ 64 := (sylow_card_section_le T K
    (eK.toMonoidHom.comp (QuotientGroup.mk' (center K)))
    (eK.surjective.comp (QuotientGroup.mk'_surjective (center K))) P).trans hT
  have hm : p % 8 = 5 := hcard ▸ Theory.ClassicalSmallSylow.psl3_mod_eight_of_small_sylow
    P hP (hcard ▸ hsign)
  have ho : Odd (Nat.card F) := by rw [hcard, Nat.odd_iff]; omega
  refine ⟨hm, ?_⟩
  rcases component_linear_three_cover hK ho eK with ⟨_, j, _⟩ | ⟨_, _, j, _⟩
  · exact .inr ⟨j⟩
  · exact .inl ⟨j.symm⟩

/-- The unitary source component, with its coefficient field and literal
Frobenius involution retained. -/
theorem component_unitary_three_small_sylow_models
    (eG : G ≃* (H ⧸ pPrimeCore 3 H)) (hK : IsComponent G K)
    (T : Sylow 2 G) (hT : Nat.card T ≤ 64)
    (J : HermitianForm 3 F) {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card F = p ^ 2) (hconj : ∀ x, J.conj x = x ^ p)
    (hsign : p % 4 = 3)
    (eK : K ⧸ center K ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    p % 8 = 3 ∧ (Nonempty (K ≃* J.specialSubgroup) ∨
      Nonempty (K ≃* ProjectiveSpecialUnitaryMatrixGroup J)) := by
  let P : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J) := default
  have hP : Nat.card P ≤ 64 := (sylow_card_section_le T K
    (eK.toMonoidHom.comp (QuotientGroup.mk' (center K)))
    (eK.surjective.comp (QuotientGroup.mk'_surjective (center K))) P).trans hT
  have hm := Theory.ClassicalSmallSylow.psu3_mod_eight_of_small_sylow
    J hp.one_lt hcard hconj P hP hsign
  refine ⟨hm, ?_⟩
  rcases component_unitary_three_cover eG hK J hp (by omega) hcard hconj eK with
    ⟨_, j, _⟩ | ⟨_, _, j, _⟩
  · exact .inr ⟨j⟩
  · exact .inl ⟨j.symm⟩

end CFSG.Quasithin.ChapterF.SourceAssembly
