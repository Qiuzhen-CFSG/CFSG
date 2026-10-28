module

public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups
public import CFSG.Quasithin.ClassicalModels
public import Theory.SpecificGroups.PSL3.OddSolvableGeneration
public import Theory.SpecificGroups.ProjectiveLinearInvolutions

/-!
# Rank-one E-generation for inner PSL₃ over odd fields

The two opposite abelian parabolic radicals, each joined with a common Sylow
two-subgroup, are solvable and generate the actual projective matrix group.
Solvable E-generation and E-member inheritance therefore prove the rank-one
bound. Transport uses the multiplicative equivalence in `ClassicalGroup.IsPSL`.

This proves the inner branch of Aschbacher--Smith E.1.14(7), printed p.214,
with the odd-prime convention of A.2.3(2), printed p.33. The argument works
over every finite odd field and in particular includes p=5. It uses neither
PSL₂ E-generation nor the unfinished general composition-factor reduction.
The proper almost-simple extension remains with the parent assembly.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration

/-- The concrete matrix quotient over any finite field of odd characteristic
is rank-one E-generated. -/
theorem isEGenerated_one_PSLThree_of_two_ne_zero (F : Type*) [Field F] [Finite F]
    (h2 : (2 : F) ≠ 0) : IsEGenerated 1 PSL(3, F) := by
  obtain ⟨T, P, Q, hTP, hTQ, hP, hQ, hPQ⟩ :=
    Matrix.PSL3.OddSolvableGeneration.exists_solvable_generating_pair F h2
  let _ := hP
  let _ := hQ
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  apply top_unique
  change ⊤ ≤ ChiefOrbit.generationTarget 1 T Ω
  rw [← hPQ]
  exact sup_le
    (ChiefOrbit.solvable_overgroup_le_generationTarget (by decide) T P hTP hΩ)
    (ChiefOrbit.solvable_overgroup_le_generationTarget (by decide) T Q hTQ hΩ)

/-- Actual `IsPSL` transport, proving the requested inner odd-prime branch
without needing simplicity or SQTK as additional hypotheses. -/
theorem isEGenerated_one_of_isPSL_three_odd {G : Type*} [Group G] [Finite G]
    {q : ℕ} (hodd : Odd q) (hmodel : ClassicalGroup.IsPSL G 3 q) :
    IsEGenerated 1 G := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hmodel
  exact (isEGenerated_one_PSLThree_of_two_ne_zero F
    (Field.two_ne_zero_of_odd_card F (hF ▸ hodd))).map_equiv e.symm

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration
