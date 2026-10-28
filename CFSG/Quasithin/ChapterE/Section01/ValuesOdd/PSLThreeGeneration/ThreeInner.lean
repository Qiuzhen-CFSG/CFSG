module

public import CFSG.Quasithin.ChapterE.Section01.Basic
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.ChapterE.Section01.ParameterReduction.ChiefOrbit.NormalizerDiagonal.Overgroups
public import Theory.SpecificGroups.PSL3Three.GeneratingParabolics
public import Theory.SpecificGroups.PSL3Three.ParabolicSolvability
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Rank-one E-generation for the inner PSL₃(3) model

Two solvable parabolics contain a common Sylow two-subgroup and generate the
actual matrix quotient. Solvable E-generation and E-member inheritance place
both parabolics inside the ambient generation target for every elementary
family. Sylow conjugacy then gives generation at every Sylow subgroup.

Field and group equivalences transport this conclusion to the exact IsPSL
predicate, whose field need not be definitionally ZMod 3. The existing ATLAS
field-transport API is reused with its attribution and license in
`Theory/AtlasPort/ExceptionalIsomorphisms/Support.lean`.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.12--14, printed p.214, and A.2.3(2), printed p.33. This proves the
inner p=3 case of E.1.14(7); it does not assert generation of a graph extension.
-/

public section
open Subgroup Matrix Matrix.PSL3Three
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration

/-- The concrete projective group PSL₃(3) is rank-one E-generated. -/
theorem isEGenerated_one_PSLThreeThree : IsEGenerated 1 PSL := by
  let _ := lineStabilizer_isSolvable
  let _ := planeStabilizer_isSolvable
  obtain ⟨T, hline, hplane⟩ := exists_sylowTwo_le_parabolics
  apply IsEGeneratedAt.isEGenerated (T := T)
  intro Ω hΩ
  apply top_unique
  rw [← lineStabilizer_sup_planeStabilizer]
  exact sup_le
    (ChiefOrbit.solvable_overgroup_le_generationTarget (by decide) T lineStabilizer hline hΩ)
    (ChiefOrbit.solvable_overgroup_le_generationTarget (by decide) T planeStabilizer hplane hΩ)

/-- Transport across the actual model witness, allowing any field of order three. -/
theorem isEGenerated_one_of_isPSL_three_three {G : Type*} [Group G] [Finite G]
    (hG : ClassicalGroup.IsPSL G 3 3) : IsEGenerated 1 G := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hG
  let _ := Fintype.ofFinite F
  let f : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hF)
  exact isEGenerated_one_PSLThreeThree.map_equiv (e.trans (Atlas.fieldEquivPSL 3 f)).symm

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration
