module

public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Nonbinary
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.SymplecticFour.Blocks.Recognition

/-!
# The nonbinary symplectic local blocks

The actual point and plane determinant kernels are L₂(2ⁿ)-blocks for `n > 1`.
Their explicit natural extensions give every short-group clause, including
the generalized Fitting equality and irreducibility over the binary field.
The commutator layers are the concrete radicals; their fixed subgroups are
the kernels of the two natural coordinate maps. For the plane, these
coordinates include the inverse-Frobenius change of variables.

The trivial scalar center in characteristic two converts the actual SL₂
quotient equivalences into PSL₂ models. Transport through the subgroup
equivalences also proves the block statements inside the respective parabolics,
where the determinant kernels are normal.

Source: Aschbacher--Smith F.1.12(I)(2), printed pp.262--264, with block
definitions C.1.7 and C.1.12 on pp.123--124 of `refs/quasithin.pdf`.
-/

public section
namespace CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour

open Theory.SpecificGroups.SymplecticFour ChapterC

/-- Convert a genuine special-linear core-quotient isomorphism to the source's
projective group model. No family tag is substituted for an isomorphism. -/
theorem isPSL_of_specialLinearEquiv
    {G : Type*} [Group G] {F : Type} [Field F] [Finite F] [CharP F 2]
    {n : ℕ} (hF : Nat.card F = 2 ^ n)
    (e : G ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    ClassicalGroup.IsPSL G 2 (2 ^ n) := by
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨e.trans (Representation.SL2NaturalH1.projectiveEquiv (K := F)).symm⟩⟩

section Structure
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
include hcard hn

/-- The point-local commutator layer in the source block definition. -/
theorem pointLocal_blockU_eq : blockU (pointLocal (F := F)) = pointRadical :=
  pointLocal_core_commutator hcard hn

/-- The plane-local commutator layer in the source block definition. -/
theorem planeLocal_blockU_eq : blockU (planeLocal (F := F)) = Plane.radical :=
  planeLocal_core_commutator hcard hn

/-- The fixed point-local layer is the kernel of the two vector coordinates,
embedded in the local group. Its elements have coordinates `(0,0,z)`. -/
theorem pointLocal_blockFixed_map :
    (blockFixed (pointLocal (F := F))).map (blockU (pointLocal (F := F))).subtype =
      (pointRadicalVector (F := F)).ker.map pointRadical.subtype := by
  rw [blockFixed, pointLocal_blockU_eq hcard hn, pointRadical_center_eq_vector_ker]

/-- The fixed plane-local layer is the kernel of the inverse-Frobenius diagonal
coordinates. In symmetric-matrix coordinates these are the alternating matrices. -/
theorem planeLocal_blockFixed_map :
    (blockFixed (planeLocal (F := F))).map (blockU (planeLocal (F := F))).subtype =
      (Plane.naturalCoordinates (F := F)).ker.map Plane.radical.subtype := by
  rw [blockFixed, planeLocal_blockU_eq hcard hn, ← Plane.naturalCoordinates_ker]

/-- All the source short-group clauses for the actual point local. -/
theorem pointLocal_isShort : IsShort (pointLocal (F := F)) :=
  (SymplecticFourRecognition.recognition (pointNaturalExtension hcard hn) hn hcard).2.2.1

/-- All the source short-group clauses for the actual plane local. -/
theorem planeLocal_isShort : IsShort (planeLocal (F := F)) :=
  (SymplecticFourRecognition.recognition (planeNaturalExtension hcard hn) hn hcard).2.2.1

/-- The genuine point-local conjugation module, with the literal SL₂ action. -/
theorem pointLocal_isLinearBlockModel :
    IsLinearBlockModel (pointLocal (F := F))
      (Representation.specialLinearNatural (k := F) 2) :=
  (SymplecticFourRecognition.recognition (pointNaturalExtension hcard hn) hn hcard).2.2.2

/-- The genuine plane-local conjugation module, with its Frobenius twist removed. -/
theorem planeLocal_isLinearBlockModel :
    IsLinearBlockModel (planeLocal (F := F))
      (Representation.specialLinearNatural (k := F) 2) :=
  (SymplecticFourRecognition.recognition (planeNaturalExtension hcard hn) hn hcard).2.2.2

end Structure

section NamedBlocks
variable {F : Type} [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hcard : Nat.card F = 2 ^ n) (hn : 1 < n)
include hcard hn

private theorem isL2EvenBlock_of_naturalExtension
    {L : Type*} [Group L] [Finite L] {Q : Subgroup L} [Q.Normal]
    (d : NaturalExtension (F := F) Q) : IsL2EvenBlock L n := by
  have h := SymplecticFourRecognition.recognition d hn hcard
  refine ⟨hn, h.2.2.1, F, inferInstance, inferInstance, hcard, ?_, h.2.2.2⟩
  obtain ⟨e⟩ := h.2.2.2.quotient_iso
  exact isPSL_of_specialLinearEquiv hcard e

/-- The point determinant kernel is an L₂(2ⁿ)-block for `n > 1`. -/
theorem pointLocal_isL2EvenBlock : IsL2EvenBlock (pointLocal (F := F)) n :=
  isL2EvenBlock_of_naturalExtension hcard hn (pointNaturalExtension hcard hn)

/-- The plane determinant kernel is an L₂(2ⁿ)-block for `n > 1`. -/
theorem planeLocal_isL2EvenBlock : IsL2EvenBlock (planeLocal (F := F)) n :=
  isL2EvenBlock_of_naturalExtension hcard hn (planeNaturalExtension hcard hn)

/-- The point local, viewed as a subgroup inside its parabolic, has the same
intrinsic L₂-block structure through the actual subgroup equivalence. -/
theorem pointLocal_relative_isL2EvenBlock :
    IsL2EvenBlock ((pointLocal (F := F)).subgroupOf pointParabolic) n :=
  isL2EvenBlock_of_naturalExtension hcard hn
    ((pointNaturalExtension hcard hn).comap (Subgroup.subgroupOfEquivOfLe pointLocal_le))

/-- The plane local, viewed inside its parabolic, is an intrinsic L₂-block. -/
theorem planeLocal_relative_isL2EvenBlock :
    IsL2EvenBlock ((planeLocal (F := F)).subgroupOf planeParabolic) n :=
  isL2EvenBlock_of_naturalExtension hcard hn
    ((planeNaturalExtension hcard hn).comap (Subgroup.subgroupOfEquivOfLe planeLocal_le))

/-- The point local is an L₂-block of the point parabolic. -/
theorem pointLocal_isBlockOfType :
    IsBlockOfType ((pointLocal (F := F)).subgroupOf pointParabolic)
      (IsL2EvenBlock ((pointLocal (F := F)).subgroupOf pointParabolic) n) := by
  have h := pointLocal_relative_isL2EvenBlock hcard hn
  exact ⟨⟨inferInstance, h.2.1, pointLocal_normal.isSubnormal⟩, h⟩

/-- The plane local is an L₂-block of the plane parabolic. -/
theorem planeLocal_isBlockOfType :
    IsBlockOfType ((planeLocal (F := F)).subgroupOf planeParabolic)
      (IsL2EvenBlock ((planeLocal (F := F)).subgroupOf planeParabolic) n) := by
  have h := planeLocal_relative_isL2EvenBlock hcard hn
  exact ⟨⟨inferInstance, h.2.1, planeLocal_normal.isSubnormal⟩, h⟩

end NamedBlocks

end CFSG.Quasithin.ChapterF.GreenBook.LieModels.SymplecticFour
