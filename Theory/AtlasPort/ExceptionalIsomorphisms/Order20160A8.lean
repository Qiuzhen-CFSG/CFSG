module

/-
Copyright (c) 2026 Gerald Höhn and ATLAS contributors. All rights reserved.
Adapted from ATLAS, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Released under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.BinaryMaps
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.Geometry
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The exceptional A₈–PSL₄(2) equivalence

The faithful deleted quadratic module identifies S₈ with O⁺₆(2): duad incidence
reconstructs the eight points and proves surjectivity. The exterior square of
SL₄(2) embeds in this same orthogonal group. Its image has index two in S₈,
so it is the alternating subgroup. Finally the scalar center of SL₄(2) is
trivial, identifying its actual projective quotient with A₈.

Adapted from Gerald Höhn and ATLAS contributors,
`Atlas/Comparisons/Exceptional/Order20160A8.lean` and the deleted-module and
exterior-square constructions cited in its descendants. The binary incidence
argument replaces the general D₃/A₃ order and Dickson-invariant development.
This supplies the actual model equivalence used in Aschbacher–Smith,
*The Classification of Quasithin Groups*, printed p. 511 (PDF p. 528).
-/

noncomputable section
namespace Atlas.Order20160A8
open scoped MatrixGroups

private theorem symmetric_card : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

/-- The deleted-module action exhausts the full binary split isometry group. -/
private def symmetricEquivOrthogonal : Equiv.Perm (Fin 8) ≃* O_DPlus 3 (ZMod 2) :=
  MulEquiv.ofBijective DeletedEight.orthogonalHom
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨DeletedEight.orthogonalHom_injective,
      le_antisymm (Nat.card_le_card_of_injective _ DeletedEight.orthogonalHom_injective)
        (by rw [symmetric_card]; exact Geometry.orthogonal_card_le)⟩)

/-- An actual permutation representation obtained by comparing the two quadratic actions. -/
private def linearPermutationHom : SL(4,ZMod 2) →* Equiv.Perm (Fin 8) :=
  symmetricEquivOrthogonal.symm.toMonoidHom.comp Exterior.toOrthogonal

private theorem linearPermutationHom_injective : Function.Injective linearPermutationHom :=
  symmetricEquivOrthogonal.symm.injective.comp Exterior.binary_injective

private theorem linearPermutationHom_range :
    linearPermutationHom.range = alternatingGroup (Fin 8) := by
  apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
  have hcard : Nat.card linearPermutationHom.range = 20160 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective linearPermutationHom_injective).toEquiv,
      sl4Two_card]
  have h := linearPermutationHom.range.card_mul_index
  rw [hcard, symmetric_card] at h
  omega

private def sl4TwoEquivAlt8 : SL(4,ZMod 2) ≃* alternatingGroup (Fin 8) :=
  (MonoidHom.ofInjective linearPermutationHom_injective).trans
    (MulEquiv.subgroupCongr linearPermutationHom_range)

end Atlas.Order20160A8

namespace Atlas.Comparisons.Exceptional
open scoped MatrixGroups

/-- The exceptional PSL₄(2) ≃ A₈ equivalence, comparing the faithful exterior-square
and deleted-permutation-module actions on the same split quadratic space. -/
public def psl4TwoEquivAlt8 :
    Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2) ≃* alternatingGroup (Fin 8) :=
  Atlas.Order20160A8.sl4TwoEquivPSL.symm.trans Atlas.Order20160A8.sl4TwoEquivAlt8

/-- The exceptional comparison intertwines the exterior-square and deleted-module
actions on the same split quadratic space. This specification permits clients to
use that compatibility without unfolding the private comparison construction. -/
public theorem psl4TwoEquivAlt8_orthogonal (g : SL(4,ZMod 2)) :
    Atlas.Order20160A8.DeletedEight.orthogonalHom
        (psl4TwoEquivAlt8 (Atlas.Order20160A8.sl4TwoEquivPSL g)).val =
      Atlas.Order20160A8.Exterior.toOrthogonal g := by
  change Atlas.Order20160A8.DeletedEight.orthogonalHom
      (Atlas.Order20160A8.linearPermutationHom
        (Atlas.Order20160A8.sl4TwoEquivPSL.symm (Atlas.Order20160A8.sl4TwoEquivPSL g))) = _
  rw [MulEquiv.symm_apply_apply]
  exact Atlas.Order20160A8.symmetricEquivOrthogonal.apply_symm_apply _

/-- The A₈-to-PSL₄(2) direction used to transport an actual central quotient. -/
public def alt8EquivPSL4Two :
    alternatingGroup (Fin 8) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 4) (ZMod 2) :=
  psl4TwoEquivAlt8.symm

/-- The inverse exceptional comparison has the same concrete orthogonal marking. -/
public theorem alt8EquivPSL4Two_orthogonal (a : alternatingGroup (Fin 8)) :
    Atlas.Order20160A8.DeletedEight.orthogonalHom a.val =
      Atlas.Order20160A8.Exterior.toOrthogonal
        (Atlas.Order20160A8.sl4TwoEquivPSL.symm (alt8EquivPSL4Two a)) := by
  have h := psl4TwoEquivAlt8_orthogonal
    (Atlas.Order20160A8.sl4TwoEquivPSL.symm (alt8EquivPSL4Two a))
  simpa only [MulEquiv.apply_symm_apply, alt8EquivPSL4Two] using h

end Atlas.Comparisons.Exceptional
