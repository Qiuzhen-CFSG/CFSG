module

public import Theory.AtlasPort.LinearGroups.G2.LieShortParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.LieLongParabolic.Quotient
public import Theory.AtlasPort.LinearGroups.G2.BinaryException
public import Theory.SpecificGroups.PSL2.OuterSolvable.Models

/-!
# Solvability of the binary G₂ parabolics

At field order two the split torus disappears, so each full parabolic is its
rank-one local group. Its actual two-core quotient is PSL₂(2), whose solvability
comes from the faithful action on the four binary vectors. Extension by the
two-core proves solvability of both parabolics over every field of order two.

This is the local input for the q = 2 case of Aschbacher--Smith E.1.14(1),
printed p.214. The literal quotient maps are those constructed for F.1.12(I)(3),
printed pp.262--264, in the licensed ATLAS port. See LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff; no new upstream source is copied here.
-/

public section

open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped MatrixGroups
namespace Atlas.G2.BinaryParabolicSolvable
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [CharP F 2] in
private theorem solvable_of_binary_quotient {H : Type*} [Group H] [Finite H]
    (hF : Nat.card F = 2) (e : H ⧸ pCore 2 H ≃* PSL(2, F)) :
    Group.IsSolvable H := by
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  let : Group.IsSolvable PSL(2,F) := Theory.PSL2.OuterSolvable.isSolvable_of_card_two hF
  let : Group.IsSolvable (H ⧸ pCore 2 H) :=
    Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 H)).mpr
    ⟨inferInstance, inferInstance⟩

theorem parabolic_isSolvable (hF : Nat.card F = 2) (i : Fin 2) :
    Group.IsSolvable (if i = 0 then parabolic₁ (F := F) else parabolic₂ :
      Subgroup (Model F)) := by
  fin_cases i
  · change Group.IsSolvable (parabolic₁ (F := F))
    have he : parabolic₁ (F := F) = local₁ := by
      change borel ⊔ closure {weylS} = unipotent ⊔ closure {weylS}
      rw [borel_eq_unipotent_of_card_two hF]
    rw [he]
    exact solvable_of_binary_quotient hF local₁CoreQuotientEquivPSL
  · change Group.IsSolvable (parabolic₂ (F := F))
    have he : parabolic₂ (F := F) = local₂ := by
      change borel ⊔ closure {weylR} = unipotent ⊔ closure {weylR}
      rw [borel_eq_unipotent_of_card_two hF]
    rw [he]
    exact solvable_of_binary_quotient hF local₂CoreQuotientEquivPSL
end Atlas.G2.BinaryParabolicSolvable
