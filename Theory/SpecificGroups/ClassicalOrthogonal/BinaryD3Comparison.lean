module

public import Theory.SpecificGroups.ClassicalOrthogonal.TheoremDRootNormalizer.ScalarQuotients
public import Theory.SpecificGroups.ClassicalOrthogonal.Fundamental.SplitOddCentralizers.ResidualContainment
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.BinaryMaps
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.Geometry
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.IsPerfect

/-!
# Binary split-six comparison from the genuine deleted action

The existing faithful deleted action identifies the full split orthogonal
group with S8. Its elementary subgroup is normal. When the source consumer
supplies perfectness and nontriviality, its image is a nontrivial normal
subgroup of A8, hence all of A8. Characteristic-two projectivization is
injective, so this identifies the literal projective elementary carrier.
No model simplicity or order theorem is assumed beyond the actual source
perfectness; the full orthogonal action is the checked ATLAS construction.
Source: GLS3 §2.7; Aschbacher--Smith A.2.18, printed p.40.
-/

public noncomputable section
open Subgroup Theory.AlgebraicGroup
namespace ClassicalOrthogonal.BinaryD3Comparison
open Atlas.Order20160A8
/-- The checked deleted action identifies the full split-six isometry group. -/
def symmetricEquiv : Equiv.Perm (Fin 8) ≃* O_DPlus 3 (ZMod 2) :=
  MulEquiv.ofBijective DeletedEight.orthogonalHom
    ((Nat.bijective_iff_injective_and_card _).mpr ⟨DeletedEight.orthogonalHom_injective,
      le_antisymm (Nat.card_le_card_of_injective _ DeletedEight.orthogonalHom_injective)
        (by
          have hs : Nat.card (Equiv.Perm (Fin 8)) = 40320 := by
            simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
          rw [hs]
          exact Geometry.orthogonal_card_le)⟩)

/-- The actual nontrivial perfect elementary carrier is A8. -/
def projectiveEquivAlternating
    [Group.IsPerfect (POmegaPlus 3 (ZMod 2))] [Nontrivial (POmegaPlus 3 (ZMod 2))] :
    POmegaPlus 3 (ZMod 2) ≃* alternatingGroup (Fin 8) := by
  let Q := formD 3 (ZMod 2)
  let N : Subgroup (Equiv.Perm (Fin 8)) :=
    (elementarySubgroup Q).map symmetricEquiv.symm.toMonoidHom
  let e : POmegaPlus 3 (ZMod 2) ≃* N :=
    (TheoremDRootNormalizer.elementaryProjectiveEquiv Q).symm.trans
      ((elementarySubgroup Q).equivMapOfInjective
        symmetricEquiv.symm.toMonoidHom symmetricEquiv.symm.injective)
  let : Group.IsPerfect N := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  let : Nontrivial N := e.injective.nontrivial
  let : N.Normal :=
    (ClassicalOrthogonal.Fundamental.SplitOddBlocks.elementary_normal Q).map
      symmetricEquiv.symm.toMonoidHom symmetricEquiv.symm.surjective
  have hle : N ≤ alternatingGroup (Fin 8) := by
    rw [← alternatingGroup.commutator_perm_eq (by simp : 5 ≤ Nat.card (Fin 8))]
    rw [← Subgroup.commutator_eq_self (H := N)]
    exact Subgroup.commutator_mono le_top le_top
  let H := N.subgroupOf (alternatingGroup (Fin 8))
  let : Nontrivial H := (Subgroup.subgroupOfEquivOfLe hle).symm.injective.nontrivial
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have ht : H = ⊤ := (inferInstance : H.Normal).eq_bot_or_eq_top.resolve_left
    ((Subgroup.nontrivial_iff_ne_bot H).mp inferInstance)
  have heq : N = alternatingGroup (Fin 8) := by
    apply le_antisymm hle
    intro x hx
    have hh : (⟨x, hx⟩ : alternatingGroup (Fin 8)) ∈ H := ht ▸ Subgroup.mem_top _
    exact hh
  exact e.trans (MulEquiv.subgroupCongr heq)
end ClassicalOrthogonal.BinaryD3Comparison
