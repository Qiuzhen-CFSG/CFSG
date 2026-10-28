module
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.PairSymmetric
public import Theory.Representation.BinaryOffender.StableRestriction
public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization

/-!
# Stable families on the same marked natural pair

The class-sum comparison for the source marked S₅ product identifies all
fixed codimensions. Restriction along its actual embedding therefore carries
any supported stable family to a stable family on the genuine natural pair.
The paired Thompson-image source proof applies this to the original maximum
 elementary images; no new module-comparison hypothesis is introduced.

Source: Aschbacher–Smith E.2.3(3), pp.216–217.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation Representation.BinaryOffender Stellmacher
namespace CFSG.Quasithin.ChapterB
open SourceInduction
section Generic
variable {H V : Type*} [Group H] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (Y : Subgroup H)
    (d : SourceTwoFactorCase (ρ.comp Y.subtype))
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))

/-- The same source marked product restricts any stable family supported in
its actual layer, without assuming a natural representation on the original module. -/
theorem stable_family_on_symmetric_product
    (P : Set (Subgroup H)) (hP : IsStable ρ P) (hPY : ∀ A ∈ P, A ≤ Y) :
    IsStable BinaryPermutation.FivePair.action
      {A | A.map (Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom) ∈ P} := by
  let j := Y.subtype.comp c.action.groupEquiv.symm.toMonoidHom
  have hj : Function.Injective j := Y.subtype_injective.comp c.action.groupEquiv.symm.injective
  apply hP.restrict_of_fixedCodim BinaryPermutation.FivePair.action ρ j hj
  · intro A
    have hh := c.symmetric_fixedCodim (A.map c.action.groupEquiv.symm.toMonoidHom)
    have hc : (A.map c.action.groupEquiv.symm.toMonoidHom).map c.action.groupEquiv.toMonoidHom = A :=
      c.action.groupEquiv.mapSubgroup.apply_symm_apply A
    rw [hc] at hh
    change Module.finrank (ZMod 2) (V ⧸ fixedSpace (ρ.comp Y.subtype) _) = _ at hh
    rw [fixedSpace_comp_map ρ Y.subtype,map_map] at hh
    exact hh.symm
  · obtain ⟨A,hA⟩ := hP.1
    refine ⟨(A.subgroupOf Y).map c.action.groupEquiv.toMonoidHom,?_⟩
    have hc : j.comp c.action.groupEquiv.toMonoidHom = Y.subtype := by
      ext x
      simp [j]
    rwa [map_map,hc,map_subgroupOf_eq_of_le (hPY A hA)]

end Generic
end CFSG.Quasithin.ChapterB
