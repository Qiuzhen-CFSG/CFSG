module
public import CFSG.Quasithin.ChapterG.Section10.Components
public import Theory.Representation.NormalComponentConstituents.Orthogonal

/-!
# The adapted constituent decomposition in G.10.7

Every constituent of the actual normal component orbit has either its
nondegenerate orthogonal complement or a conjugate dual constituent whose
sum is nondegenerate. All complements are invariant for the same normal
orbit. This is G.10.7(3), in the form needed for the marked-point argument
G.10.13 and the homogeneous cases of G.10.15.

Source: Aschbacher--Smith, printed pp.359--361.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section10
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- Orthogonal constituent data for the literal ambient orbit of a component.
The partner is an actual conjugate with its original H-representation. -/
@[expose] def ComponentOrthogonalData (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) (L : Subgroup G) : Prop :=
  let H := componentOrbit L ⊤
  letI := componentOrbit_top_normal L
  ∀ I : Submodule (ZMod 2) V, ∀ hI : IsIrrPlus ρ H I,
    ((B.restrict I).Nondegenerate ∧ IsCompl I (B.orthogonal I) ∧
      H ≤ subspaceStabilizer ρ (B.orthogonal I)) ∨
    ∃ g : G,
      let J := conjugateSubrepresentation ρ H (invariantSubspace ρ H I hI.choose) g
      IsIrrPlus ρ H J.toSubmodule ∧
      (∀ u ∈ I, ∀ w ∈ I, B u w = 0) ∧
      Disjoint I J.toSubmodule ∧
      Nonempty (Representation.Equiv (invariantSubspace ρ H I hI.choose).toRepresentation
        J.toRepresentation.dual) ∧
      (B.restrict (I ⊔ J.toSubmodule)).Nondegenerate ∧
      IsCompl (I ⊔ J.toSubmodule) (B.orthogonal (I ⊔ J.toSubmodule)) ∧
      H ≤ subspaceStabilizer ρ (B.orthogonal (I ⊔ J.toSubmodule))

namespace Hypothesis
variable [Finite G] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
  (h : Hypothesis ρ B v W X X₀)
include h

/-- The G.10.7 adapted pairing for every Irr-plus member of the actual orbit. -/
theorem component_orthogonal_data (hn : ¬ Group.IsSolvable G) (L : Subgroup G) :
    ComponentOrthogonalData ρ B L := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  intro I hI
  exact hI.orthogonal_alternative ρ B h.preserves
    (h.irreducible_of_not_solvable hn) h.alternating h.nondegenerate H

/-- The moved component and homogeneous selection retain the complete adapted
orthogonal pairing data for all of its constituents. -/
theorem exists_moved_component_orthogonal_selection (hn : ¬ Group.IsSolvable G)
    (hF : X ⊓ centralizer (fittingSubgroup G : Set G) ≠ ⊥) :
    ∃ L : Subgroup G, IsComponent G L ∧ ⁅L,X⁆ ≠ ⊥ ∧
      ComponentOrbitSelection ρ B L X ∧ ComponentOrthogonalData ρ B L := by
  obtain ⟨L,hL,hm,hs⟩ := h.exists_moved_component_selection hn hF
  exact ⟨L,hL,hm,hs,h.component_orthogonal_data hn L⟩

/-- The adapted orthogonal complement is semisimple for the original normal
component orbit. This supplies the remaining irreducible summands of G.10.7(3). -/
theorem component_orthogonal_complement_semisimple (hn : ¬ Group.IsSolvable G)
    (L : Subgroup G) (I : Submodule (ZMod 2) V)
    (hs : componentOrbit L ⊤ ≤ subspaceStabilizer ρ I) :
    IsSemisimpleRepresentation
      (invariantSubspace ρ (componentOrbit L ⊤) (B.orthogonal I)
        (orthogonal_invariant ρ B h.preserves hs)).toRepresentation := by
  let := componentOrbit_top_normal L
  exact subrepresentation_semisimple_of_normal_restriction ρ
    (h.irreducible_of_not_solvable hn) (componentOrbit L ⊤) _

end Hypothesis
end CFSG.Quasithin.ChapterG.Section10
