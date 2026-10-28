module

public import Theory.GroupAction.QuaternionCentralizerPlacement
public import Theory.GroupTheory.SpecificGroups.QuaternionDihedralProduct
public import Theory.SpecificGroups.GL2.ThreeQuaternionPlacement
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.QuaternionPlacement.Coverage

/-!
# Sufficient centralizer calculations for the three outer involution types

The field and graph branches reduce to dihedral-times-C₂ Sylow subgroups
of their full automorphism centralizers. For the graph-field branch it
suffices to construct a homomorphism from its full centralizer to GL₂(3) × C₂
with three-group kernel, and to place the eight quaternion matrix fibers
in the actual inner image times the marked cyclic subgroup.

These are conditional reductions. No Sylow model or graph-field centralizer
map is assumed to have been constructed by this module. Each condition
must be discharged before asserting representative quaternion placement.

Source: Aschbacher–Smith 16.1.4(4)–(6), printed p.1171, for the three
involution types; proof of 16.4.9(2), printed p.1192, for the quaternion
placement used by the component-normalizer argument.
-/

public section

open Subgroup
namespace Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement
open ExtendedCentralizer.ProjectiveFixer
noncomputable section

/-- The full centralizer of a marked automorphism, inside the actual automorphism group. -/
abbrev automorphismCentralizer (a : MulAut PSL) : Subgroup (MulAut PSL) :=
  centralizer ({a} : Set (MulAut PSL))

/-- The actual inner image joined with the marked cyclic subgroup. -/
abbrev innerWith (a : MulAut PSL) : Subgroup (MulAut PSL) :=
  (MulAut.conj : PSL →* MulAut PSL).range ⊔ zpowers a

/-- A dihedral-times-C₂ Sylow model excludes quaternion subgroups in the full centralizer. -/
theorem not_quaternion_of_dihedral_sylow (a : MulAut PSL) {n : ℕ}
    (S : Sylow 2 (automorphismCentralizer a)) (e : S ≃* DihedralGroup n × C2)
    (P : Subgroup (MulAut PSL)) (hPC : P ≤ automorphismCentralizer a)
    (hP : Nonempty (P ≃* QuaternionGroup 2)) : False := by
  obtain ⟨eP⟩ := hP
  let f : QuaternionGroup 2 →* automorphismCentralizer a :=
    (inclusion hPC).comp eP.symm.toMonoidHom
  have hf : Function.Injective f := (inclusion_injective hPC).comp eP.symm.injective
  apply QuaternionGroup.not_injective_of_sylow_dihedral_prod S e _ f hf
  decide

/-- The field branch follows from its actual centralizer Sylow model. -/
theorem field_placement_of_sylow_model
    (S : Sylow 2 (automorphismCentralizer pslFrobenius))
    (e : S ≃* DihedralGroup 8 × C2)
    (P : Subgroup (MulAut PSL)) (hP : Nonempty (P ≃* QuaternionGroup 2))
    (hPC : P ≤ automorphismCentralizer pslFrobenius) : P ≤ innerWith pslFrobenius :=
  (not_quaternion_of_dihedral_sylow pslFrobenius S e P hPC hP).elim

/-- The graph branch follows from its actual centralizer Sylow model. -/
theorem graph_placement_of_sylow_model
    (S : Sylow 2 (automorphismCentralizer (PSL3.OuterSolvable.graph F)))
    (e : S ≃* DihedralGroup 4 × C2)
    (P : Subgroup (MulAut PSL)) (hP : Nonempty (P ≃* QuaternionGroup 2))
    (hPC : P ≤ automorphismCentralizer (PSL3.OuterSolvable.graph F)) :
    P ≤ innerWith (PSL3.OuterSolvable.graph F) :=
  (not_quaternion_of_dihedral_sylow (PSL3.OuterSolvable.graph F) S e P hPC hP).elim

/-- The graph-field branch follows from the marked ternary matrix map and its kernel. -/
theorem graphField_placement_of_matrix_model
    (f : automorphismCentralizer graphField →* GeneralLinearGroup (Fin 2) (ZMod 3) × C2)
    (hker : IsPGroup 3 f.ker)
    (hinner : ∀ x : automorphismCentralizer graphField,
      ((f x).1.val = 1 ∨ (f x).1.val = -1 ∨ (f x).1.val ^ 2 = -1) →
      (x : MulAut PSL) ∈ innerWith graphField)
    (P : Subgroup (MulAut PSL)) (hP : Nonempty (P ≃* QuaternionGroup 2))
    (hPC : P ≤ automorphismCentralizer graphField) : P ≤ innerWith graphField := by
  obtain ⟨eP⟩ := hP
  have he : Nonempty (P.subgroupOf (automorphismCentralizer graphField) ≃* QuaternionGroup 2) :=
    ⟨(subgroupOfEquivOfLe hPC).trans eP⟩
  have hle := GeneralLinearGroup.quaternion_le_of_three_kernel_matrix_image f hker
    ((innerWith graphField).subgroupOf (automorphismCentralizer graphField))
    hinner (P.subgroupOf (automorphismCentralizer graphField)) he
  intro x hx
  exact hle (show (⟨x, hPC hx⟩ : automorphismCentralizer graphField) ∈
    P.subgroupOf (automorphismCentralizer graphField) from hx)

end
end Matrix.PSL3Four.InnerFamilyNormalizer.QuaternionPlacement
