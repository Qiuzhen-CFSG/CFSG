module

public import Theory.SpecificGroups.Held.Automorphisms.InvolutionFixedData.Inner.Reduction

/-!
# The canonical subgroup and orbit for the Held 2A cover

The candidate is the derived subgroup of the literal fixed subgroup of
`MulAut.conj Held.a`. Its normality is relative to that fixed subgroup.
The original degree-2058 action restricts to the orbit of ATLAS letter 26;
its kernel and faithful image provide independent interfaces for a central
kernel calculation and comparison with the matrix PSL₃(4).

The definitions do not assert the orbit size, perfectness, subgroup orders,
or any projective identification. A perfect subgroup of index two must
coincide with this candidate, since its quotient is abelian.

Source: GLS3 Table 5.3p, interpreted on printed pp.260–261. The representation
and conversion from GAP's right action are retained in `Held/Model/Source`.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace Held.InvolutionFixedData.TwoA
/-- The literal fixed subgroup of conjugation by the retained ATLAS generator. -/
abbrev centralizer : Subgroup He := (MulAut.conj a).fixedSubgroup
/-- The canonical candidate for the perfect central cover, normal inside the fixed subgroup. -/
abbrev derived : Subgroup centralizer := commutator centralizer
/-- The orbit of the zero-based letter 25 (ATLAS letter 26) under the actual derived subgroup. -/
abbrev PointOrbit := MulAction.orbit derived (25 : Fin 2058)
/-- The restriction of the given permutation action to this orbit. -/
def orbitAction : derived →* Equiv.Perm PointOrbit := MulAction.toPermHom derived PointOrbit
/-- The pointwise stabilizer of the chosen orbit inside the derived subgroup. -/
abbrev orbitKernel : Subgroup derived := orbitAction.ker
/-- The faithful permutation image on the chosen orbit; no recognition is asserted. -/
abbrev orbitImage : Subgroup (Equiv.Perm PointOrbit) := orbitAction.range

theorem centralizer_eq : centralizer = Subgroup.centralizer ({a} : Set He) :=
  MulAut.fixedSubgroup_conj a
theorem derived_normal : derived.Normal := inferInstance
theorem derived_characteristic : derived.Characteristic := inferInstance
theorem derived_map : derived.map centralizer.subtype = ⁅centralizer, centralizer⁆ :=
  Subgroup.map_subtype_commutator centralizer
theorem orbitAction_apply (d : derived) (x : PointOrbit) :
    (orbitAction d x : Fin 2058) = representation d.val.val x.val := rfl
theorem mem_orbitKernel (d : derived) : d ∈ orbitKernel ↔
    ∀ x : PointOrbit, representation d.val.val x.val = x.val := by
  change orbitAction d = 1 ↔ _
  constructor
  · intro h x
    exact congrArg (fun p : Equiv.Perm PointOrbit => (p x : Fin 2058)) h
  · intro h
    apply Equiv.ext
    intro x
    exact Subtype.ext (h x)

/-- Any perfect subgroup of index two in the fixed subgroup is the canonical candidate.
This permits finite certificates to use convenient generators without changing the witness. -/
theorem perfect_subgroup_eq_derived_of_index_two (K : Subgroup centralizer) [Group.IsPerfect K] (hi : K.index = 2) :
    K = derived := by
  let : K.Normal := Subgroup.normal_of_index_eq_two hi
  let : IsCyclic (centralizer ⧸ K) := isCyclic_of_prime_card hi
  apply le_antisymm
  · rw [← K.commutator_eq_self]
    exact (Subgroup.commutator_mono le_top le_top)
  · exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp inferInstance

end Held.InvolutionFixedData.TwoA
