module

public import Theory.SpecificGroups.Held.Automorphisms.OuterInvolution.FixedStructure.Generators
public import Mathlib.GroupTheory.GroupAction.SubMulAction

/-!
# A concrete candidate for the triple-A7 subgroup

The candidate is generated inside the literal fixed subgroup by the checked
(5,7,6) pair. Its action on the orbit of ATLAS letter 31 is inherited from
the defining degree-2058 representation. Thus the orbit kernel and image
below refer to this actual subgroup, rather than to an abstract replacement.

Source: GLS3 Table 5.3p and its perfect-cover convention on pp.260–261.
The order bound for the full fixed subgroup and the central A7 quotient
are separate finite-certificate obligations.
-/

@[expose] public section
open Subgroup
namespace Held.OuterInvolution.FixedStructure

abbrev fixed : Subgroup He := action.fixedSubgroup

def aFixed : fixed := ⟨a, (MulAut.mem_fixedSubgroup action a).mpr a_fixed⟩

def brayFixed : fixed := ⟨bray, (MulAut.mem_fixedSubgroup action bray).mpr bray_fixed⟩

def first : fixed := brayFixed ^ 2

def second : fixed := (aFixed * brayFixed) ^ 12

/-- The specific subgroup whose index and central quotient remain to be certified. -/
def candidate : Subgroup fixed := closure {first, second}

theorem first_mem : first ∈ candidate := subset_closure (Set.mem_insert _ _)

theorem second_mem : second ∈ candidate := subset_closure (Set.mem_insert_of_mem _ rfl)

def firstGenerator : candidate := ⟨first, first_mem⟩

def secondGenerator : candidate := ⟨second, second_mem⟩

theorem closure_pair : closure ({firstGenerator, secondGenerator} : Set candidate) = ⊤ := by
  apply Subgroup.map_injective candidate.subtype_injective
  rw [MonoidHom.map_closure]
  simp only [Set.image_insert_eq, Set.image_singleton]
  change candidate = (⊤ : Subgroup candidate).map candidate.subtype
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem firstGenerator_pow : firstGenerator ^ 5 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change (bray ^ 2) ^ 5 = 1
  rw [← pow_mul]
  exact bray_pow_ten

theorem secondGenerator_pow : secondGenerator ^ 7 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  change ((a * bray) ^ 12) ^ 7 = 1
  rw [← pow_mul, show 12 * 7 = 21 * 4 from rfl, pow_mul,
    a_bray_pow_twenty_one, one_pow]

theorem productGenerator_pow : (firstGenerator * secondGenerator) ^ 6 = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  exact pair_product_pow_six

/-- The point orbit under the candidate, using zero-based letter 30. -/
abbrev PointOrbit := MulAction.orbit candidate (30 : Fin 2058)

def orbitAction : candidate →* Equiv.Perm PointOrbit := MulAction.toPermHom candidate PointOrbit

abbrev orbitKernel : Subgroup candidate := orbitAction.ker

abbrev orbitImage : Subgroup (Equiv.Perm PointOrbit) := orbitAction.range

theorem orbitAction_apply (d : candidate) (x : PointOrbit) :
    (orbitAction d x : Fin 2058) = representation d.val.val x.val := rfl

theorem mem_orbitKernel (d : candidate) : d ∈ orbitKernel ↔
    ∀ x : PointOrbit, representation d.val.val x.val = x.val := by
  change orbitAction d = 1 ↔ _
  constructor
  · intro h x
    exact congrArg (fun p : Equiv.Perm PointOrbit => (p x : Fin 2058)) h
  · intro h
    apply Equiv.ext
    intro x
    exact Subtype.ext (h x)

end Held.OuterInvolution.FixedStructure
