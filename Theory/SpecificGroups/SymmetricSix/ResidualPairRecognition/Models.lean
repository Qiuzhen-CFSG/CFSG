module

public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Duad.Models
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Two tetrahedral subgroups of the symmetric group on six letters

The duad embedding is the alternating action on the four complementary letters.
The syntheme embedding is the action on the six edges of a tetrahedron, ordered
so opposite edges form the standard syntheme. Both maps are injective. In A₄,
the elements whose squares are one form the normal Klein four Sylow subgroup,
and every element is a product of two elements whose cubes are one.

The small action tables are checked by kernel reduction. These models support
the residual calculation in Aschbacher–Smith, the paragraph following 15.4.23,
printed p.1165 (combined manuscript, 1 March 2004).
-/

@[expose] public section

open Subgroup Equiv
namespace Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
set_option maxRecDepth 100000
abbrev A := alternatingGroup (Fin 4)
local instance : Fintype (Equiv.Perm (Fin 4)) := fintypePerm
local instance : Fintype S6 := fintypePerm
instance (g : Equiv.Perm (Fin 4)) : Decidable (g ∈ A) :=
  inferInstanceAs (Decidable (g.sign = 1))
local instance : Fintype A := Subtype.fintype _

/-- The six edges of a tetrahedron, with opposite edges consecutive. -/
def edge (i : Fin 6) : Finset (Fin 4) :=
  ![{0,1}, {2,3}, {0,2}, {1,3}, {0,3}, {1,2}] i

def edgeIndex (s : Finset (Fin 4)) : Fin 6 :=
  if s = edge 0 then 0 else if s = edge 1 then 1 else
  if s = edge 2 then 2 else if s = edge 3 then 3 else
  if s = edge 4 then 4 else 5

def edgeAction (a : A) (i : Fin 6) : Fin 6 := edgeIndex ((edge i).image a.val)

def synthemeHom : A →* S6 where
  toFun a := {
    toFun := edgeAction a
    invFun := edgeAction a⁻¹
    left_inv := by revert a; decide +kernel
    right_inv := by revert a; decide +kernel }
  map_one' := by decide +kernel
  map_mul' := by decide +kernel

def duadHom : A →* S6 :=
  duadProductHom.comp ((1 : A →* Equiv.Perm (Fin 2)).prod A.subtype)

theorem duadHom_injective : Function.Injective duadHom := by
  intro a b h
  exact Subtype.ext (congrArg Prod.snd (duadProductHom_injective h))

theorem synthemeHom_injective : Function.Injective synthemeHom := by decide +kernel

def klein : Subgroup A where
  carrier := {a | a ^ 2 = 1}
  one_mem' := by decide
  mul_mem' := by decide +kernel
  inv_mem' := by decide +kernel

instance (a : A) : Decidable (a ∈ klein) := inferInstanceAs (Decidable (a ^ 2 = 1))

instance : klein.Normal where
  conj_mem := by decide +kernel

theorem klein_card : Nat.card klein = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem klein_core : pCore 2 A = klein := by
  have hcard : Nat.card A = 12 := by rw [Nat.card_eq_fintype_card]; decide +kernel
  have hp : IsPGroup 2 klein := IsPGroup.of_card (n := 2) klein_card
  let P : Sylow 2 A := hp.toSylow (by
    have hi := klein.card_mul_index
    rw [klein_card, hcard] at hi
    have he : klein.index = 3 := by omega
    rw [he]
    decide)
  exact le_antisymm (pCore_isPGroup.le_sylow_of_normal P) (le_sSup ⟨inferInstance, hp⟩)

theorem odd_factorization (a : A) : ∃ b c : A, b ^ 3 = 1 ∧ c ^ 3 = 1 ∧ b * c = a := by
  revert a
  decide +kernel

instance (g : S6) : Decidable (g ∈ duadHom.range) :=
  inferInstanceAs (Decidable (∃ a : A, duadHom a = g))
instance (g : S6) : Decidable (g ∈ synthemeHom.range) :=
  inferInstanceAs (Decidable (∃ a : A, synthemeHom a = g))

end Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
