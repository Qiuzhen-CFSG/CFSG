module

public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeSylow
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Tactic

/-!
# The regular dihedral subgroup on eight letters

The fixed rotation and reflection act regularly. A conjugate of the established
binary-tree two-group supplies an obstruction to proper extensions of this
subgroup inside a group in which it is Sylow. All permutation certificates
below are checked by the kernel.
-/

@[expose] public section
open Equiv Subgroup
namespace Theory.SpecificGroups.SymmetricEight.RegularDihedralPair

abbrev P8 := Equiv.Perm (Fin 8)

def r : P8 where
  toFun := ![6,0,7,1,2,4,3,5]
  invFun := ![1,3,4,6,5,7,0,2]
  left_inv := by decide
  right_inv := by decide

def s : P8 where
  toFun := ![5,4,3,2,1,0,7,6]
  invFun := ![5,4,3,2,1,0,7,6]
  left_inv := by decide
  right_inv := by decide

def tWord (i : Fin 8) : P8 := r ^ (i.val % 4) * s ^ (i.val / 4)

private theorem words_mul (i j : Fin 8) :
    ∃ k : Fin 8, tWord i * tWord j = tWord k := by
  decide +revert +kernel

private theorem words_inv (i : Fin 8) : ∃ j : Fin 8, (tWord i)⁻¹ = tWord j := by
  decide +revert +kernel

def twoGroup : Subgroup P8 where
  carrier := Set.range tWord
  one_mem' := ⟨0, by decide⟩
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨k, hk⟩ := words_mul i j
    exact ⟨k, hk.symm⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := words_inv i
    exact ⟨j, hj.symm⟩

instance (g : P8) : Decidable (g ∈ twoGroup) :=
  inferInstanceAs (Decidable (∃ i : Fin 8, tWord i = g))

theorem r_mem : r ∈ twoGroup := ⟨1, by decide⟩
theorem s_mem : s ∈ twoGroup := ⟨4, by decide⟩
theorem tWord_mem (i : Fin 8) : tWord i ∈ twoGroup := ⟨i, rfl⟩
theorem r_four : r ^ 4 = 1 := by decide
theorem r_square_ne : r ^ 2 ≠ 1 := by decide

theorem twoGroup_card : Nat.card twoGroup = 8 := by
  let f : Fin 8 → twoGroup := fun i => ⟨tWord i, tWord_mem i⟩
  have hi : Function.Injective tWord := by decide +kernel
  have hb : Function.Bijective f := ⟨fun i j h => hi (congrArg Subtype.val h), by
    rintro ⟨g, i, rfl⟩
    exact ⟨i, rfl⟩⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hb)]
  simp

theorem twoGroup_regular : Function.Bijective (fun i : Fin 8 => tWord i 0) := by
  decide +kernel

def treeMarking : P8 where
  toFun := ![0,2,4,1,6,5,3,7]
  invFun := ![0,3,1,6,2,5,4,7]
  left_inv := by decide
  right_inv := by decide

def obstruction : Subgroup P8 :=
  A6ShadowTwoLocals.treeGroup.comap (MulAut.conj treeMarking).toMonoidHom

def treeCode (g : P8) : Fin 128 :=
  ⟨((g⁻¹ 0).val % 2 + 2 * ((g⁻¹ 2).val % 2) +
    4 * ((g⁻¹ 4).val % 2) + 8 * ((g⁻¹ 6).val % 2) +
    16 * ((g⁻¹ 0).val / 2 % 2) + 32 * ((g⁻¹ 4).val / 2 % 2) +
    64 * ((g⁻¹ 0).val / 4)) % 128, Nat.mod_lt _ (by decide)⟩

/-- A direct normal-form equality certifying membership in the obstruction. -/
def TreeTest (g : P8) : Prop :=
  let h := treeMarking * g * treeMarking⁻¹
  h = A6ShadowTwoLocals.treeWord (treeCode h)

instance (g : P8) : Decidable (TreeTest g) := inferInstanceAs (Decidable (_ = _))

theorem treeTest_mem {g : P8} (h : TreeTest g) : g ∈ obstruction := by
  change treeMarking * g * treeMarking⁻¹ ∈ A6ShadowTwoLocals.treeGroup
  rw [show treeMarking * g * treeMarking⁻¹ = _ from h]
  exact A6ShadowTwoLocals.treeWord_mem _

theorem twoGroup_le_obstruction : twoGroup ≤ obstruction := by
  rintro _ ⟨i, rfl⟩
  exact treeTest_mem ((by decide +kernel : ∀ i : Fin 8, TreeTest (tWord i)) i)

theorem obstruction_isPGroup : IsPGroup 2 obstruction :=
  (IsPGroup.of_card (p := 2) (n := 7) A6ShadowTwoLocals.card_treeGroup).comap_of_injective
    (MulAut.conj treeMarking).toMonoidHom (MulAut.conj treeMarking).injective

/-- The literal eight-group is a maximal two-subgroup of the ambient subgroup. -/
def MaximalTwo (X : Subgroup P8) : Prop :=
  twoGroup ≤ X ∧ ∀ K : Subgroup P8, IsPGroup 2 K → K ≤ X → twoGroup ≤ K → K = twoGroup

theorem maximalTwo_of_sylow (X : Subgroup P8) (S : Sylow 2 X)
    (hS : (S : Subgroup X).map X.subtype = twoGroup) : MaximalTwo X := by
  have hTX : twoGroup ≤ X := by
    rw [← hS]
    rintro _ ⟨g, _, rfl⟩
    exact g.property
  refine ⟨hTX, ?_⟩
  intro K hK hKX hTK
  have hSK : (S : Subgroup X) ≤ K.subgroupOf X := by
    intro g hg
    exact hTK (hS ▸ mem_map_of_mem X.subtype hg)
  have he := S.is_maximal' hK.comap_subtype hSK
  apply le_antisymm ?_ hTK
  intro g hg
  have hgS : (⟨g, hKX hg⟩ : X) ∈ (S : Subgroup X) := he ▸ hg
  exact hS ▸ mem_map_of_mem X.subtype hgS

theorem mem_twoGroup_of_obstruction {X : Subgroup P8} (hX : MaximalTwo X)
    {g : P8} (hg : g ∈ X) (ho : g ∈ obstruction) : g ∈ twoGroup := by
  have he := hX.2 (X ⊓ obstruction) (obstruction_isPGroup.to_le inf_le_right)
    inf_le_left (le_inf hX.1 twoGroup_le_obstruction)
  exact he ▸ show g ∈ X ⊓ obstruction from ⟨hg, ho⟩

def eval {n : ℕ} (generators : Fin n → P8) (w : List (Fin n)) : P8 :=
  (w.map generators).prod

theorem eval_mem {n : ℕ} (X : Subgroup P8) (generators : Fin n → P8)
    (h : ∀ i, generators i ∈ X) (w : List (Fin n)) : eval generators w ∈ X := by
  induction w with
  | nil => exact X.one_mem
  | cons i w ih => exact X.mul_mem (h i) ih

end Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
