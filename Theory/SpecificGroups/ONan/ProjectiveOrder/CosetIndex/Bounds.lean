module

public import Theory.SpecificGroups.ONan.ProjectiveOrder.Setup
public import Theory.GroupTheory.PresentedGroupBounds
public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.Group.Subgroup.Lattice

/-!
# Bounds for the index of the O'Nan local subgroup

A cover by 122,760 representatives gives the upper bound by generation and
Lagrange's equality. For the lower bound, an arbitrary action suffices: if both
local generators fix an object with 122,760 distinct translates, the local
subgroup lies in its stabilizer and its index is at least that large. The
representatives in the two arguments need not coincide.

The concrete certificates are separate obligations; these lemmas assume neither
the ambient order nor the local subgroup order. See `../Setup.lean` for the
ATLAS subgroup words and source attribution.
-/

namespace ONan.OrderCertificate

/-- The two ambient projective generators indexed for coset certificates. -/
@[expose] public def cosetGenerators : Bool → Model
  | false => generatorA
  | true => generatorB

/-- The indexed pair generates the fixed model. -/
public theorem closure_cosetGenerators :
    Subgroup.closure (Set.range cosetGenerators) = ⊤ := by
  have h : Set.range cosetGenerators = ({generatorA, generatorB} : Set Model) := by
    ext x
    simp [cosetGenerators]
  rw [h]
  exact closure_generators

/-- Actual projective coset transitions give the numerical upper bound. -/
public theorem localSubgroup_index_le_of_cover
    (C : Subgroup.GeneratorCosetCover localSubgroup cosetGenerators (Fin 122760)) :
    localSubgroup.index ≤ 122760 := by
  have h := (C.finite_card_le closure_cosetGenerators).2
  rw [Nat.card_fin, card_model_eq] at h
  exact Nat.le_of_mul_le_mul_left h Nat.card_pos

/-- It suffices to check the two defining words to get a fixed object. -/
public theorem localSubgroup_le_stabilizer {X : Type*} [MulAction Model X] (x : X)
    (ha : localA • x = x) (hb : localB • x = x) :
    localSubgroup ≤ MulAction.stabilizer Model x := by
  apply (Subgroup.closure_le _).mpr
  exact Set.pair_subset_iff.mpr ⟨ha, hb⟩

/-- Distinct translates of a fixed object bound the index from below. -/
public theorem localSubgroup_index_ge_of_action {X : Type*} [MulAction Model X] (x : X)
    (ha : localA • x = x) (hb : localB • x = x)
    (repr : Fin 122760 → Model)
    (hinj : Function.Injective (fun i => repr i • x)) :
    122760 ≤ localSubgroup.index := by
  let f : Fin 122760 → MulAction.orbit Model x :=
    fun i => ⟨repr i • x, MulAction.mem_orbit x (repr i)⟩
  have hf : Function.Injective f := by
    intro i j h
    exact hinj (congrArg Subtype.val h)
  have : Finite (MulAction.orbit Model x) :=
    (Finite.finite_mulAction_orbit x).to_subtype
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Nat.card_fin, Nat.card_coe_set_eq, ← MulAction.index_stabilizer] at hcard
  exact hcard.trans (Subgroup.index_antitone (localSubgroup_le_stabilizer x ha hb))

end ONan.OrderCertificate
