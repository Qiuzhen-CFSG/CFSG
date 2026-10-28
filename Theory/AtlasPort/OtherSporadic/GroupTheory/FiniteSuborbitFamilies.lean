/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/FiniteSuborbitFamilies.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.FiniteSuborbitPrimitivity

/-!
# Primitivity from suborbit families

A disjoint partition by stabilizer-transitive families reduces the block criterion to divisibility of sums of family sizes.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/FiniteSuborbitFamilies.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
-/

@[expose] public section

noncomputable section
namespace Atlas.GroupTheory
open scoped BigOperators
open MulAction

/-- An actual finite family partition can be used directly in the suborbit
criterion, without making the geometric development choose numerical labels. -/
theorem primitive_of_suborbit_families {G X I : Type*}
    [Group G] [MulAction G X] [Finite X] [IsPretransitive G X]
    [Fintype I] [DecidableEq I] [DecidableEq X]
    (a : X) (F : I → Finset X) (i₀ : I) (ha : a ∈ F i₀)
    (hcover : ∀ x, ∃ i, x ∈ F i)
    (hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)))
    (htrans : ∀ i x y, x ∈ F i → y ∈ F i →
      ∃ g : stabilizer G a, g • x = y)
    (harith : ∀ S : Finset I, i₀ ∈ S → (∑ i ∈ S, (F i).card) ∣ Nat.card X →
      (∑ i ∈ S, (F i).card) = 1 ∨ (∑ i ∈ S, (F i).card) = Nat.card X) :
    IsPreprimitive G X := by
  classical
  let f : X → I := fun x => (hcover x).choose
  have hf (x : X) : x ∈ F (f x) := (hcover x).choose_spec
  have hi (x : X) (i : I) : f x = i ↔ x ∈ F i := by
    constructor
    · intro h; simpa only [h] using hf x
    · intro hx
      by_contra h
      exact (Finset.disjoint_left.mp (hdisjoint h)) (hf x) hx
  have hcard (i : I) : Nat.card {x : X // f x = i} = (F i).card := by
    let e : {x : X // f x = i} ≃ {x : X // x ∈ F i} :=
      { toFun := fun x => ⟨x.val,(hi x.val i).mp x.property⟩
        invFun := fun x => ⟨x.val,(hi x.val i).mpr x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e]
    exact Nat.card_eq_finsetCard _
  refine primitive_of_suborbit_sums a f ?_ (fun i => (F i).card) hcard ?_
  · intro x y hxy
    exact htrans (f x) x y (hf x) ((hi y (f x)).mp hxy.symm)
  · intro S hS hd
    rw [(hi a i₀).mpr ha] at hS
    exact harith S hS hd

end Atlas.GroupTheory
