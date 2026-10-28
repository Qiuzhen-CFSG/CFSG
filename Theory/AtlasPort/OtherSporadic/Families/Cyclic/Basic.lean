/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Families/Cyclic/Basic.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Algebra.Group.Action.TypeTags
public import Mathlib.GroupTheory.GroupAction.Transitive

/-!
# Basic

The cyclic model is the multiplicative form of the additive residue group.
Its order and simplicity reduce to the corresponding facts about finite cyclic groups.

Source: Gerald Höhn, ATLAS, `Atlas/Families/Cyclic/Basic.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for downstream calculations in the source API.
-/

@[expose] public section

namespace Atlas.Families.Cyclic

abbrev Model (m : ℕ) := Multiplicative (ZMod m)
def IsAdmissible (m : ℕ) : Prop := m.Prime
def order (m : ℕ) : ℕ := m
def generator (m : ℕ) : Model m := Multiplicative.ofAdd 1

theorem finite (m : ℕ) (hm : 0 < m) : Finite (Model m) := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  infer_instance

theorem card (m : ℕ) (hm : 0 < m) : Nat.card (Model m) = order m := by
  let : NeZero m := ⟨Nat.ne_of_gt hm⟩
  simp [Model, order]

theorem commutative (m : ℕ) (a b : Model m) : a * b = b * a := mul_comm a b

theorem cyclic (m : ℕ) : IsCyclic (Model m) := inferInstance

theorem generator_order (m : ℕ) : orderOf (generator m) = m := by
  exact (orderOf_ofAdd_eq_addOrderOf (1 : ZMod m)).trans (ZMod.addOrderOf_one m)

theorem generator_generates (m : ℕ) : Subgroup.zpowers (generator m) = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨i, hi⟩ := ZMod.intCast_surjective x.toAdd
  refine ⟨i, ?_⟩
  change Multiplicative.ofAdd (i • (1 : ZMod m)) = x
  simpa using congrArg Multiplicative.ofAdd hi

theorem isSimpleGroup_iff (m : ℕ) (hm : 0 < m) :
    IsSimpleGroup (Model m) ↔ IsAdmissible m := by
  rw [CommGroup.is_simple_iff_prime_card, card m hm]
  rfl

theorem isSimpleGroup (p : ℕ) (hp : IsAdmissible p) : IsSimpleGroup (Model p) :=
  (isSimpleGroup_iff p hp.pos).2 hp

theorem translation (m : ℕ) (a : Model m) (x : ZMod m) : a • x = a.toAdd + x := rfl

theorem translation_mul (m : ℕ) (a b : Model m) (x : ZMod m) :
    (a * b) • x = a • (b • x) := mul_smul a b x

theorem regular (m : ℕ) (x y : ZMod m) : ∃! a : Model m, a • x = y := by
  refine ⟨Multiplicative.ofAdd (y - x), by simp [translation], ?_⟩
  intro a ha
  change a.toAdd + x = y at ha
  have h : a.toAdd = y - x := eq_sub_of_add_eq ha
  exact congrArg (Multiplicative.ofAdd : ZMod m → Model m) h

theorem faithful (m : ℕ) : FaithfulSMul (Model m) (ZMod m) := by
  constructor
  intro a b h
  have h0 := h 0
  simpa [translation] using h0

theorem transitive (m : ℕ) : MulAction.IsPretransitive (Model m) (ZMod m) :=
  ⟨fun x y => (regular m x y).exists⟩

theorem simple_iff_exists_prime_model (G : Type*) [CommGroup G] :
    IsSimpleGroup G ↔ ∃ p, IsAdmissible p ∧ Nonempty (G ≃* Model p) := by
  constructor
  · intro h
    let := h
    obtain ⟨p, hp, ⟨e⟩⟩ := exists_prime_addEquiv_ZMod (G := G)
    exact ⟨p, hp, ⟨e.toMultiplicativeRight⟩⟩
  · rintro ⟨p, hp, ⟨e⟩⟩
    let := isSimpleGroup p hp
    exact e.isSimpleGroup

theorem not_simple_one : ¬ IsSimpleGroup (Model 1) := by
  rw [isSimpleGroup_iff 1 (by decide)]
  exact Nat.not_prime_one

theorem simple_two : IsSimpleGroup (Model 2) := isSimpleGroup 2 (by exact Nat.prime_two)
theorem simple_three : IsSimpleGroup (Model 3) := isSimpleGroup 3 (by exact Nat.prime_three)
theorem not_simple_four : ¬ IsSimpleGroup (Model 4) := by
  rw [isSimpleGroup_iff 4 (by decide)]
  change ¬ Nat.Prime 4
  decide

end Atlas.Families.Cyclic
