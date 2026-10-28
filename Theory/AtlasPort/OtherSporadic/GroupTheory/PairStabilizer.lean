/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/PairStabilizer.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Mathlib.GroupTheory.GroupAction.SubMulAction.OfStabilizer
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Setwise and pointwise pair stabilizers

Restriction to the two-point set identifies the pointwise kernel and gives its index.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/PairStabilizer.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies are exposed where the downstream stabilizer constructions use reduction.
-/

@[expose] public section

noncomputable section
namespace Atlas.GroupTheory
open MulAction
open scoped Pointwise

variable {G X : Type*} [Group G] [MulAction G X]

abbrev PairStabilizer (a b : X) := stabilizer G ({a,b} : Set X)

theorem pairStabilizer_mem (a b : X) (hab : a ≠ b) (g : G) :
    g ∈ PairStabilizer (G := G) a b ↔
      (g • a = a ∧ g • b = b) ∨ (g • a = b ∧ g • b = a) := by
  rw [mem_stabilizer_iff]
  constructor
  · intro hg
    have ha : g • a ∈ ({a,b} : Set X) := hg ▸ Set.smul_mem_smul_set (Or.inl rfl)
    have hb : g • b ∈ ({a,b} : Set X) := hg ▸ Set.smul_mem_smul_set (Or.inr rfl)
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact False.elim (hab (smul_left_cancel g (ha.trans hb.symm)))
    · exact Or.inl ⟨ha,hb⟩
    · exact Or.inr ⟨ha,hb⟩
    · exact False.elim (hab (smul_left_cancel g (ha.trans hb.symm)))
  · rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
    · simp [Set.smul_set_insert,Set.smul_set_singleton,ha,hb]
    · simp [Set.smul_set_insert,Set.smul_set_singleton,ha,hb,Set.pair_comm]

theorem pairStabilizer_swap [IsMultiplyPretransitive G X 2] (a b : X) (hab : a ≠ b) :
    ∃ g : PairStabilizer (G := G) a b, g.val • a = b ∧ g.val • b = a := by
  obtain ⟨g,ha,hb⟩ := (is_two_pretransitive_iff.mp
    (inferInstance : IsMultiplyPretransitive G X 2)) hab hab.symm
  exact ⟨⟨g,(pairStabilizer_mem a b hab g).mpr (Or.inr ⟨ha,hb⟩)⟩,ha,hb⟩

theorem pairStabilizer_transitive [IsMultiplyPretransitive G X 2]
    (a b : X) (hab : a ≠ b) : IsPretransitive (PairStabilizer (G := G) a b) ({a,b} : Set X) := by
  obtain ⟨g,hga,hgb⟩ := pairStabilizer_swap (G := G) a b hab
  constructor
  intro x y
  by_cases hxy : x = y
  · exact ⟨1,by simpa using hxy⟩
  refine ⟨g,Subtype.ext ?_⟩
  change g.val • x.val = y.val
  rcases x.prop with hx | hx <;> rcases y.prop with hy | hy
  · exact False.elim (hxy (Subtype.ext (hx.trans hy.symm)))
  · rw [hx,hy]; exact hga
  · rw [hx,hy]; exact hgb
  · exact False.elim (hxy (Subtype.ext (hx.trans hy.symm)))

def pairStabilizerPointEquiv (a b : X) (hab : a ≠ b) :
    stabilizer (PairStabilizer (G := G) a b) (⟨a,Or.inl rfl⟩ : ({a,b} : Set X)) ≃*
      fixingSubgroup G ({a,b} : Set X) where
  toFun g := ⟨g.val.val,by
    have ha : g.val.val • a = a := congrArg Subtype.val g.prop
    have hb : g.val.val • b = b := by
      rcases (pairStabilizer_mem a b hab g.val.val).mp g.val.prop with h | h
      · exact h.2
      · exact False.elim (hab (ha.symm.trans h.1))
    intro x
    rcases x.prop with h | h
    · rw [h,ha]
    · rw [h,hb]⟩
  invFun g := ⟨⟨g.val,(pairStabilizer_mem a b hab g.val).mpr
    (Or.inl ⟨g.prop ⟨a,Or.inl rfl⟩,g.prop ⟨b,Or.inr rfl⟩⟩)⟩,
    Subtype.ext (g.prop ⟨a,Or.inl rfl⟩)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem pairStabilizer_order [Finite G] [IsMultiplyPretransitive G X 2]
    (a b : X) (hab : a ≠ b) :
    Nat.card (PairStabilizer (G := G) a b) = 2 * Nat.card (fixingSubgroup G ({a,b} : Set X)) := by
  have := pairStabilizer_transitive (G := G) a b hab
  let x : ({a,b} : Set X) := ⟨a,Or.inl rfl⟩
  have he : orbit (PairStabilizer (G := G) a b) x ≃ ({a,b} : Set X) :=
    Equiv.ofBijective Subtype.val ⟨Subtype.val_injective,by
      intro y
      exact ⟨⟨y,mem_orbit_iff.mpr (exists_smul_eq _ x y)⟩,rfl⟩⟩
  have h := Nat.card_congr (orbitProdStabilizerEquivGroup (PairStabilizer (G := G) a b) x)
  rw [Nat.card_prod,Nat.card_congr he,Nat.card_congr (pairStabilizerPointEquiv a b hab).toEquiv] at h
  have hc : Nat.card ({a,b} : Set X) = 2 := by
    classical
    simp [Nat.card_eq_fintype_card,hab]
  rw [hc] at h
  exact h.symm

def pairRestrictionHom (a b : X) : PairStabilizer (G := G) a b →*
    Equiv.Perm ({a,b} : Set X) := MulAction.toPermHom _ _

theorem pairRestriction_ker (a b : X) (hab : a ≠ b) :
    (pairRestrictionHom (G := G) a b).ker =
      stabilizer (PairStabilizer (G := G) a b) (⟨a,Or.inl rfl⟩ : ({a,b} : Set X)) := by
  ext g
  constructor
  · intro hg
    exact congrArg (fun σ : Equiv.Perm ({a,b} : Set X) => σ ⟨a,Or.inl rfl⟩) hg
  · intro hg
    have ha : g.val • a = a := congrArg Subtype.val hg
    have hb : g.val • b = b := by
      rcases (pairStabilizer_mem a b hab g.val).mp g.prop with h | h
      · exact h.2
      · exact False.elim (hab (ha.symm.trans h.1))
    apply Equiv.ext
    intro x
    apply Subtype.ext
    change g.val • x.val = x.val
    rcases x.prop with h | h
    · rw [h,ha]
    · rw [h,hb]

def pairRestrictionKernelEquiv (a b : X) (hab : a ≠ b) :
    (pairRestrictionHom (G := G) a b).ker ≃* fixingSubgroup G ({a,b} : Set X) :=
  (MulEquiv.subgroupCongr (pairRestriction_ker a b hab)).trans (pairStabilizerPointEquiv a b hab)

theorem pairRestriction_surjective [Finite G] [IsMultiplyPretransitive G X 2]
    (a b : X) (hab : a ≠ b) : Function.Surjective (pairRestrictionHom (G := G) a b) := by
  classical
  let f := pairRestrictionHom (G := G) a b
  have hk := Nat.card_congr (pairRestrictionKernelEquiv (G := G) a b hab).toEquiv
  have h := f.ker.card_mul_index
  rw [Subgroup.index_ker,pairStabilizer_order a b hab,← hk] at h
  have hr : Nat.card f.range = 2 := by
    rw [mul_comm 2] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := f.ker)) h
  have hp : Nat.card (Equiv.Perm ({a,b} : Set X)) = 2 := by
    rw [Nat.card_perm]
    have hc : Nat.card ({a,b} : Set X) = 2 := by simp [Nat.card_eq_fintype_card,hab]
    rw [hc]
    rfl
  exact MonoidHom.range_eq_top.mp (Subgroup.eq_top_of_card_eq f.range (hr.trans hp.symm))

end Atlas.GroupTheory
