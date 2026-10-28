module

/-
Adapted from Atlas/GroupTheory/FiniteGeneratorActionComparison.lean,
revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917, by Gerald Höhn
and the ATLAS contributors. ATLAS Research and Attribution License 1.0
applies; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
Changes: Lean 4.33 module boundaries, narrow imports, and CFSG order APIs.
-/

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.Group.Subgroup.Ker
set_option warningAsError false

public section

/-!
# Comparing faithful actions through generators

Two finite groups of equal order are isomorphic when their faithful actions
have compatible images on a generating set. Generation gives range inclusion;
equal cardinality gives equality, and the two range equivalences give the map.
-/


namespace Atlas.GroupTheory

variable {G H P : Type*} [Group G] [Group H] [Group P]

theorem range_le_of_generators (f : G →* P) (k : H →* P)
    (S : Set G) (hS : Subgroup.closure S = ⊤)
    (h : ∀ s ∈ S, f s ∈ k.range) : f.range ≤ k.range := by
  rw [MonoidHom.range_eq_map, ← hS, MonoidHom.map_closure]
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨s, hs, rfl⟩
  exact h s hs

theorem ranges_eq_of_generators_of_card [Finite G] [Finite H]
    (f : G →* P) (k : H →* P) (hf : Function.Injective f)
    (hk : Function.Injective k) (hc : Nat.card G = Nat.card H)
    (S : Set G) (hS : Subgroup.closure S = ⊤)
    (h : ∀ s ∈ S, f s ∈ k.range) : f.range = k.range := by
  let : Finite k.range := Finite.of_equiv H (MonoidHom.ofInjective hk).toEquiv
  apply Subgroup.eq_of_le_of_card_ge (range_le_of_generators f k S hS h)
  rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv,
    ← Nat.card_congr (MonoidHom.ofInjective hk).toEquiv, hc]

noncomputable def equivOfGeneratorActions [Finite G] [Finite H]
    (f : G →* P) (k : H →* P) (hf : Function.Injective f)
    (hk : Function.Injective k) (hc : Nat.card G = Nat.card H)
    (S : Set G) (hS : Subgroup.closure S = ⊤)
    (h : ∀ s ∈ S, f s ∈ k.range) : G ≃* H :=
  (MonoidHom.ofInjective hf).trans
    ((MulEquiv.subgroupCongr (ranges_eq_of_generators_of_card f k hf hk hc S hS h)).trans
      (MonoidHom.ofInjective hk).symm)

theorem equivOfGeneratorActions_coherence [Finite G] [Finite H]
    (f : G →* P) (k : H →* P) (hf : Function.Injective f)
    (hk : Function.Injective k) (hc : Nat.card G = Nat.card H)
    (S : Set G) (hS : Subgroup.closure S = ⊤)
    (h : ∀ s ∈ S, f s ∈ k.range) (g : G) :
    k (equivOfGeneratorActions f k hf hk hc S hS h g) = f g := by
  exact MonoidHom.apply_ofInjective_symm hk _

end Atlas.GroupTheory
