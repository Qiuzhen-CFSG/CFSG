/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/GroupTheory/TwoActionObstruction.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.GroupTheory.PrimitiveMap

/-!
# Two-action obstruction to a normal factor

Map a primitive orbit to normal orbits; either alternative forces an excluded divisibility.

Source: Gerald Höhn, ATLAS, `Atlas/GroupTheory/TwoActionObstruction.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies are exposed where the downstream stabilizer constructions use reduction.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Atlas.GroupTheory
open MulAction
open scoped Pointwise

/-- A primitive orbit of a subgroup obstructs a normal factor of incompatible order. -/
theorem normal_factor_two_action_obstruction {G K A X : Type*}
    [Group G] [Group K] [MulAction K A] [MulAction G X]
    [Finite G] [Finite A] [Finite X] [IsPreprimitive K A] [IsPretransitive G X]
    (φ : K →* G) (j : A →ₑ[φ] X) (a : A)
    (N : Subgroup G) [N.Normal]
    (hfactor : ∀ g : G, ∃ n : N, ∃ k : K, g = n.val * φ k)
    (hA : ¬ Nat.card A ∣ Nat.card X) (hN : ¬ Nat.card X ∣ Nat.card N) : False := by
  classical
  have hj (k : K) (b : A) : j (k • b) = φ k • j b := j.map_smul' k b
  let B := orbit N (j a)
  let f : A →ₑ[φ] Set X := {
    toFun b := orbit N (j b)
    map_smul' k b := by
      rw [hj]
      exact (smul_orbit_eq_orbit_smul N (j b) (φ k)).symm }
  have hr : Set.range f = orbit G B := by
    ext C
    constructor
    · rintro ⟨b,rfl⟩
      obtain ⟨k,hk⟩ := exists_smul_eq K a b
      refine mem_orbit_iff.mpr ⟨φ k,?_⟩
      change φ k • orbit N (j a) = orbit N (j b)
      rw [smul_orbit_eq_orbit_smul,← hj,hk]
    · rintro ⟨g,rfl⟩
      obtain ⟨n,k,hg⟩ := hfactor g
      refine ⟨k • a,?_⟩
      change orbit N (j (k • a)) = g • orbit N (j a)
      rw [hg,mul_smul,hj,smul_orbit_eq_orbit_smul]
      exact (smul_orbit n (φ k • j a)).symm
  have hB : IsBlock G B := IsBlock.orbit_of_normal _
  have hc := hB.ncard_block_mul_ncard_orbit_eq ⟨j a,mem_orbit_self _⟩
  have hcr : Nat.card (Set.range f) = Nat.card (orbit G B) := Nat.card_congr (Equiv.setCongr hr)
  rcases primitive_map_injective_or_constant f with hi | he
  · apply hA
    have hca : Nat.card A = Nat.card (orbit G B) :=
      (Nat.card_congr (Equiv.ofInjective f hi)).trans hcr
    refine ⟨B.ncard,?_⟩
    change B.ncard * Nat.card (orbit G B) = Nat.card X at hc
    rw [← hca] at hc
    exact hc.symm.trans (Nat.mul_comm _ _)
  · have hs : Set.range f = {f a} := by
      ext C
      constructor
      · rintro ⟨b,rfl⟩; exact he b a
      · intro h; exact ⟨a,h.symm⟩
    have ho : Nat.card (orbit G B) = 1 := by
      rw [← hcr,hs]
      simp
    change B.ncard * Nat.card (orbit G B) = Nat.card X at hc
    rw [ho,mul_one] at hc
    apply hN
    have hn := Nat.card_congr (orbitProdStabilizerEquivGroup N (j a))
    rw [Nat.card_prod] at hn
    change Nat.card (orbit N (j a)) = Nat.card X at hc
    rw [hc] at hn
    exact ⟨_,hn.symm⟩

end Atlas.GroupTheory
