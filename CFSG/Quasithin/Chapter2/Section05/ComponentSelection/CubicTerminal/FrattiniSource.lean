module
public import Theory.GroupTheory.PairedNormalizerFrattini

/-!
# The original common Sylow and Frattini rechoice

A cubic subgroup in the literal triple normalizer extends to an actual Sylow
three-subgroup there. The original crossing x swaps D and Dˣ and preserves R;
Frattini's argument rechooses x to normalize this same Sylow while preserving
all three marked subgroups. The source right-conjugation convention is
retained throughout: Dˣ is `D.conjBy x⁻¹`.

The order-nine and faithful-action calculations are separate from this
construction. Source: Aschbacher--Smith 2.5.7, final paragraph, printed p.556.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CubicTerminal
variable {G : Type*} [Group G] [Finite G]

theorem exists_common_sylow_rechoice (D R X : Subgroup G) (x : G)
    (hD : x ^ 2 ∈ normalizer (D : Set G)) (hR : x ∈ normalizer (R : Set G))
    (hX : Nat.card X = 3)
    (hXN : X ≤ normalizer (D : Set G) ⊓ normalizer (D.conjBy x⁻¹ : Set G) ⊓
      normalizer (R : Set G)) :
    ∃ Y : Subgroup G, X ≤ Y ∧
      (∃ P : Sylow 3 (pairNormalizer D R x⁻¹),
        (P : Subgroup (pairNormalizer D R x⁻¹)).map (pairNormalizer D R x⁻¹).subtype = Y) ∧
      ∃ y : G, y ∈ normalizer (Y : Set G) ∧
        D.conjBy y⁻¹ = D.conjBy x⁻¹ ∧
        (D.conjBy x⁻¹).conjBy y⁻¹ = D ∧ R.conjBy y⁻¹ = R := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let N := pairNormalizer D R x⁻¹
  have hp : IsPGroup 3 (X.subgroupOf N) :=
    (IsPGroup.of_card (p := 3) (n := 1) hX).comap_subtype
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hXle : X ≤ (P : Subgroup N).map N.subtype := by
    rw [← map_subgroupOf_eq_of_le hXN]
    exact map_mono hP
  have hDinv : (x⁻¹) ^ 2 ∈ normalizer (D : Set G) := by
    rw [inv_pow]
    exact (normalizer (D : Set G)).inv_mem hD
  obtain ⟨y, hy, hDy, hDxy, hRy⟩ := pair_frattini_rechoice D R x⁻¹ hDinv
    ((normalizer (R : Set G)).inv_mem hR) P
  refine ⟨_, hXle, ⟨P, rfl⟩, y⁻¹, (normalizer _).inv_mem hy, ?_⟩
  simpa only [inv_inv] using And.intro hDy (And.intro hDxy hRy)
end CFSG.Quasithin.Chapter2.Section05.ComponentSelection.CubicTerminal
