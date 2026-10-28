module
public import Theory.SpecificGroups.AlternatingFiveBorelProjection
public import Theory.GroupTheory.TwoPerfectCubicImages.SupportedCommutator
/-!
# Supported transpositions saturate the A₄ projection

A transposition normalizing the point stabilizer A₄ fixes its distinguished
point. Its commutator with a suitable cubic is a nontrivial cubic. The
normal-subgroup criterion for two-perfect cubic extensions then puts the
whole residual actor into the component containing its supported commutators.
Source: Aschbacher–Smith, 13.6.15, printed p.930 (PDF p.947).
-/

public section
open Subgroup
open scoped commutatorElement
namespace AlternatingFiveProjection
open BinaryPermutation.AlternatingFiveBorel BinaryPermutation.AlternatingFiveFlag
local instance : DecidablePred (· ∈ B) := fun g => inferInstanceAs (Decidable (g.val 4=4))
local instance : Fintype B := Subtype.fintype _

private theorem normalizing_fixes : ∀ t : Equiv.Perm (Fin 5),
    (∀ b : B, (t*b.val.val*t⁻¹) 4=4) → t 4=4 := by decide +kernel

private theorem cubic_commutator : ∀ t : Equiv.Perm (Fin 5),
    t.IsSwap → t 4=4 → (⁅c₀.val.val,t⁆)^3=1 ∧ ⁅c₀.val.val,t⁆≠1 := by
  simp only [Equiv.Perm.IsSwap]
  decide +kernel

theorem le_component_of_supported_transposition {D : Type*} [Group D]
    (H C : Subgroup D) [C.Normal]
    (hp : IsPPerfect 2 H) (hc : Nat.card (H ⧸ pCore 2 H) = 3)
    (r : D →* Equiv.Perm (Fin 5))
    (hr : H.map r = B.map (alternatingGroup (Fin 5)).subtype)
    (a : D) (ha : a ∈ normalizer (H : Set D)) (hat : (r a).IsSwap)
    (hcomm : ∀ h ∈ H, ⁅h,a⁆ ∈ C) : H ≤ C := by
  have hn : r a ∈ normalizer (B.map (alternatingGroup (Fin 5)).subtype : Set _) := by
    rw [← hr]
    exact le_normalizer_map r (mem_map.mpr ⟨a,ha,rfl⟩)
  have hafix : r a 4=4 := normalizing_fixes (r a) (by
    intro b
    have hb := (hn b.val.val).mp (mem_map.mpr ⟨b.val,b.property,rfl⟩)
    obtain ⟨x,hx,hxb⟩ := hb
    exact hxb ▸ hx)
  have hbc : c₀.val.val ∈ H.map r := by
    rw [hr]
    exact mem_map.mpr ⟨c₀.val,c₀.property,rfl⟩
  obtain ⟨b,hb,he⟩ := hbc
  have hm : r ⁅b,a⁆ = ⁅c₀.val.val,r a⁆ := by
    simp only [commutatorElement_def,map_mul,map_inv,he]
  have ht := cubic_commutator (r a) hat hafix
  exact le_normal_of_supported_cubic_commutator H C hp hc r a ha hcomm ⟨b,hb⟩
    (by rw [hm]; exact ht.1) (by rw [hm]; exact ht.2)
end AlternatingFiveProjection
