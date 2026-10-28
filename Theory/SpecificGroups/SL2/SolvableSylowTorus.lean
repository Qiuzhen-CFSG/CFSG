module
public import Theory.SpecificGroups.SL2.SolvableSylowCore
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Torus quotients of solvable binary SL₂ Sylow overgroups

The Borel diagonal homomorphism restricts to every solvable full-Sylow
subgroup of a binary SL₂ cover. Its kernel is exactly the subgroup's
two-core. Thus the literal core quotient embeds in the field's unit group,
and its order divides the torus order. No complement is chosen.

Source: the rank-one Borel calculation used in Aschbacher--Smith
14.6.15, printed pp.1033--1034.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.SpecialLinearGroup
variable {A F : Type*} [Group A] [Finite A] [Field F] [Finite F] [CharP F 2]

/-- The actual two-core quotient embeds into the multiplicative field group. -/
theorem solvable_sylow_overgroup_torus_embedding
    (q : A →* SL(2,F)) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hns : ¬ Group.IsSolvable SL(2,F)) (P : Sylow 2 A)
    (B : Subgroup A) [Group.IsSolvable B] (hPB : (P : Subgroup A) ≤ B) :
    ∃ f : (B ⧸ pCore 2 B) →* Fˣ, Function.Injective f := by
  have hc := solvable_sylow_overgroup_core q hq hk hns P B hPB
  have hn : B ≤ normalizer (P : Set A) := by
    change B ≤ normalizer ((P : Subgroup A) : Set A)
    rw [←hc]
    exact B.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
  obtain ⟨d,_,hd⟩ := exists_sylowNormalizer_diagonal q hq P (hk.le_sylow_of_normal P)
  let f : B →* Fˣ := d.comp (inclusion hn)
  have he : f.ker = pCore 2 B := by
    ext x
    change d (inclusion hn x) = 1 ↔ x ∈ pCore 2 B
    rw [hd]
    change (x : A) ∈ (P : Subgroup A) ↔ x ∈ pCore 2 B
    rw [←hc]
    exact mem_map_iff_mem B.subtype_injective
  let e : (B ⧸ pCore 2 B) ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq he.symm).trans (QuotientGroup.quotientKerEquivRange f)
  exact ⟨f.range.subtype.comp e.toMonoidHom,f.range.subtype_injective.comp e.injective⟩

/-- The literal quotient order divides the rank-one torus order. -/
theorem solvable_sylow_overgroup_quotient_card_dvd
    (q : A →* SL(2,F)) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (hns : ¬ Group.IsSolvable SL(2,F)) (P : Sylow 2 A)
    (B : Subgroup A) [Group.IsSolvable B] (hPB : (P : Subgroup A) ≤ B) :
    Nat.card (B ⧸ pCore 2 B) ∣ Nat.card F - 1 := by
  obtain ⟨f,hf⟩ := solvable_sylow_overgroup_torus_embedding q hq hk hns P B hPB
  simpa only [Nat.card_units] using card_dvd_of_injective f hf
end Matrix.SpecialLinearGroup
