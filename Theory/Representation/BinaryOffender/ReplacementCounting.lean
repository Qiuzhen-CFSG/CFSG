module

public import Theory.Representation.BinaryOffender.ReplacementConstruction
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.GroupTheory.Index

/-!
# Counting the cosets in binary Thompson replacement

Writing `B = C_A([v,A])`, displacement of `v` induces an injection from the
left cosets `A/B` into `([v,A] + C_V(A))/C_V(A)`. This map need not be a
homomorphism; the proof uses it only as an injection of finite sets.
The resulting cardinal inequality and rank-nullity give the replacement
rank bound. In particular the quotient by `B` is formed inside `A`, with
no ambient normality assumption.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, proof of B.1.4(3), printed pp. 68–69.
-/

public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem displacement_difference_fixed_iff {A : Subgroup G}
    (hA : IsElementaryTwo A) (v : V) (a b : A) :
    ρ (a : G) v - ρ (b : G) v ∈ fixedSpace ρ A ↔
      (a⁻¹ * b : A) ∈ (replacementSubgroup ρ A v).subgroupOf A := by
  change _ ↔ (a : G)⁻¹ * (b : G) ∈ replacementSubgroup ρ A v
  rw [mem_replacementSubgroup_iff_displacement ρ hA (A.mul_mem (A.inv_mem a.property) b.property)]
  have heq : ρ (a : G)⁻¹ (ρ (b : G) v - ρ (a : G) v) =
      ρ ((a : G)⁻¹ * b) v - v := by
    simp only [map_sub, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply]
  have heq' : ρ (a : G) (ρ ((a : G)⁻¹ * b) v - v) =
      ρ (b : G) v - ρ (a : G) v := by
    rw [map_sub, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  constructor
  · intro h
    have hn := (fixedSpace ρ A).neg_mem h
    simp only [neg_sub] at hn
    have hf := (Representation.mem_invariants _ _).mp hn a⁻¹
    change ρ (a : G)⁻¹ (ρ (b : G) v - ρ (a : G) v) = _ at hf
    rw [heq] at hf
    exact hf.symm ▸ hn
  · intro h
    have hf := (Representation.mem_invariants _ _).mp h a
    change ρ (a : G) (ρ ((a : G)⁻¹ * b) v - v) = _ at hf
    rw [heq'] at hf
    have hn := hf.symm ▸ h
    simpa only [neg_sub] using (fixedSpace ρ A).neg_mem hn

private theorem replacement_quotient_card_le [Finite G] [FiniteDimensional (ZMod 2) V]
    {A : Subgroup G} (hA : IsElementaryTwo A) (v : V) :
    Nat.card (A ⧸ (replacementSubgroup ρ A v).subgroupOf A) ≤
      Nat.card (↥(displacementSpan ρ A v ⊔ fixedSpace ρ A) ⧸
        (fixedSpace ρ A).comap (displacementSpan ρ A v ⊔ fixedSpace ρ A).subtype) := by
  let W := displacementSpan ρ A v ⊔ fixedSpace ρ A
  let F := (fixedSpace ρ A).comap W.subtype
  let C := (replacementSubgroup ρ A v).subgroupOf A
  let δ : A → W := fun a => ⟨ρ (a : G) v - v,
    Submodule.mem_sup_left (Submodule.subset_span ⟨a, a.property, rfl⟩)⟩
  have hδ (a b : A) :
      (Submodule.Quotient.mk (δ a) : W ⧸ F) = Submodule.Quotient.mk (δ b) ↔
        QuotientGroup.leftRel C a b := by
    rw [Submodule.Quotient.eq, QuotientGroup.leftRel_apply]
    change (ρ (a : G) v - v) - (ρ (b : G) v - v) ∈ fixedSpace ρ A ↔ _
    rw [sub_sub_sub_cancel_right]
    exact displacement_difference_fixed_iff ρ hA v a b
  let f : (A ⧸ C) → W ⧸ F := Quotient.lift (fun a => Submodule.Quotient.mk (δ a))
    (fun a b hab => (hδ a b).mpr hab)
  have hf : Function.Injective f := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b hab
    exact Quotient.sound ((hδ a b).mp hab)
  let : Finite (W ⧸ F) := Module.finite_of_finite (ZMod 2)
  exact Nat.card_le_card_of_injective f hf

/-- The displacement-coset injection gives the rank bound needed for replacement. -/
theorem replacement_rank_bound [Finite G] [FiniteDimensional (ZMod 2) V]
    {A : Subgroup G} (hA : IsElementaryTwo A) (v : V) :
    weight ρ A ≤ rank (replacementSubgroup ρ A v) +
      Module.finrank (ZMod 2) ↥(displacementSpan ρ A v ⊔ fixedSpace ρ A) := by
  let W := displacementSpan ρ A v ⊔ fixedSpace ρ A
  let F := (fixedSpace ρ A).comap W.subtype
  let B := replacementSubgroup ρ A v
  have hBA : B ≤ A := replacementSubgroup_le ρ A v
  have hcardB : Nat.card B = 2 ^ rank B := by
    by_cases hB : B = ⊥
    · simp [hB]
    · exact (hA.of_le hBA hB).card_eq_two_pow_rank
  have hcardC : Nat.card (B.subgroupOf A) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv
  have hcardQ : Nat.card (A ⧸ B.subgroupOf A) * Nat.card B = Nat.card A := by
    rw [← hcardC]
    exact (B.subgroupOf A).index_mul_card
  have hdimF : Module.finrank (ZMod 2) F = Module.finrank (ZMod 2) (fixedSpace ρ A) :=
    (Submodule.comapSubtypeEquivOfLe (show fixedSpace ρ A ≤ W from le_sup_right)).finrank_eq
  have hdimQ := F.finrank_quotient_add_finrank
  rw [hdimF] at hdimQ
  have hbound := replacement_quotient_card_le ρ hA v
  change Nat.card (A ⧸ B.subgroupOf A) ≤ Nat.card (W ⧸ F) at hbound
  have hpow : 2 ^ rank A ≤ 2 ^ (Module.finrank (ZMod 2) (W ⧸ F) + rank B) := by
    rw [← hA.card_eq_two_pow_rank, pow_add, ← hcardB, ← hcardQ]
    apply Nat.mul_le_mul_right
    simpa only [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W ⧸ F),
      Nat.card_eq_fintype_card, ZMod.card] using hbound
  have hrank : rank A ≤ Module.finrank (ZMod 2) (W ⧸ F) + rank B :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hpow
  change rank A + Module.finrank (ZMod 2) (fixedSpace ρ A) ≤
    rank B + Module.finrank (ZMod 2) W
  omega
end Representation.BinaryOffender
