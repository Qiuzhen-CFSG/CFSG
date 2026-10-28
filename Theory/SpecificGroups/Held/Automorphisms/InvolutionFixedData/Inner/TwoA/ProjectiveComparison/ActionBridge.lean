module

public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Recovering a perfect action from compatible projective generators

Pairs of actors agreeing on a point injection form a subgroup of the product.
Generation makes its projection to the model surjective. Faithfulness makes
its projection to the ambient group injective. If the ambient group is perfect
and has at most twice the model order, this latter projection has index at most
two and is therefore surjective. Transitivity then makes the point injection
surjective, so the model projection is also injective.

This is the action-comparison step for GLS3 Table 5.3p, 2A row. It requires
actual compatible actions; group orders alone do not supply the comparison.
-/

@[expose] public section

namespace Held.InvolutionFixedData.TwoA.ProjectiveComparison

section Agreement
variable {G H X Y : Type*} [Group G] [Group H] [MulAction G X] [MulAction H Y]

/-- Pairs of actors that agree on the given point map. -/
def agreement (f : Y → X) : Subgroup (G × H) where
  carrier := {p | ∀ y, p.1 • f y = f (p.2 • y)}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb y
    change (a.1 * b.1) • f y = f ((a.2 * b.2) • y)
    rw [mul_smul, hb, ha, mul_smul]
  inv_mem' := by
    intro a ha y
    change a.1⁻¹ • f y = f (a.2⁻¹ • y)
    apply (MulAction.toPerm a.1).injective
    change a.1 • (a.1⁻¹ • f y) = a.1 • f (a.2⁻¹ • y)
    rw [smul_inv_smul, ha, smul_inv_smul]

def agreementLeft (f : Y → X) : agreement (G := G) (H := H) f →* G :=
  (MonoidHom.fst G H).comp (agreement f).subtype

def agreementRight (f : Y → X) : agreement (G := G) (H := H) f →* H :=
  (MonoidHom.snd G H).comp (agreement f).subtype

theorem agreementRight_surjective (f : Y → X) (S : Set H)
    (hS : Subgroup.closure S = ⊤)
    (hlift : ∀ s ∈ S, ∃ g : G, ∀ y, g • f y = f (s • y)) :
    Function.Surjective (agreementRight (G := G) (H := H) f) := by
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hS, Subgroup.closure_le]
  intro s hs
  obtain ⟨g, hg⟩ := hlift s hs
  exact ⟨⟨(g, s), hg⟩, rfl⟩

theorem labels_mem_orbit [MulAction.IsPretransitive H Y]
    (f : Y → X) (S : Set H) (hS : Subgroup.closure S = ⊤)
    (hlift : ∀ s ∈ S, ∃ g : G, ∀ y, g • f y = f (s • y))
    (y₀ y : Y) : f y ∈ MulAction.orbit G (f y₀) := by
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H y₀ y
  obtain ⟨r, hr⟩ := agreementRight_surjective f S hS hlift h
  refine ⟨agreementLeft f r, ?_⟩
  change r.val.1 • f y₀ = f y
  rw [r.property]
  change f (agreementRight f r • y₀) = f y
  rw [hr, hh]

theorem agreementLeft_injective [FaithfulSMul H Y] (f : Y → X)
    (hf : Function.Injective f) : Function.Injective (agreementLeft (G := G) (H := H) f) := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext hab
  apply eq_of_smul_eq_smul (α := Y)
  intro y
  apply hf
  change f (a.val.2 • y) = f (b.val.2 • y)
  rw [← a.property, ← b.property]
  exact congrArg (fun g : G => g • f y) hab

theorem labels_surjective_of_left [MulAction.IsPretransitive G X] [Nonempty Y]
    (f : Y → X) (hl : Function.Surjective (agreementLeft (G := G) (H := H) f)) :
    Function.Surjective f := by
  classical
  let y₀ : Y := Classical.arbitrary Y
  intro x
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (f y₀) x
  obtain ⟨r, rfl⟩ := hl g
  exact ⟨agreementRight f r • y₀, (r.property y₀).symm.trans hg⟩

theorem agreementRight_injective [FaithfulSMul G X] (f : Y → X)
    (hf : Function.Surjective f) : Function.Injective (agreementRight (G := G) (H := H) f) := by
  intro a b hab
  apply Subtype.ext
  apply Prod.ext _ hab
  apply eq_of_smul_eq_smul (α := X)
  intro x
  obtain ⟨y, rfl⟩ := hf x
  change a.val.1 • f y = b.val.1 • f y
  rw [a.property, b.property]
  exact congrArg (fun h : H => f (h • y)) hab

/-- A partial comparison of generating actions extends to the entire faithful
transitive action when the ambient perfect group has at most twice the model order. -/
noncomputable def equivOfGeneratorLifts [Finite G] [Finite H] [Group.IsPerfect G]
    [FaithfulSMul G X] [FaithfulSMul H Y] [MulAction.IsPretransitive G X] [Nonempty Y]
    (f : Y → X) (hf : Function.Injective f)
    (hc : Nat.card G ≤ 2 * Nat.card H) (S : Set H) (hS : Subgroup.closure S = ⊤)
    (hlift : ∀ s ∈ S, ∃ g : G, ∀ y, g • f y = f (s • y)) : G ≃* H := by
  let l := agreementLeft (G := G) (H := H) f
  let r := agreementRight (G := G) (H := H) f
  have hl := agreementLeft_injective (G := G) (H := H) f hf
  have hr := agreementRight_surjective f S hS hlift
  have hcard : Nat.card H ≤ Nat.card l.range := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hl).toEquiv]
    exact Nat.card_le_card_of_surjective r hr
  have hi : l.range.index ≤ 2 := by
    have he := l.range.card_mul_index
    have hp : 0 < Nat.card H := Nat.card_pos
    nlinarith
  have htop : l.range = ⊤ := top_unique
    (Subgroup.le_of_isPerfect_of_index_le_two ⊤ l.range hi)
  have hls : Function.Surjective l := MonoidHom.range_eq_top.mp htop
  have hfs := labels_surjective_of_left f hls
  exact (MulEquiv.ofBijective l ⟨hl, hls⟩).symm.trans
    (MulEquiv.ofBijective r ⟨agreementRight_injective f hfs, hr⟩)
end Agreement
end Held.InvolutionFixedData.TwoA.ProjectiveComparison
