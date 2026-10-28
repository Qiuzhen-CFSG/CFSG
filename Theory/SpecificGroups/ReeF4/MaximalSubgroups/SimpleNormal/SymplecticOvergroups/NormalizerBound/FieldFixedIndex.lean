module

public import Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms.OuterQuotient.ParabolicClasses

/-!
# Bounding a symplectic normal extension using a field-fixed subgroup

Let N be a normal subgroup of a finite group, identified with Sp₄(F).
Conjugation acts on the at most two parabolic conjugacy classes of N.
Assume that diagram-preserving automorphisms are inner times field
automorphisms, and that a subgroup fixed pointwise by all field automorphisms
has trivial centralizer in the extension. Correcting an element of the
action kernel by an inner automorphism then puts it in that centralizer.
The kernel therefore lies in N, giving index at most two.

The semilinear classification and centralizer assertion remain explicit
premises. The application to Ree groups uses the binary A₆ of Malle,
Section 2.2, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E. This general reduction uses no Ree model,
ambient simplicity or classification of maximal subgroups.
-/

public section

namespace ReeF4.MaximalSubgroups.SimpleNormal.NormalizerBound

open Subgroup Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.DiagramAutomorphisms

noncomputable section

variable {F : Type*} [Field F]

private theorem extensionAction_inner {G : Type*} [Group G]
    (N : Subgroup G) [N.Normal] (e : Sp F ≃* N) (g : Sp F) :
    extensionAction N e (e g).val = MulAut.conj g := by
  apply MulEquiv.ext
  intro y
  apply e.injective
  apply Subtype.ext
  rw [extensionAction_apply]
  simp

/-- Field-fixed centralizer rigidity kills the kernel of the action on
parabolic classes modulo the normal symplectic subgroup. -/
theorem index_le_two_of_field_fixed_centralizer
    {G A : Type*} [Group G] [Finite G] [Group A] [Finite F] [CharP F 2]
    (N : Subgroup G) [N.Normal] (e : Sp F ≃* N) (hF : 2 < Nat.card F)
    (b : A →* Sp F)
    (hfix : ∀ (σ : F ≃+* F) (a : A), fieldAutomorphism σ (b a) = b a)
    (hC : centralizer ((N.subtype.comp (e.toMonoidHom.comp b)).range : Set G) = ⊥)
    (hclass : ∀ a : MulAut (Sp F), PreservesDiagram a →
      ∃ (g : Sp F) (σ : F ≃+* F), a = MulAut.conj g * fieldAutomorphism σ) :
    N.index ≤ 2 := by
  let ρ := (parabolicClassAction hF).comp (extensionAction N e)
  have hker : ρ.ker ≤ N := by
    intro x hx
    have hd : PreservesDiagram (extensionAction N e x) :=
      (mem_parabolicClassAction_ker_iff hF _).mp hx
    obtain ⟨g, σ, hσ⟩ := hclass _ hd
    let c : G := (e g).val⁻¹ * x
    have hc : extensionAction N e c = fieldAutomorphism σ := by
      simp only [c, map_mul, map_inv, extensionAction_inner, hσ, inv_mul_cancel_left]
    have hcC : c ∈ centralizer
        ((N.subtype.comp (e.toMonoidHom.comp b)).range : Set G) := by
      rw [mem_centralizer_iff]
      rintro y ⟨a, rfl⟩
      have he := extensionAction_apply N e c (b a)
      rw [hc, hfix] at he
      exact eq_mul_inv_iff_mul_eq.mp he
    have hc1 : c = 1 := by simpa only [hC, mem_bot] using hcC
    have hxg : x = (e g).val := by
      have h := congrArg ((e g).val * ·) hc1
      simpa only [c, ← mul_assoc, mul_inv_cancel, one_mul, mul_one] using h
    exact hxg ▸ (e g).property
  have hcard : Nat.card (Equiv.Perm (parabolicClasses hF)) ≤ 2 := by
    let := Fintype.ofFinite (parabolicClasses hF)
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    have hle : Fintype.card (parabolicClasses hF) ≤ 2 := by
      simpa only [Nat.card_eq_fintype_card] using card_parabolicClasses_le_two hF
    exact (Nat.factorial_le hle).trans (by decide)
  have hindex : ρ.ker.index ≤ 2 := by
    rw [index_ker]
    exact ρ.range.card_le_card_group.trans hcard
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero ρ.ker.index_ne_zero_of_finite)
    (index_dvd_of_le hker)).trans hindex

/-- Trivial centralizers restrict through an injective ambient map. This
allows an ambient Ree calculation to supply the relative centralizer in M. -/
theorem centralizer_range_eq_bot_of_comp
    {G H A : Type*} [Group G] [Group H] [Group A]
    (f : G →* H) (hf : Function.Injective f) (b : A →* G)
    (hC : centralizer ((f.comp b).range : Set H) = ⊥) :
    centralizer (b.range : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro g hg
  have hc : f g ∈ centralizer ((f.comp b).range : Set H) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    simpa only [MonoidHom.comp_apply, map_mul] using
      congrArg f ((mem_centralizer_iff.mp hg) (b a) ⟨a, rfl⟩)
  have he : f g = 1 := by simpa only [hC, mem_bot] using hc
  exact mem_bot.mpr (hf (he.trans (map_one f).symm))

end

end ReeF4.MaximalSubgroups.SimpleNormal.NormalizerBound
