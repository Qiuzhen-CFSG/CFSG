module

public import Theory.Representation.BinaryOffender.IrreducibleSection
public import Theory.Representation.BinaryOffender.ActionImage
public import Theory.GroupTheory.PerfectCentralizerLift
public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-!
# Faithfulness from a cubic component center

For a normal quasisimple subgroup L whose centralizer is contained in a cyclic
subgroup of order three in L, every nonzero binary module satisfying the
primitive cubic polynomial for its generator is faithful. The normal-subgroup
dichotomy puts the kernel in the component centralizer; its prime order then
forces either trivial kernel or trivial cubic action. The latter contradicts
the polynomial. The polynomial follows from commutator generation and passes
to literal invariant submodules and quotients.

These are the kernel and coprime-action steps needed before applying an
irreducible FF-module classification to sections in Aschbacher–Smith,
combined manuscript (1 March 2004), 13.8.21(2), printed p.956, and F.9.18(6),
pp.325–326. No classification or absence of strong FF-modules is assumed here.
The norm-operator argument follows the same calculation as the private
`generator_polynomial` in `BinaryOffender.NormalThree`.
-/

@[expose] public section

open Subgroup
namespace Representation.BinaryOffender
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]

/-- The primitive cubic polynomial on a binary representation. -/
def CubicPolynomial (ρ : Representation (ZMod 2) D V) (z : D) : Prop :=
  ∀ v, ρ z (ρ z v) + ρ z v + v = 0

theorem cubicPolynomial_of_moved [Finite D]
    (ρ : Representation (ZMod 2) D V) (z : D) (hz : z ^ 3 = 1)
    (hmove : subspaceCommutator ρ ⊤ (zpowers z) = ⊤) : CubicPolynomial ρ z := by
  classical
  let t := ρ z
  let N := t ^ 2 + t + 1
  have ht3 : t ^ 3 = 1 := by dsimp [t]; rw [← map_pow, hz, map_one]
  have hNt : N * t = N := by
    dsimp [N]
    rw [add_mul, add_mul, one_mul, ← pow_succ, ← pow_two, ht3]
    abel
  have hNtn (n : ℕ) : N * t ^ n = N := by
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ← mul_assoc, ih, hNt]
  have hkill : subspaceCommutator ρ ⊤ (zpowers z) ≤ LinearMap.ker N := by
    apply Submodule.span_le.mpr
    rintro v ⟨x, hx, w, _, rfl⟩
    rw [mem_zpowers_iff_mem_range_orderOf] at hx
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hx
    change N (ρ (z ^ n) w - w) = 0
    rw [map_sub, map_pow]
    exact sub_eq_zero.mpr (LinearMap.congr_fun (hNtn n) w)
  intro v
  exact hkill (by rw [hmove]; trivial)

theorem CubicPolynomial.fixed_eq_zero {ρ : Representation (ZMod 2) D V} {z : D}
    (h : CubicPolynomial ρ z) {v : V} (hv : ρ z v = v) : v = 0 := by
  have he := h v
  rw [hv, hv] at he
  have hvv : v + v = 0 := by
    have hs := @two_smul (ZMod 2) V _ _ _ v
    rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at hs
    exact hs.symm
  simpa only [hvv, zero_add] using he

theorem CubicPolynomial.subrepresentation {ρ : Representation (ZMod 2) D V} {z : D}
    (h : CubicPolynomial ρ z) (W : Subrepresentation ρ) :
    CubicPolynomial W.toRepresentation z := by
  intro v
  exact Subtype.ext (h v)

theorem CubicPolynomial.quotient {ρ : Representation (ZMod 2) D V} {z : D}
    (h : CubicPolynomial ρ z) (W : Subrepresentation ρ) :
    CubicPolynomial W.quotientRepresentation z := by
  intro v
  obtain ⟨w, rfl⟩ := W.toSubmodule.mkQ_surjective v
  exact (map_add W.toSubmodule.mkQ _ _).symm.trans
    ((congrArg W.toSubmodule.mkQ (h w)).trans (map_zero _))

/-- A quasisimple component with cubic centralizer acts faithfully whenever
its central generator satisfies the primitive cubic polynomial. -/
theorem faithful_of_cubicPolynomial [Nontrivial V]
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D)
    [L.Normal] [Theory.GroupTheory.IsQuasisimple L]
    (z : D) (hzL : z ∈ L) (hzorder : orderOf z = 3)
    (hcent : centralizer (L : Set D) ≤ zpowers z)
    (hpoly : CubicPolynomial ρ z) : Function.Injective ρ := by
  let N := (actionHom ρ).ker
  have hnL : ¬ ∀ l ∈ L, ∀ v, ρ l v = v := by
    intro ht
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    exact hv (hpoly.fixed_eq_zero (ht z hzL v))
  have hinter : L ⊓ N ≤ centralizer (L : Set D) := by
    rcases Theory.GroupTheory.IsQuasisimple.normal_le_center_or_eq_top (N.subgroupOf L)
      with hc | ht
    · intro l hl
      have hlc : (⟨l, hl.1⟩ : L) ∈ center L := hc hl.2
      rw [mem_centralizer_iff]
      intro x hx
      exact congrArg (fun y : L => (y : D)) ((mem_center_iff.mp hlc) ⟨x, hx⟩)
    · exact (hnL (by
        intro l hl v
        have hm : (⟨l, hl⟩ : L) ∈ N.subgroupOf L := ht ▸ mem_top _
        exact (actionHom_eq_one_iff ρ l).mp hm v)).elim
  have hncent : N ≤ centralizer (L : Set D) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_eq_bot_of_iterated_eq_bot
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact (le_inf (commutator_le_right _ _) (commutator_le_left _ _)).trans hinter
  have hnz : N ≤ zpowers z := hncent.trans hcent
  have hcard : Nat.card (zpowers z) = 3 := (Nat.card_zpowers z).trans hzorder
  let : Fact (Nat.card (zpowers z)).Prime := ⟨hcard ▸ Nat.prime_three⟩
  have hbot : N = ⊥ := by
    rcases (N.subgroupOf (zpowers z)).eq_bot_or_eq_top_of_prime_card with hb | ht
    · apply bot_unique
      intro n hn
      have hm : (⟨n, hnz hn⟩ : zpowers z) ∈ N.subgroupOf (zpowers z) := hn
      rw [hb] at hm
      exact congrArg Subtype.val (mem_bot.mp hm)
    · exfalso
      have hzn : z ∈ N := by
        have hm : (⟨z, mem_zpowers z⟩ : zpowers z) ∈ N.subgroupOf (zpowers z) :=
          ht ▸ mem_top _
        exact hm
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      exact hv (hpoly.fixed_eq_zero ((actionHom_eq_one_iff ρ z).mp hzn v))
  have hinj : Function.Injective (actionHom ρ) := (MonoidHom.ker_eq_bot_iff _).mp hbot
  intro x y hxy
  apply hinj
  apply imageRepresentation_injective ρ
  exact hxy

/-- Faithfulness on every nonzero invariant submodule, proved before using
an irreducible-module classification. -/
theorem faithful_subrepresentation_of_cubicPolynomial
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D)
    [L.Normal] [Theory.GroupTheory.IsQuasisimple L]
    (z : D) (hzL : z ∈ L) (hzorder : orderOf z = 3)
    (hcent : centralizer (L : Set D) ≤ zpowers z)
    (hpoly : CubicPolynomial ρ z)
    (W : Subrepresentation ρ) (hW : W ≠ ⊥) : Function.Injective W.toRepresentation := by
  have hn : W.toSubmodule ≠ ⊥ := fun he => hW (Subrepresentation.toSubmodule_injective he)
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hn
  exact faithful_of_cubicPolynomial W.toRepresentation L z hzL hzorder hcent
    (hpoly.subrepresentation W)

/-- Faithfulness on every proper invariant quotient; properness is essential. -/
theorem faithful_quotient_of_cubicPolynomial
    (ρ : Representation (ZMod 2) D V) (L : Subgroup D)
    [L.Normal] [Theory.GroupTheory.IsQuasisimple L]
    (z : D) (hzL : z ∈ L) (hzorder : orderOf z = 3)
    (hcent : centralizer (L : Set D) ≤ zpowers z)
    (hpoly : CubicPolynomial ρ z)
    (W : Subrepresentation ρ) (hW : W ≠ ⊤) : Function.Injective W.quotientRepresentation := by
  have hn : W.toSubmodule ≠ ⊤ := fun he => hW (Subrepresentation.toSubmodule_injective he)
  let : Nontrivial (V ⧸ W.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hn
  exact faithful_of_cubicPolynomial W.quotientRepresentation L z hzL hzorder hcent
    (hpoly.quotient W)

end Representation.BinaryOffender
