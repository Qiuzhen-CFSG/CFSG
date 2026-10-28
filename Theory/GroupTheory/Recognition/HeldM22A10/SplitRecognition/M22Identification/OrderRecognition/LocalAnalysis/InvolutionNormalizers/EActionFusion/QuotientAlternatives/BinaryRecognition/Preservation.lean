module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.M22Identification.OrderRecognition.LocalAnalysis.InvolutionNormalizers.EActionFusion.QuotientAlternatives.BinaryRecognition.Forms
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Linarith

/-!
# An order-360 overgroup preserves the distinguished alternating form

The orbit of the distinguished form has cardinal dividing 15, since its
stabilizer contains the faithful twisted S₄. The three-cycle fixes exactly
one form, so the orbit cardinal is 1 modulo 3 by the p-group fixed-point
congruence. Of the divisors of 15, only 1 has this residue.

Source: the concrete binary subgroup identification needed in Janko,
“A characterization of the Mathieu simple groups, I”, J. Algebra 9 (1968),
Section 2, Lemma 6, p.6. No simplicity or odd-core assumption is used.
-/

public section

open Theory.GroupTheory.HeldM22A10.LocalModelDichotomy
open Subgroup MulAction
namespace Theory.GroupTheory.HeldM22A10.BinaryRecognition
theorem fixes_of_card {G A : Type*} [Group G] [Finite G] [MulAction G A] [Finite A]
    (b : A) (S : Subgroup G) (hS : S ≤ stabilizer G b)
    (hcardS : Nat.card S = 24) (hcardG : Nat.card G = 360)
    (t : G) (ht : orderOf t = 3) (htb : t • b = b)
    (huniq : ∀ a : A, t • a = a → a = b) :
    ∀ g : G, g • b = b := by
  classical
  let T := zpowers t
  have hp : IsPGroup 3 T := IsPGroup.of_card (n := 1) (by
    simpa only [T, Nat.card_zpowers, pow_one] using ht)
  have hTb : T ≤ stabilizer G b := zpowers_le.mpr htb
  let b' : orbit G b := ⟨b, mem_orbit_self b⟩
  have hb' : b' ∈ fixedPoints T (orbit G b) := by
    intro s
    apply Subtype.ext
    exact hTb s.property
  have heq (a : fixedPoints T (orbit G b)) : a.val = b' := by
    apply Subtype.ext
    apply huniq
    exact congrArg Subtype.val (a.property ⟨t, mem_zpowers t⟩)
  let : Unique (fixedPoints T (orbit G b)) :=
    ⟨⟨b', hb'⟩, fun a => Subtype.ext (heq a)⟩
  have hmod := hp.card_modEq_card_fixedPoints (orbit G b)
  have hone : Nat.card (fixedPoints T (orbit G b)) = 1 := Nat.card_unique
  rw [hone] at hmod
  have hdiv : 24 ∣ Nat.card (stabilizer G b) := hcardS ▸ card_dvd_of_le hS
  obtain ⟨k, hk⟩ := hdiv
  have hc : Nat.card (orbit G b) * Nat.card (stabilizer G b) = 360 := by
    rw [← Nat.card_prod, Nat.card_congr (orbitProdStabilizerEquivGroup G b), hcardG]
  rw [hk] at hc
  have horb : Nat.card (orbit G b) ∣ 15 := by
    refine ⟨k, ?_⟩
    nlinarith
  have hcases : Nat.card (orbit G b) = 1 ∨ Nat.card (orbit G b) = 3 ∨
      Nat.card (orbit G b) = 5 ∨ Nat.card (orbit G b) = 15 := by
    have : ∀ n : ℕ, n ∣ 15 → n = 1 ∨ n = 3 ∨ n = 5 ∨ n = 15 := by
      intro n hn
      have hn' := Nat.le_of_dvd (by decide : 0 < 15) hn
      interval_cases n <;> norm_num at *
    exact this _ horb
  have hcard : Nat.card (orbit G b) = 1 := by
    rcases hcases with h | h | h | h
    · exact h
    all_goals simp [h, Nat.ModEq] at hmod
  have : Subsingleton (orbit G b) := (Nat.card_eq_one_iff_unique.mp hcard).1
  intro g
  exact congrArg Subtype.val (Subsingleton.elim (g • b') b')

theorem preserves_base (X : Subgroup (MulAut BinaryFour))
    (hX : twistedAction.range ≤ X) (hcard : Nat.card X = 360) :
    ∀ g : X, g.val • base = base := by
  let f : SymmetricFour →* X := twistedAction.codRestrict X (fun s => hX ⟨s, rfl⟩)
  have hf : Function.Injective f := by
    intro s t h
    exact twisted_injective (congrArg Subtype.val h)
  have hS : f.range ≤ stabilizer X base := by
    rintro _ ⟨s, rfl⟩
    exact twisted_fixes_base s
  have hSCard : Nat.card f.range = 24 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    change Nat.card (Equiv.Perm (Fin 4)) = 24
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have ht : orderOf (f cycle) = 3 := by
    rw [orderOf_injective f hf]
    exact orderOf_eq_prime cycle_cube cycle_ne_one
  exact fixes_of_card base f.range hS hSCard hcard (f cycle) ht
    (twisted_fixes_base cycle) (fun B hB => cycle_fixed_unique B hB)

end Theory.GroupTheory.HeldM22A10.BinaryRecognition
