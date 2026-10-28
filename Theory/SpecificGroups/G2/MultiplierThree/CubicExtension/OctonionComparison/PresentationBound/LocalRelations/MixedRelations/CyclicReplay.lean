module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.WordCalculus
/-!
# Cyclic-factor replay for the literal G₂(3) presentation

A fact records `ρ(i) * w = (ab)^k * ρ(j)`. Reversal and composition
reduce exponents using the original relation `(ab)^13 = 1`. A defining tree
realizes the representatives. Thus a checked root loop with exponent zero
proves an identity in the original presentation, without using a finite image.

Source: the six ATLAS G23G1-P1 words fixed in `PresentationBound.Subgroup`.
Certificate producers are untrusted; every instruction is checked in Lean.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.CyclicReplay
open Subgroup.CosetWordCertificate
variable {G : Type*} [Group G] (g : Bool → G) (c : G) (hc : c ^ 13 = 1)

theorem pow_mod (hc : c ^ 13 = 1) (n : ℕ) : c ^ (n % 13) = c ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n 13, pow_add, pow_mul, hc]
  simp

structure Fact where
  left : ℕ
  word : Word Bool
  right : ℕ
  exponent : ℕ
  deriving DecidableEq

def Holds (ρ : ℕ → G) (f : Fact) : Prop :=
  ρ f.left * eval g f.word = c ^ f.exponent * ρ f.right

variable {g c} {ρ : ℕ → G}

theorem reflexive (i : ℕ) : Holds g c ρ ⟨i, [], i, 0⟩ := by
  simp [Holds]

theorem defining (i j : ℕ) (a : Bool × Bool)
    (h : ρ i * eval g [a] = ρ j) : Holds g c ρ ⟨i, [a], j, 0⟩ := by
  simpa [Holds] using h

theorem relator (i : ℕ) (w : Word Bool) (h : eval g w = 1) :
    Holds g c ρ ⟨i, w, i, 0⟩ := by simp [Holds, h]

theorem subgroup (hρ : ρ 0 = 1) (w : Word Bool) (h : eval g w = c) :
    Holds g c ρ ⟨0, w, 0, 1⟩ := by simp [Holds, hρ, h]

theorem compose (hc : c ^ 13 = 1) {f₁ f₂ f₃ : Fact} (h₁ : Holds g c ρ f₁) (h₂ : Holds g c ρ f₂)
    (hl : f₃.left = f₁.left) (hr : f₃.right = f₂.right)
    (hm : f₁.right = f₂.left)
    (hw : f₃.word = reduce (f₁.word ++ f₂.word))
    (hk : f₃.exponent = (f₁.exponent + f₂.exponent) % 13) : Holds g c ρ f₃ := by
  change ρ f₃.left * eval g f₃.word = c ^ f₃.exponent * ρ f₃.right
  rw [hl, hr, hw, eval_append_reduce, ← mul_assoc, h₁, mul_assoc, hm, h₂,
    ← mul_assoc, ← pow_add, hk, pow_mod c hc]

theorem reverse (hc : c ^ 13 = 1) {f₁ f₂ : Fact} (h₁ : Holds g c ρ f₁)
    (hl : f₂.left = f₁.right) (hr : f₂.right = f₁.left)
    (hw : f₂.word = FreeGroup.invRev f₁.word)
    (hk : (f₂.exponent + f₁.exponent) % 13 = 0) : Holds g c ρ f₂ := by
  have hp : c ^ f₂.exponent * c ^ f₁.exponent = 1 := by
    rw [← pow_add, ← pow_mod c hc, hk, pow_zero]
  change ρ f₂.left * eval g f₂.word = c ^ f₂.exponent * ρ f₂.right
  rw [hl, hr, hw, eval_invRev]
  have he := congrArg (fun x => c ^ f₂.exponent * x * (eval g f₁.word)⁻¹) h₁
  simp only [mul_assoc, mul_inv_cancel, mul_one] at he
  simpa only [← mul_assoc, hp, one_mul] using he.symm

/-- A syntactic instruction in a cyclic-factor derivation. -/
inductive Instruction where
  | refl (i : ℕ)
  | defining (j : ℕ)
  | subgroup
  | source (i : ℕ) (r : Fin 6) (inverse : Bool) (offset : ℕ)
  | reverse (p : ℕ)
  | compose (p q : ℕ)

/-- Only literal words and natural-number arithmetic occur in this checker. -/
def check (parent : ℕ → ℕ) (letter : ℕ → Bool × Bool)
    (facts : ℕ → Fact) (n : ℕ) (op : Instruction) (out : Fact) : Bool :=
  match op with
  | .refl i => decide (out = ⟨i, [], i, 0⟩)
  | .defining j => decide (j ≠ 0 ∧ out = ⟨parent j, [letter j], j, 0⟩)
  | .subgroup => decide (out = ⟨0, [(false, true), (true, true)], 0, 1⟩)
  | .source i r inverse offset =>
      decide (out = ⟨i, Replay.variant (sourceLetters r) inverse offset, i, 0⟩)
  | .reverse p => decide (p < n ∧ out.left = (facts p).right ∧
      out.right = (facts p).left ∧ out.word = FreeGroup.invRev (facts p).word ∧
      (out.exponent + (facts p).exponent) % 13 = 0)
  | .compose p q => decide (p < n ∧ q < n ∧ out.left = (facts p).left ∧
      out.right = (facts q).right ∧ (facts p).right = (facts q).left ∧
      out.word = reduce ((facts p).word ++ (facts q).word) ∧
      out.exponent = ((facts p).exponent + (facts q).exponent) % 13)

/-- Every successful local check is an equality in the original presented group. -/
theorem check_sound (D : Definitions Bool) (facts : ℕ → Fact)
    (n : ℕ) (op : Instruction) (out : Fact)
    (hc : check D.parent D.letter facts n op out = true)
    (hs : ∀ p, p < n → Holds Presentation.generator
      (Presentation.generator false * Presentation.generator true)
      (D.repr Presentation.generator) (facts p)) :
    Holds Presentation.generator
      (Presentation.generator false * Presentation.generator true)
      (D.repr Presentation.generator) out := by
  have hpower : (Presentation.generator false * Presentation.generator true) ^ 13 = 1 :=
    generator_relations 2
  cases op with
  | refl i =>
      simp only [check, decide_eq_true_eq] at hc
      subst out
      exact reflexive i
  | defining j =>
      simp only [check, decide_eq_true_eq] at hc
      obtain ⟨hj, rfl⟩ := hc
      exact defining _ _ _ (D.repr_edge Presentation.generator j hj)
  | subgroup =>
      simp only [check, decide_eq_true_eq] at hc
      subst out
      exact subgroup (D.repr_zero _) _ (by simp [eval_cons])
  | source i r inverse offset =>
      simp only [check, decide_eq_true_eq] at hc
      subst out
      apply relator
      apply Replay.eval_variant_one
      rw [eval_sourceLetters]
      exact generator_relations r
  | reverse p =>
      simp only [check, decide_eq_true_eq] at hc
      obtain ⟨hp, hl, hr, hw, hk⟩ := hc
      exact reverse hpower (hs p hp) hl hr hw hk
  | compose p q =>
      simp only [check, decide_eq_true_eq] at hc
      obtain ⟨hp, hq, hl, hr, hm, hw, hk⟩ := hc
      exact compose hpower (hs p hp) (hs q hq) hl hr hm hw hk

/-- A finite sequence of local checks validates each retained fact. -/
theorem sound (D : Definitions Bool) (facts : ℕ → Fact) (ops : ℕ → Instruction)
    (N : ℕ) (checked : ∀ n, n < N → check D.parent D.letter facts n (ops n) (facts n) = true) :
    ∀ n, n < N → Holds Presentation.generator
      (Presentation.generator false * Presentation.generator true)
      (D.repr Presentation.generator) (facts n) := by
  intro n hn
  induction n using Nat.strong_induction_on with
  | h n ih =>
      exact check_sound D facts n (ops n) (facts n) (checked n hn)
        (fun p hp => ih p hp (hp.trans hn))

/-- The concrete consumer: a checked root loop proves its fixed local word. -/
theorem local_relation_of_checked_trace (D : Definitions Bool) (facts : ℕ → Fact)
    (ops : ℕ → Instruction) (N : ℕ)
    (checked : ∀ n, n < N → check D.parent D.letter facts n (ops n) (facts n) = true)
    (i : Fin 7) (o : ℕ) (ho : o < N)
    (hout : facts o = ⟨0, reduce (Replay.expand boundLetters (localRelatorLetters i)), 0, 0⟩) :
    eval boundGenerator (localRelatorLetters i) = 1 := by
  have h := sound D facts ops N checked o ho
  rw [hout] at h
  simp only [Holds, D.repr_zero, one_mul, pow_zero, mul_one, eval_reduce,
    Replay.eval_expand] at h
  simpa only [eval_boundLetters] using h

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.CyclicReplay
