module
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.CyclicReplay

/-!
# Shared word identities for the cyclic-factor certificate

The large coset trace uses comparatively few different word operations. A pool
records those operations once. The numeric checker only compares word indices;
`check_sound` restores the literal words and the original cyclic replay check.
The defining representatives and the modulus 13 are unchanged.

Source: the six ATLAS G23G1-P1 words and the cyclic replay in `CyclicReplay`.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Pooled
open Subgroup.CosetWordCertificate

/-- Balanced tables have logarithmic kernel lookup depth. -/
def branch {α : Type} (cutoff : Nat) (left right : Nat → α) (n : Nat) : α :=
  if n < cutoff then left n else right n

/-- The recorder's four letters, in Mathlib's positive-sign convention. -/
def letter (a : Nat) : Bool × Bool := (a / 2 != 0, a % 2 == 0)

/-- A source rule retains the actual relator, sign and rotation offset. -/
structure SourceRule where
  word : Nat
  relator : Fin 6
  inverse : Bool
  offset : Nat

/-- Finite domains prevent any claim about unused entries of the tables. -/
structure Pool where
  word : Nat → Word Bool
  empty : Nat
  singleton : Nat → Nat
  cyclic : Nat
  source : Nat → SourceRule
  sourceSize : Nat
  reversal : Nat → Nat × Nat
  reversalSize : Nat
  composition : Nat → Nat × Nat × Nat
  compositionSize : Nat

/-- These are literal list equalities, not equalities in a permutation image. -/
structure Valid (P : Pool) : Prop where
  empty : P.word P.empty = []
  singleton : ∀ a, a < 4 → P.word (P.singleton a) = [letter a]
  cyclic : P.word P.cyclic = [(false, true), (true, true)]
  source : ∀ k, k < P.sourceSize →
    P.word (P.source k).word = Replay.variant (sourceLetters (P.source k).relator)
      (P.source k).inverse (P.source k).offset
  reversal : ∀ k, k < P.reversalSize →
    P.word (P.reversal k).2 = FreeGroup.invRev (P.word (P.reversal k).1)
  composition : ∀ k, k < P.compositionSize →
    P.word (P.composition k).2.2 =
      reduce (P.word (P.composition k).1 ++ P.word (P.composition k).2.1)

/-- A parent is clamped only to make the finite table total and acyclic.
Every defining instruction still checks this exact parent. -/
def definitions (d : Nat → Nat) : Definitions Bool where
  parent n := min (d n / 4) (n - 1)
  letter n := letter (d n % 4)
  parent_lt n := by
    have := Nat.min_le_right (d (n + 1) / 4) (n + 1 - 1)
    omega

/-- Numeric fields of a fact, with its word replaced by a pool index. -/
structure NumericFact where
  left : Nat
  word : Nat
  right : Nat
  exponent : Nat

/-- Decode a 60-bit fact: 21 left, 14 word, 21 right, 4 exponent bits. -/
def fact (x : Nat) : NumericFact :=
  ⟨x / 549755813888, x / 33554432 % 16384, x / 16 % 2097152, x % 16⟩

def NumericFact.decode (P : Pool) (f : NumericFact) : CyclicReplay.Fact :=
  ⟨f.left, P.word f.word, f.right, f.exponent⟩

/-- Numeric instruction fields; the rule index selects a pooled word identity. -/
structure NumericInstruction where
  tag : Nat
  p : Nat
  q : Nat
  rule : Nat

/-- Decode 3 tag, 21 predecessor, 21 predecessor and 14 rule bits. -/
def instruction (x : Nat) : NumericInstruction :=
  ⟨x % 8, x / 8 % 2097152, x / 16777216 % 2097152, x / 35184372088832⟩

def NumericInstruction.decode (P : Pool) (op : NumericInstruction) : CyclicReplay.Instruction :=
  match op.tag with
  | 0 => .refl op.p
  | 1 => .defining op.p
  | 2 => .subgroup
  | 3 => .source op.p (P.source op.rule).relator
      (P.source op.rule).inverse (P.source op.rule).offset
  | 4 => .reverse op.p
  | _ => .compose op.p op.q

/-- All executable tests below are on natural numbers. In particular no long
word is expanded or reduced while checking a numeric trace instruction. -/
def check (P : Pool) (d : Nat → Nat) (fs : Nat → NumericFact)
    (n : Nat) (op : NumericInstruction) (out : NumericFact) : Bool :=
  match op.tag with
  | 0 => out.left == op.p && out.word == P.empty && out.right == op.p && out.exponent == 0
  | 1 => Nat.blt 0 op.p && out.left == min (d op.p / 4) (op.p - 1) &&
      out.word == P.singleton (d op.p % 4) && out.right == op.p && out.exponent == 0
  | 2 => out.left == 0 && out.word == P.cyclic && out.right == 0 && out.exponent == 1
  | 3 => Nat.blt op.rule P.sourceSize && out.left == op.p &&
      out.word == (P.source op.rule).word && out.right == op.p && out.exponent == 0
  | 4 => Nat.blt op.p n && Nat.blt op.rule P.reversalSize &&
      out.left == (fs op.p).right && out.right == (fs op.p).left &&
      (fs op.p).word == (P.reversal op.rule).1 && out.word == (P.reversal op.rule).2 &&
      (out.exponent + (fs op.p).exponent) % 13 == 0
  | _ => Nat.blt op.p n && Nat.blt op.q n && Nat.blt op.rule P.compositionSize &&
      out.left == (fs op.p).left && out.right == (fs op.q).right &&
      (fs op.p).right == (fs op.q).left &&
      (fs op.p).word == (P.composition op.rule).1 &&
      (fs op.q).word == (P.composition op.rule).2.1 &&
      out.word == (P.composition op.rule).2.2 &&
      out.exponent == ((fs op.p).exponent + (fs op.q).exponent) % 13

/-- Pool validity converts the cheaper numeric check into the exact old check. -/
theorem check_sound (P : Pool) (hP : Valid P) (d : Nat → Nat)
    (fs : Nat → NumericFact) (n : Nat) (op : NumericInstruction) (out : NumericFact)
    (h : check P d fs n op out = true) :
    CyclicReplay.check (definitions d).parent (definitions d).letter
      (fun k => (fs k).decode P) n (op.decode P) (out.decode P) = true := by
  unfold check at h
  unfold NumericInstruction.decode
  split at h <;> simp only [Bool.and_eq_true, beq_iff_eq, Nat.blt_eq] at h
  · obtain ⟨⟨⟨hl, hw⟩, hr⟩, hk⟩ := h
    simp only [CyclicReplay.check, decide_eq_true_eq, NumericFact.decode,
      hl, hw, hr, hk, hP.empty]
  · obtain ⟨⟨⟨⟨hp, hl⟩, hw⟩, hr⟩, hk⟩ := h
    simp only [CyclicReplay.check, decide_eq_true_eq, NumericFact.decode,
      hl, hw, hr, hk, definitions, hP.singleton _ (Nat.mod_lt _ (by decide))]
    exact ⟨Nat.ne_of_gt hp, trivial⟩
  · obtain ⟨⟨⟨hl, hw⟩, hr⟩, hk⟩ := h
    simp only [CyclicReplay.check, decide_eq_true_eq, NumericFact.decode,
      hl, hw, hr, hk, hP.cyclic]
  · obtain ⟨⟨⟨⟨hb, hl⟩, hw⟩, hr⟩, hk⟩ := h
    simp only [CyclicReplay.check, decide_eq_true_eq, NumericFact.decode,
      hl, hw, hr, hk, hP.source _ hb]
  · obtain ⟨⟨⟨⟨⟨⟨hp, hb⟩, hl⟩, hr⟩, hw₁⟩, hw₂⟩, hk⟩ := h
    simp only [CyclicReplay.check, NumericFact.decode]
    apply decide_eq_true_eq.mpr
    exact ⟨hp, hl, hr, by rw [hw₂, hw₁]; exact hP.reversal _ hb, hk⟩
  · obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hp, hq⟩, hb⟩, hl⟩, hr⟩, hm⟩, hw₁⟩, hw₂⟩, hw₃⟩, hk⟩ := h
    simp only [CyclicReplay.check, NumericFact.decode]
    apply decide_eq_true_eq.mpr
    exact ⟨hp, hq, hl, hr, hm,
      by rw [hw₃, hw₁, hw₂]; exact hP.composition _ hb, hk⟩

/-- Bounded chunks keep recursion and individual kernel checks small. -/
def checkChunk (P : Pool) (d : Nat → Nat) (fs : Nat → NumericFact)
    (ops : Nat → NumericInstruction) (start count : Nat) : Bool :=
  (List.range count).all fun k => check P d fs (start + k) (ops (start + k)) (fs (start + k))

theorem checkChunk_sound (P : Pool) (hP : Valid P) (d : Nat → Nat)
    (fs : Nat → NumericFact) (ops : Nat → NumericInstruction) (start count : Nat)
    (h : checkChunk P d fs ops start count = true) (n : Nat)
    (hlo : start ≤ n) (hhi : n < start + count) :
    CyclicReplay.check (definitions d).parent (definitions d).letter
      (fun k => (fs k).decode P) n ((ops n).decode P) ((fs n).decode P) = true := by
  have hm : n - start ∈ List.range count := by simp only [List.mem_range]; omega
  have hn : start + (n - start) = n := by omega
  have hc := List.all_eq_true.mp h (n - start) hm
  rw [hn] at hc
  exact check_sound P hP d fs n (ops n) (fs n) hc

/-- Concrete consumer with the literal max3 word, retaining only the finite
word-pool and numeric-check obligations for the certificate producer. -/
theorem local_relation (P : Pool) (hP : Valid P) (d : Nat → Nat)
    (fs : Nat → NumericFact) (ops : Nat → NumericInstruction) (N : Nat)
    (checked : ∀ n, n < N → check P d fs n (ops n) (fs n) = true)
    (i : Fin 7) (o : Nat) (ho : o < N)
    (hout : (fs o).decode P =
      ⟨0, reduce (Replay.expand boundLetters (localRelatorLetters i)), 0, 0⟩) :
    eval boundGenerator (localRelatorLetters i) = 1 :=
  CyclicReplay.local_relation_of_checked_trace (definitions d)
    (fun k => (fs k).decode P) (fun k => (ops k).decode P) N
    (fun n hn => check_sound P hP d fs n (ops n) (fs n) (checked n hn)) i o ho hout

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.MixedRelations.Certificates.Pooled
