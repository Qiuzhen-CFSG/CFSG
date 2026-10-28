module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.FixedLetters.Checker
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Check
public import Theory.SpecificGroups.Fischer.AtlasCarriers.CycleListDecoding

/-!
# Checking both directions of a disjoint cycle action

The published cycle product acts on each disjoint cycle separately and fixes
its complement. Its inverse therefore agrees with a map checked against the
inverse action on each cycle; the opposite map is checked against the reversed
cycle. This proves both signed comparisons without evaluating the full product
at every point. The support certificates and inverse-cycle evaluator are the
existing generic Fischer certificate APIs.

The concrete consumer is `AmbientActions.GeneratorAgreement`: exact source
decoding and local map checks are independent premises there. Source: retained
ATLAS F24G1-p306936B0.g1/.g2; the inversion is `CycleEncoding`'s convention.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.GeneratorAgreement
open AtlasCarriers
open Fi23.CentralizerSection.KernelCertificate
open Fi23.CentralizerSection.KernelCertificate.FixedLetterCheck

variable {n : Nat}

/-- The numerical cycle witness is the source decoder, with exact support. -/
structure SourceCertificate [NeZero n] (blocks : List String)
    (cs : List (List (Fin n))) (m : Nat) : Prop where
  decoded : decodeCycleBlocks n blocks = cs
  support : FixedLetterCheck.Certificate cs.flatten m

/-- Local signed actions on each short cycle and the fixed complement. -/
structure ActionCertificate (f g : Fin n → Fin n)
    (cs : List (List (Fin n))) (m : Nat) : Prop where
  inverseCycles : ∀ c ∈ cs, ∀ x ∈ c, cycleInv c x = f x
  forwardCycles : ∀ c ∈ cs, ∀ x ∈ c, cycleInv c.reverse x = g x
  fixed : ∀ x, m.testBit x.val = false → f x = x ∧ g x = x

/-- Check the inverse (or forward, with `rev = true`) action locally. -/
def cycleTest (f : Fin n → Fin n) (rev : Bool) (cs : List (List (Fin n))) : Bool :=
  cs.all fun c => c.all fun x => cycleInv (if rev then c.reverse else c) x == f x

theorem cycleTest_sound (f : Fin n → Fin n) (rev : Bool)
    (cs : List (List (Fin n))) (h : cycleTest f rev cs = true) :
    ∀ c ∈ cs, ∀ x ∈ c, cycleInv (if rev then c.reverse else c) x = f x := by
  simpa only [cycleTest, List.all_eq_true, beq_iff_eq] using h

theorem blockTests_sound (f : Fin n → Fin n) (rev : Bool)
    (blocks : List (List (List (Fin n))))
    (h : blocks.all (cycleTest f rev) = true) :
    ∀ c ∈ blocks.flatten, ∀ x ∈ c,
      cycleInv (if rev then c.reverse else c) x = f x := by
  intro c hc
  obtain ⟨cs, hcs, hc⟩ := List.mem_flatten.mp hc
  exact cycleTest_sound f rev cs ((List.all_eq_true.mp h) cs hcs) c hc

/-- Check both maps outside the proposed support. -/
def fixedTest [NeZero n] (f g : Fin n → Fin n) (m k : Nat) : Bool :=
  let x := Fin.ofNat n k
  m.testBit x.val || ((f x == x) && (g x == x))

theorem fixedTest_sound [NeZero n] (f g : Fin n → Fin n) (m e : Nat)
    (hn : n ≤ 2 ^ e) (h : checkPow (fixedTest f g m) 0 e = true) :
    ∀ x : Fin n, m.testBit x.val = false → f x = x ∧ g x = x := by
  intro x hx
  have hpoint := checkPow_sound (fixedTest f g m) e 0 h x.val
    (Nat.zero_le _) (by simpa only [Nat.zero_add] using Nat.lt_of_lt_of_le x.isLt hn)
  have hi : Fin.ofNat n x.val = x := by simp
  simpa only [fixedTest, hi, hx, Bool.false_or, Bool.and_eq_true, beq_iff_eq] using hpoint

theorem cyclesInv_eq_of_tests (f : Fin n → Fin n)
    (cs : List (List (Fin n))) (m : Nat) (hc : FixedLetterCheck.Certificate cs.flatten m)
    (hcycle : ∀ c ∈ cs, ∀ x ∈ c, cycleInv c x = f x)
    (hfix : ∀ x, m.testBit x.val = false → f x = x) (x : Fin n) :
    cyclesInv cs x = f x := by
  by_cases hx : x ∈ cs.flatten
  · obtain ⟨c, hc', hx⟩ := List.mem_flatten.mp hx
    exact cyclesInv_edge hc c hc' x (f x) hx (hcycle c hc' x hx)
  · have hm : m.testBit x.val = false :=
      Bool.eq_false_iff.mpr (fun h => hx ((hc.mem_iff x).mpr h))
    exact (cyclesInv_fixed hc x hm).trans (hfix x hm).symm

theorem cyclesProd_eq_of_tests (g : Fin n → Fin n)
    (cs : List (List (Fin n))) (m : Nat) (hc : FixedLetterCheck.Certificate cs.flatten m)
    (hcycle : ∀ c ∈ cs, ∀ x ∈ c, cycleInv c.reverse x = g x)
    (hfix : ∀ x, m.testBit x.val = false → g x = x) (x : Fin n) :
    (cs.map List.formPerm).prod x = g x := by
  apply (cs.map List.formPerm).prod⁻¹.injective
  have hinv : (cs.map List.formPerm).prod⁻¹ ((cs.map List.formPerm).prod x) = x :=
    (cs.map List.formPerm).prod.symm_apply_apply x
  rw [hinv, ← cyclesInv_eq]
  symm
  by_cases hx : x ∈ cs.flatten
  · obtain ⟨c, hc', hx⟩ := List.mem_flatten.mp hx
    have hg : g x = c.formPerm x := by
      rw [← hcycle c hc' x hx, cycleInv_eq, List.formPerm_reverse, inv_inv]
    rw [hg, cyclesInv_on_cycle cs hc.nodup c hc' _ (c.formPerm_apply_mem_of_mem hx),
      cycleInv_eq]
    exact c.formPerm.symm_apply_apply x
  · have hm : m.testBit x.val = false :=
      Bool.eq_false_iff.mpr (fun h => hx ((hc.mem_iff x).mpr h))
    rw [hfix x hm]
    exact cyclesInv_fixed hc x hm

/-- Convert independently checked decoding/support and local signed actions
to the actual source permutation and its inverse. -/
theorem signed_maps_correct [NeZero n] (blocks : List String)
    (cs : List (List (Fin n))) (m : Nat) (f g : Fin n → Fin n)
    (hs : SourceCertificate blocks cs m) (ha : ActionCertificate f g cs m) :
    (∀ x, f x = permutationFromCycleBlocks n blocks x) ∧
      (∀ x, g x = (permutationFromCycleBlocks n blocks)⁻¹ x) := by
  constructor
  · intro x
    rw [permutationFromCycleBlocks, hs.decoded, ← cyclesInv_eq]
    exact (cyclesInv_eq_of_tests f cs m hs.support ha.inverseCycles
      (fun y hy => (ha.fixed y hy).1) x).symm
  · intro x
    rw [permutationFromCycleBlocks, hs.decoded, inv_inv]
    exact (cyclesProd_eq_of_tests g cs m hs.support ha.forwardCycles
      (fun y hy => (ha.fixed y hy).2) x).symm

/-- Assemble decoding one original string block at a time. -/
theorem decode_of_blocks [NeZero n]
    {blocks : List String} {parts : List (List (List (Fin n)))}
    (h : List.Forall₂ (fun b p => decodeCycleBlocks n [b] = p) blocks parts) :
    decodeCycleBlocks n blocks = parts.flatten := by
  induction h with
  | nil => rfl
  | @cons b p bs ps hb _ ih =>
    change _ = p ++ ps.flatten
    rw [← hb, ← ih]
    simp only [decodeCycleBlocks, List.flatMap_cons, List.flatMap_nil, List.append_nil]

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.Ambient.GeneratorAgreement
