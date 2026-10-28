module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelCertificate.FixedLetters.Checker
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Data
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23InFi24Prime.Comparison.Check

/-!
# Comparing a packed map with the exact Fi23 cycle action

The existing character-list certificates identify the decoded cycles with the
original strings. Their support certificates prove that the cycles are disjoint.
It therefore suffices to compare a proposed map on each short cycle and on the
fixed complement. The checker below uses the inverse-cycle evaluator, preserving
the conversion from published right actions to the carrier's left actions.

The concrete consumers are `GeneratorA` and `GeneratorB` in this directory.
Source: ATLAS F23G1-p31671B0; attribution and hashes in `AtlasCarriers/source/`.
The comparison is used for the Fi23 subgroup in GLS3 Table 5.3v.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.SourceActionCheck
open Fi23.CentralizerSection.KernelCertificate
open Fi23.CentralizerSection.KernelCertificate.FixedLetterCheck

def cycleTest (f : Fin 31671 → Fin 31671) (cs : List (List (Fin 31671))) : Bool :=
  cs.all fun c => c.all fun x => cycleInv c x == f x

theorem cycleTest_sound (f : Fin 31671 → Fin 31671) (cs : List (List (Fin 31671)))
    (h : cycleTest f cs = true) : ∀ c ∈ cs, ∀ x ∈ c, cycleInv c x = f x := by
  simpa only [cycleTest, List.all_eq_true, beq_iff_eq] using h

theorem blockTests_sound (f : Fin 31671 → Fin 31671)
    (blocks : List (List (List (Fin 31671))))
    (h : blocks.all (cycleTest f) = true) :
    ∀ c ∈ blocks.flatten, ∀ x ∈ c, cycleInv c x = f x := by
  intro c hc
  obtain ⟨cs, hcs, hc⟩ := List.mem_flatten.mp hc
  exact cycleTest_sound f cs ((List.all_eq_true.mp h) cs hcs) c hc

def fixedTest (f : Fin 31671 → Fin 31671) (m k : Nat) : Bool :=
  let x := Fin.ofNat 31671 k
  m.testBit x.val || (f x == x)

theorem fixedTest_sound (f : Fin 31671 → Fin 31671) (m : Nat)
    (h : checkPow (fixedTest f m) 0 15 = true) :
    ∀ x : Fin 31671, m.testBit x.val = false → f x = x := by
  intro x hx
  have hpoint := checkPow_sound (fixedTest f m) 15 0 h x.val
    (Nat.zero_le _) (Nat.lt_trans x.isLt (by decide))
  have hi : Fin.ofNat 31671 x.val = x := by simp
  simpa only [fixedTest, hi, hx, Bool.false_or, beq_iff_eq] using hpoint

theorem cyclesInv_eq_of_tests (f : Fin 31671 → Fin 31671)
    (cs : List (List (Fin 31671))) (m : Nat) (hc : FixedLetterCheck.Certificate cs.flatten m)
    (hcycle : ∀ c ∈ cs, ∀ x ∈ c, cycleInv c x = f x)
    (hfix : ∀ x, m.testBit x.val = false → f x = x) (x : Fin 31671) :
    cyclesInv cs x = f x := by
  by_cases hx : x ∈ cs.flatten
  · obtain ⟨c, hc', hx⟩ := List.mem_flatten.mp hx
    exact cyclesInv_edge hc c hc' x (f x) hx (hcycle c hc' x hx)
  · have hm : m.testBit x.val = false :=
      Bool.eq_false_iff.mpr (fun h => hx ((hc.mem_iff x).mpr h))
    exact (cyclesInv_fixed hc x hm).trans (hfix x hm).symm

end Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate.SourceActionCheck
