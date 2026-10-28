module

public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.Suz.CentralizerSection.Tables
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.CycleCheck

/-!
# Kernel-checkable predicates for the Suz word tables

The balanced range checker bounds reduction depth. Its predicate checks the
two fixed complements, the literal words, inverse maps, square one, and both
centralization identities. It does not use a computation oracle.
-/

@[expose] public section
namespace Sporadic.LeechRelated.Suz.CentralizerSection.Checks
open Tables

def checkRange (p : Nat → Bool) : Nat → Nat → Bool
  | 0, start => p start
  | depth + 1, start =>
      checkRange p depth start && checkRange p depth (start + 2 ^ depth)

theorem checkRange_sound (p : Nat → Bool) (depth start : Nat)
    (h : checkRange p depth start = true) :
    ∀ i, start ≤ i → i < start + 2 ^ depth → p i = true := by
  induction depth generalizing start with
  | zero =>
    intro i hlo hhi
    have : i = start := by simpa using (show i = start by omega)
    subst i
    exact h
  | succ depth ih =>
    rw [checkRange, Bool.and_eq_true] at h
    intro i hlo hhi
    by_cases hi : i < start + 2 ^ depth
    · exact ih start h.1 i hlo hi
    · apply ih (start + 2 ^ depth) h.2 i (by omega)
      rw [pow_succ] at hhi
      omega

def wordCheck (x : Fin 1782) : Bool :=
  (wMap x == aMap (bMap (aMap (bMap (aMap (bMap (bMap x))))))) &&
  (zMap x == (wMap^[6]) x) &&
  (uMap x == bMap (aMap (bMap (aMap x)))) &&
  (vMap x == aMap (bMap (aMap (bMap (bMap
    (aMap (bMap (aMap (bMap (bMap (aMap (bMap x)))))))))))) &&
  (uMap (uiMap x) == x) && (vMap (viMap x) == x) &&
  (cMap x == uMap (zMap (uiMap (zMap (uMap x))))) &&
  (dMap x == vMap (zMap (viMap (zMap (vMap
    (zMap (viMap (zMap (vMap x))))))))) &&
  (zMap (zMap x) == x) &&
  (cMap (zMap x) == zMap (cMap x)) &&
  (dMap (zMap x) == zMap (dMap x))

def pointCheck (i : Nat) : Bool :=
  if i < 1782 then
    let x := Fin.ofNat 1782 i
    (supportA.testBit i || (aMap x == x)) &&
    (supportB.testBit i || (bMap x == x)) && wordCheck x
  else true

end Sporadic.LeechRelated.Suz.CentralizerSection.Checks
