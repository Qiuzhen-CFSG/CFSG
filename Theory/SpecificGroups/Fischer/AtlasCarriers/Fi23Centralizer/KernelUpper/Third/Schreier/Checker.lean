module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Reduction
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.InitialSteps
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Schreier.Networks
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.Third.Schreier.Planes

/-!
# Compressed checks for the literal third-stage Schreier words

A permutation pulls back a bitvector by its point action. Consequently a word
pulls back bitvectors in the reverse order to its pointwise evaluation. Testing
the fifteen separating bitplanes checks a complete permutation identity at
once. `step_of_bitStep` proves the bridge for the fixed representative and factor
codes, with the two network-to-point-map comparisons still explicit.

`SecondAgreement` and `SignedAgreement` concern only twenty generator maps;
`BitStep` concerns only the fixed numerical networks and words. These independent
certificates together imply the original `Step`, without an order, presentation,
or identification of the target generators with `KernelData.generator`.

Source: ATLAS F23G1-p31671B0; GLS3 Table 5.3u.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.Schreier

def secondBits (a : Fin 6) : Nat → Nat := BitNetwork.run (secondNetwork a)

def signedBits (a : Fin 14) : Nat → Nat := BitNetwork.run (signedNetwork a)

/-- The six circuit index maps agree with the literal source point maps. -/
def SecondAgreement : Prop :=
  ∀ a : Fin 6, ∀ x : Fin 31671,
    BitNetwork.route (secondNetwork a) x.val = (secondMap a x).val

/-- The fourteen signed circuits agree with the literal packed point maps. -/
def SignedAgreement : Prop :=
  ∀ a : Fin 14, ∀ x : Fin 31671,
    BitNetwork.route (signedNetwork a) x.val = (signedMap a x).val

theorem secondBits_testBit (h : SecondAgreement) (a : Fin 6) (p : Nat)
    (x : Fin 31671) : (secondBits a p).testBit x.val = p.testBit (secondMap a x).val := by
  rw [secondBits, BitNetwork.run_testBit _ (secondNetwork_valid a), h a x]

theorem signedBits_testBit (h : SignedAgreement) (a : Fin 14) (p : Nat)
    (x : Fin 31671) : (signedBits a p).testBit x.val = p.testBit (signedMap a x).val := by
  rw [signedBits, BitNetwork.run_testBit _ (signedNetwork_valid a), h a x]

/-- Pullback evaluates the leftmost factor first, unlike the point evaluator. -/
def wordPull {n : Nat} [NeZero n] (gen : Fin n → Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, p => p
  | k+1, w, p => wordPull gen k (w / 16) (gen (Fin.ofNat n (w % 16)) p)

theorem wordPull_testBit {n : Nat} [NeZero n]
    (gen : Fin n → Nat → Nat) (pointMap : Fin n → Fin 31671 → Fin 31671)
    (h : ∀ a p x, (gen a p).testBit x.val = p.testBit (pointMap a x).val)
    (k w p : Nat) (x : Fin 31671) :
    (wordPull gen k w p).testBit x.val = p.testBit (wordRun pointMap k w x).val := by
  induction k generalizing w p with
  | zero => rfl
  | succ k ih => rw [wordPull, ih, h]; rfl

def representativeBits (r : Fin 693) (p : Nat) : Nat :=
  wordPull secondBits (representativeCode r.val).1 (representativeCode r.val).2 p

def factorBits (a : Fin 6) (r : Fin 693) (p : Nat) : Nat :=
  wordPull signedBits (factorCode a r.val).1 (factorCode a r.val).2 p

theorem representativeBits_testBit (h : SecondAgreement) (r : Fin 693)
    (p : Nat) (x : Fin 31671) :
    (representativeBits r p).testBit x.val = p.testBit (representativeRun r x).val :=
  wordPull_testBit _ _ (secondBits_testBit h) _ _ _ _

theorem factorBits_testBit (h : SignedAgreement) (a : Fin 6) (r : Fin 693)
    (p : Nat) (x : Fin 31671) :
    (factorBits a r p).testBit x.val = p.testBit (factorRun a r x).val :=
  wordPull_testBit _ _ (signedBits_testBit h) _ _ _ _

/-- A numerical check of one whole-permutation identity on one bitplane. -/
def transitionTest (a : Fin 6) (r : Fin 693) (b : Fin 15) : Bool :=
  decide (representativeBits r (secondBits a (plane b)) =
    factorBits a r (representativeBits (transitionForward a r) (plane b)))

def BitStep (a : Fin 6) : Prop :=
  ∀ r : Fin 693, ∀ b : Fin 15, transitionTest a r b = true

theorem transition_of_bits (hSecond : SecondAgreement) (hSigned : SignedAgreement)
    (a : Fin 6) (r : Fin 693) (h : ∀ b, transitionTest a r b = true)
    (x : Fin 31671) :
    secondMap a (representativeRun r x) =
      representativeRun (transitionForward a r) (factorRun a r x) := by
  apply plane_ext
  intro b
  have he := of_decide_eq_true (h b)
  have hb := congrArg (fun p : Nat => p.testBit x.val) he
  simpa only [representativeBits_testBit hSecond, secondBits_testBit hSecond,
    factorBits_testBit hSigned] using hb

theorem step_of_bitStep (hSecond : SecondAgreement) (hSigned : SignedAgreement)
    (a : Fin 6) (h : BitStep a) : Step a :=
  fun r x => transition_of_bits hSecond hSigned a r (h r) x

end Sporadic.Fischer.Fi23.CentralizerSection.KernelUpperThird.Schreier
