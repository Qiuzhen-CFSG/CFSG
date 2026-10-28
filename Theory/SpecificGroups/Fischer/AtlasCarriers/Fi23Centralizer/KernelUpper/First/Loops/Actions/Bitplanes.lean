module

public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Contracts
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi23Centralizer.KernelUpper.First.Loops.Checks
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.BitNetwork

/-!
# Bit-mask soundness for the first Fi23 loop action squares

A numerical map acts on masks by pullback. Equality on fifteen coordinate
masks determines its action on every one of the original 31671 letters.
Path and factor pullbacks reverse the written composition order, giving
exactly the square `s (R (F x)) = R x` required by `ActionCheck`.
The last theorem applies this reduction to the literal Schreier edge using
the already checked paths and fixedness. Network semantics and numerical
mask equalities are independent certificate obligations, not hypotheses
about subgroup membership.

Source: retained ATLAS F23G1-p31671B0, inverse-cycle convention, and GLS3
Table 5.3u. The bit-network semantics is reused from the Fi22 certificate.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Actions
open Sporadic.Fischer.Fi24Prime.Fi23Lift.Certificate
open Sporadic.Fischer.Fi22.KernelCertificate

/-- Pullback along a numerical map on the original carrier. -/
def Pullback (f : Fin 31671 → Fin 31671) (t : Nat → Nat) : Prop :=
  ∀ (v : Nat) (x : Fin 31671), (t v).testBit x.val = v.testBit (f x).val

theorem pullback_network (f : Fin 31671 → Fin 31671) (ss : List BitNetwork.Stage)
    (h : ∀ x : Fin 31671, BitNetwork.route ss x.val = some (f x).val) :
    Pullback f (BitNetwork.apply ss) :=
  fun v x => BitNetwork.sound ss x.val (f x).val v (h x)

/-- The fifteen bits distinguish all letters in the original action. -/
def Separating (planes : Fin 15 → Nat) : Prop :=
  ∀ (k : Fin 15) (x : Fin 31671), (planes k).testBit x.val = x.val.testBit k.val

theorem eq_of_masks (f g : Fin 31671 → Fin 31671) (tf tg : Nat → Nat)
    (hf : Pullback f tf) (hg : Pullback g tg) (planes : Fin 15 → Nat)
    (hp : Separating planes) (he : ∀ k, tf (planes k) = tg (planes k)) : f = g := by
  funext x
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 15
  · have h := congrArg (fun v : Nat => v.testBit x.val) (he ⟨k, hk⟩)
    rw [hf, hg, hp, hp] at h
    exact h
  · have hlarge (z : Fin 31671) : z.val.testBit k = false := by
      apply Nat.testBit_lt_two_pow
      exact lt_of_lt_of_le (lt_trans z.isLt (by decide : 31671 < 2 ^ 15))
        (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 15 ≤ k))
    rw [hlarge, hlarge]

/-- Pullback reverses the written order of a path. -/
def pathTransform (a b : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, v => v
  | d + 1, w, v => pathTransform a b d (w / 2) (if w % 2 == 1 then b v else a v)

def factorTransform (c : Nat → Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, v => v
  | d + 1, w, v => factorTransform c d (w / 256) (c (w % 256) v)

theorem pathTransform_sound (a b : Nat → Nat)
    (ha : Pullback sourceA a) (hb : Pullback sourceB b) (d w : Nat) :
    Pullback (evalPath d w) (pathTransform a b d w) := by
  induction d generalizing w with
  | zero => intro v x; rfl
  | succ d ih =>
    intro v x
    simp only [pathTransform, evalPath]
    split
    · rw [ih, hb]
    · rw [ih, ha]

theorem factorTransform_sound (c : Nat → Nat → Nat)
    (hc : ∀ i, Pullback (coreMap i) (c i)) (d w : Nat) :
    Pullback (evalFactors d w) (factorTransform c d w) := by
  induction d generalizing w with
  | zero => intro v x; rfl
  | succ d ih =>
    intro v x
    simp only [factorTransform, evalFactors]
    rw [ih, hc]

/-- A full mask equality suffices for the literal numerical loop equation. -/
theorem actionCheck_of_masks (a b : Nat → Nat) (c : Nat → Nat → Nat)
    (ha : Pullback sourceA a) (hb : Pullback sourceB b)
    (hc : ∀ i, Pullback (coreMap i) (c i)) (planes : Fin 15 → Nat)
    (hp : Separating planes) (i : Fin 722)
    (he : ∀ k, factorTransform c (factorLength i) (factorBits i)
        (pathTransform a b (pathLength i) (pathBits i)
          (if i.val < 695 then a (planes k) else b (planes k))) =
      pathTransform a b (pathLength i) (pathBits i) (planes k)) :
    ∀ x, ActionCheck i x := by
  have hf : Pullback
      (fun x => sourceGenerator i
        (evalPath (pathLength i) (pathBits i)
          (evalFactors (factorLength i) (factorBits i) x)))
      (fun v => factorTransform c (factorLength i) (factorBits i)
        (pathTransform a b (pathLength i) (pathBits i)
          (if i.val < 695 then a v else b v))) := by
    intro v x
    rw [factorTransform_sound c hc, pathTransform_sound a b ha hb]
    unfold sourceGenerator
    split <;> first | exact ha _ _ | exact hb _ _
  exact fun x => congrFun (eq_of_masks _ _ _ _ hf
    (pathTransform_sound a b ha hb _ _) planes hp he) x

/-- Application to the original Schreier edge, using the already checked path
and fixedness. Only the independent core-word interpretation remains explicit. -/
theorem loop_edge_mem_of_masks (hcore : CoreActions)
    (a b : Nat → Nat) (c : Nat → Nat → Nat)
    (ha : Pullback sourceA a) (hb : Pullback sourceB b)
    (hc : ∀ i, Pullback (coreMap i) (c i)) (planes : Fin 15 → Nat)
    (hp : Separating planes) (i : Fin 722)
    (he : ∀ k, factorTransform c (factorLength i) (factorBits i)
        (pathTransform a b (pathLength i) (pathBits i)
          (if i.val < 695 then a (planes k) else b (planes k))) =
      pathTransform a b (pathLength i) (pathBits i) (planes k)) :
    edge (loopGenerator i) (loopPoint i) ∈ KernelUpperData.first :=
  loop_edge_mem hcore i (path_properties i).1
    (by simpa only [sourceGenerator_eq] using (path_properties i).2)
    (actionCheck_of_masks a b c ha hb hc planes hp i he)

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Actions
