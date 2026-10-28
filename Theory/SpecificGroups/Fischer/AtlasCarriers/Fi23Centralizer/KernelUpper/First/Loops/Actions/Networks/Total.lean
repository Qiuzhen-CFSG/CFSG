module
public import Theory.SpecificGroups.Fischer.AtlasCarriers.Fi22KernelCertificate.GraphInvariance.BitNetwork
/-!
# Total switch networks on a padded coordinate set

Disjoint low and high switch masks, contained in the padded set, route every
coordinate to exactly one coordinate in that set. This reduces network
validity to whole-integer mask checks. Applying a valid network to fifteen
separating masks then identifies its action with the fixed numerical map,
without evaluating all stages separately at every input coordinate.

The concrete consumer is the first Fi23 loop action certificate, with 32768
padded positions and the unchanged 31671-letter action. Source: retained
ATLAS F23G1-p31671B0 and GLS3 Table 5.3u. The coordinate semantics is inherited
from the proved Fi22 `BitNetwork` framework.
-/

@[expose] public section
namespace Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Actions
open Sporadic.Fischer.Fi22.KernelCertificate

def switch (n d m : Nat) : BitNetwork.Stage :=
  ⟨d, m, m <<< d, (2 ^ n - 1) ^^^ m ^^^ (m <<< d)⟩

def SwitchValid (n d m : Nat) : Prop :=
  m &&& (m <<< d) = 0 ∧ m <<< d < 2 ^ n

private theorem index_lt_of_bit {v j n : Nat} (hv : v < 2 ^ n)
    (hj : v.testBit j = true) : j < n := by
  by_cases h : j < n
  · exact h
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_gt h)
  have hl := Nat.ge_two_pow_of_testBit hj
  omega

theorem switch_route (n d m : Nat) (h : SwitchValid n d m) (i : Nat) (hi : i < n) :
    ∃ j < n, (switch n d m).route i = some j := by
  have hd := congrArg (fun v : Nat => v.testBit i) h.1
  simp only [Nat.testBit_and, Nat.zero_testBit] at hd
  have hfull : (2^n-1).testBit i = true := by simp [hi]
  cases hm : m.testBit i <;> cases hh : (m <<< d).testBit i
  · refine ⟨i, hi, ?_⟩
    simp [switch, BitNetwork.Stage.route, Nat.testBit_xor, hfull, hm, hh]
  · have hdi : d ≤ i := by
      have := hh
      simp only [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq] at this
      exact this.1
    refine ⟨i-d, by omega, ?_⟩
    simp [switch, BitNetwork.Stage.route, Nat.testBit_xor, hfull, hm, hh, hdi]
  · have hb : (m <<< d).testBit (d+i) = true := by
      simp [Nat.testBit_shiftLeft, hm]
    refine ⟨d+i, index_lt_of_bit h.2 hb, ?_⟩
    simp [switch, BitNetwork.Stage.route, Nat.testBit_xor, hfull, hm, hh]
  · simp [hm, hh] at hd

/-- A switch network is total on its padded set, certified once per mask. -/
theorem network_route (n : Nat) (ss : List (Nat × Nat))
    (h : ∀ s ∈ ss, SwitchValid n s.1 s.2) (i : Nat) (hi : i < n) :
    ∃ j < n, BitNetwork.route (ss.map (fun s => switch n s.1 s.2)) i = some j := by
  induction ss generalizing i with
  | nil => exact ⟨i, hi, rfl⟩
  | cons s ss ih =>
    obtain ⟨k, hk, hs⟩ := switch_route n s.1 s.2 (h s (by simp)) i hi
    obtain ⟨j, hj, hr⟩ := ih (fun t ht => h t (by simp [ht])) k hk
    exact ⟨j, hj, by simpa only [List.map_cons, BitNetwork.route, hs, Option.bind_some] using hr⟩

/-- Whole-mask checks can replace pointwise network-route computations.
Totality gives an output coordinate; the fifteen separating masks identify it. -/
theorem network_pullback_of_planes (ss : List (Nat × Nat))
    (hv : ∀ s ∈ ss, SwitchValid 32768 s.1 s.2)
    (planes : Fin 15 → Nat)
    (hp : ∀ (k : Fin 15) (j : Nat), j < 32768 →
      (planes k).testBit j = j.testBit k.val)
    (f : Fin 31671 → Fin 31671)
    (he : ∀ (k : Fin 15) (x : Fin 31671),
      (BitNetwork.apply (ss.map (fun s => switch 32768 s.1 s.2)) (planes k)).testBit x.val =
        (f x).val.testBit k.val) :
    ∀ (v : Nat) (x : Fin 31671),
      (BitNetwork.apply (ss.map (fun s => switch 32768 s.1 s.2)) v).testBit x.val =
        v.testBit (f x).val := by
  intro v x
  obtain ⟨j, hj, hr⟩ := network_route 32768 ss hv x.val (Nat.lt_trans x.isLt (by decide))
  have hje : j = (f x).val := by
    apply Nat.eq_of_testBit_eq
    intro k
    by_cases hk : k < 15
    · have hh := he ⟨k, hk⟩ x
      rw [BitNetwork.sound _ _ _ _ hr, hp _ _ hj] at hh
      exact hh
    · have hn : 15 ≤ k := by omega
      have hpow : 2^15 ≤ 2^k := Nat.pow_le_pow_right (by decide) hn
      rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hj hpow),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le
          (Nat.lt_trans (f x).isLt (by decide : 31671 < 2^15)) hpow)]
  exact hje ▸ BitNetwork.sound _ _ _ _ hr

end Sporadic.Fischer.Fi23.CentralizerSection.FirstTree.Loops.Actions
