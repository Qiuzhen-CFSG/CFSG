module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.TraceField.Contracts
public import Theory.Representation.ElevenTrace

/-!
# Reduction of the HS trace-field calculation to order eleven

The 512th power of a carrier element is either conjugate to its square, or has
order eleven and is conjugate to its fourth power. In the first case the
characteristic-two trace identity gives a binary trace. In the second case,
fixed-point-freeness and degree twenty give the same conclusion by taking the
trace of the geometric sum. Injectivity of Frobenius then descends the binary
trace from the 512th power to the original element.

This proves the implication from two independent, explicitly specified inputs
to `DegreeTwentyTraceField`. The carrier power fusion and universal order-eleven
fixed-space calculation still need proofs. No particular ATLAS matrix module
is substituted for the arbitrary faithful absolutely irreducible action.

Source: Guralnick--Malle, *Classification of 2F-modules, I*, Proposition 5.1,
HS paragraph, p.16; Aschbacher--Smith K.4, printed p.457. The exact consumer is
`finrank_eq_twenty_of_absolute_window_of_trace` in the sibling `SourceDegree`.
This module only imports its input boundary, preserving acyclic assembly.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
open Representation
universe v

private theorem character_sq_of_two_power
    {K H W : Type*} [Field K] [CharP K 2] [Group H]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (τ : Representation K H W) (g : H) (n : ℕ)
    (h : τ.character (g ^ (2 ^ n)) ^ 2 = τ.character (g ^ (2 ^ n))) :
    τ.character g ^ 2 = τ.character g := by
  rw [character_two_pow_charTwo] at h
  apply iterateFrobenius_inj K 2 n
  change (τ.character g ^ 2) ^ (2 ^ n) = τ.character g ^ (2 ^ n)
  simpa only [← pow_mul, Nat.mul_comm] using h

/-- The actual power fusion and the universal order-eleven fixed-space result
supply precisely the trace-field input used by binary degree descent. This is
conditional until both input contracts have been proved. -/
theorem degreeTwentyTraceField_of_powerFusion_of_elevenFixedFree
    (hfusion : TraceField.PowerFusion)
    (heleven : TraceField.DegreeTwentyElevenFixedFree.{v}) : DegreeTwentyTraceField.{v} := by
  intro hs K _ _ _ W _ _ _ τ hf hi hd g
  change τ.character g ^ 2 = τ.character g
  apply character_sq_of_two_power τ g 9
  change τ.character (g ^ 512) ^ 2 = τ.character (g ^ 512)
  rcases hfusion g with hc | ⟨ho, hc⟩
  · have ht : τ.character (g ^ 512) = τ.character ((g ^ 512) ^ 2) := by
      obtain ⟨c, h⟩ := isConj_iff.mp hc
      rw [← pow_mul]
      change τ.character (g ^ 512) = τ.character (g ^ 1024)
      rw [← h, char_conj]
    exact (character_sq_charTwo τ (g ^ 512)).symm.trans ht.symm
  · apply character_sq_eq_of_order_eleven_fixedFree τ (g ^ 512) ho
      (by simpa only [← pow_mul] using hc)
      (heleven hs K W τ hf hi hd (g ^ 512) ho)
    rw [hd]
    exact (CharP.cast_eq_zero_iff K 2 20).mpr (by decide)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims
