module

public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.Basic
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.PowerIdentities.Chunk08
public import Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelUpperBound.CentralCollection.PowerIdentities.PowerChunk13
import Mathlib.Tactic.Group

/-!
# The two zero-exponent power identities for the seven ATLAS words

Checked word traces identify both c₀⁻⁶³ c₁⁻¹⁸ c₂¹⁴ and
c₀⁻¹⁵ c₁⁻⁶ c₂² c₃ with c₆ in the genuine group F/[F,R].
The first trace uses powers of derived equations, including a ninth power;
the second uses contextual word collection. The remaining corrections are
the involution relations already proved in `Basic`.

No finiteness premise, multiplier bound, or independently supplied
commutator identity is assumed.

Source: Wilson–Nickerson–Bray, ATLAS `S62G1-P1.M`; the exact word convention,
certificates, and reproduction are documented in `PowerIdentities/source/README.md`.
-/

@[expose] public section
namespace Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection
open PowerReplay

private theorem power_trace_relation_one :
    collect ![-63, -18, 14, 0, -2, -7, 14] = 1 :=
  eqn_cycle PowerCertificate.eq_3451

private theorem power_trace_relation_two :
    collect ![0, 0, 0, 0, 0, 3, -13] = 1 :=
  eqn_cycle PowerCertificate.eq_593

/-- The first zero-exponent power combination is the final central relator. -/
theorem powerDefect_eq_centralRelator_six : powerDefect = centralRelator 6 := by
  have h4 : centralRelator 4 ^ (2 : ℤ) = 1 := by
    calc
      _ = (centralRelator 4 ^ 2) ^ (1 : ℤ) := by group
      _ = 1 := by rw [centralRelator_four_sq, one_zpow]
  have h5 : centralRelator 5 ^ (4 : ℤ) = 1 := by
    calc
      _ = (centralRelator 5 ^ 2) ^ 2 := by group
      _ = 1 := by rw [centralRelator_five_sq, one_pow]
  have h6 : centralRelator 6 ^ (-2 : ℤ) = 1 := by
    calc
      _ = (centralRelator 6 ^ 2)⁻¹ := by group
      _ = 1 := by rw [centralRelator_six_sq, inv_one]
  have hw : collect ![0, 0, 0, 0, 2, 4, -2] = 1 := by
    simpa [collect] using congrArg₂ (· * ·) (congrArg₂ (· * ·) h4 h5) h6
  have hv : (![-63, -18, 14, 0, 0, 0, -1] : Fin 7 → ℤ) =
      ![-63, -18, 14, 0, -2, -7, 14] + ![0, 0, 0, 0, 0, 3, -13] +
        ![0, 0, 0, 0, 2, 4, -2] := by decide
  have ht : collect ![-63, -18, 14, 0, 0, 0, -1] = 1 := by
    rw [hv, collect_add, collect_add, power_trace_relation_one,
      power_trace_relation_two, hw]
    simp
  have he : powerCycle + ![0, 0, 0, 0, 0, 0, -1] =
      (![-63, -18, 14, 0, 0, 0, -1] : Fin 7 → ℤ) := by decide
  rw [← he, collect_add] at ht
  have hl : collect ![0, 0, 0, 0, 0, 0, -1] = (centralRelator 6)⁻¹ := by simp [collect]
  rw [hl] at ht
  exact mul_inv_eq_one.mp ht

private theorem mixed_trace_relation_one :
    collect ![0, 0, 0, 0, 1, 6, -7] = 1 := eqn_cycle eq_5882

private theorem mixed_trace_relation_two :
    collect ![15, 6, -2, -1, -1, 0, -6] = 1 := eqn_cycle eq_24427

/-- The second zero-exponent power combination is the final central relator. -/
theorem mixedDefect_eq_centralRelator_six : mixedDefect = centralRelator 6 := by
  have h5 : centralRelator 5 ^ (6 : ℤ) = 1 := by
    calc
      _ = (centralRelator 5 ^ 2) ^ 3 := by group
      _ = 1 := by rw [centralRelator_five_sq, one_pow]
  have h6 : centralRelator 6 ^ (-14 : ℤ) = 1 := by
    calc
      _ = (centralRelator 6 ^ 2) ^ (-7 : ℤ) := by group
      _ = 1 := by rw [centralRelator_six_sq, one_zpow]
  have hw : collect ![0, 0, 0, 0, 0, 6, -14] = 1 := by
    simpa [collect] using congrArg₂ (· * ·) h5 h6
  have hv : (![-15, -6, 2, 1, 0, 0, -1] : Fin 7 → ℤ) =
      - ![0, 0, 0, 0, 1, 6, -7] + - ![15, 6, -2, -1, -1, 0, -6] +
        ![0, 0, 0, 0, 0, 6, -14] := by decide
  have ht : collect ![-15, -6, 2, 1, 0, 0, -1] = 1 := by
    rw [hv, collect_add, collect_add, collect_neg, collect_neg,
      mixed_trace_relation_one, mixed_trace_relation_two, hw]
    simp
  have he : mixedCycle + ![0, 0, 0, 0, 0, 0, -1] =
      (![-15, -6, 2, 1, 0, 0, -1] : Fin 7 → ℤ) := by decide
  rw [← he, collect_add] at ht
  have hl : collect ![0, 0, 0, 0, 0, 0, -1] = (centralRelator 6)⁻¹ := by simp [collect]
  rw [hl] at ht
  exact mul_inv_eq_one.mp ht

end Theory.SpecificGroups.SymplecticSix.UniversalDoubleCover.KernelPresentation.CentralCollection
