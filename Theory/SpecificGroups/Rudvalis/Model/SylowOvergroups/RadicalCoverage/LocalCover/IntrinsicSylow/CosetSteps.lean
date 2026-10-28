module

public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.CosetStep0
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.CosetStep1
import Mathlib.Tactic.FinCases

/-!
# All signed generator transitions for the intrinsic cosets

Witnesses from `source/GenerateCosets.g` and `source/GenerateCosets.py`.
The computation uses the unchanged ATLAS max4 and local words; see
`SylowOvergroups.Definitions` for attribution. GAP output is not trusted: all
permutation identities and separating points are checked by Lean.
-/

namespace Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.Cosets
open Theory.GroupTheory Rudvalis.OrderCertificate
set_option Elab.async false

private theorem reverse_right_step {G : Type*} [Group G] {a b c d : G}
    (h : b * a = c * d) : d * a⁻¹ = c⁻¹ * b := by
  apply (eq_inv_mul_iff_mul_eq).2
  rw [← mul_assoc, ← h, mul_inv_cancel_right]

private theorem step2 (r : Fin 21) :
    rep r * Main.gen 2 = evalWord P.L0.gen (factor 2 r) * rep (act 2 r) := by
  have ha : ∀ r, act 0 (act 2 r) = r := by decide +kernel
  have hf : ∀ r, factor 2 r = (factor 0 (act 2 r)).reverse.map P.L0.invOf := by
    decide +kernel
  have hi : Main.gen 2 = (Main.gen 0)⁻¹ := Main.gen_inv 0
  have h := reverse_right_step (step0 (act 2 r))
  rw [ha] at h
  rw [hi, hf, evalWord_reverse_map_inv P.L0.gen P.L0.invOf P.L0.gen_inv]
  exact h

private theorem step3 (r : Fin 21) :
    rep r * Main.gen 3 = evalWord P.L0.gen (factor 3 r) * rep (act 3 r) := by
  have ha : ∀ r, act 1 (act 3 r) = r := by decide +kernel
  have hf : ∀ r, factor 3 r = (factor 1 (act 3 r)).reverse.map P.L0.invOf := by
    decide +kernel
  have hi : Main.gen 3 = (Main.gen 1)⁻¹ := Main.gen_inv 1
  have h := reverse_right_step (step1 (act 3 r))
  rw [ha] at h
  rw [hi, hf, evalWord_reverse_map_inv P.L0.gen P.L0.invOf P.L0.gen_inv]
  exact h

public theorem step (i : Fin 4) (r : Fin 21) :
    rep r * Main.gen i = evalWord P.L0.gen (factor i r) * rep (act i r) := by
  fin_cases i
  · exact step0 r
  · exact step1 r
  · exact step2 r
  · exact step3 r

end Rudvalis.SylowOvergroups.RadicalCoverage.LocalCover.IntrinsicSylow.Cosets
