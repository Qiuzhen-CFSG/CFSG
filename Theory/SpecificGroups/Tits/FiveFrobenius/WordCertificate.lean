module

public import Theory.SpecificGroups.Tits.FiveFrobenius.Tables
public import Theory.SpecificGroups.Tits.Atlas1600ParrottCertificate

/-!
# Cached ATLAS words for the five-local Frobenius subgroup

The ATLAS program `TF42G1-max8W1` supplies `x1 = a` and `x2 = b^c`,
where `c = ((a*b)*(a*b^2))^3`. The remaining words were found in that
maximal subgroup by GAP, as recorded in the task's discovery calculation.
The tables below are inverse GAP point maps, with zero-based labels;
word order is preserved when passing from right actions to left actions.
Every cache and every inverse is checked by kernel reduction.

Source: https://brauer.maths.qmul.ac.uk/Atlas/exc/TF42/words/TF42G1-max8W1,
using `refs/original/n-group-global/atlas-tits-p1600-{a,b}.g`.
Regeneration: `FiveFrobenius/source/generate.py` (original project code).
-/

namespace Tits.FiveFrobenius
open Atlas1600ParrottData
set_option maxRecDepth 20000

private theorem a_eq_cache : atlas1600A = r1Perm := atlasA_word

private theorem b_eq_cache : atlas1600B = bPerm := by
  rw [atlasB_word]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem x2p_word : x2p =
    (((atlas1600A * atlas1600B) * (atlas1600A * atlas1600B ^ 2)) ^ 3)⁻¹ * atlas1600B * (((atlas1600A * atlas1600B) * (atlas1600A * atlas1600B ^ 2)) ^ 3) := by
  rw [a_eq_cache, b_eq_cache]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem up_word : up =
    x2p⁻¹ * atlas1600A⁻¹ * x2p * atlas1600A⁻¹ * x2p * (atlas1600A⁻¹ * x2p⁻¹) ^ 4 := by
  rw [a_eq_cache]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem vp_word : vp =
    x2p * atlas1600A⁻¹ * x2p⁻¹ * (atlas1600A⁻¹ * x2p) ^ 2 * (atlas1600A⁻¹ * x2p⁻¹) ^ 5 := by
  rw [a_eq_cache]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem rp_word : rp =
    (x2p⁻¹ * atlas1600A) ^ 2 * (x2p * atlas1600A) ^ 2 := by
  rw [a_eq_cache]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem sp_word : sp =
    atlas1600A * x2p * (atlas1600A * x2p⁻¹) ^ 2 * (atlas1600A * x2p) ^ 2 * atlas1600A * x2p⁻¹ := by
  rw [a_eq_cache]
  apply Equiv.ext
  apply allFin
  decide +kernel

public theorem tp_word : tp =
    x2p * atlas1600A * x2p * (atlas1600A⁻¹ * x2p⁻¹) ^ 3 * (atlas1600A⁻¹ * x2p) ^ 2 := by
  rw [a_eq_cache]
  apply Equiv.ext
  apply allFin
  decide +kernel

end Tits.FiveFrobenius
