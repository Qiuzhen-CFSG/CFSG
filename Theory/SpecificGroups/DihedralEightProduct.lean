module

public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Two exclusions in `C₂ × D₈`

The direct product of a cyclic group of order two and a dihedral group of
order eight has exponent four, so contains no cyclic group of order eight.
It also contains no quaternion group of order eight: in this product the
relations `a² = b² = (ab)²` force that common square to be the identity,
whereas quaternion generators have a nonidentity common square.

The finite square identities are checked by the Lean kernel on the
concrete Mathlib carriers. These are the exclusions used in
Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, p.570, after Lemma 2.5.27.
-/

namespace DihedralEightProduct

private theorem fourth_power_eq_one :
    ∀ d : Multiplicative (ZMod 2) × DihedralGroup 4, d ^ 4 = 1 := by
  decide +kernel

private theorem common_square_eq_one :
    ∀ a b : Multiplicative (ZMod 2) × DihedralGroup 4,
      a ^ 2 = b ^ 2 → a ^ 2 = (a * b) ^ 2 → a ^ 2 = 1 := by
  decide +kernel

/-- `C₂ × D₈` contains no quaternion subgroup of order eight. -/
public theorem not_injective_quaternionEight
    (f : QuaternionGroup 2 →* Multiplicative (ZMod 2) × DihedralGroup 4) :
    ¬ Function.Injective f := by
  intro hf
  have hsq : (f (QuaternionGroup.a 1)) ^ 2 = 1 := by
    apply common_square_eq_one _ (f (QuaternionGroup.xa 0))
    · simp only [← map_pow]
      congr 1
    · simp only [← map_mul, ← map_pow]
      congr 1
  have he : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 = 1 :=
    hf (by simpa only [map_pow, map_one] using hsq)
  exact (by decide : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1) he

/-- `C₂ × D₈` contains no cyclic subgroup of order eight. -/
public theorem not_injective_cyclicEight
    (f : Multiplicative (ZMod 8) →* Multiplicative (ZMod 2) × DihedralGroup 4) :
    ¬ Function.Injective f := by
  intro hf
  have he : (Multiplicative.ofAdd (1 : ZMod 8)) ^ 4 = 1 := by
    apply hf
    simp only [map_pow, map_one]
    exact fourth_power_eq_one _
  exact (by decide : (Multiplicative.ofAdd (1 : ZMod 8)) ^ 4 ≠ 1) he

end DihedralEightProduct
