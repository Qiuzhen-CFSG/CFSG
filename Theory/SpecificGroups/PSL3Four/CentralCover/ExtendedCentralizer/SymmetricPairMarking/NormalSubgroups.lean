module
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.SymmetricPairMarking

/-!
# Identifying the linear factor of the common normalizer

A normal subgroup of S3 times S3 which misses the three marked involutions
contains only cubic elements. If it contains the first cubic axis and misses
some cubic element, it is exactly that axis. Two small element certificates
supply the conjugacy and generation calculations; no subgroup enumeration is
needed. The actual Sylow-normalizer bridge uses this for its component kernel.
Source: Aschbacher–Smith15.3.38, printed p.1136.
-/

public section
open Subgroup
namespace Matrix.PSL3Four.ExtendedCentralizer.SymmetricPairMarking
local instance : Fintype SymmetricThree := fintypePerm

private theorem cubic_or_involution : ∀ x : Pair, x ^ 3 = 1 ∨
    ∃ g : Pair, g * x ^ 3 * g⁻¹ = (1, reflection) ∨
      g * x ^ 3 * g⁻¹ = (reflection, reflection) ∨
      g * x ^ 3 * g⁻¹ = (reflection, 1) := by decide +kernel

private theorem second_generator : ∀ x : Pair, x ^ 3 = 1 → x.2 ≠ 1 →
    ∃ i j : Fin 3, (1, rotation) = (rotation, 1) ^ i.val * x ^ j.val := by
  decide +kernel

private theorem cubic_mem (x : SymmetricThree) (hx : x ^ 3 = 1) :
    x ∈ zpowers rotation := by
  have h : ∀ y : SymmetricThree,
      y ^ 3 = 1 → y = 1 ∨ y = rotation ∨ y = rotation ^ 2 := by decide +kernel
  rcases h x hx with rfl | rfl | rfl
  · exact one_mem _
  · exact mem_zpowers _
  · exact pow_mem (mem_zpowers _) _

/-- The actual normal component intersection is the linear cubic factor.
The three marked involutions and the diagonal cubic remain outside it. -/
theorem normal_eq_first_cubic (K : Subgroup Pair) [K.Normal]
    (ht : (1, reflection) ∉ K) (hf : (reflection, reflection) ∉ K)
    (hw : (reflection, 1) ∉ K) (hrot : (rotation, 1) ∈ K)
    (hnot : ¬ (zpowers rotation).prod (zpowers rotation) ≤ K) :
    K = (zpowers rotation).prod ⊥ := by
  have hfirst (a : SymmetricThree) (ha : a ∈ zpowers rotation) : (a, 1) ∈ K := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp ha
    have hk := K.zpow_mem hrot k
    change (rotation ^ k, (1 : SymmetricThree) ^ k) ∈ K at hk
    simpa only [one_zpow] using hk
  have hcubic (x : Pair) (hx : x ∈ K) : x ^ 3 = 1 := by
    rcases cubic_or_involution x with hc | ⟨g, hg | hg | hg⟩
    · exact hc
    all_goals
      have hm := (inferInstance : K.Normal).conj_mem (x ^ 3) (K.pow_mem hx 3) g
      rw [hg] at hm
    · exact (ht hm).elim
    · exact (hf hm).elim
    · exact (hw hm).elim
  apply le_antisymm
  · intro x hx
    have hc := hcubic x hx
    have hx2 : x.2 = 1 := by
      by_contra hn
      obtain ⟨i, j, hij⟩ := second_generator x hc hn
      have hd : (1, rotation) ∈ K := hij ▸ K.mul_mem (K.pow_mem hrot i.val) (K.pow_mem hx j.val)
      apply hnot
      intro y hy
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hy.2
      have hs : (1, y.2) ∈ K := by
        rw [← hk]
        have hpow := K.zpow_mem hd k
        change ((1 : SymmetricThree) ^ k, rotation ^ k) ∈ K at hpow
        simpa only [one_zpow] using hpow
      simpa only [Prod.mk_mul_mk, mul_one, one_mul] using K.mul_mem (hfirst y.1 hy.1) hs
    exact ⟨cubic_mem x.1 (congrArg Prod.fst hc), hx2⟩
  · intro x hx
    have he : x = (x.1, 1) := Prod.ext rfl hx.2
    exact he ▸ hfirst x.1 hx.1

end Matrix.PSL3Four.ExtendedCentralizer.SymmetricPairMarking
