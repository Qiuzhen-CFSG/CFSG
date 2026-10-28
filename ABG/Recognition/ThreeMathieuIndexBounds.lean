module

public import Mathlib.GroupTheory.Sylow
public import Theory.GroupAction.SimpleCosets
public import Mathlib.Tactic

/-!
# The two subgroup indices in Wong's Mathieu branch

A proper subgroup containing an order-twenty Sylow-five normalizer and an
order-eight subgroup has index eleven or sixty-six. The Sylow congruence
and Lagrange's theorem leave orders 120, 720, 1320 and 7920; properness and
the faithful coset action of a simple group exclude the latter two.
Excluding order 120 additionally uses the quaternion structure.

Source: Wong (1964), Theorem 6(a), p.108,
DOI 10.1017/S1446788700022771.
-/

namespace ABG

variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

set_option maxRecDepth 20000 in
/-- The Sylow congruence leaves only indices eleven and sixty-six. -/
public theorem mathieu_index_eleven_or_sixtysix
    (hG : Nat.card G = 7920) (P : Sylow 5 G) (Q M : Subgroup G)
    (hQ : Nat.card Q = 8) (hQM : Q ≤ M)
    (hN : Nat.card (Subgroup.normalizer (P : Set G)) = 20)
    (hNM : Subgroup.normalizer (P : Set G) ≤ M) (hM : M ≠ ⊤) :
    M.index = 11 ∨ M.index = 66 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hPM : (P : Subgroup G) ≤ M := Subgroup.le_normalizer.trans hNM
  let R : Sylow 5 M := P.subtype hPM
  have hnorm : Subgroup.normalizer (R : Set M) =
      (Subgroup.normalizer (P : Set G)).subgroupOf M := by
    change Subgroup.normalizer (((P.subtype hPM) : Subgroup M) : Set M) = _
    rw [Sylow.coe_subtype, ← Subgroup.subgroupOf_normalizer_eq hPM]
    simp only [Sylow.coe_coe]
  have hnormcard : Nat.card (Subgroup.normalizer (R : Set M)) = 20 := by
    rw [hnorm, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv, hN]
  have hcount := card_sylow_modEq_one 5 M
  rw [R.card_eq_index_normalizer] at hcount
  have hprod := (Subgroup.normalizer (R : Set M)).index_mul_card
  rw [hnormcard] at hprod
  have hdiv : (Subgroup.normalizer (R : Set M)).index = Nat.card M / 20 := by
    omega
  rw [hdiv] at hcount
  have hmod : Nat.card M / 20 % 5 = 1 := hcount
  have hd : Nat.card M ∣ 7920 := hG ▸ M.card_subgroup_dvd_card
  have h8 : 8 ∣ Nat.card M := hQ ▸ Subgroup.card_dvd_of_le hQM
  have h20 : 20 ∣ Nat.card M := hN ▸ Subgroup.card_dvd_of_le hNM
  have hnum : ∀ d ∈ Nat.divisors 7920,
      8 ∣ d → 20 ∣ d → d / 20 % 5 = 1 →
      d = 120 ∨ d = 720 ∨ d = 1320 ∨ d = 7920 := by decide
  have horders := hnum _ (Nat.mem_divisors.mpr ⟨hd, by decide⟩) h8 h20 hmod
  have hcard := M.card_mul_index
  rw [hG] at hcard
  have hne1 : M.index ≠ 1 := fun h => hM (Subgroup.index_eq_one.mp h)
  have hne6 : M.index ≠ 6 := by
    intro hi
    have hdvd := M.card_dvd_factorial_index_of_simple hM
    norm_num [hG, hi, Nat.factorial] at hdvd
  rcases horders with h | h | h | h <;> rw [h] at hcard <;> omega

end ABG
