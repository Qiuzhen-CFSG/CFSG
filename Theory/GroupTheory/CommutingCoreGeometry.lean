module
public import Theory.GroupTheory.CommutingFactorIntersection
public import Mathlib.GroupTheory.Commutator.Basic

/-!
# Centralizer bounds across two commuting factors

Suppose disjoint commuting ambient factors contain Pᵢ ≥ Nᵢ ≥ Zᵢ.
If C_{Pᵢ}(Nᵢ) lies in Zᵢ, then C_{P₁P₂}(N₁N₂) lies in Z₁Z₂.
If an element of Pᵢ centralizing Nᵢ modulo Zᵢ must lie in Nᵢ, the same
criterion holds for the products. The modulo assertion uses raw ambient
commutators and requires no normality or quotient choice.

Write an element as ab in P₁P₂. Cross-factor commutation lets each Nᵢ
test only its corresponding coordinate. Disjointness then identifies
(Z₁Z₂) intersect Kᵢ with Zᵢ and applies the factor's modulo criterion.

Source application: Aschbacher--Smith, proof of 14.6.9(i), printed p.1027.
The source endgame applies the packet to the actual point-core geometry
and its independently proved two-factor cover.
-/

public section
open scoped Pointwise commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

private theorem centralizes_left_factor
    (A B N : Subgroup G) (hNA : N ≤ A) (hc : A ≤ centralizer (B : Set G))
    (a b : G) (hb : b ∈ B) (hab : a * b ∈ centralizer (N : Set G)) :
    a ∈ centralizer (N : Set G) := by
  have hbC : b ∈ centralizer (N : Set G) :=
    centralizer_le hNA ((le_centralizer_iff.mp hc) hb)
  simpa only [mul_inv_cancel_right] using
    (centralizer (N : Set G)).mul_mem hab ((centralizer (N : Set G)).inv_mem hbC)

private theorem mod_centralizes_left_factor
    (K₁ K₂ P₁ P₂ N₁ Z₁ Z₂ : Subgroup G)
    (hd : Disjoint K₁ K₂) (hc : K₁ ≤ centralizer (K₂ : Set G))
    (hP₁ : P₁ ≤ K₁) (hP₂ : P₂ ≤ K₂) (hN₁ : N₁ ≤ P₁)
    (hZ₁ : Z₁ ≤ K₁) (hZ₂ : Z₂ ≤ K₂)
    (a b : G) (ha : a ∈ P₁) (hb : b ∈ P₂)
    (hm : ∀ n ∈ N₁, ⁅n,a*b⁆ ∈ Z₁ ⊔ Z₂) :
    ∀ n ∈ N₁, ⁅n,a⁆ ∈ Z₁ := by
  have hZ : (Z₁ ⊔ Z₂) ⊓ K₁ = Z₁ := by
    have hh := sup_inf_sup_eq_of_disjoint_commuting_factors K₁ K₂ Z₁ Z₂ K₁ ⊥
      hd hc hZ₁ hZ₂ le_rfl bot_le
    simpa only [sup_bot_eq,inf_bot_eq,inf_eq_left.mpr hZ₁] using hh
  intro n hn
  have hnb : ⁅n,b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
    ((hc (hP₁ (hN₁ hn))) b (hP₂ hb)).symm
  have hcomm := hm n hn
  rw [commutatorElement_mul_right_eq_mul_conj,hnb,mul_one,mul_inv_cancel_right] at hcomm
  have hmem : ⁅n,a⁆ ∈ K₁ := by
    rw [commutatorElement_def]
    exact K₁.mul_mem (K₁.mul_mem (K₁.mul_mem (hP₁ (hN₁ hn)) (hP₁ ha))
      (K₁.inv_mem (hP₁ (hN₁ hn)))) (K₁.inv_mem (hP₁ ha))
  exact hZ ▸ (show ⁅n,a⁆ ∈ (Z₁ ⊔ Z₂) ⊓ K₁ from ⟨hcomm,hmem⟩)

/-- Ordinary and modulo centralizer bounds pass to the product of two disjoint commuting factors. -/
theorem commuting_core_geometry
    (K₁ K₂ P₁ P₂ N₁ N₂ Z₁ Z₂ : Subgroup G)
    (hd : Disjoint K₁ K₂) (hc : K₁ ≤ centralizer (K₂ : Set G))
    (hP₁ : P₁ ≤ K₁) (hP₂ : P₂ ≤ K₂)
    (hN₁ : N₁ ≤ P₁) (hN₂ : N₂ ≤ P₂) (hZ₁ : Z₁ ≤ N₁) (hZ₂ : Z₂ ≤ N₂)
    (hC₁ : P₁ ⊓ centralizer (N₁ : Set G) ≤ Z₁)
    (hC₂ : P₂ ⊓ centralizer (N₂ : Set G) ≤ Z₂)
    (hmod₁ : ∀ c ∈ P₁, (∀ n ∈ N₁, ⁅n,c⁆ ∈ Z₁) → c ∈ N₁)
    (hmod₂ : ∀ c ∈ P₂, (∀ n ∈ N₂, ⁅n,c⁆ ∈ Z₂) → c ∈ N₂) :
    (P₁ ⊔ P₂) ⊓ centralizer ((N₁ ⊔ N₂ : Subgroup G) : Set G) ≤ Z₁ ⊔ Z₂ ∧
      ∀ c ∈ P₁ ⊔ P₂, (∀ n ∈ N₁ ⊔ N₂, ⁅n,c⁆ ∈ Z₁ ⊔ Z₂) → c ∈ N₁ ⊔ N₂ := by
  have hPcomm : P₁ ≤ centralizer (P₂ : Set G) :=
    hP₁.trans (hc.trans (centralizer_le hP₂))
  have hprod : (↑(P₁ ⊔ P₂) : Set G) = (P₁ : Set G) * (P₂ : Set G) :=
    coe_mul_of_left_le_normalizer_right P₁ P₂ (hPcomm.trans (centralizer_le_normalizer _))
  constructor
  · rintro c ⟨hcP,hcN⟩
    have hcP' : c ∈ (P₁ : Set G) * (P₂ : Set G) := by rw [←hprod]; exact hcP
    obtain ⟨a,ha,b,hb,rfl⟩ := hcP'
    have hab : a*b = b*a := ((hPcomm ha) b hb).symm
    have haN := centralizes_left_factor P₁ P₂ N₁ hN₁ hPcomm a b hb
      (centralizer_le (show N₁ ≤ N₁ ⊔ N₂ from le_sup_left) hcN)
    have hbN := centralizes_left_factor P₂ P₁ N₂ hN₂ (le_centralizer_iff.mp hPcomm) b a ha
      (hab ▸ centralizer_le (show N₂ ≤ N₁ ⊔ N₂ from le_sup_right) hcN)
    exact mul_mem_sup (hC₁ ⟨ha,haN⟩) (hC₂ ⟨hb,hbN⟩)
  · intro c hcP hm
    have hcP' : c ∈ (P₁ : Set G) * (P₂ : Set G) := by rw [←hprod]; exact hcP
    obtain ⟨a,ha,b,hb,rfl⟩ := hcP'
    have hab : a*b = b*a := ((hPcomm ha) b hb).symm
    have haN : a ∈ N₁ := hmod₁ a ha
      (mod_centralizes_left_factor K₁ K₂ P₁ P₂ N₁ Z₁ Z₂ hd hc hP₁ hP₂ hN₁
        (hZ₁.trans (hN₁.trans hP₁)) (hZ₂.trans (hN₂.trans hP₂)) a b ha hb
        (fun n hn => hm n (mem_sup_left hn)))
    have hbN : b ∈ N₂ := hmod₂ b hb
      (mod_centralizes_left_factor K₂ K₁ P₂ P₁ N₂ Z₂ Z₁ hd.symm
        (le_centralizer_iff.mp hc) hP₂ hP₁ hN₂
        (hZ₂.trans (hN₂.trans hP₂)) (hZ₁.trans (hN₁.trans hP₁)) b a hb ha
        (by intro n hn; rw [←hab,sup_comm Z₂ Z₁]; exact hm n (mem_sup_right hn)))
    exact mul_mem_sup haN hbN

end Subgroup
