module
public import Theory.GroupTheory.PrimeRankCentralizer
public import Theory.GroupTheory.NormalizerAction

/-!
# Inner prime-order actors in a subgroup of full prime rank

Suppose B and its ambient group have prime rank two. If every inner
automorphism of exponent p in B has a lift of exponent p, a normalizing
p-element acting inner on B belongs to B. Subtract its inner lift; the
resulting p-element centralizes B and is absorbed by rank saturation.

Source application: Aschbacher--Smith, proof of 12.6.26, printed p.832,
for the cubic A₇ and M₂₂ covers and the original Sylow E₉.
-/

public section
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- If cubic inner automorphisms have cubic lifts in a full-rank subgroup,
every normalizing cubic inducing an inner automorphism lies in that subgroup. -/
theorem Subgroup.mem_of_prime_pow_eq_one_of_inner_action
    {p : ℕ} [Fact p.Prime] (B : Subgroup G)
    (hG : primeRank p G ≤ 2) (hB : primeRank p B = 2)
    (hlift : ∀ b : B, b ^ p ∈ center B → b ^ p = 1)
    {x : G} (hx : x ^ p = 1) (hn : x ∈ normalizer (B : Set G))
    (hi : B.normalizerMonoidHom ⟨x,hn⟩ ∈ MulAut.innerSubgroup B) : x ∈ B := by
  obtain ⟨b,hb⟩ := hi
  have hconj : ∀ k : B, x * k.val * x⁻¹ = (b * k * b⁻¹).val := by
    intro k
    exact congrArg Subtype.val (DFunLike.congr_fun hb k).symm
  have hbcentral : b ^ p ∈ center B := by
    have he : (MulAut.conj b) ^ p = 1 := by
      rw [hb,←map_pow,show (⟨x,hn⟩ : normalizer (B : Set G)) ^ p = 1 from Subtype.ext hx,map_one]
    have he' : MulAut.conj (b ^ p) = 1 := by simpa only [map_pow] using he
    apply mem_center_iff.mpr
    intro k
    have hh := DFunLike.congr_fun he' k
    change b ^ p * k * (b ^ p)⁻¹ = k at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  have hbp : b ^ p = 1 := hlift b hbcentral
  have hxb : Commute x b.val := by
    have hh := hconj b
    simp only [mul_inv_cancel_right] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  have hy : x * b.val⁻¹ ∈ B := by
    apply B.mem_of_prime_pow_eq_one_of_centralizes_rank_two hG hB
    · rw [(hxb.inv_right).mul_pow,hx,inv_pow,←coe_pow,hbp,coe_one,inv_one,one_mul]
    · intro k hk
      have he : (x*b.val⁻¹)*k*(x*b.val⁻¹)⁻¹ = k := by
        have hh' := hconj (b⁻¹ * ⟨k,hk⟩ * b)
        simp only [coe_mul,coe_inv] at hh'
        calc
          (x*b.val⁻¹)*k*(x*b.val⁻¹)⁻¹ = x*(b.val⁻¹*k*b.val)*x⁻¹ := by group
          _ = b.val*(b.val⁻¹*k*b.val)*b.val⁻¹ := hh'
          _ = k := by group
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
  simpa only [inv_mul_cancel_right] using B.mul_mem hy b.property
