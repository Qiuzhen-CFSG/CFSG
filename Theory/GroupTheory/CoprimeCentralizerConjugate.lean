module

public import Theory.GroupTheory.CoprimeCentralizerSupplement

/-!
# Returning conjugates in a coprime centralizer supplement

If `C(W)` supplements a normal subgroup of order coprime to `p`, a conjugate
of `W` in a common `p`-overgroup equals `W`. The quotient kills the supplement
and conjugation acts trivially on the image of `W`; injectivity on the common
prime-power overgroup lifts this equality element by element.

Source: the odd-core argument in Janko–Thompson, Math. Z. 113 (1970), §6,
printed p.395, using Lemma 3.1.
-/

namespace Subgroup

/-- A returning conjugate is fixed when a coprime normal subgroup supplements
its centralizer. -/
public theorem map_conj_eq_of_coprime_centralizer_supplement
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (W O P : Subgroup G) [O.Normal]
    (hO : Nat.Coprime p (Nat.card O))
    (hsupp : centralizer (W : Set G) ⊔ O = ⊤)
    (hP : IsPGroup p P) (hWP : W ≤ P)
    (g : G) (hg : W.map (MulAut.conj g).toMonoidHom ≤ P) :
    W.map (MulAut.conj g).toMonoidHom = W := by
  let q := QuotientGroup.mk' O
  have hinj := injective_comp_subtype_of_coprime_ker q
    (by simpa only [q, QuotientGroup.ker_mk'] using hO) P hP
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_right.mp
    (show g ∈ centralizer (W : Set G) ⊔ O by rw [hsupp]; trivial)
  have hbq : q b = 1 := (QuotientGroup.eq_one_iff b).mpr hb
  have hqg : q g = q a := by
    rw [← hab, map_mul, hbq, mul_one]
  apply eq_of_le_of_card_ge ?_ (by rw [card_map_of_injective (MulAut.conj g).injective])
  rintro x ⟨w, hw, rfl⟩
  have hconj : g * w * g⁻¹ ∈ P := hg (mem_map_of_mem _ hw)
  have heq : q (g * w * g⁻¹) = q w := by
    rw [map_mul, map_mul, map_inv, hqg, ← map_mul, ← map_inv, ← map_mul]
    rw [← ha w hw, mul_inv_cancel_right]
  have hsame : g * w * g⁻¹ = w := congrArg Subtype.val
    (hinj (a₁ := (⟨g * w * g⁻¹, hconj⟩ : P))
      (a₂ := (⟨w, hWP hw⟩ : P)) heq)
  change g * w * g⁻¹ ∈ W
  rw [hsame]
  exact hw

end Subgroup
