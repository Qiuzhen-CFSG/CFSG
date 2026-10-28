module
public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.StarPlacement.Models
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.Adequate
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.Mathieu.M11.Properties.Order
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer.LowerBound
/-!
# Separating the 13.3.2 quotient list from the intrinsic embedding list

The exact orders separate the invariant alternatives of 1.3.4, including
its retained Held case. An odd-field linear three-group has order 5616 at
p=3; for larger odd p even its projective order exceeds 6048. The even-field
symplectic parameter is at least four. Normality under T separately rules
out the exchanged-component alternative.

Source: Aschbacher--Smith, 1.3.4 and 13.3.14(d), printed pp.509--511,892.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
open Chapter1.XiEmbedding
variable {Q : Type*} [Group Q]
private theorem card_le (h : MidSizeModel Q) : Nat.card Q ≤ 6048 := by
  rcases h.card with h|h|h|h|h <;> omega
private theorem card_ne (h : MidSizeModel Q) : Nat.card Q ≠ 5616 := by
  rcases h.card with h|h|h|h|h <;> omega
private theorem polynomial_large {q : ℕ} (hq : 5 ≤ q) :
    372000 ≤ q^3 * (q^3-1) * (q^2-1) := by
  have h2 : 25 ≤ q^2 := Nat.pow_le_pow_left hq 2
  have h3 : 125 ≤ q^3 := Nat.pow_le_pow_left hq 3
  exact Nat.mul_le_mul (Nat.mul_le_mul h3 (by omega : 124 ≤ q^3-1))
    (by omega : 24 ≤ q^2-1)

theorem MidSizeModel.not_linearThree (h : MidSizeModel Q) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) : ¬ LinearThreeModel p Q := by
  have hsmall := card_le h
  have hp3 : p = 3 ∨ 5 ≤ p := by
    have := hp.two_le
    obtain ⟨k,hk⟩ := ho
    omega
  rintro (⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩)
  · have hc := Matrix.PSL3.LinearThree.DefiningSylow.card_specialLinear F
    rw [hF, ← Nat.card_congr e.toEquiv] at hc
    rcases hp3 with rfl | hb
    · exact card_ne h (by norm_num at hc; exact hc)
    · have := polynomial_large hb
      omega
  · have hc := Matrix.PSL3.LinearThree.card_projective_mul_scalar F
    rw [hF, ← Nat.card_congr e.toEquiv] at hc
    rcases hp3 with rfl | hb
    · exact card_ne h (by norm_num at hc; exact hc)
    · have := polynomial_large hb
      have hg : Nat.gcd 3 (p-1) ≤ 3 := Nat.gcd_le_left _ (by decide)
      have hm := Nat.mul_le_mul hsmall hg
      omega

theorem MidSizeModel.not_symplectic (h : MidSizeModel Q) (p : ℕ) :
    ¬ SymplecticModel p Q := by
  rintro ⟨n,he,_,F,_,_,hF,⟨e⟩⟩
  have hn : 2 ≤ n := by
    have hf : 1 < 2^n := hF ▸ Finite.one_lt_card (α := F)
    obtain ⟨k,hk⟩ := he
    by_contra hn
    have : n = 0 := by omega
    simp [this] at hf
  have hq : 4 ≤ Nat.card F := by
    rw [hF]; exact Nat.pow_le_pow_right (by decide : 0 < 2) hn
  have h2 : 16 ≤ Nat.card F ^ 2 := Nat.pow_le_pow_left hq 2
  have h4 : 256 ≤ Nat.card F ^ 4 := Nat.pow_le_pow_left hq 4
  have hb : 979200 ≤ Nat.card F ^ 4 * (Nat.card F ^ 2-1) * (Nat.card F ^ 4-1) :=
    Nat.mul_le_mul (Nat.mul_le_mul h4 (by omega : 15 ≤ Nat.card F ^ 2-1))
      (by omega : 255 ≤ Nat.card F ^ 4-1)
  have hc := Theory.SpecificGroups.SymplecticFour.card_sp F
  rw [← Nat.card_congr e.toEquiv] at hc
  have := card_le h
  omega

theorem MidSizeModel.not_exceptional (h : MidSizeModel Q) : ¬ ExceptionalModel Q := by
  have hb := card_le h
  rintro (⟨⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩)
  · rw [Nat.card_congr e.toEquiv, Sporadic.Mathieu.m11_order] at hb
    omega
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    rw [hF, ← Nat.card_congr e.toEquiv] at hc
    norm_num [Fin.prod_univ_succ] at hc
    omega
  · have hc := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    rw [hF, ← Nat.card_congr e.toEquiv] at hc
    norm_num [Fin.prod_univ_succ] at hc
    omega

theorem MidSizeModel.not_held (h : MidSizeModel Q) : ¬ Nonempty (Q ≃* Held.He) := by
  rintro ⟨e⟩
  have hb := card_le h
  rw [Nat.card_congr e.toEquiv] at hb
  have := Held.NormalizerBounds.card_lower_bound
  omega

variable {G : Type*} [Group G]
theorem not_adequate_alternatives_of_midSize {p : ℕ} {T P L : Subgroup G}
    (hp : p.Prime) (ho : Odd p) (hTL : T ≤ normalizer L)
    (hL : MidSizeModel (Chapter1.XiQuotient L)) :
    ¬ (Alternatives p T P L ∨ HeldAlternative p T P L) := by
  rintro (⟨_,hs|⟨_,hl|⟨hs,_⟩|⟨_,he⟩⟩⟩ | ⟨_,_,_,hh⟩)
  · exact hs.1.1 hTL
  · exact hL.not_linearThree hp ho hl
  · exact hL.not_symplectic p hs
  · exact hL.not_exceptional he
  · exact hL.not_held hh
end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
