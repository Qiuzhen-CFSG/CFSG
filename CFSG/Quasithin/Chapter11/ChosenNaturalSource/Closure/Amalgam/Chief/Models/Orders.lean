module
public import GorensteinWalter.PSL2Cardinality
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
public import CFSG.Quasithin.Chapter11.Section01To02.SourceDefs

/-!
# Orders in the exceptional chief-image comparison

The six displayed orders are those needed for the nonabelian simple
components of the G.6.4 models. This module does not classify those models.
It proves that a nontrivial surjective image of PSL₂(p), for prime p ≥ 11,
has none of these orders. Simplicity identifies the image with the actual
PSL₂ matrix group; the order formula and three consecutive-integer gaps
finish the comparison without enumerating matrix groups.

Source: Aschbacher--Smith, 11.5.8, printed p.784, comparing 11.1.2(2)
with G.6.4(2--3), printed pp.345--346.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models

/-- Orders of the nonabelian simple C-components of the G.6.4 one-factor models.
The repeated order 20160 represents both GL(4,2) and A₈. -/
def SmallSimpleOrder (n : ℕ) : Prop :=
  n = 60 ∨ n = 168 ∨ n = 360 ∨ n = 2520 ∨ n = 20160 ∨ n = 9999360

private theorem rankOneOrder_mono {m n : ℕ} (h : m ≤ n) :
    m * (m ^ 2 - 1) / 2 ≤ n * (n ^ 2 - 1) / 2 :=
  Nat.div_le_div_right (Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1))

private theorem rankOneOrder_gap (p k n : ℕ)
    (hlo : k * (k ^ 2 - 1) / 2 < n)
    (hhi : n < (k + 1) * ((k + 1) ^ 2 - 1) / 2) :
    p * (p ^ 2 - 1) / 2 ≠ n := by
  by_cases hp : p ≤ k
  · exact ne_of_lt ((rankOneOrder_mono hp).trans_lt hlo)
  · exact ne_of_gt (hhi.trans_le (rankOneOrder_mono (by omega : k + 1 ≤ p)))

theorem large_rankOneOrder_not_small {p : ℕ} (hp : 11 ≤ p) :
    ¬ SmallSimpleOrder (p * (p ^ 2 - 1) / 2) := by
  have hlo := rankOneOrder_mono hp
  norm_num at hlo
  rintro (h | h | h | h | h | h)
  · omega
  · omega
  · omega
  · exact rankOneOrder_gap p 17 2520 (by norm_num) (by norm_num) h
  · exact rankOneOrder_gap p 34 20160 (by norm_num) (by norm_num) h
  · exact rankOneOrder_gap p 271 9999360 (by norm_num) (by norm_num) h

/-- A surjective nontrivial image of the large prime PSL₂ quotient has
none of the simple orders in the G.6.4 comparison. -/
theorem psl2_image_not_small {Q H : Type*} [Group Q] [Group H] [Nontrivial H]
    {p : ℕ} (hp : p.Prime) (hlarge : 11 ≤ p)
    (hQ : ClassicalGroup.IsPSL Q 2 p) (f : Q →* H) (hf : Function.Surjective f) :
    ¬ SmallSimpleOrder (Nat.card H) := by
  obtain ⟨F, hfield, hfinite, hcard, ⟨e⟩⟩ := hQ
  let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup Q := e.isSimpleGroup
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · obtain ⟨y, hy⟩ := exists_ne (1 : H)
      obtain ⟨x, rfl⟩ := hf y
      exact (hy (show f x = 1 from (show x ∈ f.ker from ht.symm ▸ mem_top x))).elim
  have hc := Nat.card_congr (MulEquiv.ofBijective f ⟨hinj, hf⟩).toEquiv
  have ho : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, 1, hp, hp.odd_of_ne_two (by omega), by decide, by simpa using hcard⟩
  have horder : Nat.card H = p * (p ^ 2 - 1) / 2 := by
    rw [← hc, Nat.card_congr e.toEquiv]
    exact (GorensteinWalter.psl2_card_formula F ho).trans (by rw [hcard])
  rw [horder]
  exact large_rankOneOrder_not_small hlarge

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Chief.Models
