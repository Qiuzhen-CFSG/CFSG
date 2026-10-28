module
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M24.Orders
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models.M24.Exclusions
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.TwoQuotient
public import Theory.GroupTheory.SubgroupProductCard
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms

/-!
# The Cartan restriction for the actual M₂₄ automorphism groups

An odd abelian subgroup containing seven has order seven or twenty-one.
One containing a cyclic fifteen has order fifteen. Their products with an
ambient Sylow two-subgroup would therefore have orders 7168, 21504 or 15360.
The native double-coset exclusions rule out all three orders. The remaining
Cartan exponents are at most two. Faithful inner conjugation and the proved
trivial outer quotient extend the bound to all inner-containing automorphism
subgroups. No solvability or ordinary maximal-subgroup classification is used.

Source: Aschbacher--Smith, Definition E.3.37 and Table 7.3.4,
printed pp.239 and 699.
-/

public section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models
open Subgroup Sporadic.Mathieu
open scoped Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterE.Section06.FixedPointBounds

private theorem sylow_card (S : Sylow 2 M24) : Nat.card S = 1024 := by
  rw [Sylow.card_eq_multiplicity, m24_order]
  decide +kernel

private theorem product_card {c : ℕ} (w : NPrimeWitness M24 c) :
    Nat.card (w.abelianGroup ⊔ (w.sylow : Subgroup M24) : Subgroup M24) = Nat.card w.abelianGroup * 1024 := by
  have hs := sylow_card w.sylow
  have hd : Disjoint w.abelianGroup (w.sylow : Subgroup M24) := by
    apply disjoint_of_coprime_natCard
    rw [hs]
    exact (Nat.coprime_two_right.mpr w.odd).pow_right 10
  have hprod := card_set_mul_mul_card_inf w.abelianGroup (w.sylow : Subgroup M24)
  rw [hd.eq_bot, Subgroup.card_bot, mul_one,
    ← coe_sup_of_set_mul_comm _ _ w.permutes, hs] at hprod
  exact hprod

private theorem order_twentyone {G : Type*} [Group G] [Finite G] [IsMulCommutative G]
    (hcard : Nat.card G = 21) : ∃ g : G, orderOf g = 21 := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hcard]; decide)
  obtain ⟨y,hy⟩ := exists_prime_orderOf_dvd_card' (G := G) 7 (by rw [hcard]; decide)
  refine ⟨x*y, ?_⟩
  rw [(Commute.all x y).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hx,hy]; decide), hx, hy]

private theorem no_seven {c : ℕ} (w : NPrimeWitness M24 c) :
    ¬ 7 ∣ Nat.card w.abelianGroup := by
  intro h7
  let := w.abelian
  let H := w.abelianGroup ⊔ (w.sylow : Subgroup M24)
  have hcard := product_card w
  apply M24Cartan.no_cartan_overgroup H w.sylow le_sup_right
  rcases M24Cartan.abelian_seven_card w.abelianGroup w.odd h7 with h | h
  · exact Or.inl (by rw [h] at hcard; exact hcard)
  · obtain ⟨g, hg⟩ := order_twentyone h
    let f : w.abelianGroup →* H := Subgroup.inclusion le_sup_left
    exact Or.inr (Or.inr ⟨by rw [h] at hcard; exact hcard, f g,
      (orderOf_injective f (Subgroup.inclusion_injective _) g).trans hg⟩)

private theorem no_fifteen {c : ℕ} (w : NPrimeWitness M24 c) :
    Nat.card w.cyclicGroup ≠ 15 := by
  intro h15
  let := w.abelian
  let := w.cyclic
  have hd : 15 ∣ Nat.card w.abelianGroup := h15 ▸ card_dvd_of_le w.cyclic_le
  have h5 := (by decide : 5 ∣ 15).trans hd
  have hB : Nat.card w.abelianGroup = 15 := by
    rcases M24Cartan.abelian_five_card w.abelianGroup w.odd h5 with h | h
    · rw [h] at hd
      norm_num at hd
    · exact h
  let H := w.abelianGroup ⊔ (w.sylow : Subgroup M24)
  have hcard : Nat.card H = 15360 := by rw [product_card w, hB]
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := w.cyclicGroup)
  let f : w.cyclicGroup →* H := Subgroup.inclusion (w.cyclic_le.trans le_sup_left)
  exact M24Cartan.no_cartan_overgroup H w.sylow le_sup_right
    (Or.inr (Or.inl ⟨hcard, f x,
      (orderOf_injective f (Subgroup.inclusion_injective _) x).trans (hx.trans h15)⟩))

/-- The native Cartan parameter of M₂₄ is at most two. -/
theorem m24_nPrime_le_two : nPrime M24 ≤ 2 := by
  apply nPrime_le_iff.mpr
  intro c w
  have hcy : 2 ^ c - 1 ∣ 244823040 := by
    rw [← w.card, ← m24_order]
    exact w.cyclicGroup.card_subgroup_dvd_card
  have hc : c < 28 := by
    by_contra h
    have hp : 2 ^ 28 ≤ 2 ^ c := Nat.pow_le_pow_right (by decide) (by omega)
    have hl := Nat.le_of_dvd (by norm_num : 0 < 244823040) hcy
    norm_num at hp
    omega
  have h7 := no_seven w
  have h7cy := fun h : 7 ∣ 2 ^ c - 1 =>
    h7 ((show 7 ∣ Nat.card w.cyclicGroup by simpa only [w.card] using h).trans
      (card_dvd_of_le w.cyclic_le))
  have h15 := no_fifteen w
  have hcard := w.card
  interval_cases c <;> solve
    | omega
    | norm_num at hcy
    | norm_num at h7cy

/-- Inner-containing subgroups of the actual M₂₄ automorphism group satisfy
the source Cartan bound. -/
theorem m24_cartanRestriction (A : Subgroup (MulAut M24))
    (hA : MulAut.innerSubgroup M24 ≤ A) : nPrime A ≤ 2 :=
  (automorphism_subgroup_nPrime_le
    (MulAut.conj_injective_of_center_eq_bot M24InvolutionCentralizers.center_eq_bot)
    M24OuterRestriction.outer_isPGroup_two A hA).trans m24_nPrime_le_two

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuGeneration.Models
