module
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.ElementaryAbelian.Injective

/-!
# A fixed factor and the conjugate span of a binary seed

For V = Z<ab>, with a fixed by R, the commutators of ab with R equal
those of b when a also centralizes the moving subgroup W. If these
commutators generate W modulo Z, then <V^R> = <a>W. An elementary W
of order eight and an independent involution a give rank four.

Source: Aschbacher--Smith, 14.6.17(5) and the endgame on printed p.1042.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G : Type*} [Group G]

theorem conjugateSpanBy_eq_fixed_factor_sup
    (Z V R W : Subgroup G) (a b : G)
    (hV : V = Z ⊔ zpowers (a * b)) (hZW : Z ≤ W) (hb : b ∈ W)
    (hRW : R ≤ normalizer (W : Set G))
    (haR : a ∈ centralizer (R : Set G)) (haW : a ∈ centralizer (W : Set G))
    (hgen : W ≤ Z ⊔ closure {x : G | ∃ r ∈ R, x = ⁅b,r⁆}) :
    conjugateSpanBy V R = zpowers a ⊔ W := by
  let X := conjugateSpanBy V R
  have hZX : Z ≤ X := (hV ▸ le_sup_left).trans (le_conjugateSpanBy V R)
  have habX : a * b ∈ X := le_conjugateSpanBy V R (by
    rw [hV]; exact (le_sup_right : zpowers (a*b) ≤ Z ⊔ zpowers (a*b)) (mem_zpowers (a * b)))
  have hWX : W ≤ X := by
    apply hgen.trans
    apply sup_le hZX
    apply (closure_le _).mpr
    rintro y ⟨r,hr,rfl⟩
    have hc : ⁅a * b,r⁆ ∈ X :=
      (le_normalizer_iff_commutator_le_left.mp (le_normalizer_conjugateSpanBy V R))
        (commutator_mem_commutator habX hr)
    have hbr : ⁅b,r⁆ ∈ W :=
      (le_normalizer_iff_commutator_le_left.mp hRW) (commutator_mem_commutator hb hr)
    have he : ⁅a * b,r⁆ = ⁅b,r⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul,
        commutatorElement_eq_one_iff_mul_comm.mpr (haR r hr).symm,
        mul_one, ←haW _ hbr, mul_inv_cancel_right]
    rwa [he] at hc
  have haX : a ∈ X := by
    have hh := X.mul_mem habX (X.inv_mem (hWX hb))
    simpa using hh
  apply le_antisymm
  · apply conjugateSpanBy_le
    · rw [hV]
      exact sup_le (hZW.trans le_sup_right) (zpowers_le.mpr
        ((zpowers a ⊔ W).mul_mem
          ((le_sup_left : zpowers a ≤ zpowers a ⊔ W) (mem_zpowers a))
          ((le_sup_right : W ≤ zpowers a ⊔ W) hb)))
    · apply le_trans (le_inf ?_ hRW) (normalizer_inf_normalizer_le_normalizer_sup _ _)
      apply le_trans ?_ (centralizer_le_normalizer _)
      apply le_centralizer_iff.mpr
      exact zpowers_le.mpr haR
  · exact sup_le (zpowers_le.mpr haX) hWX

theorem primeRank_conjugateSpanBy_fixed_factor
    [Finite G] (Z V R W : Subgroup G) [IsElementaryAbelian 2 W]
    (a b : G) (ha : orderOf a = 2) (haout : a ∉ W)
    (hV : V = Z ⊔ zpowers (a * b)) (hZW : Z ≤ W) (hb : b ∈ W)
    (hRW : R ≤ normalizer (W : Set G))
    (haR : a ∈ centralizer (R : Set G)) (haW : a ∈ centralizer (W : Set G))
    (hgen : W ≤ Z ⊔ closure {x : G | ∃ r ∈ R, x = ⁅b,r⁆})
    (hcard : Nat.card W = 8) :
    primeRank 2 (conjugateSpanBy V R) = 4 := by
  rw [conjugateSpanBy_eq_fixed_factor_sup Z V R W a b hV hZW hb hRW haR haW hgen,
    sup_comm]
  have hfix : W ≤ centralizer ({a} : Set G) := by
    intro w hw
    exact mem_centralizer_singleton_iff.mpr (haW w hw)
  obtain ⟨he,hc⟩ := IsElementaryAbelian.fixed_join_card W a ha
    (W.disjoint_zpowers_of_prime_order_not_mem a ha haout) hfix
    (show Nat.card W = 2 ^ 3 by simpa using hcard)
  let := he
  let : IsElementaryAbelian 2 (⊤ : Subgroup (W ⊔ zpowers a : Subgroup G)) :=
    IsElementaryAbelian.of_injective (⊤ : Subgroup (W ⊔ zpowers a : Subgroup G)).subtype
      Subtype.val_injective
  have hlow := IsElementaryAbelian.primeRank_ge_of_card (p := 2) (n := 4)
    (⊤ : Subgroup (W ⊔ zpowers a : Subgroup G)) (by simpa using hc)
  have hupp := (primeRank_le_iff_elementary_card_le (W ⊔ zpowers a : Subgroup G)).mpr
    (fun E _ => (card_le_card_group E).trans (le_of_eq hc))
  exact le_antisymm hupp hlow

end Subgroup
