module

public import Theory.GroupTheory.PrimeRankProduct

/-!
# Three-rank below a central product with cubic intersection

Elementary subgroups in the two commuting factors multiply to an elementary
subgroup. Their intersection has order at most three, so two rank-two factors
contribute at least rank three. This is only a lower bound: arbitrary cubic
central products need not have rank at most three.

Source: Aschbacher–Smith A.2.12(II), printed p.37.
-/

public section
namespace Subgroup
open Theory.GroupTheory
variable {H : Type*} [Group H] [Finite H]

/-- Commuting rank-two factors meeting in at most three elements give rank at least three. -/
theorem three_le_primeRank_of_cubic_intersection (A B : Subgroup H)
    (hc : A ≤ centralizer (B : Set H))
    (hI : Nat.card (A ⊓ B : Subgroup H) ≤ 3)
    (hA : 2 ≤ primeRank 3 A) (hB : 2 ≤ primeRank 3 B) : 3 ≤ primeRank 3 H := by
  obtain ⟨E, hE, hEc⟩ := exists_elementaryAbelian_card_primeRank (G := A) (p := 3)
  obtain ⟨F, hF, hFc⟩ := exists_elementaryAbelian_card_primeRank (G := B) (p := 3)
  let _ := hE
  let _ := hF
  let E' := E.map A.subtype
  let F' := F.map B.subtype
  have hEA : E' ≤ A := map_subtype_le E
  have hFB : F' ≤ B := map_subtype_le F
  have hcc : F' ≤ centralizer (E' : Set H) := by
    intro y hy x hx
    exact (hc (hEA hx) y (hFB hy)).symm
  let : IsElementaryAbelian 3 E' := IsElementaryAbelian.map A.subtype
  let : IsElementaryAbelian 3 F' := IsElementaryAbelian.map B.subtype
  have hsup : IsElementaryAbelian 3 (E' ⊔ F' : Subgroup H) :=
    IsElementaryAbelian.sup_of_le_centralizer hcc
  have hE9 : 9 ≤ Nat.card E' := by
    rw [card_map_of_injective A.subtype_injective, hEc]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 3) hA
  have hF9 : 9 ≤ Nat.card F' := by
    rw [card_map_of_injective B.subtype_injective, hFc]
    exact Nat.pow_le_pow_right (by decide : 1 ≤ 3) hB
  have hi : Nat.card (E' ⊓ F' : Subgroup H) ≤ 3 :=
    (card_le_of_le (inf_le_inf hEA hFB)).trans hI
  have hcount := card_mul_eq_card_inf_mul_card_sup_of_normalizes E' F'
    (hcc.trans (centralizer_le_normalizer _))
  by_contra! hlt
  have hr : primeRank 3 H ≤ 2 := by omega
  have hsize := (primeRank_le_iff_elementary_card_le H).mp hr (E' ⊔ F') hsup
  have hprod := Nat.mul_le_mul hi hsize
  have hlarge := Nat.mul_le_mul hE9 hF9
  omega

end Subgroup
