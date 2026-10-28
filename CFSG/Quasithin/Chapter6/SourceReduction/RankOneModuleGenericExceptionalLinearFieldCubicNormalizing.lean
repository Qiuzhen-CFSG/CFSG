module

public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldCartan
public import Theory.GroupTheory.NormalizerQuotientInner

/-!
# The inner-action step of the normalizing cubic branch

For the compatible Cartans A and B, Hall restriction gives A∩H≤B: B
normalizes the odd subgroup A∩H, and the restricted Hall index is both odd
and a power of two. Consequently a cubic C≤A contained in H equals the
actual B, not merely a conjugate of B.

The quotient-action application uses K=O²(H) in G and its literal quotient
K/O₂(K). An inner cubic lies in K when the action kernel has order prime
to three, and hence equals B. The kernel condition is 5.1.16(1); ruling
out the outer-action case is the remaining argument of 5.1.18. Neither
that exclusion nor the later field-size argument is asserted here.

Source: Aschbacher--Smith, 5.1.16(1), 5.1.18, printed pp.639,642--643.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A B C : Subgroup G} {n : ℕ}

/-- The compatible right Cartan contains the whole left-Cartan intersection
with H. The Hall condition is on the actual N_G(L)∩H. -/
theorem CartanPair.left_inf_outside_le_right
    (c : CartanPair T L H A B) : A ⊓ H ≤ B := by
  let N := A ⊓ H
  let J := normalizer (L : Set G) ⊓ H
  have hNJ : N ≤ J :=
    le_inf (inf_le_left.trans (c.left_le.trans (inf_le_left.trans L.le_normalizer))) inf_le_right
  have hBN : B ≤ normalizer (N : Set G) :=
    (le_inf c.right_normalizes_left
      ((c.right_le.trans inf_le_right).trans H.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hh := OddHall.hall_restrict_of_normalizes c.right_hall c.right_le hNJ hBN
  have ho : ¬ 2 ∣ Nat.card N := by
    intro hd
    apply c.left_hall.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ _ rfl
    rw [Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact hd.trans (card_dvd_of_le (show N ≤ A from inf_le_left))
  have hi : (B.subgroupOf N).index = 1 := by
    apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
    intro p hp hd
    have hp2 : p = 2 := Classical.not_not.mp (hh.p_in_pi_of_p_dvd_index ⟨p,hp⟩ hd)
    exact ho (hp2 ▸ hd.trans (B.subgroupOf N).index_dvd_card)
  exact relIndex_eq_one.mp hi

/-- The given cubic, once contained in H, equals the given right Hall subgroup. -/
theorem LinearFieldCartan.cubic_eq_right_of_le_outside
    (c : LinearFieldCartan T L H A B C n) (hCH : C ≤ H) : C = B := by
  apply eq_of_le_of_card_ge
    ((le_inf c.cubic_le hCH).trans c.toCartanPair.left_inf_outside_le_right)
  rw [c.cubic_card, c.right_card]

/-- The literal action of the residual normalizer on K/O₂(K). Its kernel
is the source C_G(K/O₂(K)), viewed inside N_G(K). -/
abbrev linearResidualAction (H : Subgroup G) :=
  normalizerQuotientAction (residual H) (pCore 2 (residual H))

/-- The inner-action branch of 5.1.18, retaining exactly its centralizer input. -/
theorem LinearFieldCartan.cubic_eq_right_of_inner
    (c : LinearFieldCartan T L H A B C n)
    (hCN : C ≤ normalizer (residual H : Set G))
    (hker : Nat.Coprime 3 (Nat.card (linearResidualAction H).ker))
    (hinner : (C.subgroupOf (normalizer (residual H : Set G))).map
      (linearResidualAction H) ≤
        (MulAut.conj : ((residual H) ⧸ pCore 2 (residual H)) →*
          MulAut ((residual H) ⧸ pCore 2 (residual H))).range) : C = B := by
  apply c.cubic_eq_right_of_le_outside
  exact (le_of_normalizerQuotientAction_inner (residual H) (pCore 2 (residual H))
    C hCN (by simpa only [c.cubic_card] using hker) hinner).trans (map_subtype_le _)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
