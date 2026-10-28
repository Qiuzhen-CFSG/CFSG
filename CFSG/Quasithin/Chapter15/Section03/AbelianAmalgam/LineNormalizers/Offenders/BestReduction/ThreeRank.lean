module

public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.Quasithin.Rank

/-!
# The three-rank of the centralizer factor

The quotient by the temporary normal two-subgroup is the actual product
`S₃ × Ċ_E`. Odd-prime rank decreases across this quotient, and the cubic
subgroup of the first factor uses one of the two available units of rank.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.3.67, printed p.1154. This is independent of the offender classification.
-/

public section
open Subgroup

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction

private theorem symmetricThree_threeRank_pos :
    1 ≤ primeRank 3 (Equiv.Perm (Fin 3)) := by
  have hc : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hc]; decide)
  let : IsElementaryAbelian 3 (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (by simpa only [hx] using pow_orderOf_eq_one x)
  exact IsElementaryAbelian.primeRank_ge_of_card (zpowers x)
    (by rw [Nat.card_zpowers, hx, pow_one])

/-- The centralizer factor has three-rank at most one. The quotient kernel
is a normal two-group; no unrestricted quotient monotonicity is used. -/
theorem centralizerFactor_threeRank_le_one
    {G : Type*} [Group G] [Finite G] (Q C : Subgroup G) [Q.Normal]
    (hQ : IsPGroup 2 Q) (hG : primeRank 3 G ≤ 2)
    (e : (G ⧸ Q) ≃* (Equiv.Perm (Fin 3) × C.map (QuotientGroup.mk' Q))) :
    primeRank 3 (C.map (QuotientGroup.mk' Q)) ≤ 1 := by
  have hr := (primeRank_quotient_le_of_isTwoGroup 3 (by decide) Q hQ).trans hG
  rw [Theory.GroupTheory.primeRank_equiv 3 e, primeRank_prod_eq_add] at hr
  have := symmetricThree_threeRank_pos
  omega

/-- The SQTK hypothesis supplies the bound on the original temporary group. -/
theorem centralizerFactor_threeRank_le_one_of_sqtk
    {G : Type*} [Group G] [Finite G] {K : GroupClass}
    (hG : IsSQTK K G) (Q C : Subgroup G) [Q.Normal] (hQ : IsPGroup 2 Q)
    (e : (G ⧸ Q) ≃* (Equiv.Perm (Fin 3) × C.map (QuotientGroup.mk' Q))) :
    primeRank 3 (C.map (QuotientGroup.mk' Q)) ≤ 1 :=
  centralizerFactor_threeRank_le_one Q C hQ
    (hG.stronglyQuasithin 3 (by decide) (by decide)) e

/-- In particular the actual Thompson image inside this factor has the same bound. -/
theorem thompsonImage_threeRank_le_one
    {G : Type*} [Group G] [Finite G] (Q C I : Subgroup G) [Q.Normal]
    (hQ : IsPGroup 2 Q) (hG : primeRank 3 G ≤ 2) (hIC : I ≤ C)
    (e : (G ⧸ Q) ≃* (Equiv.Perm (Fin 3) × C.map (QuotientGroup.mk' Q))) :
    primeRank 3 (I.map (QuotientGroup.mk' Q)) ≤ 1 :=
  (Theory.GroupTheory.primeRank_le_of_injective 3
    (Subgroup.inclusion (map_mono hIC)) (Subgroup.inclusion_injective _)).trans
      (centralizerFactor_threeRank_le_one Q C hQ hG e)

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction
