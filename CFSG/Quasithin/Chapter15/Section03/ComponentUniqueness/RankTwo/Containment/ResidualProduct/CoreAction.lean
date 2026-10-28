module
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Containment.Reductions
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.ThreeSubgroups
public import Theory.GroupTheory.CommutatorPreimage

/-!
# The two-core action of the oriented A₄ factor

The order-four plane exhausts the intersection of an A₄ actor with the
normalizing two-group. Thus its commutators with that two-group are supported
on just this plane. Opposite support and the three-subgroups lemma force the
two actors to commute. Residual uniqueness in `A Q` supplies the needed mutual
normality; neither actor is assumed normal in the whole residual group.

This is the core-action form of the single noncentral two-chief-factor
argument in Aschbacher--Smith, 15.3.40, printed p.1138, using the two-core and
plane geometry of 15.3.7 and 15.3.11 (pp.1122--1124).
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.ResidualProduct
variable {G : Type*} [Group G]

-- The unique four in a normalized A4 exhausts its intersection with a two-group.
theorem inf_eq_plane [Finite G] {Q A W : Subgroup G}
    (hQ : IsPGroup 2 Q) (hA : Nat.card A = 12)
    (hW : Nat.card W = 4) (hWQ : W ≤ Q) (hWA : W ≤ A) :
    Q ⊓ A = W := by
  have hp : IsPGroup 2 (Q ⊓ A : Subgroup G) := hQ.to_le inf_le_left
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hp
  have hd := card_dvd_of_le (show Q ⊓ A ≤ A from inf_le_right)
  rw [hA, hn] at hd
  have hd4 : 2 ^ n ∣ 4 :=
    ((show Nat.Coprime (2 ^ n) 3 from (by decide : Nat.Coprime 2 3).pow_left n).dvd_mul_right).mp hd
  exact (eq_of_le_of_card_ge (le_inf hWQ hWA) (by rw [hW, hn]; exact Nat.le_of_dvd (by decide) hd4)).symm

-- Residual recognition is done only in A Q, not in all of Y.
theorem normalizes_actor_of_commutator_le {A B Q : Subgroup G}
    (hA : IsPPerfect 2 A) (hQ : IsPGroup 2 Q)
    (hQA : Q ≤ normalizer (A : Set G))
    (hBQ : B ≤ normalizer (Q : Set G)) (hc : ⁅A, B⁆ ≤ Q) :
    B ≤ normalizer (A : Set G) := by
  let K := A ⊔ Q
  have hAK : A ≤ K := le_sup_left
  have hQK : Q ≤ K := le_sup_right
  let : (A.subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hQA)
  have hpA : IsPPerfect 2 (A.subgroupOf K) :=
    hA.of_surjective (subgroupOfEquivOfLe hAK).symm.toMonoidHom
      (subgroupOfEquivOfLe hAK).symm.surjective
  have he : (pResidual 2 K).map K.subtype = A := by
    rw [pResidual_eq_of_isPPerfect_sup (A.subgroupOf K) (Q.subgroupOf K)
      hpA hQ.comap_subtype (by rw [← subgroupOf_sup hAK hQK]; exact subgroupOf_self _)]
    exact map_subgroupOf_eq_of_le hAK
  have hBK : B ≤ normalizer (K : Set G) := by
    have hk : K ≤ commutatorPreimage K B K :=
      sup_le (le_commutatorPreimage hAK (hc.trans hQK))
        (le_commutatorPreimage hQK
          ((le_normalizer_iff_commutator_le_left.mp hBQ).trans hQK))
    exact le_normalizer_iff_commutator_le_left.mpr
      ((commutator_mono hk le_rfl).trans
        (commutator_commutatorPreimage_le K B K K.le_normalizer))
  rw [← he]
  exact hBK.trans (normalizer_le_normalizer_characteristic_image K (pResidual 2 K))

/-- The opposite support bounds force commutation, without ambient normality of either actor. -/
theorem actors_commute {Y Q A B U W : Subgroup G}
    (hAY : A ≤ Y) (hBY : B ≤ Y)
    (hself : Y ⊓ centralizer (Q : Set G) ≤ Q)
    (hQ : IsPGroup 2 Q) (hA : IsPPerfect 2 A) (hB : IsPPerfect 2 B)
    (hQA : Q ≤ normalizer (A : Set G)) (hQB : Q ≤ normalizer (B : Set G))
    (hAQ : A ≤ normalizer (Q : Set G)) (hBQ : B ≤ normalizer (Q : Set G))
    (hWA : Q ⊓ A = W) (hUB : Q ⊓ B = U)
    (hAU : A ≤ centralizer (U : Set G)) (hBW : B ≤ centralizer (W : Set G))
    (hd : Disjoint U W) : A ≤ centralizer (B : Set G) := by
  have hQAcomm : ⁅Q, A⁆ ≤ W := hWA ▸ le_inf
    (le_normalizer_iff_commutator_le_left.mp hAQ)
    (le_normalizer_iff_commutator_le_right.mp hQA)
  have hQBcomm : ⁅Q, B⁆ ≤ U := hUB ▸ le_inf
    (le_normalizer_iff_commutator_le_left.mp hBQ)
    (le_normalizer_iff_commutator_le_right.mp hQB)
  have htriple : ⁅⁅A, B⁆, Q⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate
      (eq_bot_iff.mpr (by
        rw [commutator_comm B Q]
        exact (commutator_mono hQBcomm le_rfl).trans
          (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hAU)).le))
      (eq_bot_iff.mpr ((commutator_mono hQAcomm le_rfl).trans
        (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hBW)).le))
  have hcQ : ⁅A, B⁆ ≤ Q := (le_inf
    ((commutator_mono hAY hBY).trans (commutator_le_self Y))
    (commutator_eq_bot_iff_le_centralizer.mp htriple)).trans hself
  have hBA := normalizes_actor_of_commutator_le hA hQ hQA hBQ hcQ
  have hAB := normalizes_actor_of_commutator_le hB hQ hQB hAQ
    (by rwa [commutator_comm])
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply eq_bot_iff.mpr
  exact (le_inf
    (hUB ▸ le_inf hcQ (le_normalizer_iff_commutator_le_right.mp hAB))
    (hWA ▸ le_inf hcQ (le_normalizer_iff_commutator_le_left.mp hBA))).trans hd.le_bot

/-- Commuting factors with a centerless first factor intersect trivially. -/
theorem actors_disjoint {A B : Subgroup G}
    (hc : A ≤ centralizer (B : Set G)) (hz : center A = ⊥) : Disjoint A B := by
  apply Subgroup.disjoint_def.mpr
  intro x hxA hxB
  have hx : (⟨x, hxA⟩ : A) ∈ center A := by
    rw [mem_center_iff]
    intro a
    exact Subtype.ext (hc a.property x hxB).symm
  rw [hz] at hx
  exact congrArg Subtype.val (mem_bot.mp hx)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.ResidualProduct

