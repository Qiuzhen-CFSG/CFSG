module
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.CentralizerReduction
public import Theory.GroupTheory.GeneralizedFitting.ComponentRankNormality
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PResidual.Quotient

/-!
# Cubic subgroups at an A₆ component

An A₆ component in three-rank at most two is normal: two distinct
conjugates would contribute four to that rank. Its centralizer has order
prime to three. A two-perfect subgroup of order dividing twelve acts
through inner automorphisms, so its image modulo the component is both
a two-group and a two-perfect group, and hence trivial.

Source: the component absorption in Aschbacher–Smith 2.4.32, p.547.
-/

public section
open Subgroup Theory.GroupTheory
namespace AlternatingSix.ShadowLocal

private theorem image_mem_of_two_group_quotient
    {L A : Type*} [Group L] [Group A] (hL : IsPPerfect 2 L)
    (f : L →* A) (N : Subgroup A) [N.Normal] (hN : IsPGroup 2 (A ⧸ N))
    (l : L) : f l ∈ N := by
  have hh := pResidual_le_ker_of_isPGroup 2 ((QuotientGroup.mk' N).comp f) hN
  have hp := (pResidual_eq_top_iff 2 L).mpr hL
  exact (QuotientGroup.eq_one_iff (f l)).mp (hh (hp.symm ▸ mem_top l))
variable {H : Type*} [Group H] [Finite H]

/-- The ambient three-rank prevents a second conjugate A₆ component. -/
theorem component_normal_of_three_rank (K : Subgroup H)
    (hK : IsComponent H K) (e : K ≃* A6) (hr : primeRank 3 H ≤ 2) : K.Normal := by
  have hz : center K = ⊥ := by
    apply eq_bot_iff.mpr
    intro k hk
    have he := (centerCongr e ⟨k,hk⟩).property
    change e k ∈ center A6 at he
    rw [alternatingGroup.center_eq_bot (by simp),mem_bot] at he
    exact e.map_eq_one_iff.mp he
  obtain ⟨E,hE,hcard⟩ := alternatingGroup.exists_elementaryAbelian_nine_of_equiv e
  let := hE
  exact hK.normal_of_centerless_primeRank hz
    (IsElementaryAbelian.primeRank_ge_of_card E hcard) hr

/-- Every two-perfect subgroup of order dividing twelve lies in the A₆ component. -/
theorem cubic_twoPerfect_le_component (K : Subgroup H)
    (hK : IsComponent H K) (e : K ≃* A6) (hr : primeRank 3 H ≤ 2)
    (L : Subgroup H) (hp : IsPPerfect 2 L) (hc : Nat.card L ∣ 12) : L ≤ K := by
  let : K.Normal := component_normal_of_three_rank K hK e hr
  let a := conjugationAction K e
  have ho : IsPGroup 2 (AutA6 ⧸ AlternatingSix.ShadowLocal.inner) :=
    IsPGroup.of_card (n:=2) (by rw [←index_eq_card,inner_index]; decide)
  have hLC : L ≤ K ⊔ centralizer (K : Set H) := by
    rw [←conjugationAction_preimage_inner K e]
    intro l hl
    change a l ∈ AlternatingSix.ShadowLocal.inner
    exact image_mem_of_two_group_quotient hp (a.comp L.subtype) _ ho ⟨l,hl⟩
  let q := QuotientGroup.mk' K
  have hmap : L.map q ≤ (centralizer (K : Set H)).map q := by
    have hh := map_mono (f:=q) hLC
    simpa only [q,Subgroup.map_sup,QuotientGroup.map_mk'_self,bot_sup_eq] using hh
  have hn : ¬3 ∣ Nat.card (L.map q) := by
    intro h
    exact centralizer_three_prime_to K e hr
      (h.trans ((card_dvd_of_le hmap).trans (card_map_dvd _ _)))
  have hd : Nat.card (L.map q) ∣ 12 := (card_map_dvd _ _).trans hc
  have hg : IsPGroup 2 (L.map q) := by
    apply isPGroup_iff_card_dvd_pow.mpr
    refine ⟨2,?_⟩
    have hcop : Nat.Coprime (Nat.card (L.map q)) 3 :=
      (Nat.prime_three.coprime_iff_not_dvd.mpr hn).symm
    exact hcop.dvd_of_dvd_mul_left hd
  have ht := hp.hom_eq_one_of_isPGroup hg (q.subgroupMap L)
  intro l hl
  apply (QuotientGroup.eq_one_iff l).mp
  exact congrArg Subtype.val (DFunLike.congr_fun ht ⟨l,hl⟩)
end AlternatingSix.ShadowLocal
