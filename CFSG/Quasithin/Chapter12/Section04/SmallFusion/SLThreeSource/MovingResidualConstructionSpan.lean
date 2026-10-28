module
public import CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource.MovingResidualConstructionCubic
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.GroupTheory.PResidual.SubnormalCorePreimage
public import Theory.GroupTheory.OddCyclicThreeNormalizer
public import Theory.ElementaryAbelian.CommutingFamily
public import Theory.ElementaryAbelian.PrimeRankCard

/-!
# The elementary nine quotient of the actual moving span

Normality in C_G(E) identifies each conjugate residual's two-core quotient
with its literal quotient image. These normal cubic images commute and
span an elementary three-group. The source local rank bound limits its
order to nine; residual-preimage recovery keeps two moved images distinct,
forcing order nine. The final theorem applies this to the invariant span
constructed from the original L₁ and N_G(R).

Source: Aschbacher–Smith, proof of 12.4.6, printed p.814.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource

private theorem normal_cubic_span {H : Type*} [Group H] [Finite H]
    {ι : Type*} (P : ι → Subgroup H) (hn : ∀ i, (P i).Normal)
    (hp : ∀ i, IsPPerfect 2 (P i))
    (hc : ∀ i, Nat.card (P i ⧸ pCore 2 (P i)) = 3)
    (hr : primeRank 3 H ≤ 2) (i j : ι) (hne : P i ≠ P j) :
    IsElementaryAbelian 3 ((⨆ k, P k : Subgroup H) ⧸ pCore 2 (⨆ k, P k : Subgroup H)) ∧
    Nat.card ((⨆ k, P k : Subgroup H) ⧸ pCore 2 (⨆ k, P k : Subgroup H)) = 9 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let q := QuotientGroup.mk' (pCore 2 H)
  let A (k : ι) := (P k).map q
  have hAc (k : ι) : Nat.card (A k) = 3 :=
    (Nat.card_congr ((hn k).isSubnormal.quotientCoreImageEquiv 2).toEquiv).symm.trans (hc k)
  let : ∀ k, (A k).Normal := fun k => (hn k).map q (QuotientGroup.mk'_surjective _)
  let : ∀ k, IsCyclic (A k) := fun k => isCyclic_of_prime_card (hAc k)
  let : ∀ k, IsElementaryAbelian 3 (A k) := fun k => {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => by
      rw [← hAc k]
      exact pow_card_eq_one' }
  have hcomm (k l : ι) : A k ≤ centralizer (A l : Set (H ⧸ pCore 2 H)) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    apply commutator_eq_bot_of_odd_normalizes_card_three _ _ (hAc k)
    · rw [hAc l]; decide
    · exact le_normalizer_of_normal
  let : IsElementaryAbelian 3 (⨆ k, A k : Subgroup (H ⧸ pCore 2 H)) :=
    IsElementaryAbelian.iSup_of_le_centralizer A hcomm
  have hcard : Nat.card (⨆ k, A k : Subgroup (H ⧸ pCore 2 H)) ≤ 9 := by
    rw [IsElementaryAbelian.card_eq_pow_primeRank (p := 3)]
    change 3 ^ primeRank 3 (⨆ k, A k : Subgroup (H ⧸ pCore 2 H)) ≤ 3 ^ 2
    apply Nat.pow_le_pow_right (by decide : 0 < 3)
    exact (primeRank_subgroup_le 3 _).trans
      ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) _ pCore_isPGroup).trans hr)
  have hneA : A i ≠ A j := by
    intro he
    apply hne
    rw [← residual_core_preimage_eq (P i) (hn i).isSubnormal (hp i),
      ← residual_core_preimage_eq (P j) (hn j).isSubnormal (hp j)]
    exact congrArg (fun B : Subgroup (H ⧸ pCore 2 H) =>
      (pResidual 2 (B.comap q)).map (B.comap q).subtype) he
  have hgt : 3 < Nat.card (⨆ k, A k : Subgroup (H ⧸ pCore 2 H)) := by
    by_contra hle
    have hei : A i = ⨆ k, A k := eq_of_le_of_card_ge (le_iSup A i) (by rw [hAc i]; omega)
    have hej : A j = ⨆ k, A k := eq_of_le_of_card_ge (le_iSup A j) (by rw [hAc j]; omega)
    exact hneA (hei.trans hej.symm)
  have he9 : Nat.card (⨆ k, A k : Subgroup (H ⧸ pCore 2 H)) = 9 := by
    obtain ⟨n, he⟩ := (IsElementaryAbelian.isPGroup 3
      (⨆ k, A k : Subgroup (H ⧸ pCore 2 H))).exists_card_eq
    have hn2 : n ≤ 2 := by
      by_contra hh
      have hbig : 3 ^ 3 ≤ 3 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      rw [← he] at hbig
      omega
    interval_cases n
    · rw [he] at hgt; norm_num at hgt
    · rw [he] at hgt; norm_num at hgt
    · exact he
  let : ∀ k, (P k).Normal := hn
  have hs : (⨆ k, P k : Subgroup H).IsSubnormal := Normal.isSubnormal inferInstance
  let e := (hs.quotientCoreImageEquiv 2).trans (MulEquiv.subgroupCongr (map_iSup q P))
  exact ⟨IsElementaryAbelian.of_injective e.toMonoidHom e.injective,
    (Nat.card_congr e.toEquiv).trans he9⟩

namespace LocalGeometry
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}
  (d : LocalGeometry D)

/-- The actual local centralizer has three-rank at most two. -/
theorem plane_centralizer_threeRank
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (hCM : centralizer (d.E : Set G) ≤ normalizer (L : Set G)) :
    primeRank 3 (centralizer (d.E : Set G)) ≤ 2 := by
  have he : componentOrbit L (T : Subgroup G) = L := by
    apply le_antisymm _ (le_componentOrbit _ _)
    exact iSup_conjugates_le_of_le_normalizer _ _ _ le_rfl (structural G T L h).1
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_earlier
    uniquenessEarlier_knownSimple h.simpleQTKE T h.maximal_faithful.1
  have hm : IsMaximalTwoLocal (normalizer (L : Set G)) := by
    simpa only [he] using hu.normalizer_maximal
  exact (primeRank_mono 3 hCM).trans
    (isQuasithin_iff_twoLocal.mp h.simpleQTKE.quasithin _ hm.1 3 Nat.prime_three (by decide))

/-- Normal cubic images and the actual local rank bound give E9 for the
invariant conjugate span, without an unrestricted-subgroup injection. -/
theorem movingSpan_quotient
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (marked : SLThreeAlternative1222.{u} KnownSimple.IsKnownSimple)
    (hmodel : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hne : fixedSubgroup L V ≠ ⊥)
    (hescape : ¬ normalizer (d.R : Set G) ≤ normalizer (L : Set G))
    (hmoves : ¬ normalizer (d.R : Set G) ≤ normalizer (d.L₁ : Set G)) :
    IsElementaryAbelian 3 (d.movingSpan ⧸ pCore 2 d.movingSpan) ∧
    Nat.card (d.movingSpan ⧸ pCore 2 d.movingSpan) = 9 := by
  classical
  obtain ⟨ext⟩ := marked G T L V h D hmodel hne
  have hFE := d.fixed_le_plane h structural marked hmodel hne hescape
  have hcard := d.lineResidual_quotient_card ext hne hFE
  have hCM := d.plane_centralizer_le_normalizer h structural marked hmodel hne hescape
  obtain ⟨_, _, _, hNE, _⟩ := d.escape_geometry h structural marked hmodel hne hescape
  let C := centralizer (d.E : Set G)
  let N := normalizer (d.R : Set G)
  let Y (g : N) := d.L₁.map (MulAut.conj (g : G)).toMonoidHom
  have hYC (g : N) : Y g ≤ C :=
    (map_mono (f := (MulAut.conj (g : G)).toMonoidHom)
      (d.lineResidual_le.trans inf_le_right)).trans_eq
        (mem_normalizer_iff_map_conj_eq.mp
          (normalizer_le_normalizer_centralizer d.E (hNE g.property)))
  let P (g : N) := (Y g).subgroupOf C
  let e (g : N) : d.L₁ ≃* P g :=
    ((MulAut.conj (g : G)).subgroupMap d.L₁).trans
      (subgroupOfEquivOfLe (hYC g)).symm
  have hn (g : N) : (P g).Normal := d.conjugate_normal_in_centralizer hCM hNE g g.property
  have hp (g : N) : IsPPerfect 2 (P g) :=
    d.lineResidual_twoPerfect.of_surjective (e g).toMonoidHom (e g).surjective
  have hc (g : N) : Nat.card (P g ⧸ pCore 2 (P g)) = 3 :=
    (Nat.card_congr (QuotientGroup.congr _ _ (e g) (pCore_map_iso 2 (e g))).toEquiv).symm.trans hcard
  obtain ⟨g, hg, hgnot⟩ : ∃ g ∈ N, g ∉ normalizer (d.L₁ : Set G) := by
    simpa only [N, SetLike.le_def, not_forall, Classical.not_imp, exists_prop] using hmoves
  have hPne : P (1 : N) ≠ P ⟨g, hg⟩ := by
    intro he
    have hm := congrArg (map C.subtype) he
    rw [map_subgroupOf_eq_of_le (hYC 1), map_subgroupOf_eq_of_le (hYC ⟨g, hg⟩)] at hm
    have hY1 : Y (1 : N) = d.L₁ := by
      change d.L₁.map (MulAut.conj 1).toMonoidHom = d.L₁
      rw [map_one]
      exact map_id _
    exact hgnot (mem_normalizer_iff_map_conj_eq.mpr ((hY1.symm.trans hm).symm))
  obtain ⟨hel, hnine⟩ := normal_cubic_span P hn hp hc
    (d.plane_centralizer_threeRank h structural hCM) 1 ⟨g, hg⟩ hPne
  have hmap : (⨆ g, P g : Subgroup C).map C.subtype = d.movingSpan := by
    rw [Subgroup.map_iSup]
    change (⨆ g, (P g).map C.subtype) = ⨆ g : N, Y g
    congr 1
    funext g
    exact map_subgroupOf_eq_of_le (hYC g)
  let ei : (⨆ g, P g : Subgroup C) ≃* d.movingSpan :=
    ((⨆ g, P g : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  let eq := QuotientGroup.congr _ _ ei (pCore_map_iso 2 ei)
  let := hel
  exact ⟨IsElementaryAbelian.of_injective eq.symm.toMonoidHom eq.symm.injective,
    (Nat.card_congr eq.toEquiv).symm.trans hnine⟩

end LocalGeometry
end CFSG.Quasithin.Chapter12.Section04.SmallFusion.SLThreeSource
