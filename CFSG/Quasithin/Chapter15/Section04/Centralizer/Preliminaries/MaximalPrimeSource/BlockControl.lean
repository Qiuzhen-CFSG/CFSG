module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource.CentralResidual
public import Theory.GroupTheory.PGroup.SubnormalQuotientCore

/-!
# The outside A₃-block contradiction

A two-perfect {2,p}-actor, p>3, centralizes the rank-at-most-two three-core
in H/O₂(H). The literal alternating quotient puts every subnormal A₃-block
inside that core. A.4.2(3) normalizes the block by O₂(H), so residual recovery
lifts normalization of its image. The resulting commutator lies in O₂(L).
Adjoining this two-core to the normal actor and taking O² makes the block
normalize the original actor. No general block-commutation theorem is used.

Source: Aschbacher–Smith, printed p.1157, proof of 15.4.3(1).
-/

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The actual alternating quotient of an A₃-block is a three-group. -/
theorem alternatingThree_quotient_isPGroup {L : Subgroup G}
    (hL : ChapterC.IsAlternatingBlock L 3) : IsPGroup 3 (L ⧸ pCore 2 L) := by
  obtain ⟨e⟩ := hL.2.2.quotient_iso
  apply IsPGroup.of_card (n := 1)
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  norm_num

/-- Relative subnormality places the actual block image in O₃(H/O₂(H)). -/
theorem alternatingThree_image_le_core {H L : Subgroup G} (hLH : L ≤ H)
    (hb : ChapterC.IsBlock (L.subgroupOf H)) (ha : ChapterC.IsAlternatingBlock L 3) :
    quotientImage H L ≤ pCore 3 (H ⧸ pCore 2 H) := by
  let e := subgroupOfEquivOfLe hLH
  let eQ := QuotientGroup.congr (pCore 2 (L.subgroupOf H)) (pCore 2 L) e (pCore_map_iso 2 e)
  exact subnormal_map_quotient_core_le_pCore 3 2 (L.subgroupOf H) hb.subnormal
    ((alternatingThree_quotient_isPGroup ha).of_equiv eQ.symm)

/-- The genuine rank bound and the q-group representation kernel kill the
actor on the three-core. This uses p>3, not a later bound p=5. -/
theorem actor_centralizes_quotient_threeCore {p : ℕ} (hp : p.Prime) (ho : Odd p) (hlt : 3 < p)
    {A H : Subgroup G} (hAH : A ≤ H) (hAp : IsPPerfect 2 A)
    (hs : ∀ q : ℕ, q.Prime → q ∣ Nat.card A → q = 2 ∨ q = p)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) :
    quotientImage H A ≤ centralizer (pCore 3 (H ⧸ pCore 2 H) : Set _) := by
  let Q := H ⧸ pCore 2 H
  let P := pCore 3 Q
  let f := (QuotientGroup.mk' (pCore 2 H)).comp (inclusion hAH)
  let a : A →* MulAut P := MulAut.conjNormal.comp f
  have hr : primeRank 3 P ≤ 2 := (primeRank_subgroup_le 3 P).trans
    ((primeRank_quotient_le_of_isTwoGroup 3 (by decide) (pCore 2 H) pCore_isPGroup).trans
      (hH.stronglyQuasithin 3 Nat.prime_three (by decide)))
  have ha : a = 1 := small_rank_action_trivial hp ho (by decide) hlt hAp hs pCore_isPGroup hr a
  rintro _ ⟨x, hx, rfl⟩
  apply mem_centralizer_iff.mpr
  intro v hv
  have he := congrArg (fun b : MulAut P => (b ⟨v, hv⟩ : Q))
    (DFunLike.congr_fun ha (⟨x.val, hx⟩ : A))
  change QuotientGroup.mk' (pCore 2 H) x * v * (QuotientGroup.mk' (pCore 2 H) x)⁻¹ = v at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

omit [Finite G] in
/-- Centralizing the image of a two-perfect subnormal subgroup lifts to
normalization and a commutator bound in its own two-core. -/
theorem commutator_le_core_of_central_quotient_image {H L A : Subgroup G}
    (hLH : L ≤ H) (hAH : A ≤ H) (hsub : (L.subgroupOf H).IsSubnormal)
    (hp : IsPPerfect 2 L)
    (hc : quotientImage H A ≤ centralizer (quotientImage H L : Set _)) :
    ⁅L, A⁆ ≤ L.pCoreIn 2 := by
  have hsignal : ChapterA.Section04.IsTwoSignalizer L H (H.pCoreIn 2) :=
    (ChapterA.Section04.isTwoSignalizer_iff _ _ _).mpr
      ⟨pCoreIn_le 2 H, isPGroup_pCoreIn 2 H,
        hLH.trans (H.le_normalizer.trans
          (normalizer_le_normalizer_characteristic_image H (pCore 2 H)))⟩
  have hcoreNL := ChapterA.Section04.signalizer_le_normalizer L H (H.pCoreIn 2)
    hLH hsub hp hsignal
  have hk : (QuotientGroup.mk' (pCore 2 H)).ker ≤ normalizer (L.subgroupOf H : Set H) := by
    rw [QuotientGroup.ker_mk', ← subgroupOf_normalizer_eq hLH]
    intro x hx
    exact hcoreNL (mem_map.mpr ⟨x, hx, rfl⟩)
  let e := subgroupOfEquivOfLe hLH
  have hperfect : IsPPerfect 2 (L.subgroupOf H) := hp.of_surjective e.symm.toMonoidHom e.symm.surjective
  have hker : IsPGroup 2 (QuotientGroup.mk' (pCore 2 H)).ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hlift := comap_normalizer_map_of_pPerfect (QuotientGroup.mk' (pCore 2 H))
    (L.subgroupOf H) hperfect hker hk
  have hAN : A ≤ normalizer (L : Set G) := by
    intro a ha
    have hn : QuotientGroup.mk' (pCore 2 H) (⟨a, hAH ha⟩ : H) ∈
        normalizer (quotientImage H L : Set _) :=
      Subgroup.centralizer_le_normalizer _ (hc (mem_map.mpr ⟨_, ha, rfl⟩))
    change (⟨a, hAH ha⟩ : H) ∈ (normalizer (quotientImage H L : Set _)).comap
      (QuotientGroup.mk' (pCore 2 H)) at hn
    change (normalizer (quotientImage H L : Set _)).comap (QuotientGroup.mk' (pCore 2 H)) = _ at hlift
    rw [hlift, ← subgroupOf_normalizer_eq hLH] at hn
    exact hn
  have hcommL : ⁅L, A⁆ ≤ L := le_normalizer_iff_commutator_le_left.mp hAN
  have hcommH : ⁅L, A⁆ ≤ H.pCoreIn 2 := by
    have hz : (⁅L.subgroupOf H, A.subgroupOf H⁆).map
        (QuotientGroup.mk' (pCore 2 H)) = ⊥ := by
      rw [map_commutator]
      exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hc)
    have hi : ⁅L.subgroupOf H, A.subgroupOf H⁆ ≤ pCore 2 H := by
      simpa only [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] using hz
    have hm := map_mono (f := H.subtype) hi
    simpa only [pCoreIn, map_commutator, map_subgroupOf_eq_of_le hLH, map_subgroupOf_eq_of_le hAH] using hm
  have hn : ((H.pCoreIn 2).subgroupOf L).Normal := by
    have hnormal : ((H.pCoreIn 2).subgroupOf H).Normal := by
      rw [pCoreIn, subgroupOf, comap_map_eq_self_of_injective H.subtype_injective]
      infer_instance
    have he : (H.pCoreIn 2).subgroupOf L = ((H.pCoreIn 2).subgroupOf H).comap (inclusion hLH) := rfl
    rw [he]
    exact hnormal.comap _
  have hcore : (H.pCoreIn 2).subgroupOf L ≤ pCore 2 L :=
    le_sSup ⟨hn, (isPGroup_pCoreIn 2 H).comap_subtype⟩
  intro x hx
  exact ⟨⟨x, hcommL hx⟩, hcore (hcommH hx), rfl⟩

omit [Finite G] in
/-- The residual identity O²(A O₂(L))=A makes L normalize A. -/
theorem block_normalizes_actor {L A : Subgroup G} (hA : IsPPerfect 2 A)
    (hcoreA : L.pCoreIn 2 ≤ normalizer (A : Set G))
    (hcomm : ⁅L, A⁆ ≤ L.pCoreIn 2) : L ≤ normalizer (A : Set G) := by
  let R := L.pCoreIn 2
  let B := A ⊔ R
  have hn : (A.subgroupOf B).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le A.le_normalizer hcoreA)
  let _ := hn
  have hpA : IsPPerfect 2 (A.subgroupOf B) := hA.of_surjective
    (subgroupOfEquivOfLe (show A ≤ B from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show A ≤ B from le_sup_left)).symm.surjective
  have he : (pResidual 2 B).map B.subtype = A := by
    rw [pResidual_eq_of_isPPerfect_sup (A.subgroupOf B) (R.subgroupOf B) hpA
      (isPGroup_pCoreIn 2 L).comap_subtype (by
        rw [← subgroupOf_sup (show A ≤ B from le_sup_left) (show R ≤ B from le_sup_right)]
        exact subgroupOf_self B), map_subgroupOf_eq_of_le (show A ≤ B from le_sup_left)]
  have hLR : L ≤ normalizer (R : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hLN : L ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    intro l hl x hx
    have hB : B ≤ B.comap (MulAut.conj l).toMonoidHom := by
      apply sup_le
      · intro a ha
        change l * a * l⁻¹ ∈ B
        have hc : ⁅l, a⁆ ∈ R := hcomm (commutator_mem_commutator hl ha)
        have hm := B.mul_mem (show ⁅l, a⁆ ∈ B from mem_sup_right hc)
          (show a ∈ B from mem_sup_left ha)
        simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hm
      · intro r hr
        exact mem_sup_right (le_normalizer_iff.mp hLR l hl r hr)
    exact hB hx
  have hh := hLN.trans (normalizer_le_normalizer_characteristic_image B (pResidual 2 B))
  rwa [he] at hh

/-- Every actual A₃-block lies in M once M is the full normalizer of the
central residual. This is the contradiction to the C.2.6 outside branch. -/
theorem alternatingThree_block_le (T : Sylow 2 G) {p : ℕ}
    (hp : p.Prime) (ho : Odd p) (hlt : 3 < p)
    {M H A L : Subgroup G} (hTM : (T : Subgroup G) ≤ M) (hTH : (T : Subgroup G) ≤ H)
    (hAH : A ≤ H) (hAp : IsPPerfect 2 A)
    (hAs : ∀ q : ℕ, q.Prime → q ∣ Nat.card A → q = 2 ∨ q = p)
    (hAN : M ≤ normalizer (A : Set G)) (hNA : normalizer (A : Set G) = M)
    (hH : IsSQTK KnownSimple.IsKnownSimple H) (hLH : L ≤ H)
    (hb : ChapterC.IsBlock (L.subgroupOf H)) (ha : ChapterC.IsAlternatingBlock L 3) : L ≤ M := by
  have hc := (actor_centralizes_quotient_threeCore hp ho hlt hAH hAp hAs hH).trans
    (centralizer_le (alternatingThree_image_le_core hLH hb ha))
  have hcomm := commutator_le_core_of_central_quotient_image hLH hAH hb.subnormal ha.2.1.twoPerfect hc
  have hcore : L.pCoreIn 2 ≤ H.pCoreIn 2 :=
    pCoreAmbient_mono_of_isSubnormalIn L H 2 hLH hb.subnormal
  have hcoreT : H.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  exact (block_normalizes_actor hAp (hcore.trans (hcoreT.trans (hTM.trans hAN))) hcomm).trans_eq hNA

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeSource
