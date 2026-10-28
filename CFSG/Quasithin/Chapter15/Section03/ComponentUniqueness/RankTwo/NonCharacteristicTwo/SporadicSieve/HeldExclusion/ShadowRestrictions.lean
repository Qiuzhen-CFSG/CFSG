module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.ShadowBounds
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Two restrictions imposed by the rank-two Frattini shadow

Suppose YS has the S₃ × S₃ quotient modulo O₂,Φ and S is Sylow in H.
If |H/O₂(H)| = 72, the index of YS is at most two. Its odd index makes
YS = H. Then Φ(H/O₂(H)) has order two, contradicting O₂(H/O₂(H)) = 1.

If Y is normal in H and Y/O₂(Y) has exponent three, the shadow forces
nine to divide |Y|. Quotienting by the two-core preserves that divisor.
The actual image of Y in H/O₂(H) is a normal three-group, so nine divides
|O₃(H/O₂(H))|. Neither statement assumes a Held local catalogue.

These are necessary conditions for the Held inspection in Aschbacher--Smith,
combined manuscript (1 March 2004), 15.3.41--42, printed p.1138.
The denominator O₂,Φ is retained throughout; see the convention on p.491.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion

/-- A Sylow-containing rank-two shadow excludes a two-core quotient of order 72. -/
theorem no_shadow_of_core_index_72 {H : Type*} [Group H] [Finite H] (P : Sylow 2 H) (Y : Subgroup H)
    (hs : RankTwoShadow Y (P : Subgroup H))
    (hc : Nat.card (H ⧸ pCore 2 H) = 72) : False := by
  let U := Y ⊔ (P : Subgroup H)
  let F := twoFrattiniCore U
  have hi : F.index = 36 := by
    change Nat.card (U ⧸ F) = 36
    rw [Nat.card_congr hs.some.toEquiv]
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hcoreF : pCore 2 U ≤ F := by
    intro x hx
    change QuotientGroup.mk' (pCore 2 U) x ∈ frattini (U ⧸ pCore 2 U)
    rw [show QuotientGroup.mk' (pCore 2 U) x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hle := pCore_le_map_of_sylow_le P U (show (P : Subgroup H) ≤ U from le_sup_right)
  have hbound : Nat.card (pCore 2 H) ≤ Nat.card F := by
    calc
      _ ≤ Nat.card ((pCore 2 U).map U.subtype) :=
        Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
      _ = Nat.card (pCore 2 U) := card_map_of_injective U.subtype_injective
      _ ≤ Nat.card F :=
        Nat.card_le_card_of_injective (inclusion hcoreF) (inclusion_injective hcoreF)
  have hcount := F.card_mul_index
  have hcountU := U.card_mul_index
  have hcountH := (pCore 2 H).card_mul_index
  change Nat.card (pCore 2 H) * Nat.card (H ⧸ pCore 2 H) = Nat.card H at hcountH
  rw [hc] at hcountH
  rw [hi] at hcount
  have hidx : U.index ≤ 2 := by
    have hp : 0 < Nat.card (pCore 2 H) := Nat.card_pos
    nlinarith [Nat.mul_le_mul_right U.index hbound]
  have hnidx : ¬ 2 ∣ U.index := fun h => P.not_dvd_index
    (h.trans (index_dvd_of_le (show (P : Subgroup H) ≤ U from le_sup_right)))
  have hip : 0 < U.index := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hUt : U = ⊤ := index_eq_one.mp (by omega)
  let e : U ≃* H := (MulEquiv.subgroupCongr hUt).trans topEquiv
  let a := twoFrattiniQuotientEquiv e.toMonoidHom e.surjective
    (IsPGroup.ker_isPGroup_of_injective e.injective)
  have hiH : (twoFrattiniCore H).index = 36 := by
    change Nat.card (H ⧸ twoFrattiniCore H) = 36
    rw [← Nat.card_congr a.toEquiv]
    exact hi
  have hphi : (frattini (H ⧸ pCore 2 H)).index = 36 := by
    rw [← index_comap_of_surjective (frattini (H ⧸ pCore 2 H)) (QuotientGroup.mk'_surjective (pCore 2 H))]
    exact hiH
  have hcphi : Nat.card (frattini (H ⧸ pCore 2 H)) = 2 := by
    have hh := (frattini (H ⧸ pCore 2 H)).card_mul_index
    rw [hphi, hc] at hh
    omega
  have hp : IsPGroup 2 (frattini (H ⧸ pCore 2 H)) := IsPGroup.of_card (n := 1) (by simpa using hcphi)
  have hfcore : frattini (H ⧸ pCore 2 H) ≤ pCore 2 (H ⧸ pCore 2 H) := le_sSup ⟨inferInstance, hp⟩
  have hpre := (QuotientGroup.mk' (pCore 2 H)).comap_pCore_of_ker_isPGroup
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
  have hbot : pCore 2 (H ⧸ pCore 2 H) = ⊥ := by
    apply (comap_injective (QuotientGroup.mk'_surjective (pCore 2 H)))
    simpa only [MonoidHom.comap_bot, QuotientGroup.ker_mk'] using hpre
  have hfb : frattini (H ⧸ pCore 2 H) = ⊥ := bot_unique (hbot ▸ hfcore)
  simp only [hfb, Nat.card_unique] at hcphi
  omega

private theorem nine_coprime_twoGroup {T : Type*} [Group T] [Finite T]
    (h : IsPGroup 2 T) : Nat.Coprime 9 (Nat.card T) := by
  obtain ⟨n, hn⟩ := h.exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right _ (by decide)

private theorem nine_dvd_coreQuotient {T : Type*} [Group T] [Finite T]
    (h : 9 ∣ Nat.card T) : 9 ∣ Nat.card (T ⧸ pCore 2 T) := by
  rw [(pCore 2 T).card_eq_card_quotient_mul_card_subgroup] at h
  exact (nine_coprime_twoGroup pCore_isPGroup).dvd_of_dvd_mul_right h

/-- Normality and the exponent-three condition force nine into the three-core
of the local two-core quotient. -/
theorem shadow_nine_dvd_threeCore {H : Type*} [Group H] [Finite H]
    (P : Sylow 2 H) (Y : Subgroup H) [Y.Normal]
    (hs : RankTwoShadow Y (P : Subgroup H))
    (hexp : ∀ x : Y ⧸ pCore 2 Y, x ^ 3 = 1) :
    9 ∣ Nat.card (pCore 3 (H ⧸ pCore 2 H)) := by
  let U := Y ⊔ (P : Subgroup H)
  have hYn : (Y.subgroupOf U).Normal := inferInstance
  have ht : Y.subgroupOf U ⊔ (P : Subgroup H).subgroupOf U = ⊤ := by
    rw [← subgroupOf_sup le_sup_left le_sup_right]
    exact subgroupOf_self _
  have hquot : IsPGroup 2 (U ⧸ Y.subgroupOf U) :=
    isPGroup_quotient_of_sup_eq_top _ _ P.isPGroup'.comap_subtype ht
  have h9U : 9 ∣ Nat.card U := by
    have hi : (twoFrattiniCore U).index = 36 := by
      change Nat.card (U ⧸ twoFrattiniCore U) = 36
      rw [Nat.card_congr hs.some.toEquiv]
      simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
    exact (by norm_num : 9 ∣ 36).trans (hi ▸ (twoFrattiniCore U).index_dvd_card)
  rw [(Y.subgroupOf U).card_eq_card_quotient_mul_card_subgroup] at h9U
  have h9Y : 9 ∣ Nat.card Y := by
    have h9 := (nine_coprime_twoGroup hquot).dvd_of_dvd_mul_left h9U
    rwa [Nat.card_congr (subgroupOfEquivOfLe (show Y ≤ U from le_sup_left)).toEquiv] at h9
  let q := QuotientGroup.mk' (pCore 2 H)
  let e := coreQuotientEquivImage 2 Y
  have h9im : 9 ∣ Nat.card (Y.map q) := by
    rw [← Nat.card_congr e.toEquiv]
    exact nine_dvd_coreQuotient h9Y
  have hpY : IsPGroup 3 (Y ⧸ pCore 2 Y) := fun x => ⟨1, by simpa using hexp x⟩
  let hn : (Y.map q).Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hle : Y.map q ≤ pCore 3 (H ⧸ pCore 2 H) :=
    le_sSup ⟨hn, hpY.of_equiv e⟩
  exact h9im.trans (card_dvd_of_le hle)

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.HeldExclusion
