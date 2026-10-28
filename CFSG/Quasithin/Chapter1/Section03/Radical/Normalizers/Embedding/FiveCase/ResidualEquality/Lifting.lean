module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.FiveCase.ResidualEquality.Orders
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Lifting the equality from odd orders to the actual residuals

The marked image of Y in K/O₂(K) has order 3000. If L_C/O₂(L_C) also
has order 3000, then [L_C:Y] is a power of two. The ambient Sylow
two-subgroup normalizes Y and L_C; its intersection with L_C is Sylow.
Consequently the normalizer of Y inside L_C has both odd index and
power-of-two index, hence equals L_C. Finally L_C is perfect, so its
now-defined two-group quotient by Y is trivial.

This argument compares the original residuals, including their two-cores;
it does not infer equality merely from equality of quotient orders.
Source: Aschbacher–Smith, proof of 1.3.8, printed p.513, combined manuscript
of 1 March 2004.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase.ResidualEquality
universe u
variable {G : Type u} [Group G] [Finite G]
private theorem eq_top_of_sylow_normalizes_of_index_two_power [Group.IsPerfect G]
    (A : Subgroup G) (S : Sylow 2 G) (hS : (S : Subgroup G) ≤ normalizer (A : Set G))
    (hindex : ∃ a, A.index = 2 ^ a) : A = ⊤ := by
  obtain ⟨a, ha⟩ := hindex
  have hd : (normalizer (A : Set G)).index ∣ 2 ^ a := ha ▸ index_dvd_of_le A.le_normalizer
  have hn : ¬ 2 ∣ (normalizer (A : Set G)).index :=
    fun hh => S.not_dvd_index (hh.trans (index_dvd_of_le hS))
  have hone : (normalizer (A : Set G)).index = 1 := by
    obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    rcases b with _ | b
    · simpa using hb
    · exact (hn (hb ▸ dvd_pow_self 2 (Nat.succ_ne_zero b))).elim
  have hnormal : A.Normal := normalizer_eq_top_iff.mp (index_eq_one.mp hone)
  let := hnormal
  have hq : IsPGroup 2 (G ⧸ A) := IsPGroup.of_card (by simpa only [index_eq_card] using ha)
  let := hq.isNilpotent
  have hs : Subsingleton (G ⧸ A) := by
    by_contra hs
    let : Nontrivial (G ⧸ A) := not_subsingleton_iff_nontrivial.mp hs
    exact Group.IsPerfect.not_isSolvable (G ⧸ A) inferInstance
  let := hs
  exact top_unique (fun x _ => (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _))

private theorem eq_of_index_two_power {A D : Subgroup G} (hAD : A ≤ D)
    [Group.IsPerfect D] (T : Sylow 2 G)
    (hTA : (T : Subgroup G) ≤ normalizer (A : Set G))
    (hTD : (T : Subgroup G) ≤ normalizer (D : Set G))
    (hi : ∃ a, A.relIndex D = 2 ^ a) : A = D := by
  let H := D ⊔ (T : Subgroup G)
  let DH := D.subgroupOf H
  let : DH.Normal := normal_subgroupOf_of_le_normalizer (sup_le D.le_normalizer hTD)
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  obtain ⟨U, hU⟩ := S.exists_subgroupOf_eq_of_normal DH
  let e := subgroupOfEquivOfLe (show D ≤ H from le_sup_left)
  let V : Sylow 2 D := U.mapSurjective (f := e.toMonoidHom) e.surjective
  have hV : (V : Subgroup D) ≤ normalizer (A.subgroupOf D : Set D) := by
    rw [← subgroupOf_normalizer_eq hAD]
    rintro x ⟨y, hy, rfl⟩
    rw [hU] at hy
    exact hTA hy
  have he := eq_top_of_sylow_normalizes_of_index_two_power (A.subgroupOf D) V hV hi
  have hm := congrArg (map D.subtype) he
  simpa only [map_subgroupOf_eq_of_le hAD, ← MonoidHom.range_eq_map, range_subtype] using hm

omit [Finite G] in
private theorem index_two_power_of_cards {A D : Subgroup G} (hAD : A ≤ D)
    (ha : ∃ a, Nat.card A = 2 ^ a * 3000)
    (hd : ∃ d, Nat.card D = 2 ^ d * 3000) : ∃ a, A.relIndex D = 2 ^ a := by
  obtain ⟨a, ha⟩ := ha
  obtain ⟨d, hd⟩ := hd
  have hc := (A.subgroupOf D).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hAD).toEquiv, ha, hd] at hc
  have he : A.relIndex D * 2 ^ a = 2 ^ d := by
    apply Nat.eq_of_mul_eq_mul_right (by decide : 0 < 3000)
    change (A.subgroupOf D).index * 2 ^ a * 3000 = 2 ^ d * 3000
    nlinarith [hc]
  obtain ⟨b, _, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show A.relIndex D ∣ 2 ^ d from ⟨_, he.symm⟩)
  exact ⟨b, hb⟩

theorem residual_eq_of_quotient_order {𝒦 : GroupClass.{u}} {p r : ℕ} {L : Subgroup G}
    {T : Sylow 2 G} {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData 𝒦 p r L T C K)
    (P : Sylow p (XiP p L))
    (hmark : MarkedFiveExtension (quotientImage (normalizerResidual L (radicalCore p L T)) K)
      (quotientImage ((P : Subgroup (XiP p L)).map (XiP p L).subtype) K))
    (horder : Nat.card (XiQuotient
      (normalizerResidual L (C.map (radicalCore p L T).subtype))) = 3000) :
    normalizerResidual L (radicalCore p L T) =
      normalizerResidual L (C.map (radicalCore p L T).subtype) := by
  let := h.characteristic
  let D := normalizerResidual L (C.map (radicalCore p L T).subtype)
  let := normalizerResidual_perfect L (C.map (radicalCore p L T).subtype)
  have hle := normalizerResidual_le_of_characteristic L (radicalCore p L T) C
  apply eq_of_index_two_power hle T (t_le_normalizer_Y p h.invariant)
  · exact le_normalizer_normalizerResidual h.invariant
      ((t_le_normalizer_radicalCore p L T).trans
        (normalizer_le_normalizer_characteristic_image _ C))
  · apply index_two_power_of_cards hle
    · obtain ⟨a, ha⟩ := card_eq_power_two_mul_image h.contains_Y
      exact ⟨a, by rwa [marked_five_card hmark] at ha⟩
    · obtain ⟨d, hd⟩ := (pCore_isPGroup (p := 2) (G := D)).exists_card_eq
      have hc := (pCore 2 D).card_mul_index
      rw [hd, index_eq_card, horder] at hc
      exact ⟨d, hc.symm⟩
end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase.ResidualEquality
