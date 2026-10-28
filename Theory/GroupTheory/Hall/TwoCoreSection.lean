module

public import Theory.GroupTheory.Hall.Conjugacy
public import Theory.GroupTheory.Hall.OddNormalProducts
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.PGroupCore

/-!
# Odd Hall control from a normal abelian section

Let N be normal in a finite group G, with G = NS for a Sylow two-subgroup
S and [N,N] ≤ O₂(G). Then G is solvable. Every odd Hall subgroup Y lies
in N and meets O₂(G) trivially, so it is abelian.

The images of Y and every conjugate commute modulo O₂(G). Their Hall
property forces those images to coincide. Hall conjugacy inside O₂(G)Y
therefore supplies a conjugator in O₂(G), giving
S = O₂(G) N_S(Y) for the supplied S.

This is the Frattini argument in Aschbacher--Smith, combined manuscript
(1 March 2004), 4.4.13(2), pp.623--624. It only needs the explicit finite
group hypotheses above; no classification or marked-model input is used.
-/

public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace Subgroup.OddHall
variable {G : Type*} [Group G] [Finite G]

private theorem solvable_of_section (S : Sylow 2 G) (N : Subgroup G) [N.Normal]
    (hgen : N ⊔ S = ⊤) (hd : ⁅N, N⁆ ≤ pCore 2 G) : Group.IsSolvable G := by
  let Q := (pCore 2 G).subgroupOf N
  let : Group.IsNilpotent Q := (pCore_isPGroup.comap_subtype : IsPGroup 2 Q).isNilpotent
  have hd' : _root_.commutator N ≤ Q := by
    apply map_le_iff_le_comap.mp
    rwa [map_subtype_commutator]
  let : IsMulCommutative (N ⧸ Q) := Normal.quotient_commutative_iff_commutator_le.mpr hd'
  let : Group.IsSolvable N := (Group.isSolvable_iff_subgroup_quotient Q).mpr
    ⟨inferInstance, inferInstance⟩
  let : Group.IsNilpotent (G ⧸ N) :=
    (isPGroup_quotient_of_sup_eq_top N S S.isPGroup' hgen).isNilpotent
  exact (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, inferInstance⟩

omit [Finite G] in
private theorem hall_map {H : Type*} [Group H] [Finite H]
    {Y : Subgroup G} (hY : IsHallSubgroup oddPrimes Y)
    (f : G →* H) (hf : Function.Surjective f) : IsHallSubgroup oddPrimes (Y.map f) := by
  refine ⟨fun p hp => hY.p_in_pi_of_p_dvd_card p (hp.trans (Y.card_map_dvd f)), ?_⟩
  intro p hp
  exact hY.p_in_pi_of_p_dvd_index p (hp.trans (index_map_dvd (H := Y) hf))

private theorem hall_le_section (S : Sylow 2 G) (N : Subgroup G) [N.Normal]
    (hgen : N ⊔ S = ⊤) {Y : Subgroup G} (hY : IsHallSubgroup oddPrimes Y) : Y ≤ N := by
  let q := QuotientGroup.mk' N
  have hp : IsPGroup 2 (Y.map q) :=
    (isPGroup_quotient_of_sup_eq_top N S S.isPGroup' hgen).to_subgroup _
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hnot : ¬ 2 ∣ Nat.card (Y.map q) := fun h =>
    hY.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ (h.trans (Y.card_map_dvd q)) rfl
  have hn0 : n = 0 := by
    by_contra he
    exact hnot (hn ▸ dvd_pow_self 2 he)
  have hz : Y.map q = ⊥ := (Y.map q).eq_bot_of_card_eq (by simpa [hn0] using hn)
  simpa only [Subgroup.map_eq_bot_iff, q, QuotientGroup.ker_mk'] using hz

private theorem hall_disjoint_core {Y : Subgroup G} (hY : IsHallSubgroup oddPrimes Y) :
    Disjoint Y (pCore 2 G) := by
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
  apply disjoint_of_coprime_natCard
  rw [hn]
  exact Nat.prime_two.coprime_pow_of_not_dvd
    (fun h => hY.p_in_pi_of_p_dvd_card ⟨2, Nat.prime_two⟩ h rfl)

private theorem hall_abelian_of_section (N : Subgroup G) {Y : Subgroup G}
    (hYN : Y ≤ N) (hY : IsHallSubgroup oddPrimes Y)
    (hd : ⁅N, N⁆ ≤ pCore 2 G) : IsMulCommutative Y := by
  have hz : ⁅Y, Y⁆ = ⊥ := le_bot_iff.mp
    ((le_inf Y.commutator_le_self ((commutator_mono hYN hYN).trans hd)).trans
      (hall_disjoint_core hY).le_bot)
  apply IsMulCommutative.of_setLike_mul_comm
  intro a ha b hb
  exact commutatorElement_eq_one_iff_mul_comm.mp
    (mem_bot.mp (hz ▸ commutator_mem_commutator ha hb))

omit [Finite G] in
private theorem map_conj_mul (Y : Subgroup G) (a b : G) :
    Y.map (MulAut.conj (a * b)).toMonoidHom =
      (Y.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    mul_inv_rev, mul_assoc]

private theorem hall_frattini_of_section (S : Sylow 2 G) (N : Subgroup G) [N.Normal]
    {Y : Subgroup G} (hY : IsHallSubgroup oddPrimes Y) (hYN : Y ≤ N)
    (hd : ⁅N, N⁆ ≤ pCore 2 G) (hsolv : Group.IsSolvable G) :
    (S : Set G) = (pCore 2 G : Set G) *
      ((S : Subgroup G) ⊓ normalizer (Y : Set G) : Set G) := by
  let := hsolv
  let Q := pCore 2 G
  let q := QuotientGroup.mk' Q
  have hQS : Q ≤ S := pCore_isPGroup.le_sylow_of_normal S
  have hYq := hall_map hY q (QuotientGroup.mk'_surjective Q)
  have hNcomm : ⁅N.map q, N.map q⁆ = ⊥ := by
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hd
  apply Set.Subset.antisymm
  · intro s hs
    let V := Y.map (MulAut.conj s).toMonoidHom
    have hV : IsHallSubgroup oddPrimes V := hY.map_conj s
    have hVN : V ≤ N := by
      rintro x ⟨y, hy, rfl⟩
      exact (inferInstance : N.Normal).conj_mem y (hYN hy) s
    have hVY : V.map q ≤ Y.map q := by
      apply hYq.le_of_le_normalizer (hall_map hV q (QuotientGroup.mk'_surjective Q))
      apply le_trans _ (centralizer_le_normalizer (Y.map q : Set (G ⧸ Q)))
      apply commutator_eq_bot_iff_le_centralizer.mp
      exact le_bot_iff.mp ((commutator_mono (map_mono hVN) (map_mono hYN)).trans hNcomm.le)
    let H := Q ⊔ Y
    have hVH : V ≤ H := by
      have hh := map_le_iff_le_comap.mp hVY
      simpa only [comap_map_eq, q, QuotientGroup.ker_mk', sup_comm, H] using hh
    have hYH : Y ≤ H := le_sup_right
    obtain ⟨n, hn⟩ := exists_conj_eq_of_isHallSubgroup_of_solvable
      (inferInstance : Group.IsSolvable H) (hY.subgroupOf hYH) (hV.subgroupOf hVH)
    have he : V = Y.map (MulAut.conj (n : G)).toMonoidHom := by
      have hh := congrArg (Subgroup.map H.subtype) hn
      rwa [map_subgroupOf_eq_of_le hVH, map_subgroupOf_map_conj_eq hYH] at hh
    obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_normal_left.mp n.property
    have he' : V = Y.map (MulAut.conj a).toMonoidHom := by
      rw [← hab] at he
      exact he.trans (map_conj_mul_right_eq_of_mem_normalizer a ⟨b, Y.le_normalizer hb⟩)
    have hnY : a⁻¹ * s ∈ normalizer (Y : Set G) := by
      apply mem_normalizer_iff_map_conj_eq.mpr
      change Y.map (MulAut.conj (a⁻¹ * s)).toMonoidHom = Y
      change Y.map (MulAut.conj s).toMonoidHom = Y.map (MulAut.conj a).toMonoidHom at he'
      rw [map_conj_mul, he', ← map_conj_mul, inv_mul_cancel]
      have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
        ext x
        simp
      rw [hid, map_id]
    exact ⟨a, ha, a⁻¹ * s, ⟨S.mul_mem (S.inv_mem (hQS ha)) hs, hnY⟩, by simp⟩
  · rintro x ⟨a, ha, b, hb, rfl⟩
    exact S.mul_mem (hQS ha) hb.1

/-- A normal subgroup with abelian image modulo the two-core and a Sylow
supplement gives solvability, abelian odd Hall subgroups, and the exact
Sylow factorization by the two-core and the Hall normalizer. -/
theorem control_of_normal_abelian_section (S : Sylow 2 G) (N : Subgroup G) [N.Normal]
    (hgen : N ⊔ S = ⊤) (hd : ⁅N, N⁆ ≤ pCore 2 G) :
    Group.IsSolvable G ∧ ∀ Y : Subgroup G, IsHallSubgroup oddPrimes Y →
      IsMulCommutative Y ∧ (S : Set G) = (pCore 2 G : Set G) *
        ((S : Subgroup G) ⊓ normalizer (Y : Set G) : Set G) := by
  have hs := solvable_of_section S N hgen hd
  refine ⟨hs, fun Y hY => ?_⟩
  have hYN := hall_le_section S N hgen hY
  exact ⟨hall_abelian_of_section N hYN hY hd, hall_frattini_of_section S N hY hYN hd hs⟩

end Subgroup.OddHall
