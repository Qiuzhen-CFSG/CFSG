module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.TwoCoreSplitting.NativeSource.LocalConfiguration
public import BenderSuzuki.SE.Permutation

/-!
# Section 17 fixed points and the literal local normalizer

Lemma 16.7 applies to odd prime-power subgroups. To apply it to an arbitrary
odd subgroup Y normalized nontrivially by t, take a nonidentity displacement
inverted by t and then an odd-prime-order element in its cyclic subgroup.
Every point fixed by Y is fixed by this prime subgroup. Thus three fixed
points would force t to centralize an element that it nontrivially inverts.
The normalizer consequently preserves exactly the original two cosets.
Intersecting this setwise pair stabilizer with `C_G(tu)°` yields the actual
bound `N_{C_G(tu)°}(Y) ≤ D₀⟨t⟩`.

Source: GLS, Volume 4, Chapter 2, Lemmas 16.7 and 17.2(e,f).
-/

noncomputable section
namespace BenderSuzuki.ZD.Section17.NativeSource
open Subgroup PFAppendixIII Theory.GroupTheory PFchapter1section1
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Exactly the earlier universal source Lemma 16.7, with the distinguished
circle and the original action on cosets. -/
@[expose] public def SectionSixteenNormalizer (Z : Set G) (M : Subgroup G) : Prop :=
  ∀ (p : ℕ), p.Prime → Odd p → ∀ Y : Subgroup G, IsPGroup p Y →
    3 ≤ Nat.card (theorem4bFixedPoints M Y) →
      localCircleIn Z (normalizer (Y : Set G)) ≤ centralizer (Y : Set G)

omit [Finite G] in
private theorem exists_inverted_of_noncentral {t : G} (ht : PFAppendixIII.IsInvolution t)
    (Y : Subgroup G) (hn : t ∈ normalizer (Y : Set G))
    (hc : ¬ Y ≤ centralizer ({t} : Set G)) :
    ∃ x ∈ Y, x ≠ 1 ∧ t * x * t⁻¹ = x⁻¹ := by
  obtain ⟨y, hy, hyt⟩ := SetLike.not_le_iff_exists.mp hc
  let x := y⁻¹ * (t * y * t⁻¹)
  have hx : x ∈ Y := Y.mul_mem (Y.inv_mem hy) ((mem_normalizer_iff.mp hn y).mp hy)
  have hxne : x ≠ 1 := by
    intro he
    apply hyt
    apply mem_centralizer_singleton_iff.mpr
    have hh : y = t * y * t⁻¹ := eq_of_inv_mul_eq_one he
    calc
      y * t = (t * y * t⁻¹) * t := congrArg (fun a : G => a * t) hh
      _ = t * y := by group
  refine ⟨x, hx, hxne, ?_⟩
  have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
  dsimp only [x]
  simp only [ht.inv_eq_self, mul_inv_rev, inv_inv]
  simp [mul_assoc, htt]

/-- The application of Lemma 16.7 to an arbitrary odd subgroup. Its
prime-subgroup restriction is discharged by actual inverted-element extraction. -/
public theorem odd_noncentral_fixed_card_le_two
    (h : IsProductDisconnected Z M) (h16 : SectionSixteenNormalizer Z M)
    {t : G} (ht : t ∈ Z) (Y : Subgroup G) (hodd : Odd (Nat.card Y))
    (hn : t ∈ normalizer (Y : Set G)) (hc : ¬ Y ≤ centralizer ({t} : Set G)) :
    Nat.card (theorem4bFixedPoints M Y) ≤ 2 := by
  by_contra hlarge
  have hthree : 3 ≤ Nat.card (theorem4bFixedPoints M Y) := by omega
  obtain ⟨x, hxY, hxne, hi⟩ := exists_inverted_of_noncentral (h.involutions t ht) Y hn hc
  obtain ⟨p, y, hp, hyorder, hyY, hyne, hiy⟩ :=
    exists_prime_order_inverted_of_mem_odd_subgroup hxY hxne hi hodd
  let P := zpowers y
  have hPY : P ≤ Y := zpowers_le.mpr hyY
  have hpodd : Odd p := by
    rw [← hyorder]
    exact hodd.of_dvd_nat (by simpa only [Subgroup.orderOf_mk] using orderOf_dvd_natCard (⟨y, hyY⟩ : Y))
  have hP : IsPGroup p P := IsPGroup.of_card (n := 1) (by simp [P, Nat.card_zpowers, hyorder])
  have hPthree : 3 ≤ Nat.card (theorem4bFixedPoints M P) := by
    let f : theorem4bFixedPoints M Y → theorem4bFixedPoints M P :=
      fun a => ⟨a, fun q hq => a.property q (hPY hq)⟩
    exact hthree.trans (Nat.card_le_card_of_injective f
      (fun a b he => Subtype.ext (congrArg (fun c : theorem4bFixedPoints M P => (c : G ⧸ M)) he)))
  have htN : t ∈ normalizer (P : Set G) :=
    theorem4b_mem_normalizer_zpowers_of_inverts (h.involutions t ht) hiy
  have htC : t ∈ centralizer (P : Set G) := (h16 p hp hpodd P hP hPthree) (by
    rw [localCircleIn_eq_closure]
    exact subset_closure ⟨ht, htN⟩)
  have hc : y * t = t * y := htC y (mem_zpowers y)
  have heq : y = y⁻¹ := by
    calc
      y = t * y * t⁻¹ := by rw [← hc]; group
      _ = y⁻¹ := hiy
  have hsquare : y ^ 2 = 1 := by
    rw [pow_two]
    nth_rw 1 [heq]
    exact inv_mul_cancel _
  have hpd : p ∣ 2 := hyorder ▸ orderOf_dvd_of_pow_eq_one hsquare
  have hptwo : p = 2 := ((Nat.dvd_prime Nat.prime_two).mp hpd).resolve_left hp.ne_one
  have : Odd 2 := hptwo ▸ hpodd
  norm_num at this

omit [Finite G] in
private theorem pair_le_two_stabilizers {t : G} (ht : PFAppendixIII.IsInvolution t) :
    residualPairStabilizer M t ≤
      MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) ⊓
      MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ M) := by
  intro x hx
  constructor
  · rw [baseCoset_stabilizer]
    exact hx.1
  · rw [conjugateCoset_stabilizer, ht.inv_eq_self]
    exact hx.2

/-- Lemma 17.2(f), fixed-set clause, with the literal base and t cosets. -/
public theorem odd_noncentral_fixed_pair
    (h : IsProductDisconnected Z M) (h16 : SectionSixteenNormalizer Z M)
    {t : G} (ht : t ∈ Z) (htM : t ∉ M)
    (Y : Subgroup G) (hYD : Y ≤ residualPairStabilizer M t)
    (hodd : Odd (Nat.card Y)) (hn : t ∈ normalizer (Y : Set G))
    (hc : ¬ Y ≤ centralizer ({t} : Set G)) :
    fixedPointsOfSubgroup G (G ⧸ M) Y =
      {QuotientGroup.mk 1, QuotientGroup.mk t} := by
  have hsmall := odd_noncentral_fixed_card_le_two h h16 ht Y hodd hn hc
  have hfix := hYD.trans (pair_le_two_stabilizers (h.involutions t ht))
  have hsub : ({QuotientGroup.mk 1, QuotientGroup.mk t} : Set (G ⧸ M)) ⊆
      fixedPointsOfSubgroup G (G ⧸ M) Y := by
    intro a ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · intro y hy
      exact MulAction.mem_stabilizer_iff.mp (hfix hy).1
    · rw [Set.mem_singleton_iff.mp ha]
      intro y hy
      exact MulAction.mem_stabilizer_iff.mp (hfix hy).2
  have hne : (QuotientGroup.mk 1 : G ⧸ M) ≠ QuotientGroup.mk t := by
    intro he
    apply htM
    simpa only [inv_one, one_mul] using QuotientGroup.eq.mp he
  apply Eq.symm
  apply Set.eq_of_subset_of_ncard_le hsub
  rw [Set.ncard_pair hne]
  exact hsmall

omit [Finite G] in
/-- Exact pair fixing forces the local normalizer into the original
intersection with the circle, extended by the original involution t. -/
public theorem normalizer_inf_circle_le_twisted_pair_join
    {t : G} (ht : PFAppendixIII.IsInvolution t) (htM : t ∉ M)
    (L Y : Subgroup G) (htL : t ∈ L)
    (hfixed : fixedPointsOfSubgroup G (G ⧸ M) Y =
      {QuotientGroup.mk 1, QuotientGroup.mk t}) :
    normalizer (Y : Set G) ⊓ L ≤ (residualPairStabilizer M t ⊓ L) ⊔ zpowers t := by
  let a : G ⧸ M := QuotientGroup.mk 1
  let b : G ⧸ M := QuotientGroup.mk t
  have hab : a ≠ b := by
    intro he
    apply htM
    simpa only [inv_one, one_mul] using QuotientGroup.eq.mp he
  have ha : a ∈ fixedPointsOfSubgroup G (G ⧸ M) Y := by rw [hfixed]; exact Set.mem_insert _ _
  have hb : b ∈ fixedPointsOfSubgroup G (G ⧸ M) Y := by rw [hfixed]; exact Set.mem_insert_of_mem _ rfl
  have hta : t • a = b := by simp [a, b, MulAction.Quotient.smul_mk, smul_eq_mul]
  have htb : t • b = a := by
    simp only [← hta, smul_smul, show t * t = 1 by simpa [pow_two] using ht.sq_eq_one, one_smul]
  have memD {x : G} (hxa : x • a = a) (hxb : x • b = b) :
      x ∈ residualPairStabilizer M t := by
    constructor
    · have hh : x ∈ MulAction.stabilizer G (QuotientGroup.mk 1 : G ⧸ M) :=
        MulAction.mem_stabilizer_iff.mpr hxa
      rwa [baseCoset_stabilizer] at hh
    · have hh : x ∈ MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ M) :=
        MulAction.mem_stabilizer_iff.mpr hxb
      rwa [conjugateCoset_stabilizer, ht.inv_eq_self] at hh
  intro g hg
  have hga := fixedPoints_smul_of_mem_normalizer hg.1 ha
  have hgb := fixedPoints_smul_of_mem_normalizer hg.1 hb
  rw [hfixed] at hga hgb
  rcases Set.mem_insert_iff.mp hga with hga | hga
  · have hgb' : g • b = b := by
      rcases Set.mem_insert_iff.mp hgb with hgb | hgb
      · exact (hab (smul_left_cancel g (hga.trans hgb.symm))).elim
      · exact Set.mem_singleton_iff.mp hgb
    exact mem_sup_left ⟨memD hga hgb', hg.2⟩
  · have hga' : g • a = b := Set.mem_singleton_iff.mp hga
    have hgb' : g • b = a := by
      rcases Set.mem_insert_iff.mp hgb with hgb | hgb
      · exact hgb
      · exact (hab (smul_left_cancel g (hga'.trans (Set.mem_singleton_iff.mp hgb).symm))).elim
    have hgt : g * t ∈ residualPairStabilizer M t := memD
      (by rw [mul_smul, hta, hgb']) (by rw [mul_smul, htb, hga'])
    have hm : (g * t) * t ∈ (residualPairStabilizer M t ⊓ L) ⊔ zpowers t :=
      mul_mem_sup ⟨hgt, L.mul_mem hg.2 htL⟩ (mem_zpowers t)
    simpa only [mul_assoc, show t * t = 1 by simpa [pow_two] using ht.sq_eq_one, mul_one] using hm

/-- All of Lemma 17.2(e,f), derived for the actual local configuration.
Only the earlier source Lemma 16.7 remains explicit. -/
public theorem localData_fixed_pair_and_normalizer
    (h : IsProductDisconnected Z M) (h16 : SectionSixteenNormalizer Z M)
    (d : TwoCoreLocalData Z M) :
    let L := centralizerClosure Z (d.t * ((d.u : M) : G))
    let D₀ := residualPairStabilizer M d.t ⊓ L
    fixedPointsOfSubgroup G (G ⧸ M) D₀ =
      {QuotientGroup.mk 1, QuotientGroup.mk d.t} ∧
    ∀ Y : Subgroup G, Y ≤ D₀ → ⁅Y, zpowers d.t⁆ ≠ ⊥ → ⁅Y, zpowers d.t⁆ ≤ Y →
      fixedPointsOfSubgroup G (G ⧸ M) Y =
        {QuotientGroup.mk 1, QuotientGroup.mk d.t} ∧
      normalizer (Y : Set G) ⊓ L ≤ D₀ ⊔ zpowers d.t := by
  dsimp only
  constructor
  · exact odd_noncentral_fixed_pair h h16 d.t_mem d.t_not_mem _ inf_le_left
      d.odd_twisted_pair d.normalizes_twisted_pair d.noncentral_twisted_pair
  · intro Y hYD hne hcomm
    have hn : d.t ∈ normalizer (Y : Set G) :=
      le_normalizer_iff_commutator_le_left.mpr hcomm (mem_zpowers d.t)
    have hc : ¬ Y ≤ centralizer ({d.t} : Set G) := by
      intro hh
      apply hne
      apply commutator_eq_bot_iff_le_centralizer.mpr
      simpa only [zpowers_eq_closure, centralizer_closure] using hh
    have hfix := odd_noncentral_fixed_pair h h16 d.t_mem d.t_not_mem Y
      (hYD.trans inf_le_left) (d.odd_twisted_pair.of_dvd_nat (card_dvd_of_le hYD)) hn hc
    exact ⟨hfix, normalizer_inf_circle_le_twisted_pair_join (h.involutions d.t d.t_mem)
      d.t_not_mem _ _ (mem_centralizerClosure d.t_mem
        ((Commute.refl d.t).mul_right d.commutes_t.symm)) hfix⟩

end BenderSuzuki.ZD.Section17.NativeSource
