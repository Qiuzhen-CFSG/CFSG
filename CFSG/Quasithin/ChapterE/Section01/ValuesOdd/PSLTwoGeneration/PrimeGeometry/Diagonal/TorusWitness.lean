module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LocalModels
public import GorensteinWalter.PGL2ReflectedToriPairAlignment

/-!
# Dihedral local models for outer four-groups in PGL₂

An outer four-group has one inner and two outer involutions. Align an
outer/inner pair with the reflected torus whose 2-part has order two, then
choose an odd prime divisor of its inner torus. Adjoining the torus
involution and reflector constructs a dihedral subgroup of order `4*r`.
The four-group is Sylow in that subgroup, so the intersection with every
ambient Sylow containing the actor is exactly the required Sylow subgroup.

The prime divisor is retained with the split/nonsplit low-torus alternative
for the subsequent maximal-overgroup exclusion. No escape claim is assumed
or proved in this file.

Source: Aschbacher--Smith, E.1.2 and E.1.14(6), printed pp.210 and 214,
and the reflected-torus construction in Gorenstein--Walter.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal

open Subgroup GorensteinWalter

private theorem reflected_prime_subgroup
    {G : Type*} [Group G] [Finite G]
    (U : Subgroup G) (hU : IsCyclic U) (s t : G)
    (hsU : s ∈ U) (hs : IsInvolution s)
    (htU : t ∉ U) (ht : t ^ 2 = 1)
    (hinv : ∀ x ∈ U, t * x * t⁻¹ = x⁻¹)
    {r : ℕ} (hr : r.Prime) (hro : Odd r) (hrU : r ∣ Nat.card U) :
    ∃ H : Subgroup G, s ∈ H ∧ t ∈ H ∧
      H ≤ U ⊔ zpowers t ∧ Nonempty (H ≃* DihedralGroup (2 * r)) := by
  let : IsCyclic U := hU
  let : Fact r.Prime := ⟨hr⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := U) r hrU
  have huG : orderOf (u : G) = r := by simpa using hu
  have hsu : Commute s (u : G) := by
    exact congrArg Subtype.val (IsCyclic.isMulCommutative.is_comm.comm (⟨s, hsU⟩ : U) u)
  have hsord : orderOf s = 2 := orderOf_eq_prime hs.2 hs.1
  have hρord : orderOf (s * u) = 2 * r := by
    rw [hsu.orderOf_mul_eq_mul_orderOf_of_coprime]
    · rw [hsord, huG]
    · rw [hsord, huG]
      exact hro.coprime_two_left
  have hρpow : (s * (u : G)) ^ r = s := by
    rw [hsu.mul_pow, ← huG, pow_orderOf_eq_one, mul_one, huG]
    obtain ⟨k, hk⟩ := hro
    rw [hk, pow_add, pow_mul, hs.2, one_pow, pow_one, one_mul]
  let H : Subgroup G := zpowers (s * (u : G)) ⊔ zpowers t
  have hρU : s * (u : G) ∈ U := U.mul_mem hsU u.property
  have hρH : s * (u : G) ∈ H :=
    (le_sup_left : zpowers (s * (u : G)) ≤ H) (mem_zpowers _)
  have htH : t ∈ H := (le_sup_right : zpowers t ≤ H) (mem_zpowers _)
  let ρ : H := ⟨s * u, hρH⟩
  let σ : H := ⟨t, htH⟩
  have hgen : (⊤ : Subgroup H) = zpowers ρ ⊔ zpowers σ := by
    apply le_antisymm
    · intro x _
      have hx : (x : G) ∈ (zpowers ρ ⊔ zpowers σ).map H.subtype := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        exact x.property
      obtain ⟨y, hy, hyx⟩ := hx
      exact (Subtype.ext hyx : y = x) ▸ hy
    · exact le_top
  have hσ2 : σ ^ 2 = 1 := Subtype.ext ht
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (hinv _ hρU)
  have hσρ : σ ∉ zpowers ρ := by
    intro h
    apply htU
    obtain ⟨k, hk⟩ := h
    have hkG := congrArg Subtype.val hk
    change (s * (u : G)) ^ k = t at hkG
    rw [← hkG]
    exact U.zpow_mem hρU k
  have he := dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have hord : orderOf ρ = 2 * r := by
    simpa only [ρ, Subgroup.orderOf_mk] using hρord
  rw [hord] at he
  refine ⟨H, ?_, htH, ?_, he⟩
  · exact hρpow ▸ H.pow_mem hρH r
  · exact sup_le_sup (zpowers_le.mpr hρU) le_rfl

/-- A four-group in a group of order four times an odd number is Sylow.
Consequently any ambient two-subgroup containing it has exactly that
intersection with the smaller group. -/
theorem sylow_intersection_of_card_four_mul_odd
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (A H : Subgroup G) (hA : IsKleinFour A)
    (hAT : A ≤ T) (hAH : A ≤ H) {r : ℕ} (hro : Odd r)
    (hH : Nat.card H = 4 * r) :
    ∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup G).subgroupOf H := by
  let V := A.subgroupOf H
  have hVcard : Nat.card V = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv).trans hA.card_four
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by simpa using hVcard)
  have hVind : V.index = r := by
    have hc := V.card_mul_index
    rw [hVcard, hH] at hc
    omega
  let S : Sylow 2 H := hVp.toSylow (by rw [hVind]; exact hro.not_two_dvd_nat)
  have hP : IsPGroup 2 ((T : Subgroup G).subgroupOf H) := by
    let f : (T : Subgroup G).subgroupOf H →* T :=
      { toFun := fun x => ⟨x.val.val, x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    apply T.isPGroup'.of_injective f
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : T => (z : G)) h
  refine ⟨S, (S.is_maximal' hP ?_).symm⟩
  intro x hx
  exact hAT hx

private theorem kleinFour_le_of_pair
    {G : Type*} [Group G] [Finite G]
    (A H : Subgroup G) (hA : IsKleinFour A)
    {s t : G} (hsA : s ∈ A) (htA : t ∈ A)
    (hs1 : s ≠ 1) (ht1 : t ≠ 1) (hst : s ≠ t)
    (hsH : s ∈ H) (htH : t ∈ H) : A ≤ H := by
  classical
  let : IsKleinFour A := hA
  let : Fintype A := Fintype.ofFinite A
  have hall := IsKleinFour.eq_finset_univ
    (x := (⟨s, hsA⟩ : A)) (y := (⟨t, htA⟩ : A))
    (fun h => hs1 (congrArg Subtype.val h))
    (fun h => ht1 (congrArg Subtype.val h))
    (fun h => hst (congrArg Subtype.val h))
  intro x hx
  have hm : (⟨x, hx⟩ : A) ∈ ({⟨s, hsA⟩ * ⟨t, htA⟩, ⟨s, hsA⟩, ⟨t, htA⟩, 1} : Finset A) := by
    rw [hall]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h | h
  · have hx : x = s * t := congrArg Subtype.val h
    rw [hx]
    exact H.mul_mem hsH htH
  · have hx : x = s := congrArg Subtype.val h
    exact hx ▸ hsH
  · have hx : x = t := congrArg Subtype.val h
    exact hx ▸ htH
  · have hx : x = 1 := congrArg Subtype.val h
    exact hx ▸ H.one_mem

/-- An outer four-group meets a normal subgroup of index two in an
involution; together with either outside involution it generates the actor. -/
theorem outer_kleinFour_pair
    {G : Type*} [Group G] [Finite G]
    (J A : Subgroup G) [J.Normal] (hJ : J.index = 2)
    (hA : IsKleinFour A) (hAJ : ¬ A ≤ J) :
    ∃ s t : G, s ∈ A ∧ t ∈ A ∧ IsInvolution s ∧ IsInvolution t ∧
      Commute s t ∧ s ∉ J ∧ t ∈ J := by
  classical
  let : IsKleinFour A := hA
  obtain ⟨s, hsA, hsJ⟩ := SetLike.not_le_iff_exists.mp hAJ
  have hs1 : s ≠ 1 := fun h => hsJ (h ▸ J.one_mem)
  let B := J.subgroupOf A
  have hBi : B.index = 2 := by
    have hd : B.index ∣ 2 := by
      change J.relIndex A ∣ 2
      simpa only [hJ] using J.relIndex_dvd_index_of_normal A
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
    · have hb : B = ⊤ := index_eq_one.mp h
      exact (hsJ (show (⟨s, hsA⟩ : A) ∈ B from hb ▸ mem_top _)).elim
    · exact h
  have hBc : Nat.card B = 2 := by
    have hc := B.card_mul_index
    rw [hBi, hA.card_four] at hc
    omega
  have : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨t, ht1⟩ := exists_ne (1 : B)
  have htG : (t.val.val : G) ≠ 1 := by
    intro h
    exact ht1 (Subtype.ext (Subtype.ext h))
  refine ⟨s, t.val.val, hsA, t.val.property, ⟨hs1, ?_⟩, ⟨htG, ?_⟩, ?_, hsJ,
    t.property⟩
  · rw [pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self (⟨s, hsA⟩ : A))
  · rw [pow_two]
    exact congrArg Subtype.val (IsKleinFour.mul_self t.val)
  · exact congrArg Subtype.val (IsKleinFour.isMulCommutative.is_comm.comm
      (⟨s, hsA⟩ : A) t.val)

/-- Every four-group outside PSL₂ has a dihedral local model. The torus
has 2-part two, so the actor is the full Sylow intersection in this model.
This statement constructs the model, but does not assert escape from an
arbitrary maximal subgroup. -/
theorem outer_kleinFour_dihedral_witness
    (F : Type*) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (T : Sylow 2 (PGL2 F)) (A : Subgroup (PGL2 F)) (hA : IsKleinFour A)
    (hAT : A ≤ T) (hAJ : ¬ A ≤ commutator (PGL2 F)) :
    ∃ H : Subgroup (PGL2 F), A ≤ H ∧
      (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup (PGL2 F)).subgroupOf H) ∧
      ∃ r : ℕ, r.Prime ∧ Odd r ∧ Nonempty (H ≃* DihedralGroup (2 * r)) ∧
        ((r ∣ Nat.card F - 1 ∧ Odd ((Nat.card F - 1) / 2)) ∨
          (r ∣ Nat.card F + 1 ∧ Odd ((Nat.card F + 1) / 2))) := by
  let : Finite (PGL2 F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk
    Matrix.ProjGenLinGroup.mk_surjective
  have hJ : (commutator (PGL2 F)).index = 2 := by
    rw [pgl2_commutator_eq_psl2_range_of_card_gt_three F hF hcard]
    exact pgl2_psl2Range_index_eq_two F hF
  obtain ⟨s, t, hsA, htA, hs, ht, hst, hsJ, htJ⟩ :=
    outer_kleinFour_pair (commutator (PGL2 F)) A hJ hA hAJ
  obtain ⟨P, m, eP, d, a, hsa, hta⟩ :=
    pgl2_reflected_tori_pair_alignment F hF hcard s t hs ht hst hsJ htJ
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd d.R_card_gt_one.ne'
  have hro : Odd r := d.R_card_odd.of_dvd_nat hrd
  have hrU : r ∣ Nat.card d.U := hrd.trans (card_dvd_of_le (by
    rw [d.R_eq]
    exact inf_le_left))
  obtain ⟨H₀, hsH₀, htH₀, _, he₀⟩ := reflected_prime_subgroup d.U d.U_cyclic
    d.s d.t d.s_mem_U d.s_involution d.t_not_mem_U d.t_involution.2
    d.t_inverts_U hr hro hrU
  let H := H₀.map (MulAut.conj a).toMonoidHom
  have hsH : s ∈ H := by
    exact mem_map.mpr ⟨d.s, hsH₀, hsa.symm⟩
  have htH : t ∈ H := by
    exact mem_map.mpr ⟨d.t, htH₀, hta.symm⟩
  have hAH : A ≤ H := kleinFour_le_of_pair A H hA hsA htA hs.1 ht.1
    (fun h => hsJ (h ▸ htJ)) hsH htH
  let eH : H ≃* DihedralGroup (2 * r) :=
    (equivMapOfInjective H₀ (MulAut.conj a).toMonoidHom
      (MulAut.conj a).injective).symm.trans he₀.some
  have hHcard : Nat.card H = 4 * r := by
    rw [Nat.card_congr eH.toEquiv, DihedralGroup.nat_card]
    ring
  exact ⟨H, hAH, sylow_intersection_of_card_four_mul_odd T A H hA hAT hAH hro hHcard,
    r, hr, hro, ⟨eH⟩, d.U_card.elim
      (fun h => Or.inl ⟨h ▸ hrU, h ▸ d.U_half_odd⟩)
      (fun h => Or.inr ⟨h ▸ hrU, h ▸ d.U_half_odd⟩)⟩

/-- Application of the torus calculation to the literal `LocalModel`
predicate consumed by prime-field E-generation. Only maximal escape remains
to be established for this actor. -/
theorem outer_kleinFour_localModel
    (F : Type*) [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F)
    (T : Sylow 2 (PGL2 F)) (A : Subgroup (PGL2 F)) (hA : IsKleinFour A)
    (hAT : A ≤ T) (hAJ : ¬ A ≤ commutator (PGL2 F)) :
    ∃ H : Subgroup (PGL2 F), A ≤ H ∧
      (∃ S : Sylow 2 H, (S : Subgroup H) = (T : Subgroup (PGL2 F)).subgroupOf H) ∧
      LocalModel A H := by
  obtain ⟨H, hAH, hS, r, hr, hro, he, _⟩ :=
    outer_kleinFour_dihedral_witness F hF hcard T A hA hAT hAJ
  exact ⟨H, hAH, hS, Or.inr ⟨r, hr, hro, he⟩⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.Diagonal
