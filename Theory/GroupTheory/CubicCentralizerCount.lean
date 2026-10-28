module
public import Theory.GroupTheory.CentralizerGeneratorIndex
public import Theory.GroupTheory.Involution.OddRotation
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.SmallQuotients

/-!
# A chief-factor bound from an involution centralizer

An involution outside the two-core of a finite symmetric-three extension
inverts a cubic element. Two conjugate involution centralizers intersect in
its cubic centralizer, bounding the latter index by the square of the former.
The established cubic chief-count formula then bounds every complete chief
series. A self-centralizing two-core forces the bound to be positive.

Source application: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(6.3), printed p.397. The odd-rotation extraction and chief-series comparison
are reused from their existing proved interfaces.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.CubicCentralizerCount
variable {G : Type*} [Group G] [Finite G]

theorem centralizer_cubic_index_le_square (Q : Subgroup G) [Q.Normal]
    {z x : G} (hz : z ^ 2 = 1) (hx : x ^ 3 = 1)
    (hinv : MulAut.conj z x = x⁻¹) (r : ℕ)
    (hi : (centralizer ({z} : Set G)).relIndex Q ≤ 2 ^ r) :
    (centralizer (zpowers x : Set G)).relIndex Q ≤ 4 ^ r := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hz)
  have hxx : x⁻¹ * x⁻¹ = x := by
    apply inv_injective
    simp only [mul_inv_rev, inv_inv]
    apply eq_inv_of_mul_eq_one_left
    simpa only [pow_succ, pow_zero, one_mul] using hx
  have hprod : z * (MulAut.conj x z) = x := by
    change z * (x * z * x⁻¹) = x
    have hinv' : z * x * z = x⁻¹ := by simpa only [MulAut.conj_apply, hzi] using hinv
    rw [← mul_assoc, ← mul_assoc, hinv', hxx]
  let C := centralizer ({z} : Set G)
  let D := centralizer ({(MulAut.conj x) z} : Set G)
  have hle : C ⊓ D ≤ centralizer (zpowers x : Set G) := by
    intro a ha y hy
    have hza : Commute z a := ha.1 z (Set.mem_singleton z)
    have hzca : Commute ((MulAut.conj x) z) a := ha.2 _ (Set.mem_singleton _)
    have hxa : Commute x a := hprod ▸ hza.mul_left hzca
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (hxa.zpow_left k).eq
  have hmap : Q.map (MulAut.conj x).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (by rw [Subgroup.normalizer_eq_top]; trivial)
  have hD : D.relIndex Q = C.relIndex Q :=
    Subgroup.centralizer_relIndex_equiv Q (MulAut.conj x) z hmap
  calc
    (centralizer (zpowers x : Set G)).relIndex Q ≤ (C ⊓ D).relIndex Q :=
      Subgroup.relIndex_le_of_le_left hle ((C ⊓ D).subgroupOf Q).index_ne_zero_of_finite
    _ ≤ C.relIndex Q * D.relIndex Q := Subgroup.relIndex_inf_le
    _ ≤ (2 ^ r) * (2 ^ r) := by rw [hD]; exact Nat.mul_le_mul hi hi
    _ = 4 ^ r := by rw [← mul_pow]; congr 1

theorem exists_inverted_cubic
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) {z : G}
    (hz : orderOf z = 2) (hn : z ∉ pCore 2 G) :
    ∃ x : G, orderOf x = 3 ∧ MulAut.conj z x = x⁻¹ := by
  have hz' : BenderSuzuki.PFAppendixIII.IsInvolution z := by
    refine ⟨?_, ?_⟩
    · intro he
      simp only [he, orderOf_one] at hz
      omega
    · rw [← hz]
      exact pow_orderOf_eq_one z
  obtain ⟨q, hq, hq2, x, hx, hinv⟩ :=
    BenderSuzuki.involution_outside_twoCore_inverts_odd_prime z hz' hn
  have hd : q ∣ Nat.card G := hx ▸ orderOf_dvd_natCard x
  obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
  rw [SymmetricThreeTwoCore.card_eq e, hn] at hd
  have hq3 : q = 3 := by
    rcases hq.dvd_mul.mp hd with h6 | h2
    · have h6' : q ∣ 2 * 3 := h6
      rcases hq.dvd_mul.mp h6' with h2 | h3
      · exact (hq2 (((Nat.dvd_prime Nat.prime_two).mp h2).resolve_left hq.ne_one)).elim
      · exact ((Nat.dvd_prime Nat.prime_three).mp h3).resolve_left hq.ne_one
    · have h2' : q ∣ 2 := hq.dvd_of_dvd_pow h2
      exact (hq2 (((Nat.dvd_prime Nat.prime_two).mp h2').resolve_left hq.ne_one)).elim
  refine ⟨x, hx.trans hq3, ?_⟩
  simpa only [BenderSuzuki.PFAppendixIII.rightConjugateElem, MulAut.conj_apply,
    hz'.inv_eq_self] using hinv

theorem noncentralTwoCount_le
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3)) {z : G}
    (hz : orderOf z = 2) (hn : z ∉ pCore 2 G) (r : ℕ)
    (hi : (centralizer ({z} : Set G)).relIndex (pCore 2 G) ≤ 2 ^ r)
    (s : NoncentralChiefRefinement.ChiefSeries G) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ r := by
  obtain ⟨x, hx, hinv⟩ := exists_inverted_cubic e hz hn
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hbound := centralizer_cubic_index_le_square (pCore 2 G) hz2 hx3 hinv r hi
  let f : G →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hp : IsPGroup 2 f.ker := hk ▸ pCore_isPGroup
  have hA : Nat.card (zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  rw [NoncentralChiefRefinement.CubicComparison.symmetricThree_count f hf hp _ hA s h0 h1,
    hk, Subgroup.conjugationCubicLength]
  exact (Nat.log_mono_right (b := 4) hbound).trans_eq (Nat.log_pow (by decide) _)

/-- In the characteristic-two branch the margin cannot vanish: an inverted
cubic element would otherwise centralize, and hence lie in, the two-core. -/
theorem bound_positive_of_core_selfCentralizing
    (e : (G ⧸ pCore 2 G) ≃* Equiv.Perm (Fin 3))
    (hself : centralizer (pCore 2 G : Set G) ≤ pCore 2 G) {z : G}
    (hz : orderOf z = 2) (hn : z ∉ pCore 2 G) (r : ℕ)
    (hi : (centralizer ({z} : Set G)).relIndex (pCore 2 G) ≤ 2 ^ r) : 0 < r := by
  by_contra hnpos
  have hr : r = 0 := by omega
  obtain ⟨x, hx, hinv⟩ := exists_inverted_cubic e hz hn
  have hz2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hx3 : x ^ 3 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hb := centralizer_cubic_index_le_square (pCore 2 G) hz2 hx3 hinv r hi
  rw [hr, pow_zero] at hb
  have hne := ((centralizer (zpowers x : Set G)).subgroupOf (pCore 2 G)).index_ne_zero_of_finite
  change (centralizer (zpowers x : Set G)).relIndex (pCore 2 G) ≠ 0 at hne
  have he : (centralizer (zpowers x : Set G)).relIndex (pCore 2 G) = 1 := by omega
  have hle : pCore 2 G ≤ centralizer (zpowers x : Set G) := Subgroup.relIndex_eq_one.mp he
  have hxQ := hself (Subgroup.le_centralizer_iff.mp hle (Subgroup.mem_zpowers x))
  let y : pCore 2 G := ⟨x, hxQ⟩
  have hy : orderOf y = 3 :=
    (orderOf_injective (pCore 2 G).subtype (pCore 2 G).subtype_injective y).symm.trans hx
  have hyne : y ≠ 1 := by
    intro he
    simp only [he, orderOf_one] at hy
    omega
  have hd := (pCore_isPGroup (p := 2) (G := G)).dvd_orderOf hyne
  rw [hy] at hd
  norm_num at hd

end Theory.GroupTheory.CubicCentralizerCount
