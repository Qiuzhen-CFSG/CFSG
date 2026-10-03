module

public import Theory.GroupTheory.PGroup.LargeHallRotationStructure
public import Theory.GroupTheory.CyclicFourCentralizerSylow

/-!
# Inverted order-four rotations in large binary Hall factors

A large noncyclic binary Hall factor in a finite two-group has an order-four
rotation with cyclic centralizer. If an ambient element normalizes the factor
and has elementary abelian centralizer, it inverts this rotation. In a product
of two commuting factors, the rotation's square is central in the full product.

The characteristic cyclic rotation subgroup supplies a characteristic second
omega subgroup of order four. Its normalizer fixes the square of a generator;
conjugation by the specified ambient element must invert the generator, since
fixing it would put an element of order four in an exponent-two centralizer.
The rotation centralizer bound gives cyclicity. The maps through both subgroup
inclusions are retained for applications to central products.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, p.392, Case 1.
-/

open Subgroup
open scoped IsMulCommutative

private theorem omega_two_card {R : Type*} [Group R] [Finite R] [IsCyclic R]
    (hP : IsPGroup 2 R) (hR : 8 ≤ Nat.card R) :
    Nat.card (omega R (p := 2) 2) = 4 := by
  have heq : omega R (p := 2) 2 = (powMonoidHom 4 : R →* R).ker := by
    apply le_antisymm
    · apply (closure_le _).mpr
      intro x hx
      exact hx
    · intro x hx
      exact subset_closure hx
  rw [heq, IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right]
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hn3 : 3 ≤ n := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hn ▸ hR)
  rw [hn]
  exact Nat.pow_dvd_pow 2 (by omega : 2 ≤ n)

private theorem inverted_of_mem_four {P : Type*} [Group P] [Finite P]
    (r v : P) (hr : orderOf r = 4)
    [IsElementaryAbelian 2 (centralizer ({v} : Set P))]
    (hm : v * r * v⁻¹ ∈ zpowers r) : v * r * v⁻¹ = r⁻¹ := by
  classical
  have hr4 : r ^ 4 = 1 := hr ▸ pow_orderOf_eq_one r
  have hr2 : r ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hr] at this
    norm_num at this
  have ho : orderOf (v * r * v⁻¹) = 4 := (MulAut.conj v).orderOf_eq r |>.trans hr
  rw [mem_zpowers_iff_mem_range_orderOf, hr] at hm
  obtain ⟨n, hn, he⟩ := Finset.mem_image.mp hm
  have hn4 := Finset.mem_range.mp hn
  interval_cases n
  · simp only [pow_zero] at he
    rw [← he, orderOf_one] at ho
    contradiction
  · have hfix : v * r * v⁻¹ = r := by simpa using he.symm
    have hcomm : r ∈ centralizer ({v} : Set P) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix).symm
    exact (hr2 (elemPow_eq_one_of_isElementaryAbelian r hcomm)).elim
  · rw [← he, orderOf_pow, hr] at ho
    norm_num at ho
  · rw [← he]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ, hr4]

/-- A large Hall factor commuting with a complementary factor has an inverted
order-four rotation with central square and cyclic centralizer. Only the Hall
factor's ambient normalizer and the exponent-two centralizer hypothesis are
needed for the inverting element. -/
public theorem Subgroup.exists_inverted_rotation_of_large_hall
    {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup 2 P) (H : Subgroup P) (B D : Subgroup H)
    (hD : IsBinaryHallFactor D) (hnc : ¬ IsCyclic D) (hlarge : 16 ≤ Nat.card D)
    (hc : D ≤ centralizer (B : Set H)) (hg : B ⊔ D = ⊤)
    (v : P) (hv : v ∈ normalizer (D.map H.subtype : Set P))
    [IsElementaryAbelian 2 (centralizer ({v} : Set P))] :
    ∃ r : D, orderOf r = 4 ∧ (r : H) ^ 2 ∈ center H ∧
      v * ((r : H) : P) * v⁻¹ = (((r : H) : P))⁻¹ ∧
      IsCyclic (centralizer ({r} : Set D)) := by
  obtain ⟨R, hRc, hRcyc, hR, -, hcent⟩ :=
    hD.exists_characteristic_large_rotation ((hP.to_subgroup H).to_subgroup D) hnc hlarge
  let : R.Characteristic := hRc
  let : IsCyclic R := hRcyc
  let O := omega R (p := 2) 2
  let : O.Characteristic := omega_characteristic R 2
  let W := O.map R.subtype
  let : W.Characteristic := inferInstance
  let : IsCyclic W := isCyclic_of_surjective
    (O.equivMapOfInjective R.subtype R.subtype_injective).toMonoidHom
    (O.equivMapOfInjective R.subtype R.subtype_injective).surjective
  have hW : Nat.card W = 4 := by
    rw [card_map_of_injective R.subtype_injective]
    exact omega_two_card (((hP.to_subgroup H).to_subgroup D).to_subgroup R) hR
  obtain ⟨r, hrW⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top W).mp inferInstance
  have hr : orderOf r = 4 := by rw [← Nat.card_zpowers, hrW]; exact hW
  have hnormal : (zpowers r).Normal := by rw [hrW]; infer_instance
  have hrZ : r ^ 2 ∈ center D := by
    apply mem_center_iff.mpr
    intro d
    have hd : d ∈ normalizer (zpowers r : Set D) := by
      let : (zpowers r).Normal := hnormal
      rw [normalizer_eq_top]
      trivial
    exact (mem_centralizer_singleton_iff.mp
      (normalizer_zpowers_four_le_centralizer_square r hr hd))
  have hrHZ : (r : H) ^ 2 ∈ center H := by
    have hle : B ⊔ D ≤ centralizer ({(r : H) ^ 2} : Set H) := by
      apply sup_le
      · intro b hb
        exact mem_centralizer_singleton_iff.mpr
          ((hc (D.pow_mem r.property 2)) b hb)
      · intro d hd
        apply mem_centralizer_singleton_iff.mpr
        exact congrArg D.subtype (mem_center_iff.mp hrZ (⟨d, hd⟩ : D))
    apply mem_center_iff.mpr
    intro h
    exact mem_centralizer_singleton_iff.mp (hle (hg.symm ▸ mem_top h))
  have hcyc : IsCyclic (centralizer ({r} : Set D)) := by
    apply isCyclic_of_le (H' := R)
    apply le_trans _ hcent
    change centralizer ({r} : Set D) ≤ centralizer (W : Set D)
    rw [← hrW]
    rw [zpowers_eq_closure, centralizer_closure]
  let E := D.map H.subtype
  let e : D ≃* E := D.equivMapOfInjective H.subtype H.subtype_injective
  let a : E ≃* E := E.normalizerMonoidHom ⟨v, hv⟩
  let f : D ≃* D := (e.trans a).trans e.symm
  have hfr : f r ∈ W := characteristic_iff_le_comap.mp inferInstance f
    (hrW ▸ mem_zpowers r)
  have hmem : v * ((r : H) : P) * v⁻¹ ∈ zpowers (((r : H) : P)) := by
    rw [← hrW] at hfr
    obtain ⟨k, hk⟩ := hfr
    refine ⟨k, ?_⟩
    have hh := congrArg (fun x : D => ((e x : E) : P)) hk
    simp only [f, MulEquiv.trans_apply, MulEquiv.apply_symm_apply, map_zpow] at hh
    exact hh
  exact ⟨r, hr, hrHZ, inverted_of_mem_four _ v (by simpa using hr) hmem, hcyc⟩
