module

public import Theory.GroupTheory.PGroup.CyclicTwoDisplacement
public import Theory.ElementaryAbelian.Basic
public import Theory.GroupTheory.SpecificGroups.QuaternionEightOuterInvolution
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Tactic.Group

/-!
# Displacement witnesses in a quaternion–cyclic central product

Let `R` be the product of a quaternion subgroup `Q` and its cyclic center
`C`, and let an involution `t` normalize both factors and centralize an
elementary four-subgroup `W` of `R`. If its action on `Q` is outer, then it
inverts an element of order four in `C`. When `C` has order at least eight,
every element of `W` is a displacement `x⁻¹ * t * x * t⁻¹` with `x ∈ R`.

An involution outside `C` factors as `q*d`, where both factors have order
four. Fixing the product preserves the quaternion axis modulo its center,
so the outer involution inverts `q` and `d`. The quaternion axis calculation
supplies a displacement equal to `q`. Every element of `C` whose fourth
power is one is a square, so cyclic displacements supply the correction
`d`. This argument treats each involution separately and needs no rank
bound or uniqueness hypothesis on `W`.

Source: Janko–Thompson (1970), §4, Case 2, printed p.393;
`refs/original/n-group-global/odd-core-rank-two-source/janko-thompson-1970-gdz.pdf`.
-/

open Subgroup

namespace IsPGroup
private theorem fourth_torsion_is_square {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (hG : IsPGroup 2 G) (hcard : 8 ≤ Nat.card G) (d : G) (hd : d ^ 4 = 1) :
    ∃ c : G, c ^ 2 = d := by
  obtain ⟨k, hk⟩ := hG.exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra hn
    have hle : k ≤ 2 := by omega
    have hpow : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by decide) hle
    omega
  have hdiv : 8 ∣ Nat.card G := by
    rw [hk]
    exact pow_dvd_pow 2 hk3
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G)
  have ho : orderOf g = Nat.card G := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨n, rfl⟩ := mem_powers_iff_mem_zpowers.mpr (hg d)
  have hn : 2 ∣ n := by
    have hdn : 8 ∣ n * 4 := hdiv.trans (ho ▸ orderOf_dvd_of_pow_eq_one
      (show g ^ (n * 4) = 1 by rwa [pow_mul]))
    have hdn' : 4 * 2 ∣ 4 * n := by simpa only [Nat.mul_comm] using hdn
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)).mp hdn'
  obtain ⟨m, rfl⟩ := hn
  exact ⟨g ^ m, by rw [← pow_mul, Nat.mul_comm]⟩
end IsPGroup

namespace Subgroup
private theorem central_factor_mem
    {P : Type*} [Group P] (R Q C : Subgroup P)
    (hQC : C ≤ centralizer (Q : Set P)) (hgen : Q ⊔ C = R)
    (hcenter : C = (center R).map R.subtype)
    (q : Q) (hq : q ∈ center Q) : (q : P) ∈ C := by
  have hqR : (q : P) ∈ R := hgen ▸ mem_sup_left q.property
  rw [hcenter]
  refine ⟨⟨q, hqR⟩, ?_, rfl⟩
  apply mem_center_iff.mpr
  intro r
  apply Subtype.ext
  have hle : R ≤ centralizer ({(q : P)} : Set P) := by
    rw [← hgen]
    apply sup_le
    · intro y hy
      apply mem_centralizer_singleton_iff.mpr
      exact congrArg Subtype.val (mem_center_iff.mp hq ⟨y, hy⟩)
    · intro c hc
      apply mem_centralizer_singleton_iff.mpr
      exact (mem_centralizer_iff.mp (hQC hc) q q.property).symm
  exact mem_centralizer_singleton_iff.mp (hle r.property)

private theorem quaternion_noncentral_square
    {G : Type*} [Group G] (e : G ≃* QuaternionGroup 2)
    (q : G) (hq : q ∉ center G) : q ^ 4 = 1 ∧ q ^ 2 ≠ 1 := by
  have hf : ∀ x : QuaternionGroup 2, x ^ 4 = 1 := by decide
  have hc : ∀ x : QuaternionGroup 2, x ^ 2 = 1 → ∀ y, y*x = x*y := by decide
  constructor
  · apply e.injective
    simpa only [map_pow, map_one] using hf (e q)
  · intro h
    apply hq
    apply mem_center_iff.mpr
    intro y
    apply e.injective
    simpa only [map_mul] using hc (e q) (by rw [← map_pow, h, map_one]) (e y)

private theorem noncentral_involution_factors
    {P : Type*} [Group P] (R Q C : Subgroup P) [C.Normal]
    (e : Q ≃* QuaternionGroup 2)
    (hQC : C ≤ centralizer (Q : Set P)) (hgen : Q ⊔ C = R)
    (hcenter : C = (center R).map R.subtype)
    (w : P) (hwR : w ∈ R) (hwC : w ∉ C) (hw2 : w ^ 2 = 1) :
    ∃ q : Q, ∃ d : C, (q : P) * d = w ∧
      q ∉ center Q ∧ orderOf d = 4 := by
  obtain ⟨q, hq, d, hd, hqd⟩ := mem_sup_of_normal_right.mp (hgen.symm ▸ hwR)
  let a : Q := ⟨q, hq⟩
  have hnon : a ∉ center Q := by
    intro h
    apply hwC
    rw [← hqd]
    exact C.mul_mem (central_factor_mem R Q C hQC hgen hcenter a h) hd
  have hcomm : Commute q d := mem_centralizer_iff.mp (hQC hd) q hq
  have hsquare : q ^ 2 * d ^ 2 = 1 := by rw [← hcomm.mul_pow, hqd, hw2]
  have hfourq : q ^ 4 = 1 := congrArg Subtype.val (quaternion_noncentral_square e a hnon).1
  have htwoq : q ^ 2 ≠ 1 := by
    intro h
    exact (quaternion_noncentral_square e a hnon).2 (Subtype.ext h)
  have hd2 : d ^ 2 = (q ^ 2)⁻¹ := eq_inv_of_mul_eq_one_right hsquare
  have hd4 : d ^ 4 = 1 := by
    rw [show 4 = 2 * 2 from rfl, pow_mul, hd2, inv_pow, ← pow_mul, hfourq, inv_one]
  have hdne : d ^ 2 ≠ 1 := by
    intro h
    rw [h, mul_one] at hsquare
    exact htwoq hsquare
  refine ⟨a, ⟨d, hd⟩, hqd, hnon, ?_⟩
  exact orderOf_eq_prime_pow (p := 2) (n := 1)
    (fun h => hdne (congrArg Subtype.val h)) (Subtype.ext hd4)

private theorem elementary_four_not_le_cyclic
    {P : Type*} [Group P] [Finite P] (W C : Subgroup P)
    [IsElementaryAbelian 2 W] [IsCyclic C] (hW : Nat.card W = 4) : ¬ W ≤ C := by
  intro h
  exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq (p := 2) hW
    (Subgroup.isCyclic_of_le h)
private theorem fixed_product_axis
    {P : Type*} [Group P] (Q C : Subgroup P) [Q.Normal] [C.Normal]
    (e : Q ≃* QuaternionGroup 2)
    (hQC : C ≤ centralizer (Q : Set P)) (t : P) (ht : t ^ 2 = 1)
    (houter : ¬ ∃ q₀ : Q, ∀ q : Q,
      t * (q : P) * t⁻¹ = (q₀ : P) * (q : P) * (q₀ : P)⁻¹)
    (q : Q) (d : C) (hq : q ∉ center Q)
    (hw2 : ((q : P) * d) ^ 2 = 1)
    (hfix : t * ((q : P) * d) * t⁻¹ = (q : P) * d) :
    t * (d : P) * t⁻¹ = (d : P)⁻¹ ∧
      ∃ u : Q, (u : P)⁻¹ * t * u * t⁻¹ = (q : P) := by
  let a : MulAut Q := MulAut.conjNormal t
  let b : MulAut C := MulAut.conjNormal t
  have ha : a ^ 2 = 1 := by dsimp [a]; rw [← map_pow, ht, map_one]
  have hao : ¬ ∃ z : Q, a = MulAut.conj z := by
    rintro ⟨z, hz⟩
    apply houter
    refine ⟨z, ?_⟩
    intro x
    exact congrArg Subtype.val (DFunLike.congr_fun hz x)
  have hprod : (a q : P) * (b d : P) = (q : P) * d := by
    simpa only [a, b, MulAut.conjNormal_apply, mul_assoc, inv_mul_cancel_left] using hfix
  have heq : ((q⁻¹ * a q : Q) : P) = (d : P) * (b d : P)⁻¹ := by
    change (q : P)⁻¹ * (a q : P) = _
    calc
      (q : P)⁻¹ * (a q : P) =
          (q : P)⁻¹ * ((a q : P) * (b d : P)) * (b d : P)⁻¹ := by group
      _ = (q : P)⁻¹ * ((q : P) * d) * (b d : P)⁻¹ := by rw [hprod]
      _ = (d : P) * (b d : P)⁻¹ := by group
  have hdC : ((q⁻¹ * a q : Q) : P) ∈ C := by
    rw [heq]
    exact C.mul_mem d.property (C.inv_mem (b d).property)
  have hdelta : q⁻¹ * a q ∈ center Q := by
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact mem_centralizer_iff.mp (hQC hdC) y y.property
  obtain ⟨hinv, u, hu⟩ := QuaternionGroup.outer_involution_axis_of_equiv e a ha hao q hq hdelta
  have hcomm : Commute (q : P) (d : P) := mem_centralizer_iff.mp (hQC d.property) q q.property
  have hwInv : (q : P) * d = ((q : P) * d)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by simpa only [pow_two] using hw2)
  constructor
  · change (b d : P) = (d : P)⁻¹
    apply mul_left_cancel (a := (q : P)⁻¹)
    calc
      (q : P)⁻¹ * (b d : P) = (q : P) * d := by
        simpa only [hinv, coe_inv] using hprod
      _ = (q : P)⁻¹ * (d : P)⁻¹ := by
        rw [hwInv, mul_inv_rev]
        exact hcomm.inv_inv.symm.eq
  · refine ⟨u, ?_⟩
    have h := congrArg Subtype.val hu
    simpa only [coe_mul, coe_inv, a, MulAut.conjNormal_apply, mul_assoc] using h

private theorem cyclic_displacement_correction
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (C : Subgroup P) [C.Normal] [IsCyclic C] (hC : 8 ≤ Nat.card C)
    (t : P) (d : C) (hd : orderOf d = 4)
    (hinv : t * (d : P) * t⁻¹ = (d : P)⁻¹)
    (v : C) (hv : v ^ 4 = 1) :
    ∃ c : C, (c : P)⁻¹ * t * c * t⁻¹ = (v : P) := by
  obtain ⟨y, hy⟩ := (hP.to_subgroup C).fourth_torsion_is_square hC v hv
  have hd' : (MulAut.conjNormal t : MulAut C) d = d⁻¹ := Subtype.ext hinv
  obtain ⟨c, hc⟩ := (hP.to_subgroup C).exists_displacement_eq_square_of_inverts_order_four
    (MulAut.conjNormal t) d hd hd' y
  refine ⟨c, ?_⟩
  rw [hy] at hc
  simpa only [coe_mul, coe_inv, MulAut.conjNormal_apply, mul_assoc] using
    congrArg Subtype.val hc

/-- An outer involution fixing an elementary four in a quaternion–cyclic
central product inverts an element of order four in the cyclic factor. -/
public theorem exists_inverted_four_of_quaternion_cyclic_core
    {P : Type*} [Group P] [Finite P]
    (R Q C W : Subgroup P) [Q.Normal] [C.Normal] [IsCyclic C]
    [IsElementaryAbelian 2 W] (e : Q ≃* QuaternionGroup 2)
    (hQC : C ≤ centralizer (Q : Set P)) (hgen : Q ⊔ C = R)
    (hcenter : C = (center R).map R.subtype)
    (hW : Nat.card W = 4) (hWR : W ≤ R)
    (t : P) (ht : t ^ 2 = 1) (htW : t ∈ centralizer (W : Set P))
    (houter : ¬ ∃ q₀ : Q, ∀ q : Q,
      t * (q : P) * t⁻¹ = (q₀ : P) * (q : P) * (q₀ : P)⁻¹) :
    ∃ d : C, orderOf d = 4 ∧ t * (d : P) * t⁻¹ = (d : P)⁻¹ := by
  obtain ⟨w, hwW, hwC⟩ := SetLike.not_le_iff_exists.mp
    (elementary_four_not_le_cyclic W C hW)
  have hw2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) w hwW
  obtain ⟨q, d, hqd, hqn, hd⟩ := noncentral_involution_factors R Q C e hQC hgen hcenter
    w (hWR hwW) hwC hw2
  have htw : t * w = w * t := (mem_centralizer_iff.mp htW w hwW).symm
  have hfix : t * ((q : P) * d) * t⁻¹ = (q : P) * d := by
    rw [hqd, htw, mul_inv_cancel_right]
  refine ⟨d, hd, ?_⟩
  exact (fixed_product_axis Q C e hQC t ht houter q d hqn
    (by rwa [hqd]) hfix).1

/-- If the cyclic factor has order at least eight, every element of the fixed
elementary four is a displacement of an element of the quaternion–cyclic core. -/
public theorem exists_displacement_of_quaternion_cyclic_core
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (R Q C W : Subgroup P) [Q.Normal] [C.Normal] [IsCyclic C]
    [IsElementaryAbelian 2 W] (e : Q ≃* QuaternionGroup 2)
    (hC : 8 ≤ Nat.card C)
    (hQC : C ≤ centralizer (Q : Set P)) (hgen : Q ⊔ C = R)
    (hcenter : C = (center R).map R.subtype)
    (hW : Nat.card W = 4) (hWR : W ≤ R)
    (t : P) (ht : t ^ 2 = 1) (htW : t ∈ centralizer (W : Set P))
    (houter : ¬ ∃ q₀ : Q, ∀ q : Q,
      t * (q : P) * t⁻¹ = (q₀ : P) * (q : P) * (q₀ : P)⁻¹) :
    ∀ w : W, ∃ x : R, (x : P)⁻¹ * t * x * t⁻¹ = (w : P) := by
  obtain ⟨d₀, hd₀, hinv₀⟩ := exists_inverted_four_of_quaternion_cyclic_core
    R Q C W e hQC hgen hcenter hW hWR t ht htW houter
  have hCR : C ≤ R := hgen ▸ le_sup_right
  have hQR : Q ≤ R := hgen ▸ le_sup_left
  intro w
  have hw2 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (w : P) w.property
  by_cases hwC : (w : P) ∈ C
  · let v : C := ⟨w, hwC⟩
    have hv : v ^ 4 = 1 := by
      apply Subtype.ext
      change (w : P) ^ 4 = 1
      rw [show 4 = 2 * 2 from rfl, pow_mul, hw2, one_pow]
    obtain ⟨c, hc⟩ := cyclic_displacement_correction hP C hC t d₀ hd₀ hinv₀ v hv
    exact ⟨⟨c, hCR c.property⟩, hc⟩
  · obtain ⟨q, d, hqd, hqn, hd⟩ := noncentral_involution_factors R Q C e hQC hgen hcenter
      w (hWR w.property) hwC hw2
    have htw : t * (w : P) = (w : P) * t :=
      (mem_centralizer_iff.mp htW w w.property).symm
    have hfix : t * ((q : P) * d) * t⁻¹ = (q : P) * d := by
      rw [hqd, htw, mul_inv_cancel_right]
    obtain ⟨_, u, hu⟩ := fixed_product_axis Q C e hQC t ht houter q d hqn
      (by rwa [hqd]) hfix
    obtain ⟨c, hc⟩ := cyclic_displacement_correction hP C hC t d₀ hd₀ hinv₀ d
      (by simpa only [hd] using pow_orderOf_eq_one d)
    refine ⟨⟨(u : P) * c, R.mul_mem (hQR u.property) (hCR c.property)⟩, ?_⟩
    change ((u : P) * c)⁻¹ * t * ((u : P) * c) * t⁻¹ = (w : P)
    have hcomm : Commute (q : P) (c : P) :=
      mem_centralizer_iff.mp (hQC c.property) q q.property
    calc
      ((u : P) * c)⁻¹ * t * ((u : P) * c) * t⁻¹ =
          (c : P)⁻¹ * ((u : P)⁻¹ * t * u * t⁻¹) * (t * c * t⁻¹) := by group
      _ = (c : P)⁻¹ * q * (t * c * t⁻¹) := by rw [hu]
      _ = (q : P) * ((c : P)⁻¹ * t * c * t⁻¹) := by
        rw [← hcomm.inv_right.eq]
        group
      _ = (q : P) * d := by rw [hc]
      _ = (w : P) := hqd

/-- The inverted cyclic four and all displacement witnesses, with the ambient
index-two quaternion–cyclic hypotheses. The stronger component theorems above
do not require the index, intersection-size, or normality hypotheses on `W`. -/
public theorem quaternion_cyclic_four_displacement
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (R Q C W : Subgroup P) (_hR : R.index = 2)
    (hQn : Q.Normal) (hCn : C.Normal) (hQ : Nonempty (Q ≃* QuaternionGroup 2))
    (hCc : IsCyclic C) (hC : 8 ≤ Nat.card C)
    (hQC : C ≤ centralizer (Q : Set P)) (hgen : Q ⊔ C = R)
    (_hinter : Nat.card (Q ⊓ C : Subgroup P) = 2)
    (hcenter : C = (center R).map R.subtype)
    (_hWn : W.Normal) (hWe : IsElementaryAbelian 2 W)
    (hW : Nat.card W = 4) (hWR : W ≤ R)
    (t : P) (ht : t ^ 2 = 1) (_htR : t ∉ R) (htW : t ∈ centralizer (W : Set P))
    (houter : ¬ ∃ q₀ : Q, ∀ q : Q,
      t * (q : P) * t⁻¹ = (q₀ : P) * (q : P) * (q₀ : P)⁻¹) :
    (∃ d : C, orderOf d = 4 ∧ t * (d : P) * t⁻¹ = (d : P)⁻¹) ∧
      ∀ w : W, ∃ x : R, (x : P)⁻¹ * t * x * t⁻¹ = (w : P) := by
  let := hQn
  let := hCn
  let := hCc
  let := hWe
  obtain ⟨e⟩ := hQ
  exact ⟨exists_inverted_four_of_quaternion_cyclic_core R Q C W e hQC hgen hcenter
      hW hWR t ht htW houter,
    exists_displacement_of_quaternion_cyclic_core hP R Q C W e hC hQC hgen hcenter
      hW hWR t ht htW houter⟩

end Subgroup
