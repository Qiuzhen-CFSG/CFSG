module

public import Theory.SpecificGroups.PSL3Four.AnisotropicRootRecognition.IntrinsicCoordinates.Collection
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Coset.Card
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Tactic.Group

/-!
# Intrinsic generators of the two anisotropic factors

The ambient center is coordinatized by the two marked involutions `z,u`.
Each factor modulo that center is a Klein four-group. Lifting two independent
quotient elements gives generators whose squares, and whose product's square,
are the prescribed involution. These identities give the internal swap law.
The ambient quotient has exponent two, so every cross correction is central;
its coordinates give precisely the four entries of the collection matrix.

The result `factorCollectionRelations` supplies the hypotheses of `wordHom`.
`nonempty_factorPair` constructs its generators from the intrinsic data rather
than assuming a presentation or an isomorphism. The parent module uses these
results to establish marked normal forms and the six-case fiber consequence.
Source motivation: Aschbacher, *Sporadic Groups* (1994), 8.15, 46.2–46.3 and
the proof of 46.14, printed pp.29–30,251,257–258.
-/

public section

open Subgroup
namespace Theory.GroupTheory.AnisotropicRecognition.Intrinsic

variable {K : Type*} [Group K] (F : AnisotropicFactors K)

private theorem klein_of_card {G : Type*} [Group G] [Finite G]
    (hc : Nat.card G = 4) (hs : ∀ x : G, x ^ 2 = 1) : IsKleinFour G := by
  let : Nontrivial G := (Finite.one_lt_card_iff_nontrivial).mp (by omega)
  let : IsElementaryAbelian 2 G := {
    is_comm := ⟨fun a b => (Commute.of_orderOf_dvd_two
      (fun x => orderOf_dvd_of_pow_eq_one (hs x)) a b).eq⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }
  exact ⟨hc, IsElementaryAbelian.exponent_eq_prime⟩

private theorem four_cases {G : Type*} [Group G] [Finite G] [IsKleinFour G]
    {x y : G} (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) (w : G) :
    w = x*y ∨ w = x ∨ w = y ∨ w = 1 := by
  classical
  let := Fintype.ofFinite G
  have hm : w ∈ ({x*y,x,y,1} : Finset G) :=
    (IsKleinFour.eq_finset_univ hx hy hxy).symm ▸ Finset.mem_univ w
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hm

private theorem binary_pow_add {G : Type*} [Group G] (x : G) (hx : x ^ 2 = 1)
    (i j : Bit) : x ^ (i+j).val = x ^ i.val * x ^ j.val := by
  fin_cases i <;> fin_cases j
  · change x^0 = x^0*x^0; simp
  · change x^1 = x^0*x^1; simp
  · change x^1 = x^1*x^0; simp
  · change x^0 = x^1*x^1; simpa [pow_two] using hx.symm

noncomputable def centerHom : Multiplicative Central →* center K where
  toFun t := F.z ^ t.toAdd.1.val * F.u ^ t.toAdd.2.val
  map_one' := by simp
  map_mul' x y := by
    have hs (t : center K) : t ^ 2 = 1 := by
      let := F.center_elementary
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 (center K)) t
    change F.z ^ (x.toAdd.1 + y.toAdd.1).val *
      F.u ^ (x.toAdd.2 + y.toAdd.2).val = _
    rw [binary_pow_add _ (hs _) , binary_pow_add _ (hs _)]
    change _ = (F.z ^ x.toAdd.1.val * F.u ^ x.toAdd.2.val) *
      (F.z ^ y.toAdd.1.val * F.u ^ y.toAdd.2.val)
    ac_rfl

@[simp] theorem centerHom_z : centerHom F (Multiplicative.ofAdd cz) = F.z := by
  simp [centerHom, cz, ZMod.val_one]
@[simp] theorem centerHom_u : centerHom F (Multiplicative.ofAdd cu) = F.u := by
  simp [centerHom, cu, ZMod.val_one]

variable [Finite K]

noncomputable def centerEquiv : Multiplicative Central ≃* center K := by
  have hs (t : center K) : t ^ 2 = 1 := by
    let := F.center_elementary
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (center K)) t
  let := klein_of_card F.center_card hs
  have hsurj : Function.Surjective (centerHom F) := by
    intro t
    rcases four_cases F.z_ne_one F.u_ne_one F.distinct t with rfl | rfl | rfl | rfl
    · exact ⟨Multiplicative.ofAdd czu, by simp [centerHom, czu, ZMod.val_one]⟩
    · exact ⟨Multiplicative.ofAdd cz, centerHom_z F⟩
    · exact ⟨Multiplicative.ofAdd cu, centerHom_u F⟩
    · exact ⟨1, map_one _⟩
  exact MulEquiv.ofBijective (centerHom F)
    ((Nat.bijective_iff_surjective_and_card _).mpr ⟨hsurj, by
      rw [F.center_card]; change Nat.card Central = 4; simp [Central, Bit]⟩)

@[simp] theorem centerEquiv_z : centerEquiv F (Multiplicative.ofAdd cz) = F.z :=
  centerHom_z F
@[simp] theorem centerEquiv_u : centerEquiv F (Multiplicative.ofAdd cu) = F.u :=
  centerHom_u F

/-- Two lifts generating a factor together with the ambient center. -/
structure FactorPair (H : Subgroup K) (t : center K) where
  a : K
  b : K
  a_mem : a ∈ H
  b_mem : b ∈ H
  a_noncentral : a ∉ center K
  b_noncentral : b ∉ center K
  ab_noncentral : a*b ∉ center K
  a_square : a ^ 2 = (t : K)
  b_square : b ^ 2 = (t : K)
  swap : b * a = a * b * (t : K)
  generate : ∀ S : Subgroup K, center K ≤ S → a ∈ S → b ∈ S → H ≤ S

omit [Finite K] in
private theorem swap_of_squares (x y : K) (t : center K)
    (ht : t ^ 2 = 1) (hx : x ^ 2 = (t : K)) (hy : y ^ 2 = (t : K))
    (hxy : (x*y) ^ 2 = (t : K)) : y*x = x*y*(t : K) := by
  apply mul_left_cancel (a := x*y)
  calc
    (x*y)*(y*x) = x*(y^2)*x := by simp [pow_two, mul_assoc]
    _ = x*(t : K)*x := by rw [hy]
    _ = x*x*(t : K) := by rw [mul_assoc, ← mem_center_iff.mp t.property x, ← mul_assoc]
    _ = 1 := by rw [← pow_two, hx]; simpa only [Subgroup.coe_pow, Subgroup.coe_one, pow_two, Subgroup.coe_mul] using congrArg (fun w : center K => (w : K)) ht
    _ = (x*y)*(x*y*(t : K)) := by
      rw [← mul_assoc, ← pow_two, hxy]
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, pow_two, Subgroup.coe_mul] using (congrArg (fun w : center K => (w : K)) ht).symm

include F in
theorem nonempty_factorPair (H : Subgroup K) (hZH : center K ≤ H)
    (hH : Nat.card H = 16) (t : center K)
    (hs : ∀ x ∈ H, x ∉ center K → x ^ 2 = (t : K)) : Nonempty (FactorPair H t) := by
  let N := (center K).subgroupOf H
  let q := QuotientGroup.mk' N
  have hcN : Nat.card N = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZH).toEquiv).trans F.center_card
  have hcQ : Nat.card (H ⧸ N) = 4 := by
    have hh := card_eq_card_quotient_mul_card_subgroup N
    rw [hH, hcN] at hh
    omega
  have hsqQ (x : H ⧸ N) : x ^ 2 = 1 := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (F.square_central x)
  let := klein_of_card hcQ hsqQ
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := Multiplicative Central) (G₂ := H ⧸ N)
  obtain ⟨a, ha⟩ := QuotientGroup.mk'_surjective N (e (Multiplicative.ofAdd cz))
  obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective N (e (Multiplicative.ofAdd cu))
  have hane : q a ≠ 1 := by rw [ha]; exact fun h => (by decide : (Multiplicative.ofAdd cz : Multiplicative Central) ≠ 1) (e.injective (h.trans (map_one e).symm))
  have hbne : q b ≠ 1 := by rw [hb]; exact fun h => (by decide : (Multiplicative.ofAdd cu : Multiplicative Central) ≠ 1) (e.injective (h.trans (map_one e).symm))
  have habne : q a ≠ q b := by
    rw [ha, hb]; exact fun h => (by decide : (Multiplicative.ofAdd cz : Multiplicative Central) ≠ Multiplicative.ofAdd cu) (e.injective h)
  have hn (x : H) (hx : q x ≠ 1) : (x : K) ∉ center K :=
    fun hz => hx ((QuotientGroup.eq_one_iff _).mpr hz)
  have hab1 : q (a*b) ≠ 1 := by
    rw [map_mul, ha, hb, ← map_mul]
    exact fun h => (by decide : (Multiplicative.ofAdd cz * Multiplicative.ofAdd cu : Multiplicative Central) ≠ 1) (e.injective (h.trans (map_one e).symm))
  have has := hs a a.property (hn a hane)
  have hbs := hs b b.property (hn b hbne)
  have habs := hs (a*b) (a*b).property (hn (a*b) hab1)
  have ht : t ^ 2 = 1 := by
    let := F.center_elementary
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 (center K)) t
  refine ⟨⟨a, b, a.property, b.property, hn a hane, hn b hbne, hn (a*b) hab1, has, hbs,
    swap_of_squares (a : K) (b : K) t ht has hbs habs, ?_⟩⟩
  intro S hZS haS hbS x hx
  let xH : H := ⟨x, hx⟩
  have lift_mem (y : H) (hy : (y : K) ∈ S) (he : q xH = q y) : x ∈ S := by
    have hd : y⁻¹*xH ∈ N := (QuotientGroup.eq_one_iff _).mp (by
      change q (y⁻¹*xH) = 1
      rw [map_mul, map_inv, he, inv_mul_cancel])
    have hh := S.mul_mem hy (hZS hd)
    simpa [xH] using hh
  rcases four_cases hane hbne habne (q xH) with h | h | h | h
  · exact lift_mem (a*b) (S.mul_mem haS hbS) (h.trans (map_mul q a b).symm)
  · exact lift_mem a haS h
  · exact lift_mem b hbS h
  · exact lift_mem 1 S.one_mem (h.trans (map_one q).symm)

omit [Finite K] in
private theorem correction_mem_center (F : AnisotropicFactors K) (x y : K) :
    (x*y)⁻¹*(y*x) ∈ center K := by
  let q := QuotientGroup.mk' (center K)
  have hs (w : K ⧸ center K) : w^2 = 1 := by
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (center K) w
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (F.square_central w)
  have hc := Commute.of_orderOf_dvd_two
    (fun w => orderOf_dvd_of_pow_eq_one (hs w)) (q x) (q y)
  apply (QuotientGroup.eq_one_iff _).mp
  change q ((x*y)⁻¹*(y*x)) = 1
  rw [map_mul, map_inv, map_mul, map_mul, hc.eq, inv_mul_cancel]

/-- Coordinates of the correction for collecting `y*x` into `x*y`. -/
noncomputable def crossCoefficient (x y : K) : Central :=
  ((centerEquiv F).symm ⟨(x*y)⁻¹*(y*x), correction_mem_center F x y⟩).toAdd

/-- The actual four cross coefficients of four chosen lifts. -/
noncomputable def crossMatrix (a b c d : K) : Cross :=
  ⟨crossCoefficient F a c, crossCoefficient F a d,
    crossCoefficient F b c, crossCoefficient F b d⟩

theorem crossCoefficient_swap (x y : K) :
    y*x = x*y*centralEval (centerEquiv F).toMonoidHom (crossCoefficient F x y) := by
  have he : centralEval (centerEquiv F).toMonoidHom (crossCoefficient F x y) =
      (x*y)⁻¹*(y*x) :=
    congrArg Subtype.val ((centerEquiv F).apply_symm_apply _)
  rw [he, ← mul_assoc, mul_inv_cancel, one_mul]

/-- Intrinsic factor lifts satisfy the literal relations used in collection. -/
theorem factorCollectionRelations (P : FactorPair F.A F.z) (Q : FactorPair F.B F.u) :
    CollectionRelations (centerEquiv F).toMonoidHom
      (crossMatrix F P.a P.b Q.a Q.b) P.a P.b Q.a Q.b := by
  have hz : centralEval (centerEquiv F).toMonoidHom cz = (F.z : K) :=
    congrArg Subtype.val (centerEquiv_z F)
  have hu : centralEval (centerEquiv F).toMonoidHom cu = (F.u : K) :=
    congrArg Subtype.val (centerEquiv_u F)
  exact ⟨P.a_square.trans hz.symm, P.b_square.trans hz.symm,
    Q.a_square.trans hu.symm, Q.b_square.trans hu.symm,
    hz.symm ▸ P.swap, hu.symm ▸ Q.swap,
    crossCoefficient_swap F P.a Q.a, crossCoefficient_swap F P.a Q.b,
    crossCoefficient_swap F P.b Q.a, crossCoefficient_swap F P.b Q.b⟩

omit [Finite K] in
theorem FactorPair.pairWord_mem {H : Subgroup K} {t : center K} (P : FactorPair H t)
    (v : Central) : pairWord P.a P.b v ∈ H :=
  H.mul_mem (H.pow_mem P.a_mem _) (H.pow_mem P.b_mem _)

omit [Finite K] in
theorem FactorPair.pairWord_mem_center_iff {H : Subgroup K} {t : center K}
    (P : FactorPair H t) (v : Central) : pairWord P.a P.b v ∈ center K ↔ v = 0 := by
  rcases v with ⟨i,j⟩
  fin_cases i <;> fin_cases j
  · change P.a^0*P.b^0 ∈ center K ↔ ((0,0) : Central) = 0
    simp
  · change P.a^0*P.b^1 ∈ center K ↔ ((0,1) : Central) = 0
    simp [P.b_noncentral]
  · change P.a^1*P.b^0 ∈ center K ↔ ((1,0) : Central) = 0
    simp [P.a_noncentral]
  · change P.a^1*P.b^1 ∈ center K ↔ ((1,1) : Central) = 0
    simp [P.ab_noncentral]

end Theory.GroupTheory.AnisotropicRecognition.Intrinsic
