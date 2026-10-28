module

public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
public import Theory.ElementaryAbelian.FivePlaneTwelveActor.MatrixFacts
public import Theory.GroupTheory.DihedralPresentation
public import Mathlib.GroupTheory.Sylow
public import Mathlib.RingTheory.IntegralDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Recognition of the order-twelve five-plane actor

An order-twelve subgroup of the automorphism group of an elementary
abelian group of order 25, containing an elementary four-group, is
isomorphic to the dihedral group of order twelve.

Embed the supplied actor faithfully in GL₂(5). Its four-group is Sylow,
so every element has sixth power one. The determinant cannot embed the
four-group in the cyclic scalar units; its kernel therefore contains the
scalar involution −I. Choose a second involution and an element of order
three. The matrix calculation shows that the former inverts the latter.
Multiplying the order-three element by −I gives a rotation of order six;
determinants separate the reflection from its cyclic subgroup. Cardinality
then proves generation, and the dihedral presentation constructs the
actual multiplicative equivalence.

This is the independent linear recognition used in the final paragraph of
Aschbacher, *Sporadic Groups* (1994), 47.2, printed p.261 (PDF page 136).
-/

open Subgroup

namespace IsElementaryAbelian

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩
private instance : Fact (Nat.Prime 3) := ⟨by decide⟩
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem exponent_six {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 12) (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 4) (x : G) : x ^ 6 = 1 := by
  have hi : V.index = 3 := by
    have h := V.card_mul_index
    rw [hG, hV] at h
    omega
  let P := (IsElementaryAbelian.isPGroup 2 V).toSylow
    (show ¬2 ∣ V.index by omega)
  have hx : (x ^ 3) ^ 4 = 1 := by
    simpa only [← pow_mul, hG] using (pow_card_eq_one' (x := x))
  have hQ : IsPGroup 2 (zpowers (x ^ 3)) :=
    IsPGroup.of_card_dvd_pow (n := 2) (by
      simpa only [Nat.card_zpowers, show 2 ^ 2 = 4 from rfl] using
        orderOf_dvd_of_pow_eq_one hx)
  obtain ⟨Q, hQ⟩ := hQ.exists_le_sylow
  let y : Q := ⟨x ^ 3, hQ (mem_zpowers _)⟩
  have hy : (Q.equiv P y) ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) (Q.equiv P y)
  have hy' : y ^ 2 = 1 := (Q.equiv P).injective (by simpa using hy)
  have hx' : (x ^ 3) ^ 2 = 1 := congrArg Subtype.val hy'
  simpa only [← pow_mul] using hx'

private theorem recognize {G : Type*} [Group G] [Finite G]
    (hG : Nat.card G = 12) (V : Subgroup G) [IsElementaryAbelian 2 V]
    (hV : Nat.card V = 4)
    (f : G →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 5))
    (hf : Function.Injective f) : Nonempty (G ≃* DihedralGroup 6) := by
  classical
  let δ := Matrix.GeneralLinearGroup.det.comp f
  have hs (v : V) : v ^ 2 = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) v
  have hs' (v : V) : (f v.val) ^ 2 = 1 := by
    simpa only [map_pow, map_one, MonoidHom.comp_apply, Subgroup.subtype_apply] using
      congrArg (f.comp V.subtype) (hs v)
  have hzex : ∃ z : V, f z.val = -1 := by
    by_contra hn
    push Not at hn
    have hi : Function.Injective (δ.comp V.subtype) := by
      apply (δ.comp V.subtype).ker_eq_bot_iff.mp
      apply (eq_bot_iff_forall _).mpr
      intro v hv
      have hd : Matrix.GeneralLinearGroup.det (f v.val) = 1 := by
        change (δ.comp V.subtype) v = 1 at hv
        simpa [δ] using hv
      rcases Matrix.FivePlaneTwelveActor.eq_one_or_neg_one_of_det_one_of_sq_one
        (f v.val) hd (hs' v) with h | h
      · apply Subtype.ext
        exact hf (by simpa only [map_one, Subgroup.coe_one] using h)
      · exact (hn v h).elim
    have hc : IsCyclic V := isCyclic_of_injective (δ.comp V.subtype) hi
    exact IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq
      (p := 2) (by simpa using hV) hc
  obtain ⟨z, hz⟩ := hzex
  have hneg : (-1 : Matrix.GeneralLinearGroup (Fin 2) (ZMod 5)) ≠ 1 := by
    intro h
    have := congrArg (fun a : Matrix.GeneralLinearGroup (Fin 2) (ZMod 5) => a 0 0) h
    exact (by decide : (-1 : ZMod 5) ≠ 1) this
  have hz0 : z ≠ 1 := by
    intro h
    apply hneg
    rw [← hz, h]
    exact f.map_one
  have hz2 : orderOf z = 2 := orderOf_eq_prime (hs z) hz0
  have hzproper : zpowers z ≠ ⊤ := by
    intro h
    have hc := Nat.card_zpowers z
    rw [h, Nat.card_congr (topEquiv : (⊤ : Subgroup V) ≃* V).toEquiv, hV, hz2] at hc
    omega
  obtain ⟨y, hy⟩ : ∃ y : V, y ∉ zpowers z := by
    exact not_forall.mp (fun hall => hzproper ((Subgroup.eq_top_iff' _).mpr hall))
  have hy1 : f y.val ≠ 1 := by
    intro h
    have hy0 : y = 1 := Subtype.ext (hf (by simpa only [map_one, Subgroup.coe_one] using h))
    exact hy (hy0 ▸ (zpowers z).one_mem)
  have hyz : f y.val ≠ -1 := by
    intro h
    have he : y = z := Subtype.ext (hf (h.trans hz.symm))
    exact hy (he ▸ mem_zpowers z)
  have hdY : δ y.val = -1 := by
    have hsq : ((δ y.val : (ZMod 5)ˣ) : ZMod 5) ^ 2 = 1 := by
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, map_pow, map_one,
        Units.val_pow_eq_pow_val, Units.val_one] using
        congrArg (fun v : V => (δ v.val).val) (hs y)
    rcases sq_eq_one_iff.mp hsq with h | h
    · have hd : Matrix.GeneralLinearGroup.det (f y.val) = 1 := Units.ext h
      rcases Matrix.FivePlaneTwelveActor.eq_one_or_neg_one_of_det_one_of_sq_one
        (f y.val) hd (hs' y) with h | h
      · exact (hy1 h).elim
      · exact (hyz h).elim
    · exact Units.ext h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := G) 3 (by rw [hG]; decide)
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hdX : δ x = 1 := by
    have hc : ∀ a : ZMod 5, a ^ 3 = 1 → a = 1 := by decide +kernel
    apply Units.ext
    apply hc
    simpa only [map_pow, map_one, Units.val_pow_eq_pow_val, Units.val_one] using
      congrArg (fun g => (δ g).val) hx3
  have hYX : (y.val * x) ^ 2 = 1 := by
    apply hf
    rw [map_pow, map_one]
    apply Matrix.FivePlaneTwelveActor.sq_eq_one_of_det_neg_one_of_pow_six
    · change δ (y.val * x) = -1
      rw [map_mul, hdY, hdX, mul_one]
    · simpa only [map_pow, map_one] using congrArg f (exponent_six hG V hV (y.val * x))
  have hy2 : y.val ^ 2 = 1 := congrArg Subtype.val (hs y)
  have hyinv : y.val⁻¹ = y.val := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hy2)
  have hinv : y.val * x * y.val⁻¹ = x⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    simpa only [pow_two, hyinv, mul_assoc] using hYX
  have hzcentral (g : G) : Commute z.val g := by
    change z.val * g = g * z.val
    apply hf
    simp only [map_mul, hz, neg_one_mul, mul_neg_one]
  have hzpow : z.val ^ 2 = 1 := congrArg Subtype.val (hs z)
  have hzorder : orderOf z.val = 2 := by simpa only [Subgroup.orderOf_coe] using hz2
  have hzinv : z.val⁻¹ = z.val := inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hzpow)
  let c := z.val * x
  have hc : orderOf c = 6 := by
    rw [(hzcentral x).orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hzorder, hx]; decide),
      hzorder, hx]
  have hcconj : y.val * c * y.val⁻¹ = c⁻¹ := by
    change y.val * (z.val * x) * y.val⁻¹ = (z.val * x)⁻¹
    calc
      y.val * (z.val * x) * y.val⁻¹ = z.val * (y.val * x * y.val⁻¹) := by
        rw [← mul_assoc y.val z.val x, (hzcentral y.val).eq.symm]
        simp only [mul_assoc]
      _ = z.val * x⁻¹ := by rw [hinv]
      _ = (z.val * x)⁻¹ := by rw [mul_inv_rev, hzinv]; exact (hzcentral x⁻¹).eq
  have hdZ : δ z.val = 1 := by
    apply Units.ext
    change (f z.val).val.det = 1
    rw [hz]
    simp [Matrix.det_fin_two]
  have hdC : δ c = 1 := by rw [map_mul, hdZ, hdX, one_mul]
  have hyC : y.val ∉ zpowers c := by
    intro hyc
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hyc
    have h := congrArg δ hk
    rw [map_zpow, hdC, one_zpow, hdY] at h
    have := congrArg Units.val h
    exact (by decide : (1 : ZMod 5) ≠ -1) this
  let K := closure ({c, y.val} : Set G)
  have hcK : c ∈ K := subset_closure (by simp)
  have hyK : y.val ∈ K := subset_closure (by simp)
  have hCK : zpowers c ≤ K := zpowers_le.mpr hcK
  have hK6 : 6 < Nat.card K := by
    by_contra h
    have he : zpowers c = K := eq_of_le_of_card_ge hCK (by rw [Nat.card_zpowers, hc]; omega)
    exact hyC (he ▸ hyK)
  have hKidx : K.index = 1 := by
    have hm := K.card_mul_index
    rw [hG] at hm
    have hp : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    have : K.index < 2 := by
      by_contra h
      have : 2 ≤ K.index := by omega
      nlinarith
    omega
  exact dihedralGroup_equiv_of_presentation (by decide) c y.val hc hy2 hcconj
    (Subgroup.index_eq_one.mp hKidx) (by omega)

/-- An order-twelve faithful actor on the elementary five-plane, containing
an elementary four-group, is the dihedral group of order twelve. -/
public theorem nonempty_mulEquiv_dihedral_six_of_card_twelve
    {E : Type*} [Group E] [Finite E] [IsElementaryAbelian 5 E]
    (hE : Nat.card E = 25) (H : Subgroup (MulAut E)) (hH : Nat.card H = 12)
    (V : Subgroup H) [IsElementaryAbelian 2 V] (hV : Nat.card V = 4) :
    Nonempty (H ≃* DihedralGroup 6) := by
  obtain ⟨f, hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 5) (n := 2) E (by omega)
  exact recognize hH V hV (f.comp H.subtype) (hf.comp H.subtype_injective)

end IsElementaryAbelian
