module

public import Theory.GroupTheory.MarkedInnerStrongClosure.CentralTwoQuotient

/-!
# Returning conjugates in a marked central two-quotient

The original central involution acts on an embedded component by an inner
implementer. Its image in a quotient by the two-group center is a nonidentity
involution in the center of the image Sylow. The implementer lies in the
original Sylow, even when it has order greater than two.

Only conjugates of this marked quotient element are lifted. The inverse image
of the quotient Sylow is the original Sylow, so abelian strong closure makes
any two returning conjugates commute. The resulting obstruction requires a
noncommuting pair in the marked class, not fusion of all involutions.

Source application: Aschbacher--Smith 1.1.5(3)(b), pp.501--502, and the
component inspection in Proposition 2.2.2, pp.519--520 (1 March 2004 manuscript).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.MarkedInnerStrongClosure
variable {G K Q : Type*} [Group G] [Group K] [Group Q]

/-- The marked quotient element is central in the actual image Sylow, and
its original implementer belongs to the original component Sylow. -/
theorem central_two_quotient_marker [Finite K]
    (S : Subgroup G) (f : K →* G) (hf : Function.Injective f)
    (P : Sylow 2 K) (hPS : (P : Subgroup K).map f ≤ S)
    (q : K →* Q) (hq : Function.Surjective q)
    (hker : q.ker = center K) (hker2 : IsPGroup 2 q.ker)
    (z : G) (hz2 : z ^ 2 = 1) (hzc : ∀ s ∈ S, Commute z s)
    (t : K) (ht : q t ≠ 1)
    (haction : ∀ x : K, f (t * x * t⁻¹) = z * f x * z⁻¹) :
    t ∈ P ∧ orderOf (q t) = 2 ∧
      ∀ x ∈ P.mapSurjective (f := q) hq, Commute (q t) x := by
  have ht2c : t ^ 2 ∈ center K := by
    rw [mem_center_iff]
    intro x
    have he : t ^ 2 * x * (t ^ 2)⁻¹ = x := by
      apply hf
      calc
        _ = f (t * (t * x * t⁻¹) * t⁻¹) := by
          simp only [pow_two, mul_inv_rev, mul_assoc]
        _ = z * (z * f x * z⁻¹) * z⁻¹ := by rw [haction, haction]
        _ = z ^ 2 * f x * (z ^ 2)⁻¹ := by
          simp only [pow_two, mul_inv_rev, mul_assoc]
        _ = f x := by rw [hz2]; simp
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hqt2 : (q t) ^ 2 = 1 := by
    rw [← map_pow]
    exact show t ^ 2 ∈ q.ker from hker.symm ▸ ht2c
  have hqtp : IsPGroup 2 (zpowers (q t)) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hqt2).isPGroup 2 _
  have hrp : IsPGroup 2 ((zpowers (q t)).comap q) :=
    hqtp.comap_of_ker_isPGroup q hker2
  have htc (x : K) (hx : x ∈ P) : Commute t x := by
    apply mul_inv_eq_iff_eq_mul.mp
    apply hf
    rw [haction, (hzc (f x) (hPS (mem_map_of_mem f hx))).eq]
    simp only [mul_assoc, mul_inv_cancel, mul_one]
  have htN : t ∈ normalizer (P : Set K) := by
    apply centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro x hx
    exact (htc x hx).symm.eq
  have htP : t ∈ P := by
    have hh : t ∈ (zpowers (q t)).comap q ⊓ normalizer (P : Set K) :=
      ⟨mem_zpowers (q t), htN⟩
    rw [hrp.inf_normalizer_sylow P] at hh
    exact hh.2
  refine ⟨htP, orderOf_eq_prime hqt2 ht, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  exact (htc x hx).map q

/-- Returning conjugates of the marked quotient element commute. No
classification of its class, nor involutory lift, is required. -/
theorem returning_quotient_conjugates_commute [Finite K]
    (S U : Subgroup G) [IsMulCommutative U]
    (hU : IsStronglyClosedSet (U : Set G) S ⊤)
    (f : K →* G) (hf : Function.Injective f)
    (P : Sylow 2 K) (hPS : (P : Subgroup K).map f ≤ S)
    (q : K →* Q) (hq : Function.Surjective q) (hker2 : IsPGroup 2 q.ker)
    (z : G) (hzU : z ∈ U) (t : K) (htP : t ∈ P)
    (haction : ∀ x : K, f (t * x * t⁻¹) = z * f x * z⁻¹)
    (a b : P.mapSurjective (f := q) hq)
    (ha : IsConj (q t) (a : Q)) (hb : IsConj (q t) (b : Q)) : Commute a b := by
  let R : Sylow 2 Q := P.mapSurjective (f := q) hq
  have hpre : ((R : Subgroup Q).comap q) = (P : Subgroup K) :=
    comap_map_eq_self (hker2.le_sylow_of_normal P)
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  obtain ⟨h, hh⟩ := isConj_iff.mp hb
  obtain ⟨g0, rfl⟩ := hq g
  obtain ⟨h0, rfl⟩ := hq h
  have hga : q (g0 * t * g0⁻¹) = a := by
    simpa only [map_mul, map_inv] using hg
  have hhb : q (h0 * t * h0⁻¹) = b := by
    simpa only [map_mul, map_inv] using hh
  have hgaP : g0 * t * g0⁻¹ ∈ P := by
    change g0 * t * g0⁻¹ ∈ (P : Subgroup K)
    rw [← hpre]
    change q (g0 * t * g0⁻¹) ∈ R
    rw [hga]
    exact a.property
  have hhbP : h0 * t * h0⁻¹ ∈ P := by
    change h0 * t * h0⁻¹ ∈ (P : Subgroup K)
    rw [← hpre]
    change q (h0 * t * h0⁻¹) ∈ R
    rw [hhb]
    exact b.property
  have hc := (conjugates_commute_of_implementer_mem S U hU f hf (P : Subgroup K)
    hPS z hzU t htP haction _ _ hgaP hhbP
    (isConj_iff.mpr ⟨g0, rfl⟩) (isConj_iff.mpr ⟨h0, rfl⟩)).map q
  rw [hga, hhb] at hc
  exact Subtype.ext hc.eq

/-- A pair of noncommuting returning conjugates in the source-marked class
excludes the inner component action. -/
theorem false_of_central_two_quotient_returning_pair [Finite K]
    (S U : Subgroup G) [IsMulCommutative U]
    (hU : IsStronglyClosedSet (U : Set G) S ⊤)
    (f : K →* G) (hf : Function.Injective f)
    (P : Sylow 2 K) (hPS : (P : Subgroup K).map f ≤ S)
    (q : K →* Q) (hq : Function.Surjective q)
    (hker : q.ker = center K) (hker2 : IsPGroup 2 q.ker)
    (z : G) (hzU : z ∈ U) (hz2 : z ^ 2 = 1)
    (hzc : ∀ s ∈ S, Commute z s)
    (t : K) (ht : q t ≠ 1)
    (haction : ∀ x : K, f (t * x * t⁻¹) = z * f x * z⁻¹)
    (hpair : ∀ (R : Sylow 2 Q) (v : Q), v ∈ R → orderOf v = 2 →
      (∀ x ∈ R, Commute v x) →
      ∃ a b : R, IsConj v (a : Q) ∧ IsConj v (b : Q) ∧ ¬Commute a b) : False := by
  obtain ⟨htP, hto, htc⟩ :=
    central_two_quotient_marker S f hf P hPS q hq hker hker2 z hz2 hzc t ht haction
  obtain ⟨a, b, ha, hb, hab⟩ :=
    hpair (P.mapSurjective (f := q) hq) (q t) (mem_map_of_mem q htP) hto htc
  exact hab (returning_quotient_conjugates_commute S U hU f hf P hPS q hq hker2
    z hzU t htP haction a b ha hb)

end Theory.GroupTheory.MarkedInnerStrongClosure
