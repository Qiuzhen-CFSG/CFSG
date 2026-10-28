module

public import Theory.GroupTheory.MarkedInnerStrongClosure

/-!
# Marked inner fusion through a central two-quotient

The centralizing-factor argument only needs the inner implementer to belong
to the component Sylow. When the center is a two-group, its square is central,
so its cyclic subgroup is a two-group and Sylow-normalizer containment supplies
that membership. The implementer need not itself have order two.

The image of the original Sylow under a central-two quotient is Sylow, and
its inverse image is the original Sylow. Consequently returning conjugates
of the quotient implementer lift to returning conjugates of the implementer.
Abelian strong closure forces those lifts, hence their quotient images, to
commute. This excludes a quotient with one involution class and noncommuting
involutions in its Sylow two-subgroup.

Source application: Aschbacher--Smith, 1.1.5(3)(b) and the component inspection
in Proposition 2.2.2, printed pp.501--503 and 519--520 (1 March 2004 manuscript).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory.MarkedInnerStrongClosure
variable {G K Q : Type*} [Group G] [Group K] [Group Q]

/-- Once the actual implementer lies in the component Sylow, its returning
conjugates commute. Neither the implementer nor its centralizing factor is
assumed to belong to the strongly closed subgroup. -/
theorem conjugates_commute_of_implementer_mem
    (S U : Subgroup G) [IsMulCommutative U]
    (hU : IsStronglyClosedSet (U : Set G) S ⊤)
    (f : K →* G) (hf : Function.Injective f)
    (P : Subgroup K) (hPS : P.map f ≤ S)
    (z : G) (hzU : z ∈ U) (t : K) (htP : t ∈ P)
    (haction : ∀ x : K, f (t * x * t⁻¹) = z * f x * z⁻¹)
    (a b : K) (haP : a ∈ P) (hbP : b ∈ P)
    (ha : IsConj t a) (hb : IsConj t b) : Commute a b := by
  let c : G := (f t)⁻¹ * z
  have hcS : c ∈ S := S.mul_mem (S.inv_mem (hPS (mem_map_of_mem f htP))) (hU.1 hzU)
  have hcf (x : K) : Commute c (f x) := by
    apply mul_inv_eq_iff_eq_mul.mp
    change ((f t)⁻¹ * z) * f x * ((f t)⁻¹ * z)⁻¹ = f x
    calc
      _ = (f t)⁻¹ * (z * f x * z⁻¹) * f t := by group
      _ = (f t)⁻¹ * f (t * x * t⁻¹) * f t := by rw [haction]
      _ = f x := by simp only [map_mul, map_inv]; group
  have hz : z = f t * c := by dsimp [c]; group
  have hforced (a : K) (haP : a ∈ P) (ha : IsConj t a) : f a * c ∈ U := by
    obtain ⟨g, hg⟩ := isConj_iff.mp ha
    have he : f g * z * (f g)⁻¹ = f a * c := by
      rw [hz]
      calc
        _ = f g * f t * (c * (f g)⁻¹) := by group
        _ = f g * f t * ((f g)⁻¹ * c) := by rw [(hcf g).inv_right.eq]
        _ = f (g * t * g⁻¹) * c := by simp only [map_mul, map_inv]; group
        _ = f a * c := by rw [hg]
    have hs : f a * c ∈ S := S.mul_mem (hPS (mem_map_of_mem f haP)) hcS
    have hu := hU.2 z hzU (f g)⁻¹ (mem_top _) (by simpa only [inv_inv, he] using hs)
    change f a * c ∈ (U : Set G)
    simpa only [inv_inv, he] using hu
  have hh := congrArg Subtype.val
    (mul_comm (⟨f a * c, hforced a haP ha⟩ : U) ⟨f b * c, hforced b hbP hb⟩)
  change (f a * c) * (f b * c) = (f b * c) * (f a * c) at hh
  have he : f a * f b * (c * c) = f b * f a * (c * c) := by
    calc
      _ = (f a * c) * (f b * c) := ((hcf b).mul_mul_mul_comm (f a) c).symm
      _ = (f b * c) * (f a * c) := hh
      _ = f b * f a * (c * c) := (hcf a).mul_mul_mul_comm (f b) c
  exact hf (by simpa only [map_mul] using mul_right_cancel he)

/-- A two-group center permits the obstruction to be applied in the actual
central quotient. All quotient conjugates are lifted inside the original
component and the original component Sylow. -/
theorem false_of_central_two_quotient_fusion [Finite K]
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
    (hclass : ∀ a b : Q, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    (hpair : ∀ R : Sylow 2 Q,
      ∃ a b : R, orderOf a = 2 ∧ orderOf b = 2 ∧ ¬Commute a b) : False := by
  have ht2c : t ^ 2 ∈ center K := by
    rw [mem_center_iff]
    intro x
    have he : t ^ 2 * x * (t ^ 2)⁻¹ = x := by
      apply hf
      calc
        _ = f (t * (t * x * t⁻¹) * t⁻¹) := by simp only [pow_two, mul_inv_rev, mul_assoc]
        _ = z * (z * f x * z⁻¹) * z⁻¹ := by rw [haction, haction]
        _ = z ^ 2 * f x * (z ^ 2)⁻¹ := by simp only [pow_two, mul_inv_rev, mul_assoc]
        _ = f x := by rw [hz2]; simp
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hqt2 : (q t) ^ 2 = 1 := by
    rw [← map_pow]
    exact show t ^ 2 ∈ q.ker from hker.symm ▸ ht2c
  have hqtp : IsPGroup 2 (zpowers (q t)) :=
    (IsElementaryAbelian.zpowers_of_pow_eq_one (p := 2) hqt2).isPGroup 2 _
  have hrp : IsPGroup 2 ((zpowers (q t)).comap q) := hqtp.comap_of_ker_isPGroup q hker2
  have htN : t ∈ normalizer (P : Set K) := by
    apply centralizer_le_normalizer
    rw [mem_centralizer_iff]
    intro x hx
    have he : t * x * t⁻¹ = x := hf (by
      rw [haction, (hzc (f x) (hPS (mem_map_of_mem f hx))).eq]
      simp only [mul_assoc, mul_inv_cancel, mul_one])
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have htP : t ∈ P := by
    have hh : t ∈ (zpowers (q t)).comap q ⊓ normalizer (P : Set K) :=
      ⟨mem_zpowers (q t), htN⟩
    rw [hrp.inf_normalizer_sylow P] at hh
    exact hh.2
  let R : Sylow 2 Q := P.mapSurjective (f := q) hq
  have hpre : ((R : Subgroup Q).comap q) = (P : Subgroup K) :=
    comap_map_eq_self (hker2.le_sylow_of_normal P)
  have hto : orderOf (q t) = 2 := orderOf_eq_prime hqt2 ht
  obtain ⟨a, b, ha, hb, hab⟩ := hpair R
  have ha' : orderOf (a : Q) = 2 := by simpa only [Subgroup.orderOf_coe] using ha
  have hb' : orderOf (b : Q) = 2 := by simpa only [Subgroup.orderOf_coe] using hb
  obtain ⟨g, hg⟩ := isConj_iff.mp (hclass (q t) a hto ha')
  obtain ⟨h, hh⟩ := isConj_iff.mp (hclass (q t) b hto hb')
  obtain ⟨g0, rfl⟩ := hq g
  obtain ⟨h0, rfl⟩ := hq h
  have hga : q (g0 * t * g0⁻¹) = a := by simpa only [map_mul, map_inv] using hg
  have hhb : q (h0 * t * h0⁻¹) = b := by simpa only [map_mul, map_inv] using hh
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
  exact hab (Subtype.ext hc.eq)

end Theory.GroupTheory.MarkedInnerStrongClosure
