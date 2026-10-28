module
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Centralizer images from transitivity on an involution coset

Let R be the kernel of the action of I on V. If t normalizes I and
centralizes V, every I-conjugate of t lies in Rt. Transitivity on the
square-one elements of this coset permits an R-adjustment of each actor
into C_I(t). Thus restriction to C_I(t) preserves any surjective quotient
of I with kernel R.

This is the Frattini argument in Aschbacher--Smith, Quasithin Groups,
14.3.21(2), printed p.998. Only the outside coset is used.
-/

public section

open Subgroup

namespace Subgroup
variable {G K : Type*} [Group G] [Group K]

/-- The centralizer still maps onto the original quotient when the kernel
is transitive on the square-one elements in the coset of t. -/
theorem centralizer_restriction_surjective_of_involution_coset_transitivity
    (I R V : Subgroup G) (hRI : R ≤ I)
    (hIV : I ≤ normalizer (V : Set G))
    (hker : I ⊓ centralizer (V : Set G) = R)
    (t : G) (htI : t ∈ normalizer (I : Set G))
    (htV : t ∈ centralizer (V : Set G)) (ht2 : t ^ 2 = 1)
    (horbit : ∀ x : G, x ^ 2 = 1 → x * t⁻¹ ∈ R →
      ∃ r ∈ R, r⁻¹ * x * r = t)
    (π : I →* K) (hπ : Function.Surjective π)
    (hkπ : π.ker = R.subgroupOf I) :
    Function.Surjective (π.comp (inclusion (show I ⊓ centralizer ({t} : Set G) ≤ I from inf_le_left))) := by
  intro k
  obtain ⟨i, hi⟩ := hπ k
  let x : G := (i : G) * t * (i : G)⁻¹
  have hx2 : x ^ 2 = 1 := by
    change (MulAut.conj (i : G) t) ^ 2 = 1
    rw [← map_pow, ht2, map_one]
  have hxR : x * t⁻¹ ∈ R := by
    rw [← hker]
    constructor
    · change x * t⁻¹ ∈ I
      have htconj : t * (i : G)⁻¹ * t⁻¹ ∈ I :=
        (mem_normalizer_iff.mp htI _).mp (I.inv_mem i.property)
      simpa only [x, mul_assoc] using I.mul_mem i.property htconj
    · have hxC : x ∈ centralizer (V : Set G) :=
        (mem_normalizer_iff.mp (normalizer_le_normalizer_centralizer V (hIV i.property)) _).mp htV
      exact (centralizer (V : Set G)).mul_mem hxC ((centralizer (V : Set G)).inv_mem htV)
  obtain ⟨r, hr, hrt⟩ := horbit x hx2 hxR
  let c : ↥(I ⊓ centralizer ({t} : Set G)) := ⟨r⁻¹ * (i : G),
    I.mul_mem (I.inv_mem (hRI hr)) i.property,
    mem_centralizer_singleton_iff.mpr (by
      apply mul_inv_eq_iff_eq_mul.mp
      calc (r⁻¹ * (i : G)) * t * (r⁻¹ * (i : G))⁻¹ = r⁻¹ * x * r := by dsimp [x]; group
           _ = t := hrt)⟩
  refine ⟨c, ?_⟩
  have hrπ : π (⟨r, hRI hr⟩ : I) = 1 := by
    change (⟨r, hRI hr⟩ : I) ∈ π.ker
    rw [hkπ]
    exact hr
  change π ((⟨r, hRI hr⟩ : I)⁻¹ * i) = k
  rw [map_mul, map_inv, hrπ, inv_one, one_mul, hi]
end Subgroup
