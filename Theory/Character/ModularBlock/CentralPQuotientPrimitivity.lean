module

public import Theory.Character.ModularBlock.CentralNilpotentQuotient
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Primitive central idempotents under central p-group quotients

For a finite group over a finite commutative ring of characteristic `p`,
quotienting by a central p-subgroup preserves primitive central idempotents.
In particular, this applies to characteristic two and does not require an
augmentation-one hypothesis.

Coset representatives express the quotient kernel as the left ideal generated
by the elements `z - 1`. These generators are central, and their p-power
orders make them nilpotent in characteristic `p`. The general lifting result
in `CentralNilpotentQuotient` then preserves primitivity.

This is the central p-subgroup block correspondence used in Feit,
*The Representation Theory of Finite Groups*, IV.4.12. The proof here works
directly with group algebras and their central idempotents.
-/

namespace ModularBlock

open MonoidAlgebra

variable {k G : Type*} [CommRing k] [Group G]

private lemma quotient_ker_eq_span (Z : Subgroup G) [Z.Normal] :
    RingHom.ker (mapDomainRingHom k (QuotientGroup.mk' Z)) =
      Ideal.span (Set.range fun z : Z => (single (z : G) 1 : MonoidAlgebra k G) - 1) := by
  classical
  let q := QuotientGroup.mk' Z
  let t : G ⧸ Z → G := Function.surjInv (QuotientGroup.mk'_surjective Z)
  have ht (g : G ⧸ Z) : q (t g) = g := Function.surjInv_eq _ g
  let I : Ideal (MonoidAlgebra k G) :=
    Ideal.span (Set.range fun z : Z => (single (z : G) 1 : MonoidAlgebra k G) - 1)
  have hdiff (x : MonoidAlgebra k G) : x - mapDomain t (mapDomain q x) ∈ I := by
    induction x using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy =>
      simpa only [mapDomain_add, add_sub_add_comm] using I.add_mem hx hy
    | single g a =>
      simp only [mapDomain_single]
      have hz : (t (q g))⁻¹ * g ∈ Z := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q ((t (q g))⁻¹ * g) = 1
        rw [map_mul, map_inv, ht, inv_mul_cancel]
      have hm := I.mul_mem_left (single (t (q g)) a)
        (Ideal.subset_span (Set.mem_range_self (⟨(t (q g))⁻¹ * g, hz⟩ : Z)))
      simpa only [mul_sub, single_mul_single, mul_inv_cancel_left, mul_one] using hm
  apply le_antisymm
  · intro x hx
    have hx0 : mapDomain q x = 0 := RingHom.mem_ker.mp hx
    simpa only [hx0, mapDomain_zero, sub_zero] using hdiff x
  · apply Ideal.span_le.mpr
    rintro _ ⟨z, rfl⟩
    apply RingHom.mem_ker.mpr
    rw [map_sub, map_one]
    simp [(QuotientGroup.eq_one_iff _).mpr z.property, one_def]

private lemma quotient_map_surjective (Z : Subgroup G) [Z.Normal] :
    Function.Surjective (mapDomainRingHom k (QuotientGroup.mk' Z)) := by
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, map_zero _⟩
  | add a b ha hb =>
    obtain ⟨x, rfl⟩ := ha
    obtain ⟨y, rfl⟩ := hb
    exact ⟨x + y, map_add _ _ _⟩
  | single q r =>
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z q
    exact ⟨single g r, by simp⟩

private lemma single_sub_one_central (Z : Subgroup G) (hz : Z ≤ Subgroup.center G) (z : Z) :
    (single (z : G) 1 : MonoidAlgebra k G) - 1 ∈ Set.center (MonoidAlgebra k G) := by
  apply (Subring.center (MonoidAlgebra k G)).sub_mem _ (Subring.center _).one_mem
  apply Semigroup.mem_center_iff.mpr
  intro a
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp [add_mul, mul_add, ha, hb]
  | single g a => simp [Subgroup.mem_center_iff.mp (hz z.property) g]

private lemma single_sub_one_nilpotent (p : ℕ) [Fact p.Prime] [CharP k p]
    (Z : Subgroup G) (hZ : IsPGroup p Z) (z : Z) :
    IsNilpotent ((single (z : G) 1 : MonoidAlgebra k G) - 1) := by
  let : CharP (MonoidAlgebra k G) p := charP_of_injective_algebraMap' k p
  obtain ⟨n, hn⟩ := hZ.exists_pow_pow_eq_one z
  refine ⟨p ^ n, ?_⟩
  rw [sub_pow_char_pow_of_commute p n (Commute.one_right _)]
  have hg : (z : G) ^ (p ^ n) = 1 := congrArg Subtype.val hn
  simp [single_pow, hg, one_def]

/-- A central p-group quotient preserves primitive central idempotents over
any finite commutative coefficient ring of characteristic `p`. -/
public theorem mapDomain_isCentrallyPrimitive_of_central_pGroup
    [Finite k] [Finite G] (p : ℕ) [Fact p.Prime] [CharP k p]
    (Z : Subgroup G) [Z.Normal] (hcentral : Z ≤ Subgroup.center G)
    (hZ : IsPGroup p Z) (e : MonoidAlgebra k G) (he : IsCentrallyPrimitive e) :
    IsCentrallyPrimitive (mapDomainRingHom k (QuotientGroup.mk' Z) e) := by
  classical
  let : Fintype k := Fintype.ofFinite k
  let : Fintype G := Fintype.ofFinite G
  let : Finite (MonoidAlgebra k G) :=
    Finite.of_injective MonoidAlgebra.coeff MonoidAlgebra.coeff_injective
  apply he.map_of_central_nilpotent_ker
    (mapDomainRingHom k (QuotientGroup.mk' Z)) (quotient_map_surjective Z)
    (Set.range fun z : Z => (single (z : G) 1 : MonoidAlgebra k G) - 1)
    (quotient_ker_eq_span Z)
  rintro _ ⟨z, rfl⟩
  exact ⟨single_sub_one_central Z hcentral z, single_sub_one_nilpotent p Z hZ z⟩

/-- In characteristic two, quotienting by a central two-subgroup preserves
primitivity. No augmentation hypothesis is needed. -/
public theorem mapDomain_isCentrallyPrimitive_of_central_twoGroup
    [Finite k] [Finite G] [CharP k 2]
    (Z : Subgroup G) [Z.Normal] (hcentral : Z ≤ Subgroup.center G)
    (hZ : IsPGroup 2 Z) (e : MonoidAlgebra k G) (he : IsCentrallyPrimitive e) :
    IsCentrallyPrimitive (mapDomainRingHom k (QuotientGroup.mk' Z) e) :=
  mapDomain_isCentrallyPrimitive_of_central_pGroup 2 Z hcentral hZ e he

end ModularBlock
