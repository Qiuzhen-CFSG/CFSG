module

public import Theory.Character.ModularBlock.BlockBimoduleTrace
public import Theory.Character.ModularBlock.CentralTwoBimoduleVanishing
public import Mathlib.GroupTheory.QuotientGroup.Finite

/-!
# Bimodule traces and normal quotients

The sum of the traces of `x ↦ (z * g) * (x * e) * h`, over a normal subgroup
`Z`, equals `|Z|` times the corresponding trace on the quotient group algebra.
This identity holds over any commutative coefficient ring, for any element `e`.

In the group basis, the inner sum runs once through a fiber of the quotient
map, so it is a coefficient of the image of `e`. The outer sum is a function
of the quotient class, and every class has `|Z|` elements. If all nonidentity
twisted traces vanish, only the untwisted trace remains on the left.
For a central two-subgroup, an integral central idempotent, and odd-order
elements `g,h`, integral twisted-trace vanishing gives exact scaling over the
localization at the characteristic-two prime.

This is the coefficient calculation underlying the central two-subgroup
bimodule trace comparison; see Feit, *The Representation Theory of Finite
Groups*, IV.4.12. The right multiplication uses `h`, with no inverse.
-/

public section
noncomputable section
open scoped BigOperators Classical
namespace ModularBlock.BlockBimoduleTrace
attribute [local instance] Fintype.ofFinite
variable {G R : Type*} [Group G] [Finite G] [CommRing R]

private def quotientFiberEquiv (Z : Subgroup G) [Z.Normal] (a : G) :
    Z ≃ {b : G // QuotientGroup.mk' Z b = QuotientGroup.mk' Z a} where
  toFun z := ⟨a * z, by simp⟩
  invFun b := ⟨a⁻¹ * b, QuotientGroup.eq.mp b.property.symm⟩
  left_inv z := by ext; simp
  right_inv b := by ext; simp

private theorem coeff_quotient_eq_sum_fiber (Z : Subgroup G) [Z.Normal]
    (e : MonoidAlgebra R G) (a : G) :
    (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' Z) e).coeff
      (QuotientGroup.mk' Z a) =
    ∑ b : {b : G // QuotientGroup.mk' Z b = QuotientGroup.mk' Z a}, e.coeff b := by
  classical
  change (e.coeff.mapDomain (QuotientGroup.mk' Z)) (QuotientGroup.mk' Z a) = _
  rw [Finsupp.mapDomain, Finsupp.sum_apply,
    Finsupp.sum_fintype _ _ (by simp)]
  simp only [Finsupp.single_apply]
  rw [← Finset.sum_filter]
  exact Finset.sum_subtype (Finset.univ.filter (fun b : G =>
    QuotientGroup.mk' Z b = QuotientGroup.mk' Z a))
      (fun b => Finset.mem_filter.trans (and_iff_right (Finset.mem_univ b))) _

private theorem sum_quotient_pullback (Z : Subgroup G) [Z.Normal]
    (f : G ⧸ Z → R) :
    ∑ x : G, f (QuotientGroup.mk' Z x) = (Nat.card Z : R) * ∑ x : G ⧸ Z, f x := by
  classical
  rw [← Fintype.sum_fiberwise' (QuotientGroup.mk' Z) f, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective Z q
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  rw [Fintype.card_congr (quotientFiberEquiv Z a).symm, Fintype.card_eq_nat_card]

private def bimultiplicationFiberEquiv (Z : Subgroup G) [Z.Normal] (g h x : G) :
    Z ≃ {b : G // QuotientGroup.mk' Z b =
      QuotientGroup.mk' Z (x⁻¹ * g⁻¹ * x * h⁻¹)} where
  toFun z := ⟨x⁻¹ * ((z : G) * g)⁻¹ * x * h⁻¹, by simp⟩
  invFun b := ⟨x * h⁻¹ * (b : G)⁻¹ * x⁻¹ * g⁻¹, by
    apply (QuotientGroup.eq_one_iff _).mp
    change QuotientGroup.mk' Z _ = 1
    simp only [map_mul, map_inv, b.property]
    group⟩
  left_inv z := by ext; dsimp; group
  right_inv b := by ext; dsimp; group

/-- Summing the twisted traces along a normal subgroup computes its quotient trace. -/
theorem sum_trace_projectedBimultiplication_quotient
    (Z : Subgroup G) [Z.Normal] (e : MonoidAlgebra R G) (g h : G) :
    (∑ z : Z, LinearMap.trace R (MonoidAlgebra R G)
      (projectedBimultiplication e ((z : G) * g) h)) =
    (Nat.card Z : R) * LinearMap.trace R (MonoidAlgebra R (G ⧸ Z))
      (projectedBimultiplication
        (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' Z) e)
        (QuotientGroup.mk' Z g) (QuotientGroup.mk' Z h)) := by
  classical
  simp_rw [trace_projectedBimultiplication]
  rw [Finset.sum_comm]
  have hf (x : G) :
      (∑ z : Z, e.coeff (x⁻¹ * ((z : G) * g)⁻¹ * x * h⁻¹)) =
      (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' Z) e).coeff
        (QuotientGroup.mk' Z (x⁻¹ * g⁻¹ * x * h⁻¹)) := by
    rw [coeff_quotient_eq_sum_fiber]
    exact Fintype.sum_equiv (bimultiplicationFiberEquiv Z g h x)
      (fun z : Z => e.coeff (x⁻¹ * ((z : G) * g)⁻¹ * x * h⁻¹))
      (fun b => e.coeff b) (fun _ => rfl)
  simp_rw [hf, map_mul, map_inv]
  convert! sum_quotient_pullback Z (fun x =>
    (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' Z) e).coeff
      (x⁻¹ * (QuotientGroup.mk' Z g)⁻¹ * x * (QuotientGroup.mk' Z h)⁻¹)) using 1
  congr 3
  exact Subsingleton.elim _ _

/-- Exact quotient trace scaling follows from vanishing of nonidentity twists. -/
theorem trace_quotient_of_twistedTrace_eq_zero
    (Z : Subgroup G) [Z.Normal] (e : MonoidAlgebra R G) (g h : G)
    (hvanish : ∀ z : Z, z ≠ 1 →
      LinearMap.trace R (MonoidAlgebra R G)
        (projectedBimultiplication e ((z : G) * g) h) = 0) :
    LinearMap.trace R (MonoidAlgebra R G) (projectedBimultiplication e g h) =
      (Nat.card Z : R) * LinearMap.trace R (MonoidAlgebra R (G ⧸ Z))
        (projectedBimultiplication
          (MonoidAlgebra.mapDomainRingHom R (QuotientGroup.mk' Z) e)
          (QuotientGroup.mk' Z g) (QuotientGroup.mk' Z h)) := by
  classical
  rw [← sum_trace_projectedBimultiplication_quotient]
  symm
  simpa using Finset.sum_eq_single (1 : Z)
    (fun z _ hz => hvanish z hz) (by simp)

/-- Exact integral bimodule trace scaling under a central two-subgroup quotient.
Right multiplication uses `h`, without an inverse. -/
theorem integralTrace_centralTwo_quotient
    (d : PrincipalBlockConstruction.PrincipalCongruenceBlockData G)
    (Z : Subgroup G) [Z.Normal]
    (hcentral : Z ≤ Subgroup.center G) (hZ : IsPGroup 2 Z)
    (e : MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)
    (he : IsIdempotentElem e) (hec : e ∈ Set.center (MonoidAlgebra _ G))
    (g h : G) (hg : Odd (orderOf g)) (hh : Odd (orderOf h)) :
    LinearMap.trace (Localization.AtPrime d.primeIdeal)
      (MonoidAlgebra (Localization.AtPrime d.primeIdeal) G)
      (projectedBimultiplication e g h) =
    (Nat.card Z : Localization.AtPrime d.primeIdeal) *
      LinearMap.trace (Localization.AtPrime d.primeIdeal)
        (MonoidAlgebra (Localization.AtPrime d.primeIdeal) (G ⧸ Z))
        (projectedBimultiplication
          (MonoidAlgebra.mapDomainRingHom _ (QuotientGroup.mk' Z) e)
          (QuotientGroup.mk' Z g) (QuotientGroup.mk' Z h)) := by
  apply trace_quotient_of_twistedTrace_eq_zero
  intro z hz
  apply integralTrace_centralTwo_twist_eq_zero d e he hec z g h
    (hcentral z.property) (fun heq => hz (Subtype.ext heq)) _ hg hh
  obtain ⟨n, hn⟩ := isPGroup_iff_pow_pow_eq_one.mp hZ z
  exact ⟨n, congrArg (fun w : Z => (w : G)) hn⟩

end ModularBlock.BlockBimoduleTrace
