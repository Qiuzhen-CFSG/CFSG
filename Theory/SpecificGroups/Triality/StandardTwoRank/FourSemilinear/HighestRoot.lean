module

public import Theory.SpecificGroups.Triality.OuterOddSubgroups
public import Theory.SpecificGroups.Triality.RadicalCoordinates.Centers.HighestRoot
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Noninner involutions move the highest-root subgroup in binary triality

An involution outside the inner group has outer image of order two. In any
inner--coefficient expression this order divides the coefficient's order.
The coefficient therefore cannot fix the actual base subfield pointwise:
the cubic extension has degree three, so its group of automorphisms over
the base has order three. This holds for every positive binary exponent.

If the involution preserves the positive Sylow subgroup, its inner factor
lies in the Borel, since coefficient automorphisms preserve that subgroup.
The unipotent factor centralizes the highest-root curve and the torus factor
scales its parameter. Fixing the entire highest-root subgroup would make the
coefficient map a scalar map on the base field; evaluation at one makes the scalar
one, contradicting the preceding parity calculation. All computations use
the actual integral Geck curves and the faithful elementary central quotient.
No conjugacy to a pure field involution or fixed-group recognition is used.

Source: GLS3 §§2.3--2.5, especially 2.5.12(d,f)
(`refs/KGroup/GLS3/chapter2.tex`), for Aschbacher--Smith G.9.3,
printed p.356 (`refs/quasithin.pdf`).
-/

open Triality.Standard Triality.Standard.OuterOdd
open Triality.Standard.OuterOdd.Coverage
open Triality.Standard.Parabolics Triality.Standard.ConcreteBruhat
open Triality.Standard.ConcreteBruhat.FixedDescent
open Triality.Standard.PositiveCoordinates
open Triality.Standard.RadicalCoordinates.Centers
open RootPairing.IntegralGeckConstruction
open Theory.AlgebraicGroup.StandardRootSystem
public section
noncomputable section
namespace Triality.Standard.TwoRank.FourSemilinear
local instance : DecidableEq ((typeDRootPairing_base 2).support ⊕ TypeDRootIndex (2 + 2)) :=
  instDecidableEqSum

/-- A noninner involution has an even-order coefficient factor in every inner--coefficient expression. -/
theorem coefficient_even (P : Parameters) (a : MulAut (Carrier P))
    (ha : a ^ 2 = 1) (hi : a ∉ MulAut.innerSubgroup (Carrier P))
    (g : Carrier P) (e : CoefficientAut P)
    (he : a = MulAut.conj g * coefficientAction P e) : 2 ∣ orderOf e := by
  let q : MulAut (Carrier P) →* MulAut.Outer (Carrier P) := QuotientGroup.mk' _
  have hqa : orderOf (q a) = 2 := orderOf_eq_prime
    (by rw [← map_pow, ha, map_one]) (fun h => hi ((QuotientGroup.eq_one_iff a).mp h))
  have hqe : q a = outerCoefficientAction P e := by
    have hg : q (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨g, rfl⟩
    rw [he, map_mul, hg, one_mul]
    rfl
  rw [hqe] at hqa
  exact hqa ▸ orderOf_map_dvd (outerCoefficientAction P) e

/-- The actual extension field has degree three over its Frobenius fixed field. -/
theorem extensionField_finrank_fixedField (P : Parameters) :
    Module.finrank (fixedField P) (ExtensionField P) = 3 := by
  have hc := Module.natCard_eq_pow_finrank (K := fixedField P) (V := ExtensionField P)
  rw [card_extensionField, card_fixedField] at hc
  exact (Nat.pow_right_injective (by have := P.q_ge_two; omega)) hc.symm

/-- An even-order coefficient automorphism cannot fix the actual base field
pointwise, since the relative automorphism group has odd order three. -/
theorem coefficient_not_fixed_base_of_parameters (P : Parameters) (e : CoefficientAut P)
    (he : 2 ∣ orderOf e) : ¬ ∀ t : fixedField P, e t.val = t.val := by
  intro h
  let E := ExtensionField P
  let k := fixedField P
  let f : E ≃ₐ[k] E := AlgEquiv.ofRingEquiv (f := e) h
  have hc : Nat.card (E ≃ₐ[k] E) = 3 := by
    rw [IsGalois.card_aut_eq_finrank, extensionField_finrank_fixedField P]
  have hf : f ^ 3 = 1 := by simpa only [hc] using (pow_card_eq_one' (x := f))
  have hep : e ^ 3 = 1 := congrArg AlgEquiv.toRingEquiv hf
  have : 2 ∣ 3 := he.trans (orderOf_dvd_of_pow_eq_one hep)
  norm_num at this

/-- An even-order coefficient automorphism of GF(64) cannot fix GF(4) pointwise. -/
theorem coefficient_not_fixed_base (e : CoefficientAut (binaryParameters 2 (Nat.succ_pos 1)))
    (he : 2 ∣ orderOf e) :
    ¬ ∀ t : fixedField (binaryParameters 2 (Nat.succ_pos 1)), e t.val = t.val :=
  coefficient_not_fixed_base_of_parameters (binaryParameters 2 (Nat.succ_pos 1)) e he

private theorem coefficient_curve (P : Parameters) (e : CoefficientAut P)
    (i : Fin 12) (t : ExtensionField P) :
    coefficientSplit P e (curve P i t) = curve P i (e t) := by
  apply Subtype.ext
  apply Units.ext
  change (rootCurveMatrix _ (rootIndex i) t).map e = rootCurveMatrix _ (rootIndex i) (e t)
  ext j k
  simp [rootCurveMatrix, specializeMatrix, Matrix.one_apply]

private theorem coefficient_carrierToSplit (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) (x : Carrier P) :
    carrierToSplit P hp (coefficientAction P e x) =
      coefficientSplit P e (carrierToSplit P hp x) := by
  obtain ⟨y, hy⟩ := toCarrier_surjective P x
  rw [← hy]
  calc
    _ = carrierToSplit P hp (toCarrier P (coefficientElementary P e y)) :=
      congrArg (carrierToSplit P hp) (coefficientCarrier_toCarrier P e y)
    _ = elementaryInclusion P (coefficientElementary P e y) := carrierToSplit_toCarrier P hp _
    _ = coefficientSplit P e (elementaryInclusion P y) := rfl
    _ = _ := congrArg (coefficientSplit P e) (carrierToSplit_toCarrier P hp y).symm

private theorem coefficient_unipotent (P : Parameters) (hp : P.prime = 2)
    (e : CoefficientAut P) : (unipotent P).map (coefficientAction P e).toMonoidHom = unipotent P := by
  have pos (f : CoefficientAut P) (y : SplitGroup P) (hy : y ∈ positiveSubgroup P) :
      coefficientSplit P f y ∈ positiveSubgroup P := by
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨i, t, rfl⟩ := hy
      rw [show coefficientSplit P f (positiveRoot P i t) = positiveRoot P i (f t) from
        coefficientSplit_positive P f _ t]
      exact Subgroup.subset_closure ⟨i, f t, rfl⟩
    | one => simp
    | mul x y _ _ hx hy => simpa only [map_mul] using (positiveSubgroup P).mul_mem hx hy
    | inv x _ hx => simpa only [map_inv] using (positiveSubgroup P).inv_mem hx
  have preserves (f : CoefficientAut P) {x : Carrier P} (hx : x ∈ unipotent P) :
      coefficientAction P f x ∈ unipotent P := by
    apply (mem_descend_iff P hp (positiveSubgroup P) _).mpr
    rw [coefficient_carrierToSplit]
    exact pos f _ ((mem_descend_iff P hp (positiveSubgroup P) x).mp hx)
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact preserves e hx
  · intro x hx
    refine ⟨coefficientAction P e⁻¹ x, preserves e⁻¹ hx, ?_⟩
    change (coefficientAction P e) (coefficientAction P e⁻¹ x) = x
    rw [map_inv]
    exact (coefficientAction P e).apply_symm_apply x

private theorem split_torus_scales_highest (P : Parameters) (hp : P.prime = 2)
    {t : SplitGroup P} (ht : t ∈ splitTorus P) :
    ∃ c : ExtensionField P, c ≠ 0 ∧ ∀ x,
      t * curve P 11 x * t⁻¹ = curve P 11 (c * x) := by
  induction ht using Subgroup.closure_induction with
  | mem t ht =>
    obtain ⟨i, s, rfl⟩ := ht
    exact ⟨_, zpow_ne_zero _ s.ne_zero, fun x => torusWord_curve_conjugate P hp i s 11 x⟩
  | one => exact ⟨1, one_ne_zero, by simp⟩
  | mul t u _ _ ht hu =>
    obtain ⟨c, hc, ht⟩ := ht
    obtain ⟨d, hd, hu⟩ := hu
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    intro x
    calc
      (t * u) * curve P 11 x * (t * u)⁻¹ = t * (u * curve P 11 x * u⁻¹) * t⁻¹ := by group
      _ = curve P 11 ((c * d) * x) := by rw [hu, ht, mul_assoc]
  | inv t _ ht =>
    obtain ⟨c, hc, ht⟩ := ht
    refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
    intro x
    have h := ht (c⁻¹ * x)
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul] at h
    rw [← h]
    group

private theorem borel_coefficient_not_fix_highest (P : Parameters) (hp : P.prime = 2)
    (a : MulAut (Carrier P)) (ha : a ^ 2 = 1)
    (hi : a ∉ MulAut.innerSubgroup (Carrier P))
    (g : Carrier P) (hg : g ∈ borel P)
    (e : CoefficientAut P)
    (he : a = MulAut.conj g * coefficientAction P e) :
    ¬ highestRoot P ≤ a.fixedSubgroup := by
  intro hz
  obtain ⟨u, hu, t, ht, rfl⟩ := (borel_eq_mul P hp).le hg
  obtain ⟨c, _, hc⟩ := split_torus_scales_highest P hp
    ((mem_descend_iff P hp (splitTorus P) t).mp ht)
  have hscalar (z : fixedField P) : c * e z.val = z.val := by
    have hfix := hz ((highestHom_range P hp).le ⟨Multiplicative.ofAdd z, rfl⟩)
    rw [MulAut.mem_fixedSubgroup] at hfix
    have hh := congrArg (carrierToSplit P hp) hfix
    change carrierToSplit P hp (a (highestHom P hp (Multiplicative.ofAdd z))) = _ at hh
    rw [he] at hh
    change carrierToSplit P hp ((u * t) * coefficientAction P e
      (toCarrier P (elementaryHighestHom P hp (Multiplicative.ofAdd z))) * (u * t)⁻¹) = _ at hh
    simp only [highestHom, MonoidHom.comp_apply, map_mul, map_inv, coefficient_carrierToSplit P hp, carrierToSplit_toCarrier P hp,
      elementaryHighestHom_val P hp, coefficient_curve P e] at hh
    have hu' := (mem_descend_iff P hp (positiveSubgroup P) u).mp hu
    have hcomm := (Subgroup.mem_centralizer_iff.mp
      (positiveSubgroup_le_centralizer_highestCurve P (c * e z.val) hu'))
      _ (Set.mem_singleton _)
    have hre : (carrierToSplit P hp u * carrierToSplit P hp t) * curve P 11 (e z.val) *
        (carrierToSplit P hp u * carrierToSplit P hp t)⁻¹ = curve P 11 (c * e z.val) := by
      calc
        _ = carrierToSplit P hp u * (carrierToSplit P hp t * curve P 11 (e z.val) *
          (carrierToSplit P hp t)⁻¹) * (carrierToSplit P hp u)⁻¹ := by group
        _ = _ := by rw [hc, ← hcomm]; group
    apply highestCurve_injective P
    exact hre.symm.trans hh
  have hc1 : c = 1 := by simpa using hscalar 1
  exact coefficient_not_fixed_base_of_parameters P e (coefficient_even P a ha hi _ e he)
    (fun z => by simpa [hc1] using hscalar z)

/-- A noninner involution preserving the actual positive Sylow subgroup cannot
fix its entire highest-root subgroup. All coverage and Borel premises are discharged. -/
theorem binary_noninner_involution_not_fix_highestRoot (n : ℕ) (hn : 0 < n)
    [IsSimpleGroup (BinaryCarrier n hn)]
    [Group.IsPerfect (BinaryCarrier n hn)]
    (a : MulAut (BinaryCarrier n hn)) (ha : a ^ 2 = 1)
    (hi : a ∉ MulAut.innerSubgroup (BinaryCarrier n hn))
    (hU : (unipotent (binaryParameters n hn)).map a.toMonoidHom =
      unipotent (binaryParameters n hn)) :
    ¬ highestRoot (binaryParameters n hn) ≤ a.fixedSubgroup := by
  let P := binaryParameters n hn
  obtain ⟨g, e, he⟩ := Coverage.binary_inner_coefficient n hn a
  have hg : g ∈ borel P := by
    rw [← normalizer_unipotent_eq_borel P rfl]
    apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    calc
      (unipotent P).map (MulAut.conj g).toMonoidHom =
          ((unipotent P).map (coefficientAction P e).toMonoidHom).map
            (MulAut.conj g).toMonoidHom := by rw [coefficient_unipotent P rfl]
      _ = (unipotent P).map a.toMonoidHom := by
        rw [Subgroup.map_map, he]
        rfl
      _ = unipotent P := hU
  exact borel_coefficient_not_fix_highest P rfl a ha hi g hg e he

/-- A noninner involution preserving the actual positive Sylow subgroup cannot
fix its entire highest-root subgroup. All coverage and Borel premises are discharged. -/
theorem noninner_involution_not_fix_highestRoot
    [IsSimpleGroup (BinaryCarrier 2 (Nat.succ_pos 1))]
    [Group.IsPerfect (BinaryCarrier 2 (Nat.succ_pos 1))]
    (a : MulAut (BinaryCarrier 2 (Nat.succ_pos 1))) (ha : a ^ 2 = 1)
    (hi : a ∉ MulAut.innerSubgroup (BinaryCarrier 2 (Nat.succ_pos 1)))
    (hU : (unipotent (binaryParameters 2 (Nat.succ_pos 1))).map a.toMonoidHom =
      unipotent (binaryParameters 2 (Nat.succ_pos 1))) :
    ¬ highestRoot (binaryParameters 2 (Nat.succ_pos 1)) ≤ a.fixedSubgroup :=
  binary_noninner_involution_not_fix_highestRoot 2 (Nat.succ_pos 1) a ha hi hU

end Triality.Standard.TwoRank.FourSemilinear
