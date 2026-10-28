module

public import Theory.SpecificGroups.PSL2.BinaryAutomorphismOrder
public import Theory.SpecificGroups.PSL2.ElementaryAutomorphisms.Bounds.FieldInvolution

/-!
# The half-degree formula for an outer binary SL₂ involution

Semilinear coverage and the faithful SL₂-to-PSL₂ quotient in characteristic
two retain the actual formula: an outer involution is inner times the
half-degree Frobenius. Cyclicity and the order of the finite-field automorphism
group identify this Frobenius on any field carrier, not just a chosen GF model.
This form is used by the Schur-trace calculation in
`Theory.Representation.SL2.SchurOuterPeriod`.

Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.1(2),
manuscript p.22; GLS, Volume 2, Theorem 26.24.
-/

public section

open scoped MatrixGroups
namespace Theory.PSL2
variable {K : Type*} [Field K] [Finite K] [CharP K 2]

private theorem frobenius_order_of_card {r : ℕ} (hc : Nat.card K = 2 ^ r) :
    orderOf (frobeniusEquiv K 2) = r := by
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  let f : (K ≃ₐ[ZMod 2] K) →* (K ≃+* K) :=
    { toFun := AlgEquiv.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun a b h => AlgEquiv.ext fun x =>
    DFunLike.congr_fun h x
  have he : f (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) =
      frobeniusEquiv K 2 := by
    ext x
    change x ^ Fintype.card (ZMod 2) = x ^ 2
    rw [ZMod.card]
  rw [← he, orderOf_injective f hf,
    FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
  apply (Nat.pow_right_injective (by decide : 2 ≤ 2))
  simpa only [Nat.card_zmod] using (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)).symm.trans hc

private theorem field_involution_eq {r : ℕ} (hr : 0 < r)
    (hc : Nat.card K = 2 ^ r) (δ : K ≃+* K) (hδ : orderOf δ = 2) :
    Even r ∧ δ = iterateFrobeniusEquiv K 2 (r / 2) := by
  let : IsCyclic (K ≃+* K) := OuterSolvable.finiteFieldAut_isCyclic
  let : Finite (K ≃+* K) := Finite.of_injective
    (fun a : K ≃+* K => (a : K → K)) DFunLike.coe_injective
  have he : Even r := even_iff_two_dvd.mpr (by
    have hd := orderOf_dvd_natCard δ
    rwa [hδ, FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hc] at hd)
  refine ⟨he, IsCyclic.eq_of_orderOf_eq_two hδ ?_⟩
  have horder := frobenius_order_of_card hc
  have hh := orderOf_pow_orderOf_div (x := frobeniusEquiv K 2)
    (horder.symm ▸ hr.ne') (horder.symm ▸ even_iff_two_dvd.mp he)
  simpa only [iterateFrobeniusEquiv_eq_pow, horder] using hh

/-- Semilinear coverage retains the actual half-degree Frobenius map. -/
theorem sl2_outer_involution_formula {r : ℕ} (hr : 0 < r)
    (hc : Nat.card K = 2 ^ r) (a : MulAut SL(2,K)) (ha : a ^ 2 = 1)
    (hout : a ∉ MulAut.innerSubgroup SL(2,K)) :
    Even r ∧ ∃ c : SL(2,K), a = MulAut.conj c *
      sl2FieldAut (iterateFrobeniusEquiv K 2 (r / 2)) := by
  let q := sl2QuotientEquiv K
  let b := MulAut.congr q a
  have hb : b ^ 2 = 1 := by rw [← map_pow, ha, map_one]
  obtain ⟨g, δ, hform⟩ := BenderSuzuki.ZD.Linear.semilinear_coverage b
  have hbout : b ∉ inner K := by
    intro h
    apply hout
    change MulAut.congr q a ∈ MulAut.innerSubgroup (Group K) at h
    rw [← MulAut.map_innerSubgroup_congr q, Subgroup.mem_map_equiv] at h
    simpa only [MulEquiv.symm_apply_apply] using h
  have hδ := (outer_conjugate_field_of_semilinear b hb g δ hform hbout).1
  obtain ⟨heven, rfl⟩ := field_involution_eq hr hc δ hδ
  refine ⟨heven, q.symm g, ?_⟩
  have hg : MulAut.congr q (MulAut.conj (q.symm g)) = MulAut.conj g := by
    ext x
    simp [MulAut.congr, MulAut.conj_apply]
  apply (MulAut.congr q).injective
  rw [map_mul, hg]
  exact hform
end Theory.PSL2
