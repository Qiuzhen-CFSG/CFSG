module
public import Theory.FieldTheory.MultiplicativeSpan
public import Theory.FieldTheory.CubicDisplacement
public import Mathlib.FieldTheory.Fixed
/-!
# Ninth-power displacement over a finite quadratic field

If a field of order q² has q > 8, an automorphism with ninth-power
multiplicative displacement is trivial. The ninth powers have at least q
elements, so they span the field additively; the automorphism fixes this span.

This supplies the coefficient-field calculation for the cubic kernel of the
projective unitary torus in Aschbacher--Smith 12.6.31, printed pp.836--837.
-/
public section
namespace FiniteField
variable {F : Type*} [Field F] [Finite F]

theorem eq_one_of_unit_displacement_ninth {q : ℕ}
    (hq : 8 < q) (hcard : Nat.card F = q^2) (σ : F ≃+* F)
    (hσ : ∀ u : Fˣ, (Units.map σ.toMonoidHom u * u⁻¹)^9 = 1) : σ = 1 := by
  let U := (powMonoidHom 9 : Fˣ →* Fˣ).range
  have hU : q ≤ Nat.card U := by
    have hk : Nat.card (powMonoidHom 9 : Fˣ →* Fˣ).ker ≤ 9 := by
      rw [IsCyclic.card_powMonoidHom_ker]
      exact Nat.gcd_le_right _ (by decide)
    have hm := (powMonoidHom 9 : Fˣ →* Fˣ).ker.card_mul_index
    rw [Subgroup.index_ker,Nat.card_units,hcard] at hm
    by_contra h
    have hb : q^2-1 ≤ 9*(q-1) := by
      rw [←hm]
      exact Nat.mul_le_mul hk (by change Nat.card U ≤ q-1; omega)
    have hsq : q^2-1+1=q^2 := Nat.sub_add_cancel (by nlinarith)
    have hs : q-1+1=q := Nat.sub_add_cancel (by omega)
    nlinarith
  have hspan := MultiplicativeSpan.additive_span_eq_top_of_large_units U hcard hU
  let K := FixedBy.subfield F σ
  have hle : AddSubgroup.closure (Set.range (fun u : U => (u.val : F))) ≤
      K.toSubring.toAddSubgroup := by
    apply (AddSubgroup.closure_le _).mpr
    rintro x ⟨u,rfl⟩
    obtain ⟨v,hv⟩ := u.property
    have hh := hσ v
    rw [mul_pow,inv_pow,mul_inv_eq_one] at hh
    change σ (u.val : F) = (u.val : F)
    rw [←hv]
    exact (map_pow σ (v : F) 9).trans (congrArg Units.val hh)
  rw [hspan] at hle
  ext x
  exact hle (AddSubgroup.mem_top x)
end FiniteField
