module
public import Theory.SpecificGroups.PSL3.SplitPrimeRank
public import Theory.FieldTheory.PrimeOrderFixedUnits
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# The split torus fixed by a prime-order coefficient actor

The fixed coefficient field retains p in its unit order by p-group
fixed-point counting. Its determinant-one split torus has rank two.
The literal map to PSL₃ over the original field has kernel contained in
the scalar center, whose order divides three. Away from three this loses
no prime rank and supplies an elementary fixed subgroup of order p².

Source: Aschbacher–Smith A.3.18, printed pp.51–53.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.SplitPrimeActors
open OuterSolvable
variable {F : Type*} [Field F]

/-- The fixed coefficient matrices map to the actual fixed projective subgroup. -/
def fixedCoefficientMap (σ : F ≃+* F) :
    SL(3, FixedBy.subfield F σ) →* (fieldAction F σ).fixedSubgroup :=
  ((projection F).comp (SpecialLinearGroup.map (FixedBy.subfield F σ).subtype)).codRestrict
    (fieldAction F σ).fixedSubgroup (fun x => by
      apply (MulAut.mem_fixedSubgroup _ _).mpr
      change fieldAction F σ (QuotientGroup.mk
        (SpecialLinearGroup.map (FixedBy.subfield F σ).subtype x)) = _
      rw [fieldAction_mk]
      congr 1
      apply Subtype.ext
      ext i j
      exact (x.val i j).property)

private theorem coefficientSL_injective (σ : F ≃+* F) :
    Function.Injective (SpecialLinearGroup.map (FixedBy.subfield F σ).subtype (n := Fin 3)) := by
  intro x y h
  apply Subtype.ext
  ext i j
  exact congrArg (fun g : SL(3,F) => g.val i j) h

variable [Finite F] {p : ℕ} [Fact p.Prime]

/-- Its scalar kernel is prime to every prime different from three. -/
theorem fixedCoefficientMap_kernel_coprime (σ : F ≃+* F) (hp : p ≠ 3) :
    Nat.Coprime p (Nat.card (fixedCoefficientMap σ).ker) := by
  let f := SpecialLinearGroup.map (FixedBy.subfield F σ).subtype (n := Fin 3)
  let k : (fixedCoefficientMap σ).ker →* center SL(3,F) :=
    (f.comp (fixedCoefficientMap σ).ker.subtype).codRestrict (center SL(3,F)) (fun x => by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val x.property)
  have hk : Function.Injective k := by
    intro x y h
    apply Subtype.ext
    exact coefficientSL_injective σ (congrArg Subtype.val h)
  have hd : Nat.card (fixedCoefficientMap σ).ker ∣ Nat.card (center SL(3,F)) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hk).toEquiv]
    exact card_subgroup_dvd_card k.range
  apply Nat.Coprime.of_dvd_right (hd.trans (Matrix.SL3.card_center_dvd_three F))
  exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun h =>
    hp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_three).mp h))

/-- The actual fixed projective subgroup has split prime rank at least two. -/
theorem field_fixed_rank (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hp : p ≠ 3) (hd : p ∣ Nat.card F - 1) :
    2 ≤ primeRank p (fieldAction F σ).fixedSubgroup := by
  have hK := FiniteField.prime_dvd_fixed_units σ hσ hd
  rw [Nat.card_units] at hK
  exact (SplitPrimeRank.special_rank (FixedBy.subfield F σ) hK).trans
    (primeRank_le_of_coprime_ker p (fixedCoefficientMap σ)
      (fixedCoefficientMap_kernel_coprime σ hp))

/-- An elementary subgroup of order p² is pointwise fixed in the original PSL₃. -/
theorem exists_fixed_elementary (σ : F ≃+* F) (hσ : orderOf σ = p)
    (hp : p ≠ 3) (hd : p ∣ Nat.card F - 1) :
    ∃ E : Subgroup PSL(3,F), IsElementaryAbelian p E ∧ Nat.card E = p^2 ∧
      E ≤ (fieldAction F σ).fixedSubgroup := by
  have hr := field_fixed_rank σ hσ hp hd
  obtain ⟨B,hB,hcard⟩ := exists_elementaryAbelian_card_primeRank
    (G := (fieldAction F σ).fixedSubgroup) (p := p)
  let := hB
  obtain ⟨C,hC⟩ := Sylow.exists_subgroup_card_pow_prime (G := B) p
    (n := 2) (by rw [hcard]; exact pow_dvd_pow p hr)
  let : IsElementaryAbelian p C := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (fun c => by
      apply Subtype.ext
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p p B) c.val) }
  let f : B →* PSL(3,F) := (fieldAction F σ).fixedSubgroup.subtype.comp B.subtype
  have hf : Function.Injective f :=
    (fieldAction F σ).fixedSubgroup.subtype_injective.comp B.subtype_injective
  refine ⟨C.map f,IsElementaryAbelian.map f,?_,?_⟩
  · rw [card_map_of_injective hf,hC]
  · rintro _ ⟨c,_,rfl⟩
    exact c.val.property

end Matrix.PSL3.SplitPrimeActors
