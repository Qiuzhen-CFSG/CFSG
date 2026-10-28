module

public import Theory.SpecificGroups.HigherClassicalCovers.Nondefining.LinearQuartic
public import Mathlib.FieldTheory.Finite.Extension

/-!
# Cubic tori and the remaining support of linear covering kernels

The units of the cubic field extension act by multiplication on K × F,
fixing the last coordinate. A basis realizes this as an injective homomorphism
into GL₄(F), with cyclic image of order p³−1 when |F|=p. Its index is
p⁶(p⁴−1)(p²−1)(p−1). Thus every Sylow r-subgroup of GL₄(F), and hence of
SL₄(F) and its actual projective quotient, is cyclic for r ∤ p(p⁴−1).

Central transfer, together with the separate quartic-prime calculation,
excludes every odd nondefining kernel prime outside p²−1. The primes
dividing p²−1 remain a separate torus-normalizer calculation. Arbitrary
coefficient fields and p=3 are retained throughout.

Source: the nondefining-kernel input to Aschbacher–Smith A.2.17, printed
p.39; covering and cyclic-Sylow conventions I.1.1–I.1.2, printed p.407.
The finite-field multiplication construction follows the existing
`G2.MultiplierOrdinary.OddCyclotomicSylow.CubicTorus`, here on K × F;
Sylow conjugacy uses its `Arithmetic` module's cyclic-index argument.
-/

open Matrix PerfectCentralCovering Subgroup
open scoped MatrixGroups
noncomputable section

namespace Theory.SpecificGroups.HigherClassicalCovers.Nondefining

private theorem exists_cubic_torus (F : Type*) [Field F] [Finite F]
    (p : ℕ) [Fact p.Prime] [CharP F p] :
    ∃ C : Subgroup (GL (Fin 4) F), IsCyclic C ∧ Nat.card C = Nat.card F ^ 3 - 1 := by
  let K := FiniteField.Extension F p 3
  let b := Module.finBasisOfFinrankEq F (K × F) (show Module.finrank F (K × F) = 4 by
    rw [Module.finrank_prod, FiniteField.finrank_extension, Module.finrank_self])
  let j : Kˣ →* (K × F)ˣ := {
    toFun u := ⟨((u : K), 1), ((u⁻¹ : Kˣ), 1), by ext <;> simp, by ext <;> simp⟩
    map_one' := by apply Units.ext; rfl
    map_mul' u v := by apply Units.ext; ext <;> simp }
  let f : Kˣ →* GL (Fin 4) F :=
    (Units.map (Algebra.leftMulMatrix b).toMonoidHom).comp j
  have hf : Function.Injective f := by
    intro u v h
    apply Units.ext
    exact congrArg Prod.fst (Algebra.leftMulMatrix_injective b (congrArg Units.val h))
  let e := MonoidHom.ofInjective hf
  refine ⟨f.range, e.isCyclic.mp inferInstance, ?_⟩
  rw [← Nat.card_congr e.toEquiv, Nat.card_units, FiniteField.natCard_extension]

private theorem index_cubic {F : Type*} [Field F] [Finite F]
    {p : ℕ} [Fact p.Prime] (hF : Nat.card F = p)
    (C : Subgroup (GL (Fin 4) F)) (hC : Nat.card C = p^3 - 1) :
    C.index = p^6 * (p^4 - 1) * (p^2 - 1) * (p - 1) := by
  classical
  let := Fintype.ofFinite F
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpos : 0 < p^3 - 1 := Nat.sub_pos_of_lt (one_lt_pow₀ (by omega) (by decide))
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [← hC, C.card_mul_index, hC, Matrix.card_GL_field]
  norm_num [Fin.prod_univ_succ, ← Nat.card_eq_fintype_card, hF]
  have h41 : p^4 - p = p * (p^3 - 1) := by rw [Nat.mul_sub]; ring_nf
  have h42 : p^4 - p^2 = p^2 * (p^2 - 1) := by rw [Nat.mul_sub]; ring_nf
  have h43 : p^4 - p^3 = p^3 * (p - 1) := by rw [Nat.mul_sub]; ring_nf
  rw [h41, h42, h43]
  ring

private theorem sylow_cyclic_of_cyclic_index {G : Type*} [Group G] [Finite G]
    {r : ℕ} [Fact r.Prime] (C : Subgroup G) [IsCyclic C]
    (hi : ¬ r ∣ C.index) (Q : Sylow r G) : IsCyclic Q := by
  let T : Sylow r C := default
  let A := (T : Subgroup C).map C.subtype
  have ha : IsPGroup r A := T.isPGroup'.map C.subtype
  have hai : ¬ r ∣ A.index := by
    rw [Subgroup.index_map_subtype]
    exact (Fact.out : r.Prime).not_dvd_mul T.not_dvd_index hi
  let U : Sylow r G := ha.toSylow hai
  let e := (T : Subgroup C).equivMapOfInjective C.subtype C.subtype_injective
  have hc : IsCyclic U := e.isCyclic.mp inferInstance
  exact (U.equiv Q).isCyclic.mp hc

private theorem gl_cyclic {F : Type*} [Field F] [Finite F]
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hF : Nat.card F = p)
    (hrp : r ≠ p) (hfour : ¬ r ∣ p^4 - 1) (Q : Sylow r (GL (Fin 4) F)) : IsCyclic Q := by
  classical
  let := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime (by rwa [← Nat.card_eq_fintype_card])
  obtain ⟨C, hc, hC⟩ := exists_cubic_torus F p
  let := hc
  apply sylow_cyclic_of_cyclic_index C ?_ Q
  rw [index_cubic hF C (by simpa only [hF] using hC)]
  have hr : r.Prime := Fact.out
  have hnp : ¬ r ∣ p^6 := fun h => hrp
    ((Nat.prime_dvd_prime_iff_eq hr (Fact.out : p.Prime)).mp (hr.dvd_of_dvd_pow h))
  have htwo : ¬ r ∣ p^2 - 1 := by
    intro h
    apply hfour
    have he : p^4 - 1 = (p^2 - 1) * (p^2 + 1) := by
      calc
        p^4 - 1 = (p^2)^2 - 1^2 := by ring_nf
        _ = (p^2 - 1) * (p^2 + 1) := by rw [Nat.sq_sub_sq]; ac_rfl
    rw [he]
    exact dvd_mul_of_dvd_left h _
  have hone : ¬ r ∣ p - 1 := fun h =>
    hfour (h.trans (by simpa using Nat.sub_dvd_pow_sub_pow p 1 4))
  exact hr.not_dvd_mul (hr.not_dvd_mul (hr.not_dvd_mul hnp hfour) htwo) hone

private theorem sl_cyclic {F : Type*} [Field F] [Finite F]
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hF : Nat.card F = p)
    (hrp : r ≠ p) (hfour : ¬ r ∣ p^4 - 1) (P : Sylow r SL(4,F)) : IsCyclic P := by
  let A := (P : Subgroup SL(4,F)).map SpecialLinearGroup.toGL
  obtain ⟨Q, hQ⟩ := (P.isPGroup'.map SpecialLinearGroup.toGL).exists_le_sylow
  let := gl_cyclic hF hrp hfour Q
  let f : P →* Q := (SpecialLinearGroup.toGL.comp (P : Subgroup SL(4,F)).subtype).codRestrict _
    (fun a => hQ ⟨a, a.property, rfl⟩)
  exact isCyclic_of_injective f (fun a b h => Subtype.ext
    (SpecialLinearGroup.toGL_injective (congrArg Subtype.val h)))

/-- Away from p(p⁴−1), every Sylow subgroup of the literal PSL₄ quotient is cyclic. -/
public theorem linear_sylow_isCyclic_of_not_dvd_fourth_sub_one {F : Type*} [Field F] [Finite F]
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hF : Nat.card F = p)
    (hrp : r ≠ p) (hfour : ¬ r ∣ p^4 - 1) (P : Sylow r PSL(4,F)) : IsCyclic P := by
  let q : SL(4,F) →* PSL(4,F) := QuotientGroup.mk' _
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  obtain ⟨Q, hQ⟩ := Sylow.mapSurjective_surjective hq r P
  let := sl_cyclic hF hrp hfour Q
  have hc : IsCyclic ((Q : Subgroup SL(4,F)).map q) :=
    isCyclic_of_surjective _ (q.subgroupMap_surjective (Q : Subgroup SL(4,F)))
  rwa [← Sylow.coe_mapSurjective hq, hQ] at hc

/-- Every odd nondefining kernel prime outside p²−1 is excluded, including
all cubic and quartic cyclotomic primes. No squarefree-order assumption is used. -/
public theorem linear_not_dvd_kernel_of_not_dvd_sq_sub_one {F : Type*} [Field F] [Finite F]
    {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hF : Nat.card F = p)
    (hr2 : r ≠ 2) (hrp : r ≠ p) (htwo : ¬ r ∣ p^2 - 1)
    {E : Type*} [Group E] [Finite E] (f : Cover E PSL(4,F)) :
    ¬ r ∣ Nat.card f.toMonoidHom.ker := by
  by_cases hplus : r ∣ p^2 + 1
  · exact linear_not_dvd_kernel_of_dvd_sq_add_one
      hF hr2 hrp hplus f
  have hfour : ¬ r ∣ p^4 - 1 := by
    have he : p^4 - 1 = (p^2 - 1) * (p^2 + 1) := by
      calc
        p^4 - 1 = (p^2)^2 - 1^2 := by ring_nf
        _ = (p^2 - 1) * (p^2 + 1) := by rw [Nat.sq_sub_sq]; ac_rfl
    rw [he]
    exact (Fact.out : r.Prime).not_dvd_mul htwo hplus
  exact f.not_dvd_card_multiplier_of_isCyclic_sylow (linear_sylow_isCyclic_of_not_dvd_fourth_sub_one hF hrp hfour)

end Theory.SpecificGroups.HigherClassicalCovers.Nondefining
