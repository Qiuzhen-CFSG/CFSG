module
public import Theory.SpecificGroups.PSL3.StandardCubicFixedNine.Reduction
public import Theory.SpecificGroups.PSL3.CartanActions.ResidualInner

/-!
# Odd prime-power actors in binary PSL₃

The graph factor disappears because its square is linear–field. The diagonal
outer subgroup is a cyclic group of order dividing three, so an odd prime-power
field actor centralizes it. For primes greater than three, a prime-power actor
therefore has an inner linear factor. This retains the actual coefficient
actor, and requires no semilinear descent.

Source: Aschbacher–Smith A.3.18, printed pp.51–53.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.SplitPrimeActors
open OuterSolvable ExtensionBorel
variable {F : Type*} [Field F]

private theorem linear_field_graph_square (m : GL (Fin 3) F) (σ : F ≃+* F) :
    (linearConj F m * fieldAction F σ * graph F) ^ 2 =
      linearConj F (m * GeneralLinearGroup.map σ.toRingHom (inverseTransposeGL F m)) *
        fieldAction F (σ ^ 2) := by
  have hcomm := (field_commute_graph σ).eq.symm
  rw [pow_two]
  calc
    _ = linearConj F m * fieldAction F σ * (graph F * linearConj F m) *
        fieldAction F σ * graph F := by group
    _ = linearConj F m *
        (fieldAction F σ * linearConj F (inverseTransposeGL F m)) *
        (graph F * fieldAction F σ) * graph F := by rw [graph_linearConj]; group
    _ = linearConj F m *
        (linearConj F (GeneralLinearGroup.map σ.toRingHom (inverseTransposeGL F m)) *
          fieldAction F σ) * (fieldAction F σ * graph F) * graph F := by
      rw [field_linearConj, hcomm]
    _ = (linearConj F m *
        linearConj F (GeneralLinearGroup.map σ.toRingHom (inverseTransposeGL F m))) *
        (fieldAction F σ * fieldAction F σ) * (graph F ^ 2) := by rw [pow_two]; group
    _ = _ := by rw [graph_sq, mul_one, ← map_mul, ← pow_two, ← map_pow]

/-- The actual standard actor of odd prime-power order is linear–field. -/
theorem primePower_mem_linearField {p m : ℕ} (ho : Odd p)
    (a : MulAut PSL(3,F)) (ha : a ∈ standard F) (hpow : a ^ (p^m) = 1) :
    a ∈ linearField F := by
  obtain ⟨g, σ, h | h⟩ := CartanActions.NormalizerForm.standard_factorization F
    field_linearConj graph_linearConj_exists field_commute_graph a ha
  · rw [h]
    exact (linearField F).mul_mem (mem_sup_left ⟨g,rfl⟩) (mem_sup_right ⟨σ,rfl⟩)
  · have hsq : a^2 ∈ linearField F := by
      rw [h,linear_field_graph_square]
      exact (linearField F).mul_mem (mem_sup_left ⟨_,rfl⟩) (mem_sup_right ⟨_,rfl⟩)
    apply (zpowers_le.mpr hsq)
    apply mem_zpowers_pow_iff.mpr
    exact (Nat.coprime_two_left.mpr ho.pow).of_dvd_right
      (orderOf_dvd_of_pow_eq_one hpow)

variable [Finite F]

/-- Determinant makes the diagonal outer image a cyclic quotient of the units. -/
theorem diagonalOuter_isCyclic : IsCyclic (innerDiagonalOuter F) := by
  let d : GL (Fin 3) F →* Fˣ := GeneralLinearGroup.det
  let e := QuotientGroup.quotientKerEquivOfSurjective d GeneralLinearGroup.det_surjective
  let : IsCyclic (GL (Fin 3) F ⧸ d.ker) := e.isCyclic.mpr inferInstance
  let f : GL (Fin 3) F ⧸ d.ker →* innerDiagonalOuter F :=
    QuotientGroup.lift d.ker (linearOuterAction F).rangeRestrict (fun g hg => by
      apply Subtype.ext
      exact det_ker_le_linearOuterAction_ker F hg)
  apply isCyclic_of_surjective f
  rintro ⟨_,g,rfl⟩
  exact ⟨QuotientGroup.mk g,rfl⟩

/-- Scalar determinant correction bounds the diagonal outer order by three. -/
theorem diagonalOuter_card_dvd_three : Nat.card (innerDiagonalOuter F) ∣ 3 := by
  let := diagonalOuter_isCyclic (F := F)
  rw [← IsCyclic.exponent_eq_card]
  apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
  rintro ⟨_,g,rfl⟩
  apply Subtype.ext
  change linearOuterAction F g ^ 3 = 1
  change QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)) (linearConj F g) ^ 3 = 1
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact CartanActions.ResidualInner.linearConj_cube_inner g

/-- A p-power coefficient actor, p > 3, centralizes the actual diagonal outer image. -/
theorem field_commutes_diagonalOuter {p m : ℕ} [Fact p.Prime] (hp : 3 < p)
    (σ : F ≃+* F) (hs : σ ^ (p^m) = 1) (g : GL (Fin 3) F) :
    Commute (linearOuterAction F g)
      (QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F)) (fieldAction F σ)) := by
  let D := innerDiagonalOuter F
  let := diagonalOuter_isCyclic (F := F)
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
  have hn : q (fieldAction F σ) ∈ normalizer D := by
    apply standardOuter_le_normalizer_innerDiagonalOuter
    exact ⟨fieldAction F σ,fieldAction_mem_standard F σ,rfl⟩
  let b : normalizer D := ⟨q (fieldAction F σ),hn⟩
  have hb : b ^ (p^m) = 1 := by
    apply Subtype.ext
    change q (fieldAction F σ) ^ (p^m) = 1
    rw [← map_pow,← map_pow,hs,map_one,map_one]
  have hc : Nat.Coprime (p^m) (Nat.card (MulAut D)) := by
    rw [IsCyclic.card_mulAut]
    rcases (Nat.dvd_prime Nat.prime_three).mp (diagonalOuter_card_dvd_three (F := F)) with h | h
    · change Nat.card D = 1 at h
      rw [h]
      simp
    · change Nat.card D = 3 at h
      rw [h]
      change Nat.Coprime (p^m) 2
      exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
        intro h
        have := Nat.le_of_dvd (by decide : 0 < 2) h
        omega)).pow_left m
  have he : D.normalizerMonoidHom b = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_one
    have h₁ := orderOf_dvd_of_pow_eq_one (show D.normalizerMonoidHom b ^ (p^m) = 1 by
      rw [← map_pow,hb,map_one])
    have h₂ := orderOf_dvd_natCard (D.normalizerMonoidHom b)
    simpa only [hc.gcd_eq_one] using Nat.dvd_gcd h₁ h₂
  have hf := congrArg (fun k : MulAut D => (k ⟨linearOuterAction F g,⟨g,rfl⟩⟩ : D)) he
  have hh : q (fieldAction F σ) * linearOuterAction F g *
      (q (fieldAction F σ))⁻¹ = linearOuterAction F g := congrArg Subtype.val hf
  exact (show Commute (q (fieldAction F σ)) (linearOuterAction F g) from
    mul_inv_eq_iff_eq_mul.mp hh).symm

/-- An actual p-power standard actor for p > 3 has an inner linear factor. -/
theorem inner_field_of_primePower [CharP F 2] {p m : ℕ} [Fact p.Prime]
    (hp : 3 < p) (a : MulAut PSL(3,F)) (ha : a ∈ standard F)
    (hpow : a ^ (p^m) = 1) :
    ∃ (g : PSL(3,F)) (σ : F ≃+* F),
      a = MulAut.conj g * fieldAction F σ ∧ σ ^ (p^m) = 1 := by
  have ho : Odd p := (Fact.out : p.Prime).odd_of_ne_two (by omega)
  obtain ⟨g,σ,he⟩ := linearField_factorization F a
    (primePower_mem_linearField ho a ha hpow)
  have hs := CartanActions.ResidualLinear.coefficient_pow_eq_one g σ (he ▸ hpow)
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
  have hcomm := field_commutes_diagonalOuter hp σ hs g
  have hgp : linearOuterAction F g ^ (p^m) = 1 := by
    have hh := congrArg q hpow
    rw [he,map_pow,map_mul,map_one] at hh
    change (linearOuterAction F g * q (fieldAction F σ)) ^ (p^m) = 1 at hh
    rw [hcomm.mul_pow] at hh
    have ht : q (fieldAction F σ) ^ (p^m) = 1 := by
      rw [← map_pow,← map_pow,hs,map_one,map_one]
    rwa [ht,mul_one] at hh
  have hg3 : linearOuterAction F g ^ 3 = 1 := by
    change q (linearConj F g) ^ 3 = 1
    rw [← map_pow]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact CartanActions.ResidualInner.linearConj_cube_inner g
  have hgo : linearOuterAction F g = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_one
    have hc : Nat.Coprime (p^m) 3 :=
      ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr (by
        intro h
        have := Nat.le_of_dvd (by decide : 0 < 3) h
        omega)).pow_left m
    simpa only [hc.gcd_eq_one] using Nat.dvd_gcd
      (orderOf_dvd_of_pow_eq_one hgp) (orderOf_dvd_of_pow_eq_one hg3)
  have hgin : linearConj F g ∈ MulAut.innerSubgroup PSL(3,F) :=
    (QuotientGroup.eq_one_iff _).mp hgo
  obtain ⟨x,hx⟩ := hgin
  exact ⟨x,σ,he.trans (congrArg (fun b => b * fieldAction F σ) hx.symm),hs⟩

omit [Finite F] in
/-- A coefficient actor which is inner is trivial on the coefficient field. -/
theorem field_eq_one_of_inner [CharP F 2] (σ : F ≃+* F)
    (hi : fieldAction F σ ∈ MulAut.innerSubgroup PSL(3,F)) : σ = 1 := by
  obtain ⟨g,hg⟩ := hi
  obtain ⟨x,rfl⟩ := projection_surjective F g
  have he : linearConj F (SpecialLinearGroup.toGL x) = fieldAction F σ := by
    exact (linearConj_toGL F x).trans hg
  have hh : (linearConj F (SpecialLinearGroup.toGL x)⁻¹ * fieldAction F σ)^1 = 1 := by
    rw [pow_one,map_inv,he,inv_mul_cancel]
  simpa only [pow_one] using CartanActions.ResidualLinear.coefficient_pow_eq_one _ σ hh

omit [Finite F] in
/-- The coefficient action is faithful on the original projective carrier. -/
theorem fieldAction_injective [CharP F 2] : Function.Injective (fieldAction F) := by
  apply (fieldAction F).ker_eq_bot_iff.mp
  apply eq_bot_iff.mpr
  intro σ hσ
  apply mem_bot.mpr
  apply field_eq_one_of_inner σ
  rw [show fieldAction F σ = 1 from hσ]
  exact (MulAut.innerSubgroup PSL(3,F)).one_mem

end Matrix.PSL3.SplitPrimeActors
