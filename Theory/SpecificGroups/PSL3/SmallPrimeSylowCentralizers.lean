module
public import Theory.SpecificGroups.PSL3.SylowFixedActions.OddPrimeInner
public import Theory.SpecificGroups.PSL3Three.SylowFixersInner
public import Theory.SpecificGroups.PSL3.OddInvolutionFixed.Inner
public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.LinearFactor
public import Theory.GroupAction.InnerCentralizerCardinality
public import Theory.AtlasPort.ExceptionalIsomorphisms.FieldTransportLaws
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Sylow-fixing involutions in PSL₃(3) and PSL₃(5)

The prime-field automorphism normal form and coprime determinant powers
make the outer quotient a group of order dividing two. A pointwise Sylow
two-fixer is inner, including the separately proved ternary endpoint.
The actual projective involution centralizer is an image of GL₂, so the
full automorphism centralizer has order dividing 96 or 960. In particular
it cannot contain a faithfully embedded group of order nine.

Source: Aschbacher–Smith, proof of 12.6.26, printed p.832, the odd linear
rows in the Theorem C inspection; GLS3 2.5.12(a) supplies the imported
automorphism normal form. All groups, quotient maps and Sylows are literal.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Matrix.PSL3.SmallPrimeSylowCentralizers
variable {F : Type*} [Field F] [Finite F]
  [IsSimpleGroup PSL(3,F)] [Group.IsPerfect PSL(3,F)]
open OuterSolvable

/-- The literal outer quotient has order dividing two at both small odd primes. -/
theorem outer_card_dvd_two (hF : Nat.card F = 3 ∨ Nat.card F = 5) :
    Nat.card (MulAut.Outer PSL(3,F)) ∣ 2 := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
  have hlin (g : GL (Fin 3) F) : q (linearConj F g) = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (a := 3) (b := Nat.card Fˣ)
    · rw [Nat.card_units]
      rcases hF with hF|hF <;> rw [hF] <;> decide
    · apply orderOf_dvd_of_pow_eq_one
      rw [←map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr (OddInvolutionFixed.linearConj_cube_inner g)
    · apply orderOf_dvd_of_pow_eq_one
      rw [←map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr
        (CartanActions.SixCommutators.linearConj_pow_inner F g)
  have htop : zpowers (q (graph F)) = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective (MulAut.innerSubgroup PSL(3,F)) x
    have hn : ∃ g : GL (Fin 3) F, a = linearConj F g ∨ a = linearConj F g * graph F := by
      rcases hF with hF|hF
      · exact OddInvolutionFixed.automorphism_normal_form
          (Group.IsPerfect.not_isSolvable _) (by decide : Nat.Prime 3) (by decide) hF a
      · exact OddInvolutionFixed.automorphism_normal_form
          (Group.IsPerfect.not_isSolvable _) (by decide : Nat.Prime 5) (by decide) hF a
    obtain ⟨g,rfl|rfl⟩ := hn
    · rw [hlin]; exact one_mem _
    · rw [map_mul,hlin,one_mul]; exact mem_zpowers _
  rw [←card_top (G := MulAut.Outer PSL(3,F)),←htop,Nat.card_zpowers]
  apply orderOf_dvd_of_pow_eq_one
  rw [←map_pow,graph_sq,map_one]

/-- Every involutory pointwise fixer of the specified Sylow is inner. -/
theorem sylow_fixer_inner (hF : Nat.card F = 3 ∨ Nat.card F = 5)
    (P : Sylow 2 PSL(3,F)) (a : MulAut PSL(3,F)) (ha : orderOf a = 2)
    (hP : ∀ x ∈ P, a x = x) : a ∈ MulAut.innerSubgroup PSL(3,F) := by
  classical
  rcases hF with hF|hF
  · let := Fintype.ofFinite F
    let eF : F ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    let e := Atlas.fieldEquivPSL 3 eF
    let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
    let b := MulAut.congr e a
    have hb : ∀ x ∈ Q, b x = x := by
      rintro _ ⟨x,hx,rfl⟩
      change e (a (e.symm (e x))) = e x
      rw [e.symm_apply_apply,hP x hx]
    obtain ⟨t,_,ht⟩ := Matrix.PSL3Three.sylow_fixed_inner Q b hb
    obtain ⟨x,hx⟩ := (MulAut.congr_inner_iff e a).mp ⟨t,ht⟩
    exact ⟨x,hx.symm⟩
  · exact SylowFixedActions.OddPrime.involution_mem_inner_of_fixes_sylow
      5 (by decide) (by decide) (by decide) hF P a ha hP

/-- The full automorphism centralizer cannot contain a group of order nine. -/
theorem not_nine_dvd_sylow_fixer_centralizer
    (hF : Nat.card F = 3 ∨ Nat.card F = 5)
    (P : Sylow 2 PSL(3,F)) (a : MulAut PSL(3,F)) (ha : orderOf a = 2)
    (hP : ∀ x ∈ P, a x = x) :
    ¬ 9 ∣ Nat.card (centralizer ({a} : Set (MulAut PSL(3,F)))) := by
  obtain ⟨t,rfl⟩ := sylow_fixer_inner hF P a ha hP
  have hz : center PSL(3,F) = ⊥ := center_eq_bot_of_simple_perfect
  have ht : orderOf t = 2 :=
    (orderOf_injective MulAut.conj (MulAut.conj_injective_of_center_eq_bot hz) t).symm.trans ha
  have h2 : (2 : F) ≠ 0 := GorensteinWalter.two_ne_zero_of_odd_card F (by
    rcases hF with hF|hF <;> rw [hF] <;> decide)
  obtain ⟨f,hf⟩ := OddInvolutionFixed.exists_gl2_surjective_centralizer t ht h2
  have hd := (MulAut.centralizer_conj_card_dvd hz t).trans
    (Nat.mul_dvd_mul (card_dvd_of_surjective f hf) (outer_card_dvd_two hF))
  intro hn
  have hn' := hn.trans hd
  let := Fintype.ofFinite F
  rw [Matrix.card_GL_field] at hn'
  rcases hF with hF|hF <;> norm_num [←Nat.card_eq_fintype_card,hF,Fin.prod_univ_two] at hn'
end Matrix.PSL3.SmallPrimeSylowCentralizers
