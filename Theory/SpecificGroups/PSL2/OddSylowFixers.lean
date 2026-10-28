module

public import Theory.SpecificGroups.PSL2.PrimeSylowFixers
public import GorensteinWalter.PGammaL2PureSemilinear
public import Theory.GroupAction.AutomorphismFixedTransport

/-!
# Involutions fixing Sylow two-subgroups of odd PSL₂

A projective linear Sylow fixer is inner: a Klein four in the Sylow subgroup
is self-centralizing even in PGL₂. Semilinear coverage then leaves either an
inner automorphism or a nontrivial field component. Projective Hilbert 90
conjugates the latter involution to the actual coefficient automorphism.

This extends the prime-field calculation in `PrimeSylowFixers` and the
coefficient-actor argument in Chapter15's `LinearModels/SquareFields/FieldActor`.
It needs neither a four-group of automorphisms nor a field-size residue.
Source: Aschbacher--Smith, proof of 1.1.5(3), printed p.503.
-/

public section
open Subgroup GorensteinWalter
open scoped MatrixGroups
namespace Theory.PSL2

/-- Projective linear automorphisms fixing an odd PSL₂ Sylow pointwise are
conjugation by an element of that Sylow. -/
theorem odd_pgl_sylow_fixed_inner {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (hl : 3 < Nat.card F)
    (S : Sylow 2 PSL(2,F)) (a : MulAut PSL(2,F))
    (ha : ∀ x ∈ S, a x = x) (g : PGL2 F)
    (hg : pgl2InnerAutPSL2 F hF hl g = a) :
    ∃ x ∈ S, a = MulAut.conj x := by
  obtain ⟨m, hm, ⟨eS⟩⟩ := psl2_odd_hasDihedralSylowTwo_model F hF S
  obtain ⟨V, hVS, hV⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (S : Subgroup PSL(2,F)) hm eS
  let f : PSL(2,F) →* PGL2 F := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hf : Function.Injective f := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  let W := V.map f
  let eV : V ≃* W := V.equivMapOfInjective f hf
  have hW : IsKleinFour W :=
    { card_four := (Nat.card_congr eV.toEquiv).symm.trans hV.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv eV).symm.trans hV.exponent_two }
  have hgW : g ∈ W := by
    rw [← pgl2_kleinFour_centralizer_eq_self F hF W hW]
    apply mem_centralizer_iff.mpr
    rintro _ ⟨x, hx, rfl⟩
    have h := toPGL_pgl2InnerAutPSL2_apply F hF hl g x
    rw [hg, ha x (hVS hx)] at h
    exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm
  obtain ⟨x, hx, he⟩ := hgW
  refine ⟨x, hVS hx, ?_⟩
  rw [← hg, ← he]
  exact pgl2InnerAutPSL2_toPGL F hF hl x

/-- Every involutory Sylow fixer is inner or conjugate, as an actual
automorphism, to an order-two coefficient automorphism. -/
theorem odd_sylow_fixed_involution_inner_or_field
    {F : Type*} [Field F] [Finite F]
    (hF : IsOddPrimePower (Nat.card F)) (hl : 3 < Nat.card F)
    (S : Sylow 2 PSL(2,F)) (a : MulAut PSL(2,F))
    (ha : orderOf a = 2) (hfix : ∀ x ∈ S, a x = x) :
    (∃ x, a = MulAut.conj x) ∨
      ∃ (σ : F ≃+* F) (β : MulAut PSL(2,F)), orderOf σ = 2 ∧
        MulAut.congr β a = psl2FieldAut F σ := by
  obtain ⟨p, n, hp, ho, hn, hcard⟩ := hF
  have hF : IsOddPrimePower (Nat.card F) := ⟨p, n, hp, ho, hn, hcard⟩
  let : Fact p.Prime := ⟨hp⟩
  let π := pGammaL2ToMulAutPSL2 F hF hl
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective F hcard hF hl a
  by_cases hfield : x.right = 1
  · left
    have he : x = SemidirectProduct.inl x.left := by
      apply SemidirectProduct.ext
      · rfl
      · exact hfield
    rw [he, pGammaL2ToMulAutPSL2_inl] at hx
    obtain ⟨g, _, hg⟩ := odd_pgl_sylow_fixed_inner hF hl S a hfix x.left hx
    exact ⟨g, hg⟩
  · right
    have hxord : orderOf x = 2 := by
      rw [← orderOf_injective π (pGammaL2ToMulAutPSL2_injective F hF hl), hx]
      exact ha
    have hxpow : x ^ 2 = 1 := by simpa only [hxord] using pow_orderOf_eq_one x
    have hσpow : x.right ^ 2 = 1 := by
      have h := congrArg SemidirectProduct.right hxpow
      simpa [pow_two] using h
    have hσord : orderOf x.right = 2 := orderOf_eq_prime hσpow hfield
    obtain ⟨c, hc⟩ := projective_semilinear_involution_conj_inr hF x hxord hfield
    refine ⟨x.right, (pgl2InnerAutPSL2 F hF hl c)⁻¹, hσord, ?_⟩
    have hc' := congrArg π hc
    simp only [map_mul, map_inv, π, pGammaL2ToMulAutPSL2_inl,
      pGammaL2ToMulAutPSL2_inr, hx] at hc'
    ext y
    exact DFunLike.congr_fun hc' y

end Theory.PSL2
