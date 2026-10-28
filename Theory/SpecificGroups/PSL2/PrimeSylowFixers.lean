module

public import GorensteinWalter.PGammaL2
public import GorensteinWalter.PGL2KleinFourSelfCentralizer

/-!
# Pointwise Sylow fixers of odd prime-field PSL₂

Over a prime field the coefficient automorphism in the proved projective
semilinear coverage theorem is trivial. A Sylow two-subgroup contains a
Klein four, and that four-group is self-centralizing even in PGL₂. Hence an
automorphism fixing the Sylow pointwise is conjugation by one of its elements.
The proof applies to every automorphism, including arbitrary two-elements,
and includes the primes five and seven.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
16.1.6, printed p.1172. The projective action and coverage use the actual
matrix quotient, through the imported Gorenstein–Walter matrix calculations.
-/

public section

open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2
open GorensteinWalter

/-- Every automorphism of odd prime-field PSL₂ is induced by PGL₂. -/
theorem primeField_pgl_coverage {p : ℕ} [Fact p.Prime] (hp : Odd p) (hlarge : 3 < p)
    (a : MulAut PSL(2, ZMod p)) :
    ∃ g : PGL2 (ZMod p),
      pgl2InnerAutPSL2 (ZMod p) ⟨p, 1, Fact.out, hp, by omega, by simp⟩
        (by simpa using hlarge) g = a := by
  let hK : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, hp, by omega, by simp⟩
  have hc : 3 < Nat.card (ZMod p) := by simpa using hlarge
  obtain ⟨x, hx⟩ := pGammaL2ToMulAutPSL2_surjective (ZMod p)
    (p := p) (f := 1) (by simp) hK hc a
  have hs : x.right = 1 := Subsingleton.elim _ _
  refine ⟨x.left, ?_⟩
  have he : x = SemidirectProduct.inl x.left := by
    apply SemidirectProduct.ext
    · rfl
    · exact hs
  rw [he, pGammaL2ToMulAutPSL2_inl] at hx
  exact hx

/-- Every pointwise Sylow fixer is conjugation by an element of that Sylow. -/
theorem primeField_sylow_fixed_inner {p : ℕ} [Fact p.Prime] (hp : Odd p) (hlarge : 3 < p)
    (S : Sylow 2 PSL(2, ZMod p)) (a : MulAut PSL(2, ZMod p))
    (ha : ∀ x ∈ S, a x = x) : ∃ g ∈ S, a = MulAut.conj g := by
  let hK : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, hp, by omega, by simp⟩
  have hc : 3 < Nat.card (ZMod p) := by simpa using hlarge
  obtain ⟨m, hm, ⟨eS⟩⟩ := psl2_odd_hasDihedralSylowTwo_model (ZMod p) hK S
  obtain ⟨V, hVS, hV⟩ := exists_kleinFour_le_of_dihedral_subgroup_mulEquiv
    (S : Subgroup PSL(2, ZMod p)) hm eS
  let f : PSL(2, ZMod p) →* PGL2 (ZMod p) := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hf : Function.Injective f := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  let W := V.map f
  let eV : V ≃* W := V.equivMapOfInjective f hf
  have hW : IsKleinFour W :=
    { card_four := (Nat.card_congr eV.toEquiv).symm.trans hV.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv eV).symm.trans hV.exponent_two }
  obtain ⟨g, hg⟩ := primeField_pgl_coverage hp hlarge a
  have hgW : g ∈ W := by
    rw [← pgl2_kleinFour_centralizer_eq_self (ZMod p) hK W hW]
    apply mem_centralizer_iff.mpr
    rintro _ ⟨x, hx, rfl⟩
    have h := toPGL_pgl2InnerAutPSL2_apply (ZMod p) hK hc g x
    rw [hg, ha x (hVS hx)] at h
    exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm
  obtain ⟨x, hx, he⟩ := hgW
  refine ⟨x, hVS hx, ?_⟩
  rw [← hg, ← he]
  exact pgl2InnerAutPSL2_toPGL (ZMod p) hK hc x

end Theory.PSL2
