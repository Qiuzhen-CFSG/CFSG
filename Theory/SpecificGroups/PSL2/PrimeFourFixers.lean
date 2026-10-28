module

public import Theory.SpecificGroups.PSL2.PrimeSylowFixers

/-!
# Pointwise four-group fixers in prime-field PSL₂

The prime-field automorphism coverage gives conjugation by a PGL₂ element.
A Klein four-group is self-centralizing in PGL₂, forcing that element back
into the specified four-group. This is the prime-linear centralizer
assertion of Aschbacher--Smith 2.5.8(5), printed p.556.
-/

public section
open Subgroup
open scoped MatrixGroups
namespace Theory.PSL2
open GorensteinWalter

/-- Any automorphism fixing an elementary four-group is inner by an element
of that very four-group. -/
theorem primeField_four_fixed_inner {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (hlarge : 3 < p) (V : Subgroup PSL(2, ZMod p)) [IsKleinFour V]
    (a : MulAut PSL(2, ZMod p)) (ha : ∀ x ∈ V, a x = x) :
    ∃ g ∈ V, a = MulAut.conj g := by
  let hK : IsOddPrimePower (Nat.card (ZMod p)) :=
    ⟨p, 1, Fact.out, hp, by omega, by simp⟩
  have hc : 3 < Nat.card (ZMod p) := by simpa using hlarge
  let f : PSL(2, ZMod p) →* PGL2 (ZMod p) := Matrix.ProjectiveSpecialLinearGroup.toPGL
  have hf : Function.Injective f := Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  let W := V.map f
  let eV : V ≃* W := V.equivMapOfInjective f hf
  have hW : IsKleinFour W :=
    { card_four := (Nat.card_congr eV.toEquiv).symm.trans IsKleinFour.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv eV).symm.trans IsKleinFour.exponent_two }
  obtain ⟨g, hg⟩ := primeField_pgl_coverage hp hlarge a
  have hgW : g ∈ W := by
    rw [← pgl2_kleinFour_centralizer_eq_self (ZMod p) hK W hW]
    apply mem_centralizer_iff.mpr
    rintro _ ⟨x, hx, rfl⟩
    have h := toPGL_pgl2InnerAutPSL2_apply (ZMod p) hK hc g x
    rw [hg, ha x hx] at h
    exact (mul_inv_eq_iff_eq_mul.mp h.symm).symm
  obtain ⟨x, hx, he⟩ := hgW
  refine ⟨x, hx, ?_⟩
  rw [← hg, ← he]
  exact pgl2InnerAutPSL2_toPGL (ZMod p) hK hc x

/-- The pointwise fixer lies in the inner image of every overgroup of the four. -/
theorem primeField_four_fixed_mem_inner_image {p : ℕ} [Fact p.Prime]
    (hp : Odd p) (hlarge : 3 < p) (V S : Subgroup PSL(2, ZMod p))
    [IsKleinFour V] (hVS : V ≤ S) (a : MulAut PSL(2, ZMod p))
    (ha : ∀ x ∈ V, a x = x) : a ∈ S.map MulAut.conj := by
  obtain ⟨g, hg, rfl⟩ := primeField_four_fixed_inner hp hlarge V a ha
  exact mem_map_of_mem MulAut.conj (hVS hg)

end Theory.PSL2
