module

public import Theory.SpecificGroups.PSL2.SylowFixedQuotients
public import CFSG.Quasithin.ClassicalModels
public import CFSG.Quasithin.FermatMersenne
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Odd-prime PSL₂ Sylow centers and fixed quotients in the component branch

An arbitrary finite field in the source model witness is identified with
its prime field. Entrywise transport gives an equivalence of the actual
projective matrix groups. For Fermat or Mersenne primes p ≥ 7, the dihedral
Sylow calculation bounds the center by two. For p = 5, the proved
PSL₂(5) ≃ A₅ isomorphism supplies Sylow order, pointwise-fixer innerness,
and identity on normalized three-group quotients D/O₂(D).

The quotient is the literal quotient by the intrinsic two-core. The
permutation proof applies to every D satisfying the quotient condition,
including the trivial subgroup; the consumer's two-perfect hypothesis is
unnecessary for this calculation. Final component elimination remains in
15.4.20 assembly.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
1.1.5(3)(e), printed p.502, and the proof of 15.4.20, printed p.1164.
-/

open scoped MatrixGroups
open Subgroup

namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup

/-- Identify the actual arbitrary-field source model with the prime-field
projective matrix group. -/
public theorem odd_linear_equiv_prime_field {L : Type*} [Group L]
    {p : ℕ} [Fact p.Prime] (hL : ClassicalGroup.IsPSL L 2 p) :
    Nonempty (L ≃* PSL(2, ZMod p)) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hL
  let : Fintype F := Fintype.ofFinite F
  have hcard' : Fintype.card F = Fintype.card (ZMod p) := by
    simpa only [← Nat.card_eq_fintype_card, Nat.card_zmod] using hcard
  let eF : F ≃+* ZMod p := FiniteField.ringEquivOfCardEq hcard'
  exact ⟨e.trans (Atlas.fieldEquivPSL 2 eF)⟩

/-- Every Sylow two-subgroup of an actual PSL₂ model at a Fermat or
Mersenne prime p ≥ 7 has center of order at most two. -/
public theorem odd_linear_sylow_center_card_le_two {L : Type*} [Group L] [Finite L]
    {p : ℕ} (hp : IsFermatOrMersennePrime p) (hp7 : 7 ≤ p)
    (hL : ClassicalGroup.IsPSL L 2 p) (P : Sylow 2 L) :
    Nat.card (center P) ≤ 2 := by
  let : Fact p.Prime := ⟨hp.1⟩
  have hparam : ∃ k : ℕ, p - 1 = 2 ^ k ∨ p + 1 = 2 ^ k := by
    rcases hp.2 with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨2 ^ a, Or.inl (by omega)⟩
    · exact ⟨a, Or.inr ha⟩
  obtain ⟨k, hk⟩ := hparam
  obtain ⟨e⟩ := odd_linear_equiv_prime_field hL
  let Q := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let eP : P ≃* Q := (P : Subgroup L).equivMapOfInjective e.toMonoidHom e.injective
  rw [Nat.card_congr (centerCongr eP).toEquiv]
  exact Theory.PSL2.SylowFixedQuotients.sylow_center_card_le_two_of_adjacent_power hp7 hk Q

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem five_alternating_equiv {L : Type*} [Group L]
    (hL : ClassicalGroup.IsPSL L 2 5) : Nonempty (L ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := odd_linear_equiv_prime_field hL
  obtain ⟨e5⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five
  exact ⟨e.trans e5⟩

variable {L : Type*} [Group L] [Finite L]

/-- The Sylow two-subgroups of any actual PSL₂(5) source model have order four. -/
public theorem odd_linear_five_sylow_card (hL : ClassicalGroup.IsPSL L 2 5)
    (P : Sylow 2 L) : Nat.card P = 4 := by
  obtain ⟨e⟩ := five_alternating_equiv hL
  exact Theory.PSL2.SylowFixedQuotients.sylow_card_of_equiv_five e P

/-- A pointwise Sylow fixer in the PSL₂(5) source model is conjugation by
an element of that Sylow subgroup. -/
public theorem odd_linear_five_fixed_inner (hL : ClassicalGroup.IsPSL L 2 5)
    (P : Sylow 2 L) (β : MulAut L) (hβ : ∀ x ∈ P, β x = x) :
    ∃ x ∈ P, β = MulAut.conj x := by
  obtain ⟨e⟩ := five_alternating_equiv hL
  exact Theory.PSL2.SylowFixedQuotients.sylow_fixed_inner_of_equiv_five e P β hβ

/-- Sylow conjugation acts as the identity on the literal normalized
three-group quotient D/O₂(D) in the PSL₂(5) source model. -/
public theorem odd_linear_five_conj_quotient (hL : ClassicalGroup.IsPSL L 2 5)
    (P : Sylow 2 L) (D : Subgroup L)
    (hn : (P : Subgroup L) ≤ normalizer (D : Set L))
    (hq : IsPGroup 3 (D ⧸ pCore 2 D)) (p : P) :
    quotientAut (pCore 2 D) (D.normalizerMonoidHom ⟨p, hn p.property⟩) = 1 := by
  obtain ⟨e⟩ := five_alternating_equiv hL
  exact Theory.PSL2.SylowFixedQuotients.sylow_conj_quotient_of_equiv_five e P D hn hq p

/-- A pointwise Sylow fixer preserves D and induces the identity on its
three-group quotient by the intrinsic two-core. -/
public theorem odd_linear_five_fixed_quotient (hL : ClassicalGroup.IsPSL L 2 5)
    (P : Sylow 2 L) (D : Subgroup L)
    (hn : (P : Subgroup L) ≤ normalizer (D : Set L))
    (hq : IsPGroup 3 (D ⧸ pCore 2 D)) (β : MulAut L) (hβ : ∀ x ∈ P, β x = x) :
    ∃ hD : D.map β.toMonoidHom = D,
      quotientAut (pCore 2 D) ((β.subgroupMap D).trans (MulEquiv.subgroupCongr hD)) = 1 := by
  obtain ⟨e⟩ := five_alternating_equiv hL
  exact Theory.PSL2.SylowFixedQuotients.sylow_fixed_quotient_of_equiv_five e P D hn hq β hβ

end CFSG.Quasithin.Chapter15.Section04.LocalSetup
