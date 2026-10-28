module

public import Theory.GroupTheory.PPrimeCoreNormalComplement
public import Mathlib.GroupTheory.Complement

/-!
# Prime-group quotients of split extensions

If `H = ND`, where `N` is normal and `N ∩ D = 1`, then `H/N ≃ D`.
Composing with the quotient by the prime-complement core of `D` gives
a surjective homomorphism. When `D` has a normal `p`-complement and
`p ∣ |D|`, its target is a nontrivial `p`-group.

This is the elementary quotient argument after Proposition 17.6 in
GLS, Volume 4, Chapter 2. Normality is needed only inside `H`.
-/

noncomputable section

namespace Subgroup

variable {H : Type*} [Group H] {D N : Subgroup H} [N.Normal]

/-- The quotient onto a complement, followed by the quotient by its `p′`-core. -/
public def IsComplement'.toPrimeComplementQuotient
    (h : D.IsComplement' N) (p : ℕ) : H →* D ⧸ pPrimeCore p D :=
  (QuotientGroup.mk' (pPrimeCore p D)).comp
    (h.QuotientMulEquiv.toMonoidHom.comp (QuotientGroup.mk' N))

public theorem IsComplement'.toPrimeComplementQuotient_surjective
    (h : D.IsComplement' N) (p : ℕ) :
    Function.Surjective (h.toPrimeComplementQuotient p) :=
  (QuotientGroup.mk'_surjective (pPrimeCore p D)).comp
    (h.QuotientMulEquiv.surjective.comp (QuotientGroup.mk'_surjective N))

end Subgroup

/-- A prime dividing the group order survives in the quotient by its
prime-complement core. No normal-complement assumption is needed here. -/
public theorem nontrivial_quotient_pPrimeCore_of_dvd_card
    {p : ℕ} [Fact p.Prime] {D : Type*} [Group D] [Finite D]
    (hp : p ∣ Nat.card D) : Nontrivial (D ⧸ pPrimeCore p D) := by
  apply QuotientGroup.nontrivial_iff.mpr
  intro htop
  have hcop := pPrimeCore_coprime_card (p := p) (G := D)
  rw [htop, Subgroup.card_top] at hcop
  exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).mp hcop hp
