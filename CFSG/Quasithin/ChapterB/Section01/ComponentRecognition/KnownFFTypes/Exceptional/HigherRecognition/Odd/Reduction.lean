module

public import Theory.Representation.BinaryOffender.EndFieldTransport
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Exceptional.HigherRecognition.Models

/-!
# The scalar and numerical reduction for odd exceptional FF exclusion

Write Q = N/Z(N) for the literal central quotient of the normal quasisimple
subgroup in the source. Two separate estimates suffice: an offender bounds
|V| by |Aut(Q)|², while the degree of a faithful absolutely irreducible
characteristic-two N-module d satisfies |Aut(Q)|² < 2^d.

We apply the latter to the actual commuting endomorphism field of the binary
restriction to N. Thus absolute irreducibility is proved, not added to the
binary hypotheses. Its degree gives a lower bound for |V|, contradicting
the first estimate. Neither estimate is proved by this reduction.

The ambient finiteness, normality, quasisimplicity, F*(H) = N and concrete
odd exceptional carrier hypotheses belong to the producers of those two
estimates. They are not needed by the scalar comparison itself.

Source: Guralnick--Malle, *Classification of 2F-modules, I*, Section 2 and
Proposition 4.6, internal pp.14--15; the projective degree input is Seitz--
Zalesskii, *On the minimal degrees of projective representations of the finite
Chevalley groups, II*, J. Algebra 158 (1993), 233--243. See ../Source.md.
-/

public section

open scoped MonoidAlgebra
open Subgroup Representation Representation.BinaryOffender
set_option backward.isDefEq.respectTransparency false

universe u v
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.Odd
variable {H : Type u} {V : Type v} [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) H V) (N : Subgroup H)
  [IsIrreducible (ρ.comp N.subtype)]

/-- Compare the original module size with the absolute degree of its actual component action. -/
theorem not_ff_of_component_estimates
    (hupper : ∀ A : Subgroup H, IsOffender ρ A →
      Nat.card V ≤ Nat.card (MulAut (N ⧸ center N)) ^ 2)
    (hdegree : Nat.card (MulAut (N ⧸ center N)) ^ 2 <
      2 ^ Module.finrank (Module.End (ZMod 2)[N] (Representation.asModule (ρ.comp N.subtype)))
        (Representation.asModule (ρ.comp N.subtype))) : ¬ IsFFModule ρ := by
  rintro ⟨A, hA⟩
  exact (not_lt_of_ge (hupper A hA))
    (hdegree.trans_le (two_pow_endField_finrank_le_card (ρ.comp N.subtype)))

/-- Instantiate a degree theorem over arbitrary finite fields at the actual
endomorphism field of the binary component action. Both numerical estimates
remain explicit; this is not yet the odd exceptional exclusion. -/
theorem not_ff_of_absolute_component_estimates
    (hρ : Function.Injective ρ)
    (hupper : ∀ A : Subgroup H, IsOffender ρ A →
      Nat.card V ≤ Nat.card (MulAut (N ⧸ center N)) ^ 2)
    (hdegree : ∀ (K : Type v) [Field K] [Finite K] [CharP K 2]
      [Module K V] [FiniteDimensional K V] (σ : Representation K N V),
      Function.Injective σ → IsAbsolutelyIrreducible σ →
        Nat.card (MulAut (N ⧸ center N)) ^ 2 < 2 ^ Module.finrank K V) :
    ¬ IsFFModule ρ := by
  apply not_ff_of_component_estimates ρ N hupper
  let σ : Representation (ZMod 2) N V := ρ.comp N.subtype
  let E := Module.End (ZMod 2)[N] σ.asModule
  let : CharP E 2 := endFieldRep_charTwo σ
  let : Module E V := endFieldModule σ
  let : FiniteDimensional E V := endFieldRep_finiteDimensional σ
  exact hdegree E σ.endFieldRep
    (endFieldRep_injective σ (fun _ _ h => Subtype.ext (hρ h)))
    (endFieldRep_isAbsolutelyIrreducible σ)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Exceptional.Higher.Odd
