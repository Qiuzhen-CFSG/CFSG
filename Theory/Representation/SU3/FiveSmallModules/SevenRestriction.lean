module

public import Theory.Representation.SU3.FiveSmallModules.SevenRestriction.Spectral
public import Theory.Representation.Quotient
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Transport of the small principal-series seven-spectra

An actual subquotient equivalence transports the characteristic polynomial,
not just its trace. A surjective central-cover map and an explicit Hermitian
basis change then put every source action into the standard matrix group.
The lifted actor is only required to have an operator of order seven. Thus
no assertion about the order of an arbitrary group-theoretic lift is needed.

Both exhaustive recognition and the concrete principal-series spectra remain
explicit inputs. Their construction is independent, and final source assembly
must discharge both, together with the universal-cover input.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
pp.10–11; Aschbacher–Smith K.2, printed p.453.
-/

public section

open BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter
open Subgroup

namespace Representation.SU3.FiveSmallModules.SevenRestriction

universe u v

/-- Recognition and the finite spectral calculation apply to the same
literal subquotient, via its actual intertwining equivalence. -/
theorem charpoly_of_principal_series_inputs
    (hrecognition : PrincipalSeriesRecognition.{u, v})
    (hspectra : PrincipalSeriesSevenSpectra.{u, v})
    {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K U : Type v} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K (standardGroup J) U)
    (hker : τ.ker ≤ center (standardGroup J)) (hi : τ.IsAbsolutelyIrreducible)
    (hd : Module.finrank K U = 20 ∨ Module.finrank K U = 21)
    (x : standardGroup J) (hx : orderOf (τ x) = 7) :
    (τ x).charpoly = sevenSpectrum K (Module.finrank K U) := by
  obtain ⟨χ, S, T, ⟨e⟩⟩ := hrecognition F J hc hconj K U τ hker hi hd
  have hdim := e.toLinearEquiv.finrank_eq
  have horder := operator_order_eq_of_equiv e x
  have hs := hspectra F J hc hconj K χ S T (by rwa [← hdim]) x (horder.trans hx)
  exact (charpoly_eq_of_equiv e x).trans
    (hs.trans (congrArg (sevenSpectrum K) hdim.symm))

private theorem absolute_comp_surjective
    {K R Q U : Type*} [Field K] [Group R] [Group Q]
    [AddCommGroup U] [Module K U]
    (f : R →* Q) (hf : Function.Surjective f)
    (τ : Representation K Q U) (hi : τ.IsAbsolutelyIrreducible) :
    IsAbsolutelyIrreducible (τ.comp f) := by
  constructor
  change IsIrreducible ((τ.extendScalars (AlgebraicClosure K)).comp f)
  exact (irreducible_comp_surjective_iff f hf _).mpr hi.irreducible_of_closure

/-- Central-cover pullback and Hermitian basis change preserve the actual
operators. This yields the characteristic polynomial on the original module. -/
theorem charpoly_of_central_cover
    (hrecognition : PrincipalSeriesRecognition.{u, v})
    (hspectra : PrincipalSeriesSevenSpectra.{u, v})
    {F : Type u} {R : Type*} [Field F] [Finite F] [Group R]
    (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    (f : J.specialSubgroup →* R) (hs : Function.Surjective f)
    (hk : f.ker ≤ center J.specialSubgroup)
    {K U : Type v} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K R U) (hf : Function.Injective τ)
    (hi : τ.IsAbsolutelyIrreducible)
    (hd : Module.finrank K U = 20 ∨ Module.finrank K U = 21)
    (x : R) (hx : orderOf x = 7) :
    (τ x).charpoly = sevenSpectrum K (Module.finrank K U) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hfixed : Nat.card {a : F // J.conj a = a} = 5 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj 5 1 (by decide) (by simpa only [pow_one] using hc)
        (by simpa only [pow_one] using hconj)
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J 5 hc hfixed
  let e := FormTransport.specialEquiv J C hC
  let p : standardGroup J →* R := f.comp e.symm.toMonoidHom
  have hp : Function.Surjective p := hs.comp e.symm.surjective
  let σ : Representation K (standardGroup J) U := τ.comp p
  have hσ : σ.IsAbsolutelyIrreducible := absolute_comp_surjective p hp τ hi
  have hσker : σ.ker ≤ center (standardGroup J) := by
    intro y hy
    have hy' : e.symm y ∈ f.ker := by
      apply hf
      exact (MonoidHom.mem_ker.mp hy).trans (map_one τ).symm
    have hcentral := mem_center_iff.mp (hk hy')
    apply mem_center_iff.mpr
    intro z
    apply e.symm.injective
    simpa only [map_mul] using hcentral (e.symm z)
  obtain ⟨y, rfl⟩ := hp x
  exact charpoly_of_principal_series_inputs hrecognition hspectra J hc hconj σ
    hσker hσ hd y ((orderOf_injective τ hf _).trans hx)

/-- On every central quotient of the actual SU₃ model, the two independent
principal-series inputs imply the requested order-seven displacement. -/
theorem displacement_of_central_cover
    (hrecognition : PrincipalSeriesRecognition.{u, v})
    (hspectra : PrincipalSeriesSevenSpectra.{u, v})
    {F : Type u} {R : Type*} [Field F] [Finite F] [Group R]
    (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    (f : J.specialSubgroup →* R) (hs : Function.Surjective f)
    (hk : f.ker ≤ center J.specialSubgroup)
    {K U : Type v} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K R U) (hf : Function.Injective τ)
    (hi : τ.IsAbsolutelyIrreducible)
    (hd : Module.finrank K U = 20 ∨ Module.finrank K U = 21)
    (x : R) (hx : orderOf x = 7) :
    Module.finrank K (U ⧸ invariants (τ.comp (zpowers x).subtype)) = 18 :=
  displacement_of_sevenSpectrum τ x ((orderOf_injective τ hf x).trans hx) hd
    (charpoly_of_central_cover hrecognition hspectra J hc hconj f hs hk τ hf hi hd x hx)

end Representation.SU3.FiveSmallModules.SevenRestriction
