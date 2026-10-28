module

public import Theory.Representation.SU3.FiveSmallModules.Degrees.Inputs
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport

/-!
# Principal-series reduction of the absolute degree window

A Borel eigenline makes an irreducible module an actual quotient of an induced
character. A simple-factor filtration of that induced module then bounds the
possible degrees. Pullback through a surjective central cover and an explicit
Hermitian basis change applies this argument to every source cover.

The root eigenline calculation and the principal-series filtrations remain
explicit premises. No minimum-degree theorem, faithful action on SU₃, trivial
center, or coefficient-field descent assumption is used.

Source: Guralnick–Malle, *Classification of 2F-modules I*, Proposition 4.3,
p.10; Aschbacher–Smith K.2, printed p.453.
-/

public section

open BenderSuzuki.MatrixGroups
open HermitianForm.OddPrimeSylow.NormalizedOuter
namespace Representation.SU3.FiveSmallModules.Degrees
universe u v

/-- The eigenline produces an actual quotient of the specified principal
series. Its checked filtration then excludes degrees 22, 23 and 24. -/
theorem degree_window_of_borel_inputs
    (hline : RootEigenlineInput.{u, v}) (hseries : PrincipalSeriesFiltrations.{u, v})
    {F : Type u} [Field F] [Finite F] (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    {K U : Type v} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K (standardGroup J) U)
    (hker : τ.ker ≤ Subgroup.center (standardGroup J)) (hi : τ.IsAbsolutelyIrreducible)
    (hlo : 20 ≤ Module.finrank K U) (hhi : Module.finrank K U ≤ 24) :
    Module.finrank K U = 20 ∨ Module.finrank K U = 21 := by
  by_contra h
  have h22 : 22 ≤ Module.finrank K U := by omega
  obtain ⟨χ, v, hv, hχ⟩ := hline F J hc hconj K U τ hker hi h22 hhi
  let : IsIrreducible τ := hi.irreducible_of_isAbsolutelyIrreducible τ
  have hn : inducedMap (standardBorel J) χ τ v hχ ≠ 0 := by
    intro hz
    apply hv
    have hh := inducedMap_mk_one (standardBorel J) χ τ v hχ
    rw [hz] at hh
    exact hh.symm
  have hd := (hseries F J hc hconj K χ).finrank_mem _ hn
  simp only [principalSeriesDegrees, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
  omega

/-- The source action is pulled back along a genuine surjective central
cover map, then along an actual Hermitian basis change. Neither its kernel
nor the input Gram matrix is assumed trivial or standard. -/
theorem degree_window_of_central_cover
    (hline : RootEigenlineInput.{u, v}) (hseries : PrincipalSeriesFiltrations.{u, v})
    {F : Type u} {R : Type*} [Field F] [Finite F] [Group R]
    (J : HermitianForm 3 F)
    (hc : Nat.card F = 5 ^ 2) (hconj : ∀ x, J.conj x = x ^ 5)
    (f : J.specialSubgroup →* R) (hs : Function.Surjective f)
    (hk : f.ker ≤ Subgroup.center J.specialSubgroup)
    {K U : Type v} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    (τ : Representation K R U) (hf : Function.Injective τ)
    (hi : τ.IsAbsolutelyIrreducible)
    (hlo : 20 ≤ Module.finrank K U) (hhi : Module.finrank K U ≤ 24) :
    Module.finrank K U = 20 ∨ Module.finrank K U = 21 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hfixed : Nat.card {x : F // J.conj x = x} = 5 := by
    simpa only [pow_one] using FiniteField.card_fixed_of_quadratic_frobenius
      J.conj 5 1 (by decide) (by simpa only [pow_one] using hc)
        (by simpa only [pow_one] using hconj)
  obtain ⟨C, hC⟩ := FormTransport.exists_standard_basis J 5 hc hfixed
  let e := FormTransport.specialEquiv J C hC
  let p : standardGroup J →* R := f.comp e.symm.toMonoidHom
  have hp : Function.Surjective p := hs.comp e.symm.surjective
  let σ : Representation K (standardGroup J) U := τ.comp p
  have hσ : σ.IsAbsolutelyIrreducible := absolutelyIrreducible_comp_surjective p hp τ hi
  have hσker : σ.ker ≤ Subgroup.center (standardGroup J) := by
    intro x hx
    have hx' : e.symm x ∈ f.ker := by
      apply hf
      exact (MonoidHom.mem_ker.mp hx).trans (map_one τ).symm
    have hcentral := Subgroup.mem_center_iff.mp (hk hx')
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply e.symm.injective
    simpa only [map_mul] using hcentral (e.symm y)
  exact degree_window_of_borel_inputs hline hseries J hc hconj σ hσker hσ hlo hhi

end Representation.SU3.FiveSmallModules.Degrees
