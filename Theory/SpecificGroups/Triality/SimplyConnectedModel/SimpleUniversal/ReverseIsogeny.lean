module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Carrier
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Frobenius
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.SimpleUniversal.ReverseIsogeny.FrobeniusCoordinates
public import Theory.AlgebraicGroup.Morphism.BijectiveCoordinatePowers.Connected
public import Theory.AlgebraicGroup.Morphism.FrobeniusPowerDescent.PolynomialRoots

/-!
# Reverse isogenies into the concrete Spin group

Let `H` be a connected algebraic group over an algebraically closed field of
characteristic two. Every isogeny from `H` to the concrete four-plane Clifford
Spin carrier that is injective on points admits a regular reverse isogeny.
More precisely, the composite with the incoming map is a Spin Frobenius power.

Bijective coordinate descent gives a common power of two of the coordinates
of `H` in the image of pullback. The semilinear Clifford coefficient formulas
supply polynomial roots of the matching Spin Frobenius coordinates, including
in the carrier's arbitrary basis. The general descent construction then proves
regularity of the reverse map. All arguments apply over every algebraically
closed characteristic-two field.

This proves the injective incoming-map step of the universal-version property
in GLS3, Theorem 1.10.4(b) and Definition 1.10.5, using §§1.10–1.12 and 1.15
(`refs/KGroup/GLS3/Chapter1.tex`). Triviality of the incoming point kernel is a
separate obligation of the universality assembly.
-/

public section
noncomputable section
open Theory.AlgebraicGroup
universe u

namespace Triality.SimplyConnected
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- A bijective incoming isogeny from a connected algebraic group admits a
regular reverse isogeny factoring a sufficiently high Spin Frobenius power. -/
theorem exists_reverse_isogeny_frobenius_factorization
    {H : Variety k} [AlgebraicGroup H]
    (hH : _root_.IsConnected (Set.univ : Set (Variety.Point H)))
    (φ : Morphism H (groupVariety k)) (hφ : IsIsogeny φ)
    (hinj : Function.Injective φ.onPoints) :
    ∃ (n : ℕ) (ψ : Morphism (groupVariety k) H),
      IsIsogeny ψ ∧ φ.comp ψ = regularFrobeniusLift k n := by
  obtain ⟨n, hpow⟩ := φ.toVariety.exists_uniform_coordinate_frobenius_power 2
    (φ.exists_coordinate_two_powers_of_bijective_of_connected hH ⟨hinj, hφ.1⟩)
  obtain ⟨ψ, hψ, hcomp⟩ :=
    Morphism.exists_reverse_isogeny_of_polynomial_frobenius_roots 2 n φ hφ.1
      (regularFrobeniusLift k n).onPoints (regularFrobeniusLift_bijective k n)
      (ReverseIsogeny.regularFrobeniusLift_coordinate_roots k n) hpow
  refine ⟨n, ψ, hψ, ?_⟩
  apply Morphism.ext
  funext x
  exact DFunLike.congr_fun hcomp x

/-- The reverse-isogeny clause for the concrete Spin carrier, with injectivity
of the incoming point map explicit. This does not assert a regular inverse. -/
theorem exists_reverse_isogeny_of_injective
    {H : Variety k} [AlgebraicGroup H]
    (hH : _root_.IsConnected (Set.univ : Set (Variety.Point H)))
    (φ : Morphism H (groupVariety k)) (hφ : IsIsogeny φ)
    (hinj : Function.Injective φ.onPoints) :
    ∃ ψ : Morphism (groupVariety k) H, IsIsogeny ψ := by
  obtain ⟨_, ψ, hψ, _⟩ := exists_reverse_isogeny_frobenius_factorization k hH φ hφ hinj
  exact ⟨ψ, hψ⟩

end Triality.SimplyConnected
