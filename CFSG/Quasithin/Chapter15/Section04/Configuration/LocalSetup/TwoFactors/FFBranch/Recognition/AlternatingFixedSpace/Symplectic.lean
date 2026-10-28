module

public import Theory.Representation.SymplecticNatural.CubicFixedSpace

/-!
# The natural symplectic A₆/S₆ alternatives, including extensions

The polar calculation uses the existing concrete matrix representation and
its actual equivariant bijection on nonzero vectors. It therefore treats
this model independently of the deleted-permutation model.

For extensions, the kernel of the map from the invariant layer is central
and the quotient of the whole module is trivial under the embedded A₆.
The cubic normalizer argument handles both extensions without a splitting.
The arbitrary embedding also retains genuine twists of the alternating
action and allows an outer involution to act on its trivial summands.

Source: Aschbacher–Smith B.4.2(3),(6), p.86; B.5.1(2),(4),(5), p.99;
Lemma 15.4.18, p.1163.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.AlternatingFixedSpace
open Representation Representation.BinaryOffender Representation.SymplecticCubicFixedSpace
open BinaryPermutation.CubicFixedSpace Theory.SpecificGroups.SymmetricSix

theorem polar_alternating_enlargement (S : Sylow 2 (alternatingGroup (Fin 6))) :
    ∃ d : alternatingGroup (Fin 6), d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace alternatingPolar (S : Subgroup _), alternatingPolar d v = v :=
  sylow_fixedSpace_enlargement_of_cubic _ _ (klein_isPGroup 6 (by decide)) _
    (cycle_pow 6 (by decide)) (cycle_ne_one 6 (by decide)) cycle_fixes_polar S

theorem polar_symmetric_enlargement (S : Sylow 2 S6) :
    ∃ d : S6, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ((symplecticNatural 2).comp polarRepresentation) (S : Subgroup _),
        symplecticNatural 2 (polarRepresentation d) v = v :=
  sylow_fixedSpace_enlargement_of_embedded_cubic
    ((symplecticNatural 2).comp polarRepresentation) (alternatingGroup (Fin 6)).subtype
    Subtype.val_injective _ (klein_isPGroup 6 (by decide)) _
    (cycle_pow 6 (by decide)) (cycle_ne_one 6 (by decide)) cycle_fixes_polar S

/-- The two-sided extension case with the actual polar natural section. -/
theorem polar_centralSection_enlargement
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)
    (f : alternatingGroup (Fin 6) →* D) (hf : Function.Injective f)
    (U : Subrepresentation (ρ.comp f))
    (q : U.toSubmodule →ₗ[ZMod 2] NaturalModule)
    (hq : ∀ g u, q (U.toRepresentation g u) = alternatingPolar g (q u))
    (hker : ∀ g u, q u = 0 → U.toRepresentation g u = u)
    (hquot : ∀ g v, ρ (f g) v - v ∈ U) (S : Sylow 2 D) :
    ∃ d : D, d ∉ S ∧ d ^ 3 = 1 ∧
      ∀ v ∈ fixedSpace ρ (S : Subgroup D), ρ d v = v := by
  apply sylow_fixedSpace_enlargement_of_embedded_cubic ρ f hf _
    (klein_isPGroup 6 (by decide)) _ (cycle_pow 6 (by decide))
    (cycle_ne_one 6 (by decide)) _ S
  exact cubic_fixedSpace_of_central_section (ρ.comp f) alternatingPolar _ _
    (cycle_pow 6 (by decide)) (cycle_normalizes 6 (by decide)) U q hq hker hquot
    cycle_fixes_polar

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.AlternatingFixedSpace
