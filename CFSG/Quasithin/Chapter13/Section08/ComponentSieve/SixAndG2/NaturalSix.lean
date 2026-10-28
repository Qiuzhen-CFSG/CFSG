module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Transport
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Extensions
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Normalizer
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix.Marked

/-!
# Intrinsic degree-six module facts for the A₆ component sieve

The literal natural and augmentation actions are faithful. Nontrivial
elementary actors with a total commutator line have rank one, and a
transvection actor is the full pointwise kernel on its fixed space.
These facts transport through compatible actor embeddings and module
equivalences. The full linear normalizer of the alternating natural image
is the symmetric natural image. Consequently a faithful extension of the
marked alternating action gives an actual A₆/S₆ isomorphism, retaining
both the prescribed subgroup embedding and the entire action.

The pentad outer automorphism compares the two marked natural actions.
On the standard action the syntheme's two-residual has two noncentral
irreducible sections. On the opposite action its parabolic fixes a nonzero
vector, and the distinguished rank-three transvection subgroup is not
quadratic. The residual and subgroup maps retain their literal embeddings;
the residual is distinguished from the larger full S₄ intersection.

These are intrinsic model results. The source assembly still supplies its
representation recognition, marked subgroup identifications and perfect
central-cover projection; it can then use the comparison in `SixAndG2.Cover`.

Source: Aschbacher–Smith 13.8.26–27, printed pp.962–963, and B.3.2–4, pp.83–85.
-/

public section

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix

/-- A faithful action extending the prescribed natural A₆ action identifies
the whole acting group with A₆ or S₆. The permutation embedding agrees with
the given identification of `K`, and intertwines the entire action through
the original module equivalence. The normalizer calculation is discharged. -/
theorem faithful_extension
    {H U : Type*} [Group H] [AddCommGroup U] [Module (ZMod 2) U]
    (K : Subgroup H) [K.Normal]
    (ρ : Representation (ZMod 2) H U) (hρ : Function.Injective ρ)
    (eK : K ≃* Alternating) (E : U ≃ₗ[ZMod 2] Natural)
    (he : ∀ k : K, ∀ u, E (ρ k u) = alternatingAction (eK k) (E u)) :
    ∃ f : H →* Symmetric, Function.Injective f ∧
      (∀ k : K, f k = (eK k).val) ∧
      (∀ h u, E (ρ h u) = symmetricAction (f h) (E u)) ∧
      ((∃ e : H ≃* Alternating, ∀ h, (e h).val = f h) ∨
        (∃ e : H ≃* Symmetric, ∀ h, e h = f h)) :=
  faithful_extension_of_normalizer normalizer_alternatingImage K ρ hρ eK E he

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.SixAndG2.NaturalSix
