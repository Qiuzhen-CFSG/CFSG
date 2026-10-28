module

public import Theory.Representation.CyclicDefect.ProjectivePairing.LiftContracts
public import Theory.Representation.CyclicDefect.ProjectivePairing.Characters
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Regular characters of an integral lift

The complex eigenvalues of an element whose order divides the chosen root
order are powers of the chosen complex root. They therefore come from the
coefficient ring. Descending the split characteristic polynomial along the
injective complex map gives its roots over that ring, with multiplicity.
Mapping this factorization to the residue field and lifting each root back
gives exactly the complex trace.

This proves the comparison in Feit, *The Representation Theory of Finite
Groups*, IV.2.1(vi), used in IV.3.3 (printed pp.145–146). Projectivity is not
needed for this comparison; its separate role is vanishing at singular
elements. No residue-field trace is substituted for the Brauer eigenvalue sum.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.ProjectivePairing.IntegralLift

attribute [local instance] IntegralLift.coeffRing IntegralLift.coeffLocal

variable {K G V : Type*} [Field K] [Group G] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {m : ℕ} {L : CyclicRootLift K m}
  {Q : Representation K G V} (A : IntegralLift L Q)

/-- The complex representation obtained from the actual integral action. -/
@[expose] def complexRep : Representation ℂ G (Fin A.degree → ℂ) :=
  mapCoefficients A.complex A.rep

/-- The ordinary character agrees with the lifted eigenvalue sum whenever
the element's order divides the root order. Algebraic multiplicities are
preserved by mapping the integral characteristic polynomial. -/
theorem character_eq_value_of_pow_eq_one (g : G) (hg : g ^ m = 1) :
    A.complexRep.character g = L.value Q g := by
  classical
  let : IsDomain A.Coeff := Function.Injective.isDomain A.complex A.complex_injective
  let : NeZero m := ⟨L.positive.ne'⟩
  have hrange : ∀ z ∈ ((A.rep g).charpoly.map A.complex).roots,
      z ∈ A.complex.range := by
    intro z hz
    rw [← mapCoefficients_charpoly] at hz
    have hzpow := CyclicRootLift.root_pow_eq_one
      (mapCoefficients A.complex A.rep) g hg hz
    obtain ⟨j, _, rfl⟩ := L.complex_primitive.eq_pow_of_pow_eq_one hzpow
    exact ⟨A.root ^ j, by rw [map_pow, A.root_complex]⟩
  have hs : (A.rep g).charpoly.Splits :=
    Polynomial.Splits.of_splits_map_of_injective A.complex_injective
      (IsAlgClosed.splits _) hrange
  have heigen : ∀ x ∈ (A.rep g).charpoly.roots,
      L.eigenvalue (A.residue x) = A.complex x := by
    intro x hx
    have hxc : A.complex x ∈ ((A.rep g).charpoly.map A.complex).roots := by
      rw [hs.roots_map_of_injective A.complex_injective]
      exact Multiset.mem_map.mpr ⟨x, hx, rfl⟩
    rw [← mapCoefficients_charpoly] at hxc
    have hxpow := CyclicRootLift.root_pow_eq_one
      (mapCoefficients A.complex A.rep) g hg hxc
    obtain ⟨j, _, hjx⟩ := L.complex_primitive.eq_pow_of_pow_eq_one hxpow
    have hxj : x = A.root ^ j := A.complex_injective (by
      rw [map_pow, A.root_complex]
      exact hjx.symm)
    rw [hxj, map_pow, A.root_residue, L.eigenvalue_pow_nat, map_pow, A.root_complex]
  rw [← L.value_equiv A.reduction g]
  change LinearMap.trace ℂ _ (mapCoefficients A.complex A.rep g) =
    (((mapCoefficients A.residue A.rep g).charpoly.roots).map L.eigenvalue).sum
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _),
    mapCoefficients_charpoly, mapCoefficients_charpoly,
    hs.roots_map_of_injective A.complex_injective,
    hs.roots_map_of_ne_zero ((LinearMap.charpoly_monic _).map A.residue).ne_zero,
    Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl (fun x hx => (heigen x hx).symm)

/-- The regular-element clause for the precise root-order hypothesis used
by projective pairings. -/
theorem character_eq_value_of_regular (p : ℕ)
    (horder : ∀ g : G, ¬ p ∣ orderOf g → orderOf g ∣ m)
    (g : G) (hg : ¬ p ∣ orderOf g) :
    A.complexRep.character g = L.value Q g :=
  A.character_eq_value_of_pow_eq_one g (orderOf_dvd_iff_pow_eq_one.mp (horder g hg))

end Representation.CyclicDefect.ProjectivePairing.IntegralLift
