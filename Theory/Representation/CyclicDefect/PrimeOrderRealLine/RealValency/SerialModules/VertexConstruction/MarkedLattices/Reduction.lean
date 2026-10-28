module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.Contracts
public import Theory.Representation.CyclicDefect.ProjectivePairing.Characters
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Splits

/-!
# Brauer characters of the literal ordinary lattice reductions

On an element whose order divides the compatible root order, all complex
eigenvalues lift from the localization. Descend the split characteristic
polynomial through its injective complex embedding, then reduce the same
roots, retaining multiplicities. Thus every ordinary lattice has the Brauer
character specified by the tree's decomposition, at the actual residue map.

This is Feit IV.2.1(vi), used to identify the composition factors of the
lattices on p.279. The proof follows the nonprojective part of
`ProjectivePairing/LiftComparison/Regular.lean`; ordinary lattices are not
projective lifts. No socle or composition-series existence is inferred here.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules

open ModularBlock.PrimeBlockConstruction ModularBlock.PrimeIntegralModels
open ModularBlock.BlockOrthogonality

variable {K G : Type*} [Field K] [Group G] [Finite G]
    {p m : ℕ} {d : PrimeCongruenceBlockData p G}
    [NeZero m] [NeZero (m : K)]

namespace OrdinaryLattice

/-- The root correspondence for the actual residue map recovers the
prescribed ordinary character on all elements whose orders divide m. -/
theorem character_eq_lift_value {v : d.I} (X : OrdinaryLattice d v)
    (r : CompatibleRoots d K m) (g : G) (hg : g ^ m = 1) :
    d.chi v (ConjClasses.mk g) = r.lift.value (X.reduction r) g := by
  classical
  let f := localizationToComplex d.primeIdeal
  have hf : Function.Injective f := localizationToComplex_injective d.primeIdeal
  have hrange : ∀ z ∈ ((X.rep g).charpoly.map f).roots, z ∈ f.range := by
    intro z hz
    rw [← mapCoefficients_charpoly] at hz
    have hzpow := CyclicRootLift.root_pow_eq_one (mapCoefficients f X.rep) g hg hz
    obtain ⟨j, _, rfl⟩ := r.lift.complex_primitive.eq_pow_of_pow_eq_one hzpow
    exact ⟨r.root ^ j, by simp [f, CompatibleRoots.lift]⟩
  have hs : (X.rep g).charpoly.Splits :=
    Polynomial.Splits.of_splits_map_of_injective hf (IsAlgClosed.splits _) hrange
  have heigen : ∀ x ∈ (X.rep g).charpoly.roots,
      r.lift.eigenvalue (r.residue x) = f x := by
    intro x hx
    have hxc : f x ∈ ((X.rep g).charpoly.map f).roots := by
      rw [hs.roots_map_of_injective hf]
      exact Multiset.mem_map.mpr ⟨x, hx, rfl⟩
    rw [← mapCoefficients_charpoly] at hxc
    have hxpow := CyclicRootLift.root_pow_eq_one (mapCoefficients f X.rep) g hg hxc
    obtain ⟨j, _, hjx⟩ := r.lift.complex_primitive.eq_pow_of_pow_eq_one hxpow
    have hxj : x = r.root ^ j := hf (by
      rw [map_pow]
      exact hjx.symm)
    rw [hxj, map_pow, map_pow]
    exact r.lift.eigenvalue_pow_nat j
  rw [X.character_eq]
  change LinearMap.trace ℂ _ (mapCoefficients f X.rep g) =
    (((mapCoefficients r.residue X.rep g).charpoly.roots).map r.lift.eigenvalue).sum
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _),
    mapCoefficients_charpoly, mapCoefficients_charpoly,
    hs.roots_map_of_injective hf,
    hs.roots_map_of_ne_zero ((LinearMap.charpoly_monic _).map r.residue).ne_zero,
    Multiset.map_map]
  congr 1
  exact Multiset.map_congr rfl (fun x hx => (heigen x hx).symm)

end OrdinaryLattice

/-- The tree decomposition is the Brauer-character identity of each actual
lattice reduction, with exactly its incident edge modules as summands. -/
theorem reduction_value_eq_incident_sum {n : ℕ} (r : CompatibleRoots d K m)
    (t : Tree d.chi d.block p n r.lift)
    (v : {i // i ∈ d.block}) (X : OrdinaryLattice d v.val)
    (g : G) (hg : ¬ p ∣ orderOf g) (hm : orderOf g ∣ m) :
    r.lift.value (X.reduction r) g = ∑ e ∈ t.incident v, r.lift.value (t.rep e) g := by
  classical
  rw [← X.character_eq_lift_value r g (orderOf_dvd_iff_pow_eq_one.mp hm),
    t.decomposition g hg v]
  simp [Tree.incident, Finset.sum_filter]

end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules
