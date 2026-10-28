module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.VertexConstruction.MarkedLattices.Reduction
public import Theory.Representation.PRegularTrace

/-!
# The trace identity for ordinary vertex reductions

Lift each modular eigenvalue to a power of the specified integral root.
The complex map gives its Brauer value and the residue map gives its trace.
Injectivity of the complex map therefore transports the tree decomposition
back to the localization and then to the residue field. The simultaneous
p-regular-part theorem extends the trace identity to all group elements.

These are the reduction and additivity steps of Feit IV.2.1. Trace equality
alone is not a classification of modular representations: composition-factor
multiplicities and the ordinary degree bound must still be used.
-/

public section
noncomputable section
open scoped Classical

namespace Representation.CyclicDefect.PrimeOrderRealLine

open ModularBlock.PrimeBlockConstruction ModularBlock.PrimeIntegralModels
open ModularBlock.BlockOrthogonality

variable {K G : Type*} [Field K] [Group G] [Finite G]
    {p m : ℕ} {d : PrimeCongruenceBlockData p G}
    [NeZero m] [NeZero (m : K)]

namespace CompatibleRoots

/-- A modular root lifted to the actual localization, using the same exponent
as the compatible complex root correspondence. -/
@[expose] def integralEigenvalue (r : CompatibleRoots d K m) (x : K) :
    Localization.AtPrime d.primeIdeal :=
  if h : ∃ j : Fin m, (r.residue r.root) ^ (j : ℕ) = x then
    r.root ^ (h.choose : ℕ)
  else 0

theorem complex_integralEigenvalue (r : CompatibleRoots d K m) (x : K) :
    localizationToComplex d.primeIdeal (r.integralEigenvalue x) =
      r.lift.eigenvalue x := by
  unfold integralEigenvalue CyclicRootLift.eigenvalue
  simp only [lift]
  split <;> rename_i h <;> simp [h]

theorem residue_integralEigenvalue (r : CompatibleRoots d K m) (x : K)
    (hx : x ^ m = 1) : r.residue (r.integralEigenvalue x) = x := by
  obtain ⟨j, hj, hjx⟩ := r.lift.modular_primitive.eq_pow_of_pow_eq_one hx
  have h : ∃ j : Fin m, (r.residue r.root) ^ (j : ℕ) = x := ⟨⟨j, hj⟩, hjx⟩
  rw [integralEigenvalue, dif_pos h, map_pow]
  exact h.choose_spec

variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- The eigenvalue sum before applying either coefficient map. -/
@[expose] def integralValue (r : CompatibleRoots d K m)
    (ρ : Representation K G V) (g : G) : Localization.AtPrime d.primeIdeal :=
  ((ρ g).charpoly.roots.map r.integralEigenvalue).sum

theorem complex_integralValue (r : CompatibleRoots d K m)
    (ρ : Representation K G V) (g : G) :
    localizationToComplex d.primeIdeal (r.integralValue ρ g) = r.lift.value ρ g := by
  rw [integralValue, map_multiset_sum, Multiset.map_map]
  simp only [Function.comp_def, complex_integralEigenvalue, CyclicRootLift.value]

/-- On the specified root group, the residue of the integral eigenvalue sum
is the field-valued trace, with every algebraic multiplicity retained. -/
theorem residue_integralValue [IsAlgClosed K] (r : CompatibleRoots d K m)
    (ρ : Representation K G V) (g : G) (hg : g ^ m = 1) :
    r.residue (r.integralValue ρ g) = ρ.character g := by
  rw [integralValue, map_multiset_sum, Multiset.map_map]
  change _ = LinearMap.trace K _ (ρ g)
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  congr 1
  conv_rhs => rw [← Multiset.map_id (ρ g).charpoly.roots]
  apply Multiset.map_congr rfl
  intro x hx
  exact r.residue_integralEigenvalue x (CyclicRootLift.root_pow_eq_one ρ g hg hx)

end CompatibleRoots

namespace RealValency.SerialModules

/-- Reduce the literal incident-edge character identity integrally before
passing to the coefficient field. -/
theorem reduction_character_eq_incident_sum_of_regular [IsAlgClosed K]
    {n : ℕ} (r : CompatibleRoots d K m) (t : Tree d.chi d.block p n r.lift)
    (v : {i // i ∈ d.block}) (X : OrdinaryLattice d v.val)
    (g : G) (hg : ¬ p ∣ orderOf g) (hm : orderOf g ∣ m) :
    (X.reduction r).character g = ∑ e ∈ t.incident v, (t.rep e).character g := by
  classical
  have hp : g ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp hm
  have hi : r.integralValue (X.reduction r) g =
      ∑ e ∈ t.incident v, r.integralValue (t.rep e) g := by
    apply localizationToComplex_injective d.primeIdeal
    simp only [map_sum, CompatibleRoots.complex_integralValue]
    exact reduction_value_eq_incident_sum r t v X g hg hm
  have hres := congrArg r.residue hi
  simpa only [map_sum, r.residue_integralValue _ g hp] using hres

/-- Equality of traces on all group elements. This is an input to the
composition-factor argument, not an assertion of equivalence or semisimplicity. -/
theorem reduction_character_eq_incident_sum [IsAlgClosed K] [Fact p.Prime] [CharP K p]
    {n : ℕ} (r : CompatibleRoots d K m) (t : Tree d.chi d.block p n r.lift)
    (horder : ∀ g : G, ¬ p ∣ orderOf g → orderOf g ∣ m)
    (v : {i // i ∈ d.block}) (X : OrdinaryLattice d v.val) (g : G) :
    (X.reduction r).character g = ∑ e ∈ t.incident v, (t.rep e).character g := by
  obtain ⟨h, hreg, heq⟩ := exists_pRegular_same_character (F := K) p g
  calc
    (X.reduction r).character g = (X.reduction r).character h := heq _ _
    _ = ∑ e ∈ t.incident v, (t.rep e).character h :=
      reduction_character_eq_incident_sum_of_regular r t v X h hreg (horder h hreg)
    _ = ∑ e ∈ t.incident v, (t.rep e).character g :=
      Finset.sum_congr rfl (fun e _ => (heq _ (t.rep e)).symm)

end RealValency.SerialModules
end Representation.CyclicDefect.PrimeOrderRealLine
