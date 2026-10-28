module

public import Theory.Representation.BinaryCoprimeDegree.HyperplaneOrbit
public import Theory.Representation.BinaryPrimeDegree
public import Theory.Representation.BinaryCoprimeDegree.HyperplaneBounds.PrimeContribution
public import Theory.Representation.BinaryCoprimeDegree.HyperplaneBounds.Decomposition
import Mathlib.Tactic

/-!
# Binary hyperplane-orbit degree bounds

For a faithful binary representation and a nontrivial elementary abelian
odd-order subgroup, normalizer orbits preserve the dimensions contributed
by hyperplanes. Each nonzero contribution has at least the prime degree.
The character-space decomposition shows that these contributions sum to
the moving dimension, so orbit counting gives the degree bound.
If equality holds, the common fixed space has dimension zero, and the same
orbit estimate forces every nonzero hyperplane fixed space to have exactly
the prime degree.

The final theorem discharges the dimension-sum identity internally. It
proves the representation-theoretic content of Aschbacher--Smith,
*The Classification of Quasithin Groups*, G.7.1(3), printed p.347
(PDF p.358), for any lower bound on the actual normalizer orbit lengths.
No vanishing of the common fixed space is assumed, and the unrestricted
direct-product clause of A.1.17 is not used.
-/

public section

namespace Representation.BinaryCoprimeDegree

/-- Orbit counting and the prime-degree bound imply both conclusions once
hyperplane contributions exhaust the moving dimension. -/
theorem hyperplane_orbit_degree_of_dimension_sum
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) G V) (hf : Function.Injective rho)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Subgroup G) [IsElementaryAbelian p P] (hP : P ≠ ⊥) (n : ℕ)
    (hn : ∀ H : Subgroup P, H.index = p → n ≤ Nat.card (normalizerHyperplaneOrbit P H))
    (hsum : hyperplaneDimensionSum rho P p +
        Module.finrank (ZMod 2) (invariants (rho.comp P.subtype)) =
      Module.finrank (ZMod 2) V) :
    n * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V ∧
      (Module.finrank (ZMod 2) V = n * orderOf (2 : ZMod p) →
        ∀ H : Subgroup P, H.index = p →
          invariants (rho.comp (P.subtype.comp H.subtype)) ≠ ⊥ →
          Module.finrank (ZMod 2)
            (invariants (rho.comp (P.subtype.comp H.subtype))) = orderOf (2 : ZMod p)) := by
  classical
  have hproper := fixed_finrank_lt_of_faithful rho hf P hP
  have hpos : 0 < hyperplaneDimensionSum rho P p := by omega
  obtain ⟨H₀, hH₀, hm₀⟩ := Finset.sum_pos_iff.mp hpos
  have hidx₀ := (mem_hyperplanes P p H₀).mp hH₀
  have hbound : n * orderOf (2 : ZMod p) ≤ hyperplaneDimensionSum rho P p := calc
    _ ≤ Nat.card (normalizerHyperplaneOrbit P H₀) * hyperplaneMultiplicity rho P H₀ :=
      Nat.mul_le_mul (hn H₀ hidx₀) (orderOf_le_hyperplaneMultiplicity rho hp2 P H₀ hidx₀ hm₀)
    _ ≤ _ := orbit_mul_multiplicity_le_sum rho P H₀ hidx₀
  refine ⟨by omega, ?_⟩
  intro heq H hH hfix
  have hnpos : 0 < n := by
    by_contra! hz
    have : n = 0 := by omega
    simp only [this, zero_mul] at heq
    omega
  have hcommon : Module.finrank (ZMod 2) (invariants (rho.comp P.subtype)) = 0 := by omega
  have hmult : hyperplaneMultiplicity rho P H =
      Module.finrank (ZMod 2) (invariants (rho.comp (P.subtype.comp H.subtype))) := by
    simp only [hyperplaneMultiplicity, hcommon, Nat.sub_zero]
  have hm : 0 < hyperplaneMultiplicity rho P H := by
    rw [hmult]
    exact Nat.pos_of_ne_zero fun hz => hfix (Submodule.finrank_eq_zero.mp hz)
  have hlow := orderOf_le_hyperplaneMultiplicity rho hp2 P H hH hm
  have hupp : n * hyperplaneMultiplicity rho P H ≤ n * orderOf (2 : ZMod p) := calc
    _ ≤ Nat.card (normalizerHyperplaneOrbit P H) * hyperplaneMultiplicity rho P H :=
      Nat.mul_le_mul_right _ (hn H hH)
    _ ≤ hyperplaneDimensionSum rho P p := orbit_mul_multiplicity_le_sum rho P H hH
    _ ≤ n * orderOf (2 : ZMod p) := by omega
  have hle : hyperplaneMultiplicity rho P H ≤ orderOf (2 : ZMod p) := by nlinarith
  exact hmult ▸ le_antisymm hle hlow

/-- A lower bound on all normalizer orbits of hyperplanes bounds the degree
of a faithful binary representation. In case of equality, every nonzero
hyperplane fixed space in the original module has exactly the prime degree. -/
theorem hyperplane_orbit_degree
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (rho : Representation (ZMod 2) G V) (hf : Function.Injective rho)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Subgroup G) [IsElementaryAbelian p P] (hP : P ≠ ⊥) (n : ℕ)
    (hn : ∀ H : Subgroup P, H.index = p → n ≤ Nat.card (normalizerHyperplaneOrbit P H)) :
    n * orderOf (2 : ZMod p) ≤ Module.finrank (ZMod 2) V ∧
      (Module.finrank (ZMod 2) V = n * orderOf (2 : ZMod p) →
        ∀ H : Subgroup P, H.index = p →
          invariants (rho.comp (P.subtype.comp H.subtype)) ≠ ⊥ →
          Module.finrank (ZMod 2)
            (invariants (rho.comp (P.subtype.comp H.subtype))) = orderOf (2 : ZMod p)) :=
  hyperplane_orbit_degree_of_dimension_sum rho hf hp2 P hP n hn
    (hyperplane_dimension_sum rho hp2 P)

end Representation.BinaryCoprimeDegree
