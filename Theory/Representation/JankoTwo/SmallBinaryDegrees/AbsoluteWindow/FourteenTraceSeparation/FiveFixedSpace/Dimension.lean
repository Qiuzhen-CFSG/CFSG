module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveFixedSpace.LocalGeometry
public import Theory.Representation.BinaryOddDisplacement.PrimeDivisibility
public import Theory.Representation.BinaryCoprimeDegree.HyperplaneBounds.Decomposition

/-!
# The binary fixed dimension from five-local normalizer orbits

The hyperplane decomposition gives a bound on the moved dimension itself.
Faithfulness supplies a nonzero contribution; all hyperplanes in its normalizer
orbit contribute equally, and each nonzero contribution has at least the binary
prime degree. For order 25 and orbit length at least three, this gives twelve
moved dimensions. Fixed-point counting for the five-group also makes the moved
dimension divisible by four. In dimension fourteen it is therefore exactly
twelve, leaving two fixed dimensions.

No irreducibility, modular character catalogue, or field-of-definition theorem
is used. The spectral decomposition and scalar transport are supplied by the
existing `hyperplane_dimension_sum` theorem.

Sources: Aschbacher--Smith G.7.1(3), printed p.347, for the hyperplane argument;
the local restriction needed for Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, manuscript p.16.
-/

public section
namespace Representation.BinaryCoprimeDegree
open BinaryOffender

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- The hyperplane orbit estimate bounds the moved dimension, even when the
common fixed space is nonzero. -/
theorem hyperplane_orbit_mul_primeDegree_le_fixedCodim
    (σ : Representation (ZMod 2) G V) (hf : Function.Injective σ)
    {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (P : Subgroup G) [IsElementaryAbelian p P] (hne : P ≠ ⊥) (n : ℕ)
    (horbit : ∀ H : Subgroup P, H.index = p →
      n ≤ Nat.card (normalizerHyperplaneOrbit P H)) :
    n * orderOf (2 : ZMod p) ≤ fixedCodim σ P := by
  classical
  have hproper := fixed_finrank_lt_of_faithful σ hf P hne
  have hsum := hyperplane_dimension_sum σ hp2 P
  have hpos : 0 < hyperplaneDimensionSum σ P p := by omega
  obtain ⟨H, hH, hm⟩ := Finset.sum_pos_iff.mp hpos
  have hidx := (mem_hyperplanes P p H).mp hH
  have hprime := orderOf_le_hyperplaneMultiplicity σ hp2 P H hidx hm
  have hbound : n * orderOf (2 : ZMod p) ≤ hyperplaneDimensionSum σ P p := calc
    _ ≤ Nat.card (normalizerHyperplaneOrbit P H) * hyperplaneMultiplicity σ P H :=
      Nat.mul_le_mul (horbit H hidx) hprime
    _ ≤ _ := orbit_mul_multiplicity_le_sum σ P H hidx
  have hcodim := fixedCodim_add_finrank σ P
  change fixedCodim σ P + Module.finrank (ZMod 2) (invariants (σ.comp P.subtype)) = _
    at hcodim
  omega

/-- A faithful binary fourteen-dimensional module has a two-dimensional
fixed space for an elementary order-25 subgroup with hyperplane orbits of
length at least three. -/
theorem finrank_invariants_eq_two_of_five_orbits
    (σ : Representation (ZMod 2) G V) (hf : Function.Injective σ)
    (hdim : Module.finrank (ZMod 2) V = 14)
    (P : Subgroup G) [IsElementaryAbelian 5 P] (hP : Nat.card P = 25)
    (horbit : ∀ H : Subgroup P, H.index = 5 →
      3 ≤ Nat.card (normalizerHyperplaneOrbit P H)) :
    Module.finrank (ZMod 2) (invariants (σ.comp P.subtype)) = 2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hP
    omega
  have hlo : 12 ≤ fixedCodim σ P := by
    simpa only [BinaryPrimeDegree.orderOf_two_mod_five, Nat.reduceMul] using
      hyperplane_orbit_mul_primeDegree_le_fixedCodim σ hf (by decide) P hne 3 horbit
  have hdiv : 4 ∣ fixedCodim σ P := by
    simpa only [BinaryPrimeDegree.orderOf_two_mod_five] using
      orderOf_two_dvd_fixedCodim_of_isPGroup σ (by decide : Nat.Prime 5) (by decide) P
        (IsPGroup.of_card (p := 5) (n := 2) (by simpa using hP))
  have hcodim := fixedCodim_add_finrank σ P
  change fixedCodim σ P + Module.finrank (ZMod 2) (invariants (σ.comp P.subtype)) = _
    at hcodim
  omega

end Representation.BinaryCoprimeDegree
