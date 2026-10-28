module

public import CFSG.Quasithin.ChapterA.Section01.Linear.Singer.Defs
public import CFSG.Quasithin.ChapterA.Section01.Linear.Singer.Primitive
public import CFSG.Quasithin.ChapterA.Section01.Linear.Singer.Six
public import Theory.NumberTheory.BinaryPrimitiveDivisor.General
public import FeitThompson.FinalTheorem

/-!
# Odd Singer-cycle overgroups

For A.1.12, oddness supplies solvability by the odd-order theorem. Dimensions
zero and one are immediate since their full binary linear group is trivial.
The reusable regular-action module proves the actor's order, its own
centralizer, and irreducibility, without assuming overgroup normality.

Binary Zsigmondy supplies a primitive prime outside dimension six. The
proved odd-order fixed-vector theorem completes that branch. In dimension
six, the actual F₈ centralizer realization and Dickson's theorem complete
the exceptional branch. Thus every odd-order overgroup normalizes X.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.12, printed p.22.
-/

namespace CFSG.Quasithin.ChapterA.Singer

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The solvability input to the Singer-overgroup proof follows from oddness. -/
public theorem isSolvable_of_odd (Y : Subgroup (V ≃ₗ[ZMod 2] V))
    (hodd : Odd (Nat.card Y)) : Group.IsSolvable Y := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (V ≃ₗ[ZMod 2] V) :=
    Finite.of_injective (fun g : V ≃ₗ[ZMod 2] V => (g : V → V)) DFunLike.coe_injective
  exact odd_order_theorem Y hodd

/-- The zero- and one-dimensional cases of A.1.12, with relative normality
in the specified overgroup. Cyclicity and regularity are unnecessary here. -/
public theorem normal_of_finrank_le_one (X Y : Subgroup (V ≃ₗ[ZMod 2] V))
    (hXY : X ≤ Y) (hn : Module.finrank (ZMod 2) V ≤ 1) : (X.subgroupOf Y).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mpr
    (LinearGroup.le_normalizer_of_binary_finrank_le_one hn X Y)

/-- A cyclic binary linear group regular on nonzero vectors is normal in
each of its odd-order overgroups. -/
public theorem normal_of_odd (X Y : Subgroup (V ≃ₗ[ZMod 2] V))
    (hcyc : IsCyclic X) (hreg : LinearGroup.IsRegularOnNonzero X)
    (hXY : X ≤ Y) (hodd : Odd (Nat.card Y)) : (X.subgroupOf Y).Normal := by
  by_cases hn : Module.finrank (ZMod 2) V ≤ 1
  · exact normal_of_finrank_le_one X Y hXY hn
  have hsolv := isSolvable_of_odd Y hodd
  by_cases h6 : Module.finrank (ZMod 2) V = 6
  · let := hcyc
    exact Six.normal_of_finrank_eq_six h6 X Y hreg hXY hodd hsolv
  obtain ⟨r, hr, hord⟩ := Theory.NumberTheory.exists_prime_orderOf_two (by omega) h6
  exact normal_of_primitive_prime X Y hcyc hreg hXY hodd hsolv (by omega) hr hord
    (primeFixedPointCentralization_of_odd Y hodd)

end CFSG.Quasithin.ChapterA.Singer
