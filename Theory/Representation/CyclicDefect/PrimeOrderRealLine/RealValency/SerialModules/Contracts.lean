module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.Roots
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.Tree
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.Series
public import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# Integral origins and composition series of vertex modules

The integral lattices and their reductions are separate objects. An ordinary
lattice is a finite free representation over the localization at the specified
block prime, with the prescribed complex character. Reduction uses the exact
residue map from `CompatibleRoots`.

`VertexSeries` asks for one serial reduction with each incident simple as its
socle. Its factor ordering is initially arbitrary. `ConsecutiveUnique` is the
local absence of branching used in Feit's proof of VII.2.23. The final
`CyclicVertexFamily` additionally records a common successor and actual dual
equivalences. None of these series or family structures has an existence
instance. Only existence of ordinary lattices is proved here, using the
prime-generic integral-model theorem; that does not prove serial reduction.

Source: Feit VII.2.20, VII.2.23, VII.2.25, pp.279--280 and 302--304.
-/

public section
noncomputable section
open scoped Classical

namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules

open ModularBlock.PrimeBlockConstruction ModularBlock.PrimeIntegralModels
open ModularBlock.PrincipalBlockConstruction ModularBlock.BlockOrthogonality

variable {p : ℕ} {G : Type*} [Group G] [Finite G]

/-- An actual ordinary-character lattice at the specified cyclotomic prime. -/
structure OrdinaryLattice (d : PrimeCongruenceBlockData p G) (v : d.I) where
  degree : ℕ
  rep : Representation (Localization.AtPrime d.primeIdeal) G
    (Fin degree → Localization.AtPrime d.primeIdeal)
  character_eq : d.chi v = characterClassFunction
    (Representation.mapCoefficients (localizationToComplex d.primeIdeal) rep)

namespace OrdinaryLattice

variable {d : PrimeCongruenceBlockData p G} {v : d.I} {K : Type*} [Field K] {m : ℕ}

/-- The reduced module uses the same residue map as the tree's root lift. -/
@[expose] def reduction (X : OrdinaryLattice d v) (r : CompatibleRoots d K m) :
    Representation K G (Fin X.degree → K) :=
  Representation.mapCoefficients r.residue X.rep

/-- The integral rank is the degree of the prescribed ordinary character. -/
theorem character_one (X : OrdinaryLattice d v) :
    d.chi v (ConjClasses.mk 1) = (X.degree : ℂ) := by
  rw [X.character_eq]
  change (Representation.mapCoefficients (localizationToComplex d.primeIdeal)
    X.rep).character 1 = _
  simp

end OrdinaryLattice

/-- Ordinary lattices exist at this prime; nothing about seriality of their
reductions is asserted. -/
theorem exists_ordinaryLattice (d : PrimeCongruenceBlockData p G) [Fact p.Prime] (v : d.I) :
    Nonempty (OrdinaryLattice d v) := by
  have hP : d.primeIdeal ≠ ⊥ := by
    intro h
    have hp := PrimeSelector.prime_mem_primeIdeal d
    rw [h, Ideal.mem_bot] at hp
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp
  obtain ⟨n, ρ, hρ⟩ := ModularBlock.PrimeIntegralModels.exists_integral_model
    d.primeIdeal d.eta_spec hP (d.chi v) (d.complete.1 v)
  exact ⟨⟨n, ρ, hρ⟩⟩

variable {d : PrimeCongruenceBlockData p G} {K : Type*} [Field K] {m n : ℕ}
    {L : CyclicRootLift K m}

/-- Any ordinary lattice at this vertex has exactly the sum of the incident
simple dimensions. This fixes the rank of the required reduction, without
asserting that its extensions have the serial structure. -/
theorem lattice_degree_eq_incident_sum (t : Tree d.chi d.block p n L) (hp : p ≠ 1)
    (v : {i // i ∈ d.block}) (X : OrdinaryLattice d v.val) :
    X.degree = ∑ e ∈ t.incident v, t.degree e :=
  (t.sum_degrees hp v X.character_one).symm

/-- One actual serial reduction per incident socle, with every incident simple
occurring once. The order need not yet be compatible between the modules. -/
structure VertexSeries (t : Tree d.chi d.block p n L) (r : CompatibleRoots d K m)
    (v : {i // i ∈ d.block}) where
  lattice : ↥(t.incident v) → OrdinaryLattice d v.val
  series : ∀ e, ExhaustiveSeries ((lattice e).reduction r) (t.incident v).card
  ordering : ↥(t.incident v) → Fin (t.incident v).card ≃ ↥(t.incident v)
  first : ∀ e (h : 0 < (t.incident v).card), ordering e ⟨0, h⟩ = e
  factor_equiv : ∀ e i, Nonempty (((series e).factor i).Equiv (t.rep (ordering e i).val))

namespace VertexSeries

variable {t : Tree d.chi d.block p n L} {r : CompatibleRoots d K m}
    {v : {i // i ∈ d.block}}

/-- The same simple factor cannot have two different successors in these
ascending series. This is the local conclusion of Feit VII.8.2 used in VII.2.23,
and is a separate proof obligation, not part of `VertexSeries`. -/
@[expose] def ConsecutiveUnique (a : VertexSeries t r v) : Prop :=
  ∀ e f (i j : Fin (t.incident v).card)
    (hi : i.val + 1 < (t.incident v).card) (hj : j.val + 1 < (t.incident v).card),
    a.ordering e i = a.ordering f j →
      a.ordering e ⟨i.val + 1, hi⟩ = a.ordering f ⟨j.val + 1, hj⟩

end VertexSeries

/-- The full module-valued family required by the real-valency assembly.
Existence must discharge seriality, consecutive uniqueness and dual closure. -/
structure CyclicVertexFamily (t : Tree d.chi d.block p n L) (r : CompatibleRoots d K m)
    (v : {i // i ∈ d.block}) extends VertexSeries t r v where
  successor : Equiv.Perm ↥(t.incident v)
  cyclic : successor.IsCycleOn Set.univ
  powers : ∀ e i, (successor ^ i.val) e = ordering e i
  dual_closed : ∀ e, ∃ f, Nonempty (((lattice e).reduction r).dual.Equiv
    ((lattice f).reduction r))

end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules
