module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.VertexConstruction.Contracts

/-!
# Combining marked socles with composition flags

The lattice selection in Feit I.17.12 and the identification of composition
factors are separate constructions. A simple socle lies in the first nonzero
term of every saturated flag. That term is simple, so the inclusion is an
equality. Inequivalence of the tree's edge modules then forces its label to
be the marked edge; no permutation of the subspaces is needed.

This supplies the assembly boundary for the lattices X_ui on printed p.279
of Feit, *The Representation Theory of Finite Groups*. Existence of the two
inputs below is not asserted here. Neither seriality nor exhaustive flags
are required.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules

variable {K G V W : Type*} [Field K] [Group G]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- An actual simple subspace, identified with the prescribed representation,
which lies in every nonzero invariant subspace. -/
structure SimpleSocle (ρ : Representation K G V) (σ : Representation K G W) where
  subspace : Subrepresentation ρ
  atom : IsAtom subspace
  equiv : Nonempty (subspace.toRepresentation.Equiv σ)
  le_nonzero : ∀ U : Subrepresentation ρ, U ≠ ⊥ → subspace ≤ U

namespace SimpleSocle

/-- Every saturated flag begins with the given simple socle. -/
theorem eq_first_term {ρ : Representation K G V} {σ : Representation K G W}
    (S : SimpleSocle ρ σ) {s : ℕ} (c : SaturatedFlag ρ s) (h : 0 < s) :
    S.subspace = c.term (⟨0, h⟩ : Fin s).succ :=
  ((c.first_isAtom h).le_iff_eq S.atom.ne_bot).mp
    (S.le_nonzero _ (c.first_isAtom h).ne_bot)

end SimpleSocle

open ModularBlock.PrimeBlockConstruction

variable [Finite G] {p m n : ℕ} {d : PrimeCongruenceBlockData p G}
    {L : CyclicRootLift K m}

/-- A composition flag of an ordinary reduction, with each incident edge
occurring once. No edge is designated as its first factor. -/
structure IncidentFlag (t : Tree d.chi d.block p n L) (r : CompatibleRoots d K m)
    (v : {i // i ∈ d.block}) (X : OrdinaryLattice d v.val) where
  flag : SaturatedFlag (X.reduction r) (t.incident v).card
  ordering : Fin (t.incident v).card ≃ ↥(t.incident v)
  factor_equiv : ∀ i, Nonempty ((flag.factor i).Equiv (t.rep (ordering i).val))

/-- Lattice selection with a specified simple socle, before choosing any
composition flag. The lattice is over the literal localization in d. -/
structure MarkedLattice (t : Tree d.chi d.block p n L) (r : CompatibleRoots d K m)
    (v : {i // i ∈ d.block}) (e : ↥(t.incident v)) where
  lattice : OrdinaryLattice d v.val
  socle : SimpleSocle (lattice.reduction r) (t.rep e.val)

namespace IncidentFlag

variable {t : Tree d.chi d.block p n L} {r : CompatibleRoots d K m}
    {v : {i // i ∈ d.block}} {X : OrdinaryLattice d v.val}

/-- The actual quotient equivalences and inequivalent edge modules determine
the initial label of any composition flag of a marked lattice. -/
theorem ordering_zero_eq (c : IncidentFlag t r v X) (e : ↥(t.incident v))
    (S : SimpleSocle (X.reduction r) (t.rep e.val))
    (h : 0 < (t.incident v).card) : c.ordering ⟨0, h⟩ = e := by
  obtain ⟨q⟩ := S.equiv
  rw [S.eq_first_term c.flag h] at q
  obtain ⟨f⟩ := c.factor_equiv ⟨0, h⟩
  have he : Nonempty ((t.rep e.val).Equiv (t.rep (c.ordering ⟨0, h⟩).val)) :=
    ⟨q.symm.trans ((c.flag.firstFactorEquiv h).symm.trans f)⟩
  apply Subtype.ext
  by_contra hn
  exact (t.inequivalent (Ne.symm hn)).false he.some

end IncidentFlag

/-- Assemble the exact VertexFlags contract from independently constructed
marked lattices and composition flags. The first factor and socle clauses
are proved on the unchanged subspaces and quotient actions. -/
@[expose] def vertexFlagsOfMarkedLattices
    (t : Tree d.chi d.block p n L) (r : CompatibleRoots d K m)
    (v : {i // i ∈ d.block})
    (a : ∀ e : ↥(t.incident v), MarkedLattice t r v e)
    (c : ∀ e, IncidentFlag t r v (a e).lattice) : VertexFlags t r v where
  lattice e := (a e).lattice
  flag e := (c e).flag
  ordering e := (c e).ordering
  first e h := (c e).ordering_zero_eq e (a e).socle h
  factor_equiv e := (c e).factor_equiv
  socle_le e h U hU := by
    rw [← (a e).socle.eq_first_term (c e).flag h]
    exact (a e).socle.le_nonzero U hU

/-- Choice supplies the full family once lattice selection and the
composition-factor theorem have both been proved. -/
theorem exists_vertexFlags_of_markedLattices
    (t : Tree d.chi d.block p n L) (r : CompatibleRoots d K m)
    (marked : ∀ (v : {i // i ∈ d.block}) (e : ↥(t.incident v)),
      Nonempty (MarkedLattice t r v e))
    (flags : ∀ (v : {i // i ∈ d.block}) (X : OrdinaryLattice d v.val),
      Nonempty (IncidentFlag t r v X)) :
    Nonempty (∀ v : {i // i ∈ d.block}, VertexFlags t r v) :=
  ⟨fun v => vertexFlagsOfMarkedLattices t r v (fun e => (marked v e).some)
    (fun e => (flags v ((marked v e).some.lattice)).some)⟩

end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules
