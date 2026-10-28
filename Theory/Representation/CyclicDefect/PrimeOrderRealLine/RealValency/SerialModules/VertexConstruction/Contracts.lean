module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.Contracts
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules.VertexConstruction.Filtrations

/-!
# Marked lattices before proving seriality

`VertexFlags` records actual ordinary lattices at the given prime whose
reductions have the marked edge as their simple socle. Each comes with a
saturated composition flag having exactly the incident factors, once each.
It does not claim that the flag exhausts all invariant subspaces.

The I.17.12 lattice construction and the VII.8.1--2 socle-layer argument can
use this common boundary independently. The latter must prove `UniqueCovers`
and `ConsecutiveUnique`; `toVertexSeries` then builds the existing exhaustive
series interface. Simple socles and indecomposability are verified for these
supplied flags without using the missing cover exclusion.

Source: Feit, *The Representation Theory of Finite Groups*, I.17.12,
VII.2.20, VII.2.23 and VII.8.1--2, pp.279--280 and 302--303. Neither existence
of `VertexFlags` nor the two exclusions is asserted here.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules

open ModularBlock.PrimeBlockConstruction
variable {K G : Type*} [Field K] [Group G] [Finite G]
    {p : ℕ} {d : PrimeCongruenceBlockData p G} {m n : ℕ}
    {L : CyclicRootLift K m}

/-- Marked simple-socle lattices with one saturated composition flag each.
The flags need not be exhaustive, and no successor consistency is assumed. -/
structure VertexFlags (t : Tree d.chi d.block p n L) (r : CompatibleRoots d K m)
    (v : {i // i ∈ d.block}) where
  lattice : ↥(t.incident v) → OrdinaryLattice d v.val
  flag : ∀ e, SaturatedFlag ((lattice e).reduction r) (t.incident v).card
  ordering : ↥(t.incident v) → Fin (t.incident v).card ≃ ↥(t.incident v)
  first : ∀ e (h : 0 < (t.incident v).card), ordering e ⟨0, h⟩ = e
  factor_equiv : ∀ e i, Nonempty (((flag e).factor i).Equiv (t.rep (ordering e i).val))
  socle_le : ∀ e (h : 0 < (t.incident v).card)
    (U : Subrepresentation ((lattice e).reduction r)), U ≠ ⊥ →
    (flag e).term (⟨0, h⟩ : Fin (t.incident v).card).succ ≤ U

namespace VertexFlags

variable {t : Tree d.chi d.block p n L} {r : CompatibleRoots d K m}
    {v : {i // i ∈ d.block}}

/-- The local upper-cover exclusion needed to make every supplied flag
exhaustive. This is a proof obligation, not a field of `VertexFlags`. -/
@[expose] def UniqueCovers (a : VertexFlags t r v) : Prop :=
  ∀ e (i : Fin (t.incident v).card) (W : Subrepresentation ((a.lattice e).reduction r)),
    (a.flag e).term i.castSucc ⋖ W → W = (a.flag e).term i.succ

/-- The second source obligation: equal composition-factor labels have
equal next labels whenever both next positions exist. -/
@[expose] def ConsecutiveUnique (a : VertexFlags t r v) : Prop :=
  ∀ e f (i j : Fin (t.incident v).card)
    (hi : i.val + 1 < (t.incident v).card) (hj : j.val + 1 < (t.incident v).card),
    a.ordering e i = a.ordering f j →
      a.ordering e ⟨i.val + 1, hi⟩ = a.ordering f ⟨j.val + 1, hj⟩

/-- Construct the exhaustive series while preserving the literal lattice,
residue map, invariant subspaces, quotient actions and factor equivalences. -/
@[expose] def toVertexSeries (a : VertexFlags t r v) (h : a.UniqueCovers) :
    VertexSeries t r v where
  lattice := a.lattice
  series e := (a.flag e).toExhaustive (h e)
  ordering := a.ordering
  first := a.first
  factor_equiv := a.factor_equiv

/-- The construction keeps every factor label and hence its proved
consecutive-factor uniqueness. -/
theorem toVertexSeries_consecutiveUnique (a : VertexFlags t r v)
    (h : a.UniqueCovers) (hc : a.ConsecutiveUnique) :
    (a.toVertexSeries h).ConsecutiveUnique := hc

/-- The marked simple socle already proves that the reduction cannot split. -/
theorem no_nontrivial_complement (a : VertexFlags t r v) (e : ↥(t.incident v))
    (U W : Subrepresentation ((a.lattice e).reduction r)) (h : IsCompl U W) :
    U = ⊥ ∨ W = ⊥ :=
  (a.flag e).no_nontrivial_complement_of_simple_socle (a.socle_le e) U W h

/-- Identify the actual simple socle with the specified edge representation,
using the literal quotient by the zero flag term. -/
theorem socle_equiv (a : VertexFlags t r v) (e : ↥(t.incident v))
    (h : 0 < (t.incident v).card) :
    Nonempty (((a.flag e).term (⟨0, h⟩ : Fin (t.incident v).card).succ).toRepresentation.Equiv
      (t.rep e.val)) := by
  obtain ⟨f⟩ := a.factor_equiv e ⟨0, h⟩
  rw [a.first e h] at f
  exact ⟨((a.flag e).firstFactorEquiv h).symm.trans f⟩

end VertexFlags
end Representation.CyclicDefect.PrimeOrderRealLine.RealValency.SerialModules
