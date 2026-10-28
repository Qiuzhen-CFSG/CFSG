module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.Reduction
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.Tree

/-!+# Decomposition modules and cyclic incidence as separate outputs

`Decomposition` retains a complete family of actual simple modules selected
by the literal reduced principal projector. Its nonnegative decomposition
numbers give ordinary restrictions, and its columns are afforded by actual
projective modules. Existence is the modular reduction and reciprocity theorem
(Feit I.17.8--9), not a field of the ordinary congruence-block data.

`Incidence` is the additional cyclic-defect conclusion (Feit VII.2.13--15
and the connectedness used in VII.6.4). It asserts two distinct endpoints
per column and connectedness, without assuming acyclicity or excluding
parallel columns. `Assembly` derives those graph properties from the vertex
count and combines these outputs into the shared module-valued `Tree`.
-/

public section
noncomputable section
open scoped BigOperators Classical

namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree
open ModularBlock.PrimeBlockConstruction

variable {p : ℕ} {G : Type*} [Group G] [Finite G]
    {K : Type*} [Field K] {m : ℕ}

/-- Actual modular decomposition and projective reciprocity at the specified
prime. No number of simple modules or cyclic incidence is assumed. -/
structure Decomposition (d : PrimeCongruenceBlockData p G)
    (residue : Localization.AtPrime d.primeIdeal →+* K)
    (L : CyclicRootLift K m) (n : ℕ) where
  degree : Fin n → ℕ
  rep : ∀ e, Representation K G (Fin (degree e) → K)
  irreducible : ∀ e, Representation.IsIrreducible (rep e)
  inequivalent : Pairwise fun e f => IsEmpty ((rep e).Equiv (rep f))
  inBlock : ∀ e, (rep e).asAlgebraHom (reducedPrincipal d residue) = 1
  complete : ∀ (k : ℕ) (ρ : Representation K G (Fin k → K)),
    Representation.IsIrreducible ρ → ρ.asAlgebraHom (reducedPrincipal d residue) = 1 →
      ∃ e, Nonempty (ρ.Equiv (rep e))
  multiplicity : {i // i ∈ d.block} → Fin n → ℕ
  restriction : ∀ g, ¬ p ∣ orderOf g → ∀ v : {i // i ∈ d.block},
    d.chi v.val (ConjClasses.mk g) =
      ∑ e, (multiplicity v e : ℂ) * L.value (rep e) g
  projective : ∀ e, ProjectiveCharacterLift p L
    (fun g => ∑ v : {i // i ∈ d.block},
      (multiplicity v e : ℂ) * d.chi v.val (ConjClasses.mk g))

/-- The cyclic theorem's incidence and connectedness conclusions, retaining
the exact decomposition numbers of the supplied actual modules. -/
structure Incidence {d : PrimeCongruenceBlockData p G}
    {residue : Localization.AtPrime d.primeIdeal →+* K}
    {L : CyclicRootLift K m} {n : ℕ} (a : Decomposition d residue L n) where
  left : Fin n → {i // i ∈ d.block}
  right : Fin n → {i // i ∈ d.block}
  endpoints_ne : ∀ e, left e ≠ right e
  multiplicity_eq : ∀ v e,
    a.multiplicity v e = if v = left e ∨ v = right e then 1 else 0
  connected : (endpointGraph left right).Connected

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree
