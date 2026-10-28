module

public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.Contracts

/-!
# Isomorphism classes of the actual simple modules

The number of entries in a complete inequivalent family is the number of
isomorphism classes of representations selected by its group-algebra element.
We use finite-dimensional matrix representations and quotient by actual
intertwining equivalences. Thus this count does not depend on chosen bases
or on a decomposition matrix.

The application to `Decomposition` connects its literal representations to
the class sets used in Feit VII.1.3 and VII.3.12. It does not establish the
local classification or the Green correspondence in those results.
-/

public section
noncomputable section

namespace Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount

variable {K G : Type*} [Field K] [Group G]

/-- A finite-dimensional irreducible representation selected by the given
element of the group algebra. -/
structure SimpleModel (e : MonoidAlgebra K G) where
  degree : ℕ
  rep : Representation K G (Fin degree → K)
  irreducible : Representation.IsIrreducible rep
  inBlock : rep.asAlgebraHom e = 1

/-- The relation is actual representation equivalence, including changes of basis. -/
@[expose] def simpleModelSetoid (e : MonoidAlgebra K G) : Setoid (SimpleModel e) where
  r a b := Nonempty (a.rep.Equiv b.rep)
  iseqv :=
    ⟨fun a => ⟨Representation.Equiv.refl a.rep⟩,
      fun ⟨f⟩ => ⟨f.symm⟩,
      fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

/-- Isomorphism classes of the actual simple representations selected by `e`. -/
@[expose] def SimpleClass (e : MonoidAlgebra K G) := Quotient (simpleModelSetoid e)

/-- Send a representation to its isomorphism class. -/
@[expose] def SimpleModel.toClass {e : MonoidAlgebra K G} (a : SimpleModel e) :
    SimpleClass e := Quotient.mk (simpleModelSetoid e) a

theorem SimpleModel.toClass_eq_iff {e : MonoidAlgebra K G} (a b : SimpleModel e) :
    a.toClass = b.toClass ↔ Nonempty (a.rep.Equiv b.rep) := by
  constructor
  · exact Quotient.exact
  · intro h
    exact Quotient.sound (s := simpleModelSetoid e) h

/-- Completeness and inequivalence give a bijection to the class set.
No numerical count or Brauer-tree conclusion is assumed. -/
def simpleClassEquivOfFamily {ι : Type*} (e : MonoidAlgebra K G)
    (degree : ι → ℕ) (rep : ∀ i, Representation K G (Fin (degree i) → K))
    (hirr : ∀ i, Representation.IsIrreducible (rep i))
    (hin : ∀ i, (rep i).asAlgebraHom e = 1)
    (hne : Pairwise fun i j => IsEmpty ((rep i).Equiv (rep j)))
    (hcomplete : ∀ (k : ℕ) (ρ : Representation K G (Fin k → K)),
      Representation.IsIrreducible ρ → ρ.asAlgebraHom e = 1 →
        ∃ i, Nonempty (ρ.Equiv (rep i))) :
    ι ≃ SimpleClass e := by
  let model (i : ι) : SimpleModel e := ⟨degree i, rep i, hirr i, hin i⟩
  apply Equiv.ofBijective (fun i => (model i).toClass)
  constructor
  · intro i j hij
    by_contra hneij
    obtain ⟨f⟩ := (SimpleModel.toClass_eq_iff (model i) (model j)).mp hij
    exact (hne hneij).false f
  · intro c
    induction c using Quotient.inductionOn with
    | h b =>
      obtain ⟨i, ⟨f⟩⟩ := hcomplete b.degree b.rep b.irreducible b.inBlock
      exact ⟨i, Quotient.sound ⟨f.symm⟩⟩

variable [Finite G] {p m n : ℕ}
    {d : ModularBlock.PrimeBlockConstruction.PrimeCongruenceBlockData p G}
    {residue : Localization.AtPrime d.primeIdeal →+* K} {L : CyclicRootLift K m}

/-- The supplied decomposition enumerates precisely the actual ambient simples. -/
def decompositionSimpleClassEquiv (a : Decomposition d residue L n) :
    Fin n ≃ SimpleClass (reducedPrincipal d residue) :=
  simpleClassEquivOfFamily _ a.degree a.rep a.irreducible a.inBlock
    a.inequivalent a.complete

/-- Convert the family count to the intrinsic count of isomorphism classes. -/
theorem card_simpleClass (a : Decomposition d residue L n) :
    Nat.card (SimpleClass (reducedPrincipal d residue)) = n := by
  simpa only [Nat.card_fin] using Nat.card_congr (decompositionSimpleClassEquiv a).symm

end Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.CyclicIncidence.SimpleCount
