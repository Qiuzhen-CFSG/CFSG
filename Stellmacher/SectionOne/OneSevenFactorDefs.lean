module

public import Stellmacher.SectionsOneToFourDefs

/-!
# Factors used in the global assembly of (1.7)

The source's Ω-star family consists of `SL₂(2)` subgroups with four-element
action commutator which are normal in their join with the odd core. The
assembly below indexes those factors together with the already-known
four-element action commutator of their derived subgroup. The local
restricted (1.6) construction supplies this additional property for every
factor needed to generate `J(V,S)`. This refined family remains invariant
under conjugation and is sufficient for the unchanged conclusion of (1.7).

Source: refs/latex/stellmacher-n-group.tex, proof of (1.7), journal p. 19.
-/

namespace Stellmacher.SectionOne
universe u

/-- An SL2 factor carrying the derived-action data supplied by local (1.6). -/
@[expose] public def IsOneSevenFactor
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (D : Subgroup G) : Prop :=
  IsSL2Two D ∧
    oneOmega (G := G) (V := V) ((commutator D).map D.subtype) ∧
    Nat.card (commutatorAction D V) = 4 ∧
    (D.subgroupOf (oddCore G ⊔ D)).Normal

end Stellmacher.SectionOne
