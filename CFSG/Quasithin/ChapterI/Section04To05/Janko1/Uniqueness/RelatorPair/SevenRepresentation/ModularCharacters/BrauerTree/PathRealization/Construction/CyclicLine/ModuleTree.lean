module

public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Uniqueness.RelatorPair.SevenRepresentation.ModularCharacters.BrauerTree.PathRealization.Construction.CyclicLine.Preparation
public import Theory.Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree.Assembly

/-!
# Principal eleven-block module-tree assembly

The literal reduction of the identified congruence projector has maximal
Brauer support at every Sylow eleven-subgroup. The Sylow subgroup is cyclic
of order eleven, and its centralizer has index ten in its normalizer.

Given actual modular decomposition data and the cyclic incidence theorem,
the eleven ordinary rows force a genuine tree with distinct edges. The
adapter retains the same simple modules, projective modules, and compatible
root lift. It does not assert their existence: principal-block primitivity,
modular decomposition and reciprocity, and cyclic incidence remain source
obligations. Final tree existence belongs to this module.

Source: Feit I.17.8--9, III.8--9, V.6.2, VII.2.1 and VII.2.11--15,
VII.6.4--8; see the parent `Construction/Source.md`.
-/

namespace CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction

open Representation.CyclicDefect.PrimeOrderRealLine
open Representation.CyclicDefect.PrimeOrderRealLine.ModuleTree

variable {G : Type*} [Group G] [Finite G] {d : OrdinaryData G}

/-- Maximal Brauer support and the actual local group data, all at the
same prime and over the literal eleven-characteristic coefficient field. -/
public theorem principalBlock_sylow_support (b : PrincipalBlockIdentification d)
    (r : CompatibleRoots b.data ElevenClosure 15960)
    (horder : Nat.card G = 175560) (P : Sylow 11 G) :
    Maximal (HasBrauerSupport 11 (reducedPrincipal b.data r.residue)) (P : Subgroup G) ∧
      Nat.card P = 11 ∧ IsCyclic P ∧
      (Subgroup.centralizer (P : Set G)).relIndex
        (Subgroup.normalizer (P : Set G)) = 10 := by
  exact ⟨sylow_maximal_brauerSupport b.data r.residue P,
    sylow_eleven_card horder P, sylow_eleven_isCyclic horder P,
    sylow_eleven_centralizer_index d horder P⟩

/-- The exceptional-multiplicity quotient is one once the principal-block
theorem identifies the inertial index with this actual local index. -/
public theorem principalBlock_local_multiplicity_quotient
    (d : OrdinaryData G) (horder : Nat.card G = 175560) (P : Sylow 11 G) :
    (Nat.card P - 1) /
      (Subgroup.centralizer (P : Set G)).relIndex
        (Subgroup.normalizer (P : Set G)) = 1 := by
  rw [sylow_eleven_card horder P, sylow_eleven_centralizer_index d horder P]

/-- Actual consumer of the modular decomposition and cyclic incidence
outputs. The number of vertices is discharged by the given row identification. -/
public theorem principalBlock_tree_of_incidence (b : PrincipalBlockIdentification d)
    (r : CompatibleRoots b.data ElevenClosure 15960) {n : ℕ}
    (a : Decomposition b.data r.residue (principalBlock_rootLift b r) n)
    (hn : n = 10) (c : Incidence a) :
    Nonempty (Tree b.data.chi b.data.block 11 10 (principalBlock_rootLift b r)) := by
  subst n
  exact ⟨c.toTree (principalBlock_card b)⟩

end CFSG.Quasithin.Janko1SevenRepresentation.ModularCharacters.BrauerTree.Construction
