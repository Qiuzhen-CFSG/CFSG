module

public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.Setup
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!
# The surviving Lie models and the binary derived endpoint

`CaseB` records the four alternatives in Aschbacher–Smith 2.3.9(7)(b),
combined manuscript of 1 March 2004, printed p.525. The symplectic option
uses the commutator subgroup of the full matrix group and includes n=1.
The L₃(4) option retains the actual quotient by O₂(L). The triple A₆ cover
is specified by quasisimplicity, its center of order three, and an actual
isomorphism of its central quotient with A₆, as in Notation A.3.5.

Restricting the checked six-letter polar representation to commutator
subgroups proves that the A₆ case of 1.1.5(3)(c) lies in the binary
symplectic family. This is a comparison of the concrete groups; neither
the existence of the polar representation nor its surjectivity is inferred
from a group-order match alone.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter2.ComponentRefinement.LieType
open Subgroup Theory.GroupTheory
variable (K : Type*) [Group K]

/-- The commutator subgroup of the full symplectic matrix group, including n=1. -/
def IsDerivedSymplecticFour : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F),
    Nat.card F = 2 ^ n ∧
      Nonempty (K ≃* commutator (Matrix.symplecticGroup (Fin 2) F))

/-- The quasisimple triple central cover in Notation A.3.5. -/
def IsTripleAlternatingSixCover : Prop :=
  IsQuasisimple K ∧ Nat.card (center K) = 3 ∧
    Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin 6))

/-- Exactly the four alternatives in 2.3.9(7)(b). -/
def CaseB : Prop :=
  IsDerivedSymplecticFour K ∨
    (∃ n : ℕ, 1 ≤ n ∧ ClassicalGroup.IsPSL K 3 (2 ^ n)) ∨
    ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 4 ∨
    IsTripleAlternatingSixCover K

private noncomputable def derivedSpFourBinaryEquiv :
    commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2)) ≃*
      alternatingGroup (Fin 6) := by
  let e := Theory.SpecificGroups.SymplecticFour.Binary.symmetricSixEquiv.symm
  refine (e.subgroupMap _).trans (MulEquiv.subgroupCongr ?_)
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr e.surjective]
  exact alternatingGroup.commutator_perm_eq (by norm_num)

variable {K}
/-- The A₆ input of 1.1.5(3)(c) is the binary derived symplectic endpoint,
via the actual six-letter polar representation. -/
theorem isDerivedSymplecticFour_of_alternatingSix
    (e : K ≃* alternatingGroup (Fin 6)) : IsDerivedSymplecticFour K := by
  exact ⟨1, by decide, ZMod 2, inferInstance, inferInstance, by norm_num,
    ⟨e.trans derivedSpFourBinaryEquiv.symm⟩⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement.LieType

end
