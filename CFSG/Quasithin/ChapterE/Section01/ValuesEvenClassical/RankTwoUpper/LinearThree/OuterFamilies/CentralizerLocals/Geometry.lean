module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.CentralizerReduction

/-!
# Concrete geometry inputs for outer PSL₃ centralizers

The binary input is an actual S₃ epimorphism with two-group kernel and
nontrivial actor image. The nonbinary input identifies the intrinsic inner
centralizer as nonabelian simple and retains a nontrivial inner actor.
Both inputs retain the whole conjugate actor, the actual Sylow centralizer,
and generation of the marked socle. Neither is an established model theorem.

`CentralizerLocals` derives the literal E1/E2 conditions from these inputs.
The graph/field model calculations must construct them under the exact-rank
hypothesis of E.1.14(1), printed p.214; the local conditions are E.1.2, p.210.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
variable {G : Type*} [Group G] [Finite G]

/-- Model facts for the binary centralizer, before verifying E1. -/
def BinaryCentralizerGeometry (L : Subgroup G) (T : Sylow 2 G) (A : Subgroup G) : Prop :=
  ∃ g z : G,
    let B := A.map (MulAut.conj g).toMonoidHom
    let C := centralizer ({z} : Set G)
    B ≤ (T : Subgroup G) ∧ z ∈ B ∧ z ∉ L ∧
    (∃ S : Sylow 2 C, (S : Subgroup C) = (T : Subgroup G).subgroupOf C) ∧
    ∃ π : C →* Equiv.Perm (Fin 3), Function.Surjective π ∧ IsPGroup 2 π.ker ∧
      ¬ B.subgroupOf C ≤ π.ker ∧ L ≤ C ⊔ (T : Subgroup G)

/-- Model facts for graph or field centralizers with a nonabelian simple
inner centralizer. Perfectness explicitly excludes cyclic simple groups. -/
def SimpleCentralizerGeometry (L : Subgroup G) (T : Sylow 2 G) (A : Subgroup G) : Prop :=
  ∃ g z : G,
    let B := A.map (MulAut.conj g).toMonoidHom
    let C := centralizer ({z} : Set G)
    let D := L.subgroupOf C
    B ≤ (T : Subgroup G) ∧ z ∈ B ∧ z ∉ L ∧
    (∃ S : Sylow 2 C, (S : Subgroup C) = (T : Subgroup G).subgroupOf C) ∧
    IsSimpleGroup D ∧ Group.IsPerfect D ∧ B ⊓ L ≠ ⊥ ∧ L ≤ C ⊔ (T : Subgroup G)

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies
