module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.LocalGeometry
public import Theory.SpecificGroups.PSL3Three.GraphLocalQuotients

/-!+# The shared concrete-placement interface for PSL₃(3)

The local witnesses are conjugates of the actual graph-involution centralizer.
Their S₃ quotients, two-group kernels and order-48 calculations are proved in
`GraphLocalQuotients`. Thus an intersection of order sixteen establishes the
literal Sylow clause, and escape from the intrinsic two-core establishes
nontriviality of the actor's quotient image.

The remaining placement calculation must construct the conjugating elements
and verify containment, intersection order, escape from the two-core and
generation. The assembly is conditional on these geometric inputs. The inner
and outer actor proofs may import this module independently; final assembly
belongs to `ConcreteGeometry`.

Source: Aschbacher–Smith E.1.2, E.1.5 and E.1.14(7), printed pp.209–210,
214; Asc82a, Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open Matrix.PSL3Three.GraphLocalQuotients

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree
namespace ConcreteGeometry

/-- The remaining geometry for an actor. The local group is a fixed concrete
centralizer conjugate; its quotient structure is already proved. -/
@[expose] def CentralizerPlacement (T : Sylow 2 G) (A : Subgroup G) : Prop :=
  ∃ g c : G,
    let B := A.map (MulAut.conj g).toMonoidHom
    B ≤ (T : Subgroup G) ∧ B ≤ localSubgroup c ∧
    (T : Subgroup G) ⊓ centralizer (B : Set G) ≤ localSubgroup c ∧
    Nat.card ((T : Subgroup G).subgroupOf (localSubgroup c)) = 16 ∧
    ¬ B.subgroupOf (localSubgroup c) ≤ pCore 2 (localSubgroup c) ∧
    (T : Subgroup G) ⊔ localSubgroup c = ⊤

/-- The concrete quotient calculation discharges the Sylow and epimorphism
obligations of the local placement contract. -/
theorem localGeometryAt_of_centralizerPlacements (T : Sylow 2 G)
    (h : ∀ A : Subgroup G, IsElementaryAbelian 2 A → A ≤ (T : Subgroup G) →
      1 < Group.rank A → CentralizerPlacement T A) : LocalGeometryAt T := by
  intro A hA hAT hrank
  obtain ⟨g, c, hBT, hBK, hcent, hcard, hcore, hgen⟩ := h A hA hAT hrank
  refine ⟨g, localSubgroup c, hBT, hBK, hcent,
    exists_localSylow_of_card T c hcard,
    ⟨localQuotient c, localQuotient_surjective c, localQuotient_ker_isPGroup c, ?_⟩,
    hgen⟩
  rwa [localQuotient_ker]


end ConcreteGeometry
end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree
