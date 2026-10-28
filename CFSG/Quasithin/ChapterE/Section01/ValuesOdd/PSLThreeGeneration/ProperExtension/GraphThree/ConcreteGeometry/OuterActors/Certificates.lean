module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.Placement
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.Coordinates

/-!
# The remaining finite certificates for outer actors

The local calculation gives intersection order sixteen and generation for
the centralizer at coordinate `(13,true)`. Independently, the actor calculation conjugates
each whole elementary outer actor inside the standard Sylow and verifies
containment, Sylow-centralizer containment and escape from the intrinsic
local two-core. These are explicit outstanding proof contracts; neither is
asserted here. Their final assembly is in `OuterActors`.

Source: Aschbacher–Smith E.1.2/E.1.5/E.1.14(7), printed pp.209–210, 214;
Asc82a Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open Matrix.PSL3Three.GraphLocalQuotients
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry


/-- Intersection order and generation for the selected local centralizer. -/
@[expose] def StandardLocalCertificates : Prop :=
  Nat.card (OuterActors.standardSubgroup.subgroupOf
    (localSubgroup (OuterActors.localConjugator true))) = 16 ∧
  OuterActors.standardSubgroup ⊔ localSubgroup (OuterActors.localConjugator true) = ⊤

/-- The finite actor calculation. The whole original actor is conjugated,
and the Sylow centralizer condition is retained separately. -/
@[expose] def StandardOuterActorCertificates : Prop := ∀ A : Subgroup G,
  IsElementaryAbelian 2 A → A ≤ OuterActors.standardSubgroup →
  1 < Group.rank A → ¬ A ≤ innerPart (ZMod 3) →
  ∃ g : G,
    let B := A.map (MulAut.conj g).toMonoidHom
    B ≤ OuterActors.standardSubgroup ∧
    B ≤ localSubgroup (OuterActors.localConjugator true) ∧
    OuterActors.standardSubgroup ⊓ centralizer (B : Set G) ≤
      localSubgroup (OuterActors.localConjugator true) ∧
    ¬ B.subgroupOf (localSubgroup (OuterActors.localConjugator true)) ≤
      pCore 2 (localSubgroup (OuterActors.localConjugator true))


end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry
