module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.Placement
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.Certificates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.ActorCertificates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.LocalCertificates
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.Transport

/-!
# Assembly of the outer-actor placement calculation

The finite actor calculation places every outer four-group and eight-group
of the explicit 32-element Sylow in the selected graph-involution centralizer.
The independent local calculation proves intersection order sixteen and
generation. Sylow conjugacy transports all six placement clauses to any
Sylow subgroup while retaining the whole original actor. The unconditional
theorem discharges the outer premise of `exists_localGeometry_of_inner_outer`;
the separate inner branch remains with that theorem's assembly owner.

Source: Aschbacher–Smith E.1.2/E.1.5/E.1.14(7), printed pp.209–210, 214;
Asc82a Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
open Matrix.PSL3Three.GraphLocalQuotients
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry
/-- Conditional assembly of the two independent finite calculations, followed
by the proved Sylow-conjugacy transport. The unconditional theorem below
supplies both certificates. -/
theorem centralizerPlacement_outer_of_standard_certificates
    (hloc : StandardLocalCertificates) (hact : StandardOuterActorCertificates)
    (T : Sylow 2 G) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hr : 1 < Group.rank A)
    (hout : ¬ A ≤ innerPart (ZMod 3)) : CentralizerPlacement T A := by
  apply centralizerPlacement_outer_of_one_sylow OuterActors.standardSylow _ T A hA hAT hr hout
  intro B hB hBS hrB hoB
  obtain ⟨g,hBT,hBK,hcent,hcore⟩ := hact B hB hBS hrB hoB
  exact ⟨g, OuterActors.localConjugator true, hBT, hBK, hcent, hloc.1,
    hcore, hloc.2⟩

/-- Every whole outer elementary actor of rank at least two admits concrete
graph-centralizer placement. This discharges `houter` in
`exists_localGeometry_of_inner_outer`, with no finite-certificate premises. -/
theorem centralizerPlacement_of_outer
    (T : Sylow 2 G) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (hr : 1 < Group.rank A)
    (hout : ¬ A ≤ innerPart (ZMod 3)) : CentralizerPlacement T A :=
  centralizerPlacement_outer_of_standard_certificates
    standardLocalCertificates standardOuterActorCertificates T A hA hAT hr hout

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry
