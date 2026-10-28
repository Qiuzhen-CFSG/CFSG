module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.ActorGeometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.Obstruction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.ModelInputs
public import CFSG.Quasithin.Defs
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.Reduction
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSUThreeGeneration.OuterFamilies.EightActors.FamilyTransport

/-!
# Outer eight-group actors in odd-prime PSU₃ extensions

`Reduction` constructs a Sylow-central socle involution in the original
order-eight actor and a mixed four-group with an outer involution. It proves
the exact kernel-cardinality conditions for the local two-core and radical
quotients, with consumers in both E1 and E2.

`FamilyTransport` proves that generation for the actual restricted family
in the involution centralizer traps that centralizer in the obstruction.
The centralizer containment and the subsequent unitary geometry remain
independent prerequisites. Final assembly of the unconditional eight-actor
exclusion belongs here; it is not yet asserted.

Source: Aschbacher--Smith E.1.1--2, E.1.5, E.1.8 and E.1.14(7), pp.209--214;
Aschbacher, GF(2)-representations of finite groups (1982), Lemma 4.11.
-/
