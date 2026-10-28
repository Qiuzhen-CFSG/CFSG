module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.Transvections

/-!
# The common Ru2 marking needed for the fixed commutator seed

These maps retain the original H/Q map and the SL₂(4) marking in Ru2.
The local identification is that the image of S is an actual
Sylow two-subgroup under that marking. This statement does not assert
any commutator-image conclusion.

Source: Aschbacher–Smith, J.2.2(1) and J.2.3 assertion (!),
printed pp.432–433 (PDF pp.443–444).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry.FixedSeed
variable {G : Type*} [Group G] [Finite G]

/-- The literal image map S → H/Q ≃ S₅. -/
def coreMap (d : LocalSetup G) : d.toTypeRuSetup.S →* S5 :=
  d.ru2.quotientMap.comp (inclusion d.S_le_H)

/-- Inclusion into S₅ using the original Ru2 marking. -/
def markingMap (d : LocalSetup G) : SL2FourNatural.SL →* S5 :=
  (alternatingGroup (Fin 5)).subtype.comp d.ru2.naturalAction.marking.toMonoidHom

/-- The precise local action identification required by the seed proof. -/
def HasNaturalSylowImage (d : LocalSetup G) : Prop :=
  ∃ P : Sylow 2 SL2FourNatural.SL,
    (coreMap d).range = (P : Subgroup SL2FourNatural.SL).map (markingMap d)

end CFSG.Quasithin.ChapterJ.SpecialCore.CommutatorGeometry.FixedSeed
