module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Inputs

/-!
# The six-letter action model for the paired orbit

The model specifies the actual two-core quotient and the literal opposite-orbit
image. It neither assumes a natural subgroup complement nor supplies either
recognition conclusion. The input retains all original source hypotheses; its
construction from the original hypotheses is supplied in Recognition.Source.

Source: MS93 (3.6), printed p.871; characteristic replacement in Section 7.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition
variable {M : Type*} [Group M] [Finite M] {K R : Subgroup M} {geo : Geometry R}
  (o : PairedOrbit K R geo)
/-- The group-action construction. The actor is the literal pullback
of the selected opposite orbit. No natural module or kernel displacement is a field. -/
structure PermutationModel where
  projection : M →* Equiv.Perm (Fin 6)
  onto : Function.Surjective projection
  kernel : projection.ker = pCore 2 M
  component_image : K.map projection = alternatingGroup (Fin 6)
  actor_elementary : IsElementaryAbelian 2 ((o.opposite.comap (embedM R)).map projection)


universe u
/-- The intermediate group-action contract used by the literal orbit calculation.
It retains every original source hypothesis and the independently selected orbit. -/
def PermutationModelInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥), InitialNatural h e hz →
      ∀ d : Replacement L R, CentralLayer d → replacementDistance h d = 2 →
        (¬ core d.radical (alpha d.radical) ≤
          (frattini (Q d.radical (alpha d.radical))).map
            (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) →
        ∀ o : PairedOrbit (pResidual 2 d.overgroup) d.radical (replacementGeometry h d),
          Nonempty (PermutationModel o)

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
