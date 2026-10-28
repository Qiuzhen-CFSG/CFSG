module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.LocalBounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.NaturalStructure.CriticalCriterion.Generation

/-!
# Simultaneous transport of the higher orbit layers

The right action sends every vertex used in an orbit layer to its actual
image. In particular, conjugating the second layer transports all three
vertices, including its two later path choices. These equations do not
identify spans built from different unproved choices.

The consumer in `TwoCases` uses the transported center to locate the
conjugated second layer in its own Q, while retaining the original seed.
Source: Meierfrankenfeld--Stellmacher (1993), (4.5.5), printed p.899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases
open NormalizerTransfer PathCentrality
variable {M : Type*} [Group M] {L R : Subgroup M} {geometry : Geometry R}

/-- Transport both vertices of the first orbit layer. -/
theorem rightConjugate_hatV (g : FreeAmalgam R) (a c : Vertex R) :
    rightConjugate (hatV R a c) g = hatV R (act R g a) (act R g c) := by
  rw [hatV_eq_conjugatesIn, rightConjugate, CriticalCriterion.conjugatesIn_map,
    ← Z_act, ← stabilizer_act, ← hatV_eq_conjugatesIn]

/-- Transport all three vertices of the second orbit layer. -/
theorem rightConjugate_hatW (g : FreeAmalgam R) (a c d : Vertex R) :
    rightConjugate (hatW R a c d) g =
      hatW R (act R g a) (act R g c) (act R g d) := by
  change (conjugatesIn (hatV R c d) (stabilizer R a)).map
    (MulAut.conj g⁻¹).toMonoidHom = _
  rw [CriticalCriterion.conjugatesIn_map, ← stabilizer_act]
  change conjugatesIn (rightConjugate (hatV R c d) g) _ = _
  rw [rightConjugate_hatV]
  rfl

/-- Transport all four vertices of the third orbit layer. -/
theorem rightConjugate_hatSix (g : FreeAmalgam R) (a c d e : Vertex R) :
    rightConjugate (hatSix R a c d e) g =
      hatSix R (act R g a) (act R g c) (act R g d) (act R g e) := by
  change (conjugatesIn (hatW R c d e) (stabilizer R a)).map
    (MulAut.conj g⁻¹).toMonoidHom = _
  rw [CriticalCriterion.conjugatesIn_map, ← stabilizer_act]
  change conjugatesIn (rightConjugate (hatW R c d e) g) _ = _
  rw [rightConjugate_hatW]
  rfl

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases
