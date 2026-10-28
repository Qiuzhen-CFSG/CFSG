module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SixPathReflectionClass
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.AlphaRootClass

/-!
# The native class of the prescribed alpha reflection

The actual root witness in the source choice (14.2) maps to the native
positive-unipotent subgroup. If it fixes the opposite alpha point, whose
last coordinate is one, the three-coordinate calculation puts it in the
actual derived group of full G₂(2). The original local-actor conjugator
then puts the selected reflection in that same normal subgroup.

The application retains the literal map from the universal source group
and the exact involution witness in the prescribed six-path radical. It
does not construct a native marking or deduce the opposite-point coordinate
from an arbitrary source path. Those geometric inputs remain explicit.
Source: DGS, Groups and Graphs (1985), (14.2), printed p.210, and the
binary six-path calculation in (14.17), printed pp.222--223.
-/

public section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan.BinarySixPathReflectionClass
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {h : HypothesisF11 L S} {i : Bool} {t : (reducedAmalgam L S).Universal}

/-- Opposite-point fixation of the actual path-root witness supplies the
native derived class of the prescribed source reflection. -/
theorem native_image_mem_derived
    (d : BinarySixPathReflectionClass h i t)
    (φ : (reducedAmalgam L S).Universal →* Atlas.G2.Model (ZMod 2))
    (hroot : φ d.root ∈ Atlas.G2.unipotent)
    (v : Atlas.SplitOctonion.Carrier (ZMod 2)) (hv : v 7 = 1)
    (hfix : (φ d.root).val v = v) :
    φ t ∈ commutator (Atlas.G2.Model (ZMod 2)) := by
  apply d.image_mem_normal_of_root φ (commutator (Atlas.G2.Model (ZMod 2)))
  exact Atlas.G2.BinaryParabolicPair.alpha_fixer_mem_derived (φ d.root) hroot v hv hfix

/-- The geometric version uses the actual positive-unipotent orbit of the
opposite basis point, without a separate coordinate premise. -/
theorem native_image_mem_derived_of_opposite_orbit
    (d : BinarySixPathReflectionClass h i t)
    (φ : (reducedAmalgam L S).Universal →* Atlas.G2.Model (ZMod 2))
    (hroot : φ d.root ∈ Atlas.G2.unipotent)
    (u : Atlas.G2.Model (ZMod 2)) (hu : u ∈ Atlas.G2.unipotent)
    (hfix : (φ d.root).val (u.val (Atlas.SplitOctonion.basisVector 7)) =
      u.val (Atlas.SplitOctonion.basisVector 7)) :
    φ t ∈ commutator (Atlas.G2.Model (ZMod 2)) := by
  apply d.image_mem_normal_of_root φ (commutator (Atlas.G2.Model (ZMod 2)))
  exact Atlas.G2.BinaryParabolicPair.alpha_fixer_mem_derived_of_opposite_orbit
    (φ d.root) hroot u hu hfix

end ReducedCartan.BinarySixPathReflectionClass
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
