module
public import CFSG.Quasithin.Chapter14.Section02.ProperDiagramResidual
public import Theory.GroupTheory.NormalCentralQuotientAction
import all CFSG.Quasithin.Chapter14.Section02.NormalKOne

/-!
# The characteristic kernel of the original marked component map

The original component cover has simple image, so its kernel is the
center of the component modulo its two-core. Thus the actual marked map
has kernel the preimage of that center, a characteristic subgroup.
This supplies the kernel needed to extend the marked action to Mc.

Source: Aschbacher--Smith 14.2.9 and 14.2.12, printed pp.983--984.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02
open ChapterE ChapterE.Structure
open ChapterE.Section06.FixedPointBounds.ParabolicCartan.MarkedModels
variable {H D : Type*} [Group H] [Finite H] [Group D]

theorem original_markedParabolicMap_kernel
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (e : sourceImage (ChapterB.minimalParabolicMax T hP) K ≃* D) :
    (markedParabolicMap (ChapterB.minimalParabolicMax T hP) K e).ker =
      centralPreimage (pCore 2 K) := by
  let c := originalComponentStarCover T hP hs K hK hqK hgen
  let := hqK
  let : IsSimpleGroup (sourceImage (ChapterB.minimalParabolicMax T hP) K) :=
    (source_component_simple_image T hP hs K hK hgen).1
  let : IsQuasisimple (sourceImage (ChapterB.minimalParabolicMax T hP) K) :=
    (source_component_simple_image T hP hs K hK hgen).2.1.2
  have hk : c.toMonoidHom.ker = center (K ⧸ pCore 2 K) :=
    c.toCovering.ker_eq_center_of_isSimple
  have hf : markedParabolicMap (ChapterB.minimalParabolicMax T hP) K e =
      e.toMonoidHom.comp (c.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))) := by
    ext x
    rfl
  rw [hf,MonoidHom.ker_comp_of_injective _ _ e.injective,← MonoidHom.comap_ker,hk]
  rfl

theorem original_markedParabolicMap_kernel_characteristic
    (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬Group.IsSolvable H) (K : Subgroup H) (hK : K.IsCComponent)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (hgen : K ⊔ (T : Subgroup H) = ⊤)
    (e : sourceImage (ChapterB.minimalParabolicMax T hP) K ≃* D) :
    (markedParabolicMap (ChapterB.minimalParabolicMax T hP) K e).ker.Characteristic := by
  rw [original_markedParabolicMap_kernel T hP hs K hK hqK hgen e]
  infer_instance
end CFSG.Quasithin.Chapter14.Section02
