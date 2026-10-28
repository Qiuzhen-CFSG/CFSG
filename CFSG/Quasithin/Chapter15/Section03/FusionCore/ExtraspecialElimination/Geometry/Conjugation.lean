module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ContainedOffenderRoute.GeometricAssembly
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.SectionConstruction
public import CFSG.Quasithin.ChapterE.Section03.Offenders.Transport.Foundations
public import Theory.GroupTheory.AmalgamLocalCores
public import Theory.GroupTheory.SubgroupCenterImageBound
public import Theory.Frattini.OmegaProducts

/-!
# Conjugating the actual section action

Relative commutator kernels, two-cores and omega-centers follow the same
ambient conjugation. The quotient-centralizer identity then reconstructs
the faithful section action at a conjugate endpoint. This preserves the
literal endpoint groups and their quotient kernels used in F.9 geometry.

Source: Aschbacher--Smith, F.9.17 and 15.3.49(f)--(h), combined manuscript
(1 March 2004), printed pp.324 and 1143.
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
variable {G : Type*} [Group G]

namespace Geometry

private theorem map_sectionCentralizer_le
    (H U Z : Subgroup G) (hHZ : H ≤ normalizer (Z : Set G)) (g : G) :
    (sectionCentralizer H U Z).map (MulAut.conj g).toMonoidHom ≤
      sectionCentralizer (H.map (MulAut.conj g).toMonoidHom)
        (U.map (MulAut.conj g).toMonoidHom) (Z.map (MulAut.conj g).toMonoidHom) := by
  apply le_commutatorPreimage (map_mono (commutatorPreimage_le H U Z))
  rw [← map_commutator]
  exact map_mono (commutator_commutatorPreimage_le H U Z hHZ)

/-- The relative commutator kernel follows the same ambient conjugation. -/
theorem sectionCentralizer_conjugate
    (H U Z : Subgroup G) (hHZ : H ≤ normalizer (Z : Set G)) (g : G) :
    (sectionCentralizer H U Z).map (MulAut.conj g).toMonoidHom =
      sectionCentralizer (H.map (MulAut.conj g).toMonoidHom)
        (U.map (MulAut.conj g).toMonoidHom) (Z.map (MulAut.conj g).toMonoidHom) := by
  apply le_antisymm (map_sectionCentralizer_le H U Z hHZ g)
  apply (map_le_map_iff_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective).mp
  have hn : H.map (MulAut.conj g).toMonoidHom ≤
      normalizer (Z.map (MulAut.conj g).toMonoidHom : Set G) :=
    (map_mono hHZ).trans (le_normalizer_map _)
  have hr := map_sectionCentralizer_le (H.map (MulAut.conj g).toMonoidHom)
    (U.map (MulAut.conj g).toMonoidHom) (Z.map (MulAut.conj g).toMonoidHom) hn g⁻¹
  simpa only [ChapterE.offender_map_conj_inverse] using hr

private theorem quotientCentralizer_image
    (H U Z : Subgroup G) [(Z.subgroupOf H).Normal]
    (hUH : U ≤ H) (hHZ : H ≤ normalizer (Z : Set G)) :
    (CosetSetup.quotientCentralizer H U Z).map H.subtype = sectionCentralizer H U Z := by
  apply le_antisymm
  · apply le_commutatorPreimage (map_subtype_le _)
    rw [commutator_comm]
    apply commutator_le.mpr
    rintro u hu x ⟨x, hx, rfl⟩
    exact (CosetSetup.mem_quotientCentralizer_iff H U Z hUH x).mp hx u hu
  · intro x hx
    have hxH := commutatorPreimage_le H U Z hx
    refine ⟨⟨x, hxH⟩, ?_, rfl⟩
    apply (CosetSetup.mem_quotientCentralizer_iff H U Z hUH _).mpr
    intro u hu
    have hc : ⁅U, sectionCentralizer H U Z⁆ ≤ Z := by
      rw [commutator_comm]
      exact commutator_commutatorPreimage_le H U Z hHZ
    exact hc (commutator_mem_commutator hu hx)

/-- The omega-center containment is preserved by the literal conjugation. -/
theorem centered_conjugate {H U : Subgroup G}
    (h : U ≤ (center (omegaOneAmbient (localTwoCore H))).map
      (omegaOneAmbient (localTwoCore H)).subtype) (g : G) :
    U.map (MulAut.conj g).toMonoidHom ≤
      (center (omegaOneAmbient (localTwoCore (H.map (MulAut.conj g).toMonoidHom)))).map
        (omegaOneAmbient (localTwoCore (H.map (MulAut.conj g).toMonoidHom))).subtype := by
  have hcore : (localTwoCore H).map (MulAut.conj g).toMonoidHom =
      localTwoCore (H.map (MulAut.conj g).toMonoidHom) :=
    (Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
      2 (MulAut.conj g).toMonoidHom (MulAut.conj g).injective H).symm
  have hm := map_mono (f := (MulAut.conj g).toMonoidHom) h
  rw [map_subgroup_center_eq _ (MulAut.conj g).injective,
    map_omegaOneAmbient_injective _ (MulAut.conj g).injective, hcore] at hm
  exact hm

end Geometry

namespace SectionAction

/-- Construct the section action at a conjugate endpoint from its transported
kernel. All three groups use the same ambient conjugating element. -/
noncomputable def conjugate {H U Z : Subgroup G} [IsElementaryAbelian 2 U]
    (action : SectionAction H U Z) (hUH : U ≤ H) (g : G) :
    letI := IsElementaryAbelian.map (p := 2) (A := U) (MulAut.conj g).toMonoidHom
    SectionAction (H.map (MulAut.conj g).toMonoidHom)
      (U.map (MulAut.conj g).toMonoidHom) (Z.map (MulAut.conj g).toMonoidHom) := by
  let f := (MulAut.conj g).toMonoidHom
  letI : IsElementaryAbelian 2 (U.map f) := IsElementaryAbelian.map _
  have hnormal : H.map f ≤ normalizer (Z.map f : Set G) :=
    (map_mono action.normalizes_layer).trans (le_normalizer_map _)
  letI : ((Z.map f).subgroupOf (H.map f)).Normal :=
    normal_subgroupOf_of_le_normalizer hnormal
  apply ComponentReduction.sectionActionOfCentralizer _ _ _
    (map_mono action.layer_le) (map_mono hUH)
    ((map_mono action.normalizes).trans (le_normalizer_map _)) hnormal
  apply (map_injective (H.map f).subtype_injective)
  rw [Geometry.quotientCentralizer_image _ _ _ (map_mono hUH) hnormal,
    ← Geometry.sectionCentralizer_conjugate H U Z action.normalizes_layer g,
    Geometry.sectionCentralizer_eq_core_intersection H U Z H action le_rfl,
    inf_eq_right.mpr (show localTwoCore H ≤ H from pCoreIn_le 2 H)]
  exact (Theory.GroupTheory.AmalgamLocalCores.pCoreIn_map_of_injective
    2 (MulAut.conj g).toMonoidHom (MulAut.conj g).injective H).symm

end SectionAction
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
