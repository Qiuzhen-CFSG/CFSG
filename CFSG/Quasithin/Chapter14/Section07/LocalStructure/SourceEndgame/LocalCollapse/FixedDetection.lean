module
public import Mathlib.Algebra.Group.Defs
public import Theory.Representation.SL2FourNaturalBorelFixedLifting
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections.Basic
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.Preparation
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceSetup
import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.Setup
import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.ChiefFactors.HAccounting.DualSection
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.RootRecognition.Marking
import Mathlib.Algebra.Module.ZMod

@[expose] public section
noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.FixedDetection
open Chapter12.Section08 CriticalFusion.Source ChiefFactors
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

abbrev sectionAction (s : CriticalIntersections.SourceDuality F X Y) :=
  s.qAction.comp (inclusion (K_le_H F))

def qKToQH (hc : d.SectionCentralizer) : QK F →* F.H.pCoreIn 2 :=
  inclusion (QK_le_QH d hc)

theorem coordinate_kernel_le (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y) (b : QKDualCoordinates d) :
    b.qSection.coordinates.ker ≤ (s.qSection.coordinates.comp (qKToQH d hc)).ker := by
  intro q hq
  change s.qSection.coordinates (qKToQH d hc q) = 1
  rw [s.qSection.coordinates_eq_one_iff, q_centralizer_eq_h_centralizer d hc]
  exact (b.qSection.coordinates_eq_one_iff q).mp hq

def coordinateInclusion (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y) (b : QKDualCoordinates d) :
    Module.Dual (ZMod 2) SL2FourNatural.V →ₗ[ZMod 2] Y :=
  (AddMonoidHom.toMultiplicative.symm
    (b.qSection.coordinates.liftOfSurjective b.qSection.onto
      ⟨s.qSection.coordinates.comp (qKToQH d hc), coordinate_kernel_le d hc s b⟩)).toZModLinearMap 2

theorem coordinateInclusion_apply (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y) (b : QKDualCoordinates d) (q : QK F) :
    coordinateInclusion d hc s b (b.qSection.coordinates q).toAdd =
      (s.qSection.coordinates (qKToQH d hc q)).toAdd := by
  change ((AddMonoidHom.toMultiplicative.symm
    (b.qSection.coordinates.liftOfSurjective b.qSection.onto
      ⟨s.qSection.coordinates.comp (qKToQH d hc), coordinate_kernel_le d hc s b⟩)).toZModLinearMap 2)
      (b.qSection.coordinates q).toAdd = _
  simp

theorem coordinateInclusion_injective (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y) (b : QKDualCoordinates d) :
    Function.Injective (coordinateInclusion d hc s b) := by
  apply LinearMap.ker_eq_bot.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  obtain ⟨q, hq⟩ := b.qSection.onto (Multiplicative.ofAdd v)
  have hq' : (b.qSection.coordinates q).toAdd = v := congrArg Multiplicative.toAdd hq
  have hz : s.qSection.coordinates (qKToQH d hc q) = 1 := by
    change (s.qSection.coordinates (qKToQH d hc q)).toAdd = 0
    rw [← coordinateInclusion_apply, hq']
    exact hv
  have hC : (q : G) ∈ C F := by
    have hh := (s.qSection.coordinates_eq_one_iff _).mp hz
    rwa [q_centralizer_eq_h_centralizer d hc] at hh
  have hb := (b.qSection.coordinates_eq_one_iff q).mpr hC
  exact hq'.symm.trans (congrArg Multiplicative.toAdd hb)

theorem coordinateInclusion_equivariant (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y) (b : QKDualCoordinates d)
    (k : K F) (v : Module.Dual (ZMod 2) SL2FourNatural.V) :
    coordinateInclusion d hc s b (SL2FourNatural.naturalRepresentation.dual (RootRecognition.qK d k) v) =
      sectionAction s k (coordinateInclusion d hc s b v) := by
  obtain ⟨q, hq⟩ := b.qSection.onto (Multiplicative.ofAdd v)
  have hq' : (b.qSection.coordinates q).toAdd = v := congrArg Multiplicative.toAdd hq
  rw [← hq', ← HAccounting.natural_dual_on_lift d (inclusion (K_le_H F) k)
    (RootRecognition.qK d k) (RootRecognition.qK_marking d k)]
  rw [← b.qSection.equivariant, coordinateInclusion_apply, coordinateInclusion_apply]
  exact s.qSection.equivariant (inclusion (K_le_H F) k) (qKToQH d hc q)

def dualInclusion (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y) (b : QKDualCoordinates d) :
    IntertwiningMap (SL2FourNatural.naturalRepresentation.dual.comp (RootRecognition.qK d))
      (sectionAction s) :=
  (coordinateInclusion d hc s b).intertwiningMap_of_isIntertwiningMap _ _
    (coordinateInclusion_equivariant d hc s b)

theorem displacement_mem_range (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y) (b : QKDualCoordinates d)
    (k : K F) (y : Y) :
    sectionAction s k y - y ∈ (coordinateInclusion d hc s b).range := by
  obtain ⟨q, hq⟩ := s.qSection.onto (Multiplicative.ofAdd y)
  let kH : F.H := inclusion (K_le_H F) k
  let r : F.H.pCoreIn 2 :=
    (⟨kH * q * (kH : G)⁻¹,
      (mem_normalizer_iff.mp (s.qSection.normalized kH.property) q).mp q.property⟩ :
      F.H.pCoreIn 2) * q⁻¹
  have hr : (r : G) ∈ QK F := by
    apply (le_sup_left : ⁅F.H.pCoreIn 2, K F⁆ ≤ QK F)
    rw [commutator_comm]
    exact commutator_mem_commutator k.property q.property
  refine ⟨(b.qSection.coordinates ⟨r, hr⟩).toAdd, ?_⟩
  rw [coordinateInclusion_apply]
  change (s.qSection.coordinates (_ * q⁻¹)).toAdd = _
  rw [map_mul, map_inv, toAdd_mul, toAdd_inv, ← sub_eq_add_neg]
  rw [s.qSection.equivariant, hq]
  rfl

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.FixedDetection


namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.FixedDetection
open Chapter12.Section08 CriticalFusion.Source ChiefFactors
open CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors
open CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}
  {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)
  {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

/-- Gaschütz fixed-vector detection for the literal QK/C section.  The Sylow
witness and its marked image are kept explicit, so source assembly can use the
actual parabolic Sylow and the original qK map. -/
theorem fixed_detection_on_QK
    (hc : d.SectionCentralizer)
    (s : CriticalIntersections.SourceDuality F X Y)
    (b : QKDualCoordinates d)
    (B : Sylow 2 (K F))
    (hmark : ((RootRecognition.qK d).comp (B : Subgroup (K F)).subtype).range =
      Matrix.SpecialLinearGroup.rankOneBorel SL2FourNatural.F)
    (hdisp : ∀ k : K F, ∀ y : Y, s.qAction (Subgroup.inclusion (K_le_H F) k) y - y ∈
      (coordinateInclusion d hc s b).range) :
    ∀ y ∈ fixedSpace (s.qAction.comp (Subgroup.inclusion (K_le_H F)))
      (B : Subgroup (K F)), ∀ k : K F,
      s.qAction (Subgroup.inclusion (K_le_H F) k) y = y := by
  let q := RootRecognition.qK d
  let i := dualInclusion d hc s b
  have h := Representation.SL2FourNaturalBorelFixedLifting.fixed_of_marked_borel
    (s.qAction.comp (Subgroup.inclusion (K_le_H F))) q
    (RootRecognition.qK_surjective d) i (coordinateInclusion_injective d hc s b) B hmark
    (by
      intro k y
      exact hdisp k y)
  intro y hy k
  exact h y hy k

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.LocalCollapse.FixedDetection
