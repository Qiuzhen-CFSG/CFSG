module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Normalizers
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.ModuleCover
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.CriticalIntersections
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.MarkedPartitions.Ambient

/-!
# Connecting the original module to the critical intersection

The marked chart supplies all three module calculations required by the
intersection argument. A nonzero upper parameter supplies an actual element
of Uα outside O₂(H), so the duality argument applies to the original action.
This proves point noncontainment and the complement needed by the ambient
partitions without assuming either conclusion. The literal earlier duality,
commutator identity and reciprocal geodesic placement remain explicit.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
14.7.69(a)–(f), printed p.1072. The earlier inputs are produced by qt-14-07,
qt-14-03 and qt-14-05-terminal-duality. This is the forward calculation;
the reciprocal source transport and final fusion assembly remain separate.
-/

@[expose] public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08
open Representation.OneCohomology Representation.SL2FourNatural Matrix.SpecialLinearGroup
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  {X Y : Type u} [AddCommGroup X] [Module (ZMod 2) X]
  [AddCommGroup Y] [Module (ZMod 2) Y]

namespace Data.CriticalChart
variable {d : Data T L V F W} {hc : d.SectionCentralizer}
  {c : CriticalPath (L := L) F} (b : d.CriticalChart hc c)

include b

/-- The three previously independent calculations, on the literal original section. -/
theorem moduleCalculations (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) :
    CriticalIntersections.ModuleCalculations d c (c.Uα_le_H earlier) := by
  obtain ⟨hm, hf, hd⟩ := b.original_module_calculations earlier sep localActors
    (c.Uα_le_H earlier)
  exact ⟨hm, hf, hd⟩

/-- A nonidentity quotient actor is lifted in Uα itself, not in an unrelated model. -/
theorem exists_actor_outside_core :
    ∃ h : F.H, (h : G) ∈ c.Uα ∧ (h : G) ∉ F.H.pCoreIn 2 := by
  obtain ⟨a, ha, he⟩ := b.upper_lift 1
  refine ⟨a, ha, ?_⟩
  intro hcore
  have ha' : a ∈ d.qH.ker := by rw [d.qH_ker]; exact hcore
  have hz : b.conjugator * upper (1 : SL2FourNatural.F) * b.conjugator⁻¹ = 1 := by
    apply d.alternatingActor_injective
    rw [← he, map_one]
    exact ha'
  have hu : upper (1 : SL2FourNatural.F) = 1 := by
    apply (MulAut.conj b.conjugator).injective
    simpa only [map_one, MulAut.conj_apply] using hz
  have h10 : (1 : SL2FourNatural.F) = 0 := by
    simpa [upper] using congrArg (fun s : SL => s.1 0 1) hu
  exact one_ne_zero h10

/-- The original marked module and the genuine 14.5.21 duality give the
point noncontainment in the contradiction branch of 14.7.69. -/
theorem point_not_le_critical
    (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (s : CriticalIntersections.SourceDuality F X Y)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hfull : star F c.Uα = star F (Q T L)) :
    ¬ F.Vi 1 ≤ c.Uα := by
  obtain ⟨h, hh, hn⟩ := b.exists_actor_outside_core
  exact CriticalIntersections.point_not_le_Uα d hc sep s c earlier hUH
    (b.moduleCalculations earlier sep localActors) hcomm hfull h hh
    (b.actor_displacement_finrank h hh hn) (b.actor_displacement_disjoint h hh hn)

/-- The complement used by the ambient partitions is a consequence of the
original-module and duality calculations. -/
theorem ambientComplement_of_full_image
    (earlier : c.EarlierImages) (sep : d.ModuleSeparation)
    (localActors : b.LocalActors) (s : CriticalIntersections.SourceDuality F X Y)
    (hUH : F.U ≤ conjugate F.H c.conjugator)
    (hcomm : ⁅F.U, F.H.pCoreIn 2⁆ = F.Vi 1)
    (hfull : star F c.Uα = star F (Q T L)) : b.AmbientComplement := by
  have hp := b.point_not_le_critical earlier sep localActors s hUH hcomm hfull
  have hf := CriticalIntersections.critical_intersection_complement d hc c earlier hUH
    (b.moduleCalculations earlier sep localActors) hcomm hp
  exact ⟨hf.2.1, hf.2.2.1⟩

end Data.CriticalChart
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
