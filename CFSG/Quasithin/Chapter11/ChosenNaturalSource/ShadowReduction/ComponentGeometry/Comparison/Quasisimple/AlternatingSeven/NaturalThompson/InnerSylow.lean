module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.PlaneAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.Orbits.Displacement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Incidence.PointImage

/-!
# The inner Sylow lifts to the original point residual

In each natural row the marked inner Sylow is conjugate to the standard
positive-unipotent subgroup. That subgroup lies in the point-parabolic
solvable residual. The actual residual projections lift its elements to
L1 with unchanged image in L/O2(L). Uniqueness of the invariant field flag
transports the result to the caller's original flag.

This retains the literal quotient map in all three SL3, Sp4 and G2 rows.
It supplies the inner factor in the last paragraph of Aschbacher--Smith
11.4.2, printed p.777, using the parabolics of sections11.0--11.1.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} (S : D.NonbinaryNaturalInput)

theorem sl3_innerSylow_lift
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (l : L) (hl : (l : G) ∈ T) :
    ∃ k : (LocalGeometry.SL3.flag D S m).Li 0,
      QuotientGroup.mk' (pCore 2 L) ⟨k,(LocalGeometry.localResidual_le _ k.property).1⟩ =
        QuotientGroup.mk' (pCore 2 L) l := by
  let c := LocalGeometry.SL3.coordinates D S m
  have hq : c.quotientMap l ∈ (LocalGeometry.SL3.innerSylow D S m : Subgroup SL(3,S.field.Carrier)) := by
    rw [LocalGeometry.SL3.innerSylow_eq]
    exact mem_map_of_mem _ hl
  rw [← LocalGeometry.SL3.alignment_sylow] at hq
  obtain ⟨y,hy,he⟩ := hq
  have hyl : y ∈ LocalGeometry.SL3.PlaneAction.localGroup (F := S.field.Carrier) 0 := hy.1
  obtain ⟨k,hk⟩ := LocalGeometry.SL3.PlaneAction.localProjection_surjective D S m 0 ⟨y,hyl⟩
  refine ⟨k, c.groupEquiv.injective ?_⟩
  have hk' := congrArg Subtype.val hk
  rw [LocalGeometry.SL3.PlaneAction.localProjection_coe] at hk'
  change (MulAut.conj (LocalGeometry.SL3.alignment D S m)⁻¹) (c.quotientMap _) = y at hk'
  have h := congrArg (MulAut.conj (LocalGeometry.SL3.alignment D S m)) hk'
  change c.quotientMap _ = c.quotientMap l
  simpa [MulAut.conj_apply, mul_assoc] using h.trans he

theorem sp4_innerSylow_lift
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (l : L) (hl : (l : G) ∈ T) :
    ∃ k : (LocalGeometry.Sp4.flag m S).Li 0,
      QuotientGroup.mk' (pCore 2 L) ⟨k,(LocalGeometry.localResidual_le _ k.property).1⟩ =
        QuotientGroup.mk' (pCore 2 L) l := by
  have hq : (LocalGeometry.Coordinates.sp4 m).quotientMap l ∈
      (LocalGeometry.Sp4.Orbits.modelSylow S m : Subgroup (Theory.SpecificGroups.SymplecticFour.Sp S.field.Carrier)) := by
    rw [LocalGeometry.Sp4.Orbits.modelSylow_coe, ← LocalGeometry.Sp4.alignment_spec]
    exact mem_map_of_mem _ hl
  obtain ⟨k,hk⟩ := LocalGeometry.Sp4.Orbits.pointMap_image_contains_sylow S m hq
  exact ⟨k,(LocalGeometry.Coordinates.sp4 m).groupEquiv.injective hk⟩

theorem g2_innerSylow_lift
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (l : L) (hl : (l : G) ∈ T) :
    ∃ k : (LocalGeometry.G2.flag S m).Li 0,
      QuotientGroup.mk' (pCore 2 L) ⟨k,(LocalGeometry.localResidual_le _ k.property).1⟩ =
        QuotientGroup.mk' (pCore 2 L) l := by
  have hq : LocalGeometry.G2.derivedMap S m l ∈
      (LocalGeometry.G2.modelSylow S m : Subgroup _) := by
    change _ ∈ (LocalGeometry.G2.innerSylow (D := D) : Subgroup L).map _
    rw [LocalGeometry.G2.innerSylow_coe]
    exact mem_map_of_mem _ hl
  obtain ⟨k,hk⟩ := LocalGeometry.G2.ResidualIncidence.pointMap_image_contains_sylow S m hq
  exact ⟨k,(LocalGeometry.Coordinates.g2 m).groupEquiv.injective
    ((LocalGeometry.G2.derivedEquiv S).injective hk)⟩

theorem innerSylow_lift {c : LocalGeometry.Coordinates D S.field}
    (f : LocalGeometry.InvariantFlag c) (l : L) (hl : (l : G) ∈ T) :
    ∃ k : f.Li 0,
      QuotientGroup.mk' (pCore 2 L) ⟨k,(LocalGeometry.localResidual_le _ k.property).1⟩ =
        QuotientGroup.mk' (pCore 2 L) l := by
  cases c with
  | sl3 m =>
    have hf := LocalGeometry.SL3.flag_unique D S m 0 (f.space 0) (f.dimension 0) (f.invariant 0)
    have hL : f.Li 0 = (LocalGeometry.SL3.flag D S m).Li 0 :=
      congrArg (fun U => LocalGeometry.localResidual L ((LocalGeometry.Coordinates.sl3 m).preimage U)) hf
    obtain ⟨k,hk⟩ := sl3_innerSylow_lift S m l hl
    exact ⟨⟨k,hL.symm ▸ k.property⟩,hk⟩
  | sp4 m =>
    have hf := LocalGeometry.Sp4.flag_unique m S 0 (f.space 0) (f.dimension 0) (f.invariant 0)
    have hL : f.Li 0 = (LocalGeometry.Sp4.flag m S).Li 0 :=
      congrArg (fun U => LocalGeometry.localResidual L ((LocalGeometry.Coordinates.sp4 m).preimage U)) hf
    obtain ⟨k,hk⟩ := sp4_innerSylow_lift S m l hl
    exact ⟨⟨k,hL.symm ▸ k.property⟩,hk⟩
  | g2 m =>
    have hf := LocalGeometry.G2.flag_unique S m 0 (f.space 0) (f.dimension 0) (f.invariant 0)
    have hL : f.Li 0 = (LocalGeometry.G2.flag S m).Li 0 :=
      congrArg (fun U => LocalGeometry.localResidual L ((LocalGeometry.Coordinates.g2 m).preimage U)) hf
    obtain ⟨k,hk⟩ := g2_innerSylow_lift S m l hl
    exact ⟨⟨k,hL.symm ▸ k.property⟩,hk⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Quasisimple.AlternatingSeven.NaturalThompson
