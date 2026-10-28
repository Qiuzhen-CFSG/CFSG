module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.Quotient.SymplecticModel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.Residuals
public import Theory.GroupTheory.PCoreInRestriction

/-!
# A long root inside the original symplectic point radical

The original local residual maps onto the residual of its marked parabolic.
Its two-core maps onto the model two-core since the projection kernel is a
two-group. A central root in the standard point radical therefore lifts into
O₂(L₁), and hence into the original R₁. This discharges root placement in the
corrected quotient's dual fixed-space calculation.

Source: Aschbacher–Smith 11.1.5, printed pp.765–766, and I.2.3(1b).
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Matrix Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
namespace PointGeometry.Sp4Core
open Theory.SpecificGroups.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

/-- The component marking applied to an actual ambient subgroup. -/
@[expose] def modelImage (A : Subgroup G) : Subgroup (Sp S.field.Carrier) :=
  (A.subgroupOf L).map (Coordinates.sp4 m).quotientMap

/-- Two-core images retain the literal original projection. -/
theorem modelImage_core (A : Subgroup G) (hA : A ≤ L) :
    modelImage D S m (A.pCoreIn 2) = (modelImage D S m A).pCoreIn 2 := by
  have hk : IsPGroup 2 (Coordinates.sp4 m).quotientMap.ker := by
    have he : (Coordinates.sp4 m).quotientMap.ker = pCore 2 L := by
      ext l
      change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ l ∈ pCore 2 L
      rw [←m.groupEquiv.map_one,m.groupEquiv.injective.eq_iff]
      exact QuotientGroup.eq_one_iff l
    rw [he]
    exact pCore_isPGroup
  change ((A.pCoreIn 2).subgroupOf L).map _ = _
  rw [←pCoreIn_subgroupOf 2 A L hA]
  exact map_pCoreIn_of_ker_isPGroup _ hk _

/-- The actual local residual maps onto the marked stabilizer residual. -/
theorem modelImage_residual (U : Submodule S.field.Carrier (Coordinates.sp4 m).Space) :
    modelImage D S m (localResidual L ((Coordinates.sp4 m).preimage U)) =
      (solvableResidual ((Coordinates.sp4 m).modelStabilizer U)).map
        ((Coordinates.sp4 m).modelStabilizer U).subtype := by
  let c := Coordinates.sp4 m
  ext x
  constructor
  · rintro ⟨l,hl,rfl⟩
    let y : localResidual L (c.preimage U) := ⟨l,hl⟩
    exact ⟨(c.residualProjection U y).val,(c.residualProjection U y).property,
      c.residualProjection_coe U y⟩
  · rintro ⟨x,hx,rfl⟩
    obtain ⟨y,hy⟩ := c.residualProjection_surjective U ⟨x,hx⟩
    exact ⟨⟨y,(localResidual_le _ y.property).1⟩,y.property,
      (c.residualProjection_coe U y).symm.trans (congrArg (fun z => z.val.val) hy)⟩

/-- The caller's original point residual is the conjugate standard point-local. -/
theorem modelImage_point (f : InvariantFlag (Coordinates.sp4 m)) :
    modelImage D S m (f.Li 0) =
      pointLocal.map (MulAut.conj (Sp4.alignment m)).toMonoidHom := by
  have hf : f.space 0 = Sp4.space m 1 :=
    Sp4.space_inner_unique m 0 (f.space 0) (f.dimension 0)
      (inf_le_left.trans (f.invariant 0))
  change modelImage D S m (localResidual L ((Coordinates.sp4 m).preimage (f.space 0))) = _
  rw [modelImage_residual,hf]
  let R (A : Subgroup (Sp S.field.Carrier)) := (solvableResidual A).map A.subtype
  have hp := congrArg (fun A : Subgroup (Coordinates.sp4 m).ModelGroup =>
    (solvableResidual A).map A.subtype) (Sp4.modelStabilizer_space m 0)
  apply hp.trans
  change R ((pointParabolic (F := S.field.Carrier)).map
    (MulAut.conj (Sp4.alignment m)).toMonoidHom) = _
  let A := pointParabolic (F := S.field.Carrier)
  let e := MulAut.conj (Sp4.alignment m)
  let j := e.subgroupMap A
  have hm := congrArg (Subgroup.map (A.map e.toMonoidHom).subtype)
    (map_solvableResidual_eq j.toMonoidHom j.surjective)
  have hc : (A.map e.toMonoidHom).subtype.comp j.toMonoidHom =
      e.toMonoidHom.comp A.subtype := rfl
  have he : (R A).map e.toMonoidHom = R (A.map e.toMonoidHom) := by
    change ((solvableResidual A).map j.toMonoidHom).map (A.map e.toMonoidHom).subtype =
      (solvableResidual (A.map e.toMonoidHom)).map (A.map e.toMonoidHom).subtype at hm
    change ((solvableResidual A).map A.subtype).map e.toMonoidHom = _
    rw [Subgroup.map_map,hc] at hm
    rw [Subgroup.map_map]
    exact hm
  rw [←he]
  change ((solvableResidual (pointParabolic (F := S.field.Carrier))).map
    pointParabolic.subtype).map e.toMonoidHom = _
  rw [pointParabolic_solvableResidual_eq S.field.card_eq S.nonbinary]

/-- Every literal matrix long root belongs to the standard point-local two-core. -/
theorem root_mem_point_core (t : S.field.Carrier) :
    Representation.OneCohomology.SymplecticFour.rootElement 0 t ∈
      (pointLocal (F := S.field.Carrier)).pCoreIn 2 := by
  change _ ∈ (pCore 2 (pointLocal (F := S.field.Carrier))).map pointLocal.subtype
  rw [pointLocal_core_eq S.field.card_eq S.nonbinary]
  refine ⟨pointRadicalElement 0 0 t,pointRadicalElement_mem _ _ _,?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pointRadicalElement,pointRadicalMatrix,
      Representation.OneCohomology.SymplecticFour.rootElement,
      Representation.OneCohomology.SymplecticFour.rootMatrix,Matrix.single]

/-- One conjugate long root lies in the actual component image of the original R₁. -/
theorem exists_root_placement (f : InvariantFlag (Coordinates.sp4 m)) :
    ∃ g : Representation.SymplecticFourOrthogonalCover.L (K := S.field.Carrier),
      Roots.conjugateGroup g ≤ ((f.Ri 0).subgroupOf L).map (SymplecticModel.actor D S m) := by
  obtain ⟨a,ha⟩ := (Coordinates.sp4 m).quotientMap_surjective (Sp4.alignment m)
  let g := SymplecticModel.actor D S m a
  have hg : g.val = Sp4.alignment m := (SymplecticModel.actor_val D S m a).trans ha
  refine ⟨g,?_⟩
  rintro r ⟨s,hs,rfl⟩
  have hc : s.val ∈ (pointLocal (F := S.field.Carrier)).pCoreIn 2 := by
    obtain ⟨t,ht⟩ := (RootSubgroup.mem_group_iff 0 s.val).mp hs
    rw [←ht]
    exact root_mem_point_core D S t
  have himage : (g*s*g⁻¹).val ∈ modelImage D S m ((f.Li 0).pCoreIn 2) := by
    rw [modelImage_core D S m (f.Li 0) ((localResidual_le _).trans inf_le_left),modelImage_point]
    rw [←map_pCoreIn_of_injective 2 _ _ (MulAut.conj (Sp4.alignment m)).injective]
    refine ⟨s.val,hc,?_⟩
    change Sp4.alignment m * s.val * (Sp4.alignment m)⁻¹ = g.val*s.val*g.val⁻¹
    rw [hg]
  obtain ⟨l,hl,he⟩ := himage
  have hR : (f.Li 0).pCoreIn 2 ≤ f.Ri 0 :=
    pCoreIn_mono_of_normalizes le_sup_left
      (sup_le (f.Li 0).le_normalizer (f.sylow_normalizes_Li 0))
  refine ⟨l,hR hl,?_⟩
  apply Subtype.ext
  exact (SymplecticModel.actor_val D S m l).trans he

/-- The fixed-space bound is now proved on Q and the original point radical,
including the full possible nonsplit quotient. -/
theorem core_fixed_le_denominator (hb : ChapterC.IsShort L)
    (f : InvariantFlag (Coordinates.sp4 m)) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ⊓ centralizer (f.Ri 0 : Set G) ≤
      cohomologyDenominator T L V := by
  obtain ⟨g,hg⟩ := exists_root_placement D S m f
  exact SymplecticModel.core_fixed_le_denominator_of_root_placement D S m hb g hg

end PointGeometry.Sp4Core
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
