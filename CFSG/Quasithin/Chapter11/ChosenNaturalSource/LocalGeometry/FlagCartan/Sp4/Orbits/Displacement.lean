module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.PlaneAction.FixedLifting
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.DisplacementFamily
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.Coordinates

/-!
# The actual point-residual Sylow and its fixed and displacement spaces

The original quotient map of L1 contains the aligned symplectic Sylow and
has a two-group kernel. Pulling that Sylow back gives an actual Sylow of L1.
The intrinsic natural flag identifies V2 by displacement into V1. Fixed
lifting through the central cover identifies its ordinary fixed subgroup
in V and in V3 as V1, which has smaller field dimension than V2.

Thus the ordinary fixed-plane description cannot supply source 11.1.4.
The corrected displacement-family consumer is in Orbits.Normalizer.
The statements retain the full original C_V(L), and do not refute the
ambient source theorem under all its standing hypotheses.

Source: Aschbacher--Smith, opening §11.1 and 11.1.4, pp.760--761,765;
fixed lifting uses I.2.3(1), p.413.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Representation
open scoped IsMulCommutative
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.Orbits
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))

/-- The point residual acts through the original component quotient. -/
def pointMap : (flag m S).Li 0 →* Sp S.field.Carrier :=
  (Coordinates.sp4 m).quotientMap.comp (inclusion ((localResidual_le _).trans inf_le_left))

/-- The full inner Sylow, using the common flag alignment. -/
def modelSylow : Sylow 2 (Sp S.field.Carrier) :=
  (unipotentSylow S.field.card_eq S.field.degree_pos).mapSurjective
    (f := (MulAut.conj (alignment m)).toMonoidHom) (MulAut.conj (alignment m)).surjective

theorem modelSylow_coe : (modelSylow S m : Subgroup (Sp S.field.Carrier)) =
    unipotent.map (MulAut.conj (alignment m)).toMonoidHom := rfl

theorem pointMap_ker_isTwoGroup : IsPGroup 2 (pointMap S m).ker := by
  let hRL : (flag m S).Li 0 ≤ L := (localResidual_le _).trans inf_le_left
  let j : (pointMap S m).ker →* pCore 2 L :=
    ((inclusion hRL).comp (pointMap S m).ker.subtype).codRestrict _ (by
      intro x
      apply (QuotientGroup.eq_one_iff _).mp
      apply (Coordinates.sp4 m).groupEquiv.injective
      rw [map_one]
      exact x.property)
  exact (pCore_isPGroup (p := 2) (G := L)).of_injective j (by
    intro x y h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : pCore 2 L => (z.val : G)) h)))

theorem pointMap_image_contains_sylow :
    (modelSylow S m : Subgroup _) ≤ (pointMap S m).range := by
  rintro _ ⟨y,hy,rfl⟩
  obtain ⟨l,hl⟩ := PlaneAction.localProjection_surjective S m 0 ⟨y,hy.1⟩
  refine ⟨l,?_⟩
  have he := congrArg Subtype.val hl
  rw [PlaneAction.localProjection_coe] at he
  change (Coordinates.sp4 m).quotientMap
    ⟨l.val,(localResidual_le _ l.property).1⟩ =
      (alignment m) * y * (alignment m)⁻¹
  calc
    _ = (alignment m) *
        ((alignment m)⁻¹ * (show Sp S.field.Carrier from
          (Coordinates.sp4 m).quotientMap ⟨l.val,(localResidual_le _ l.property).1⟩) *
          (alignment m)) * (alignment m)⁻¹ := by group
    _ = _ := by rw [he]

/-- An actual Sylow of L1 with the marked inner image. -/
def pointSylow : Sylow 2 ((flag m S).Li 0) :=
  (modelSylow S m).comapOfKerIsPGroup (pointMap S m)
    (pointMap_ker_isTwoGroup S m) (pointMap_image_contains_sylow S m)

theorem pointSylow_image :
    (pointSylow S m : Subgroup ((flag m S).Li 0)).map (pointMap S m) = modelSylow S m :=
  Subgroup.map_comap_eq_self (pointMap_image_contains_sylow S m)

/-- Original ambient commutators project to natural vector displacements. -/
theorem projection_displacement (l : L) (v : V) :
    ((Coordinates.sp4 m).projection
      (V.normalizerMonoidHom (inclusion D.normalizes l) v * v⁻¹)).toAdd =
      (Coordinates.sp4 m).modelAction ((Coordinates.sp4 m).quotientMap l)
        ((Coordinates.sp4 m).projection v).toAdd - ((Coordinates.sp4 m).projection v).toAdd := by
  rw [map_mul,map_inv]
  simp only [toAdd_mul,toAdd_inv,← sub_eq_add_neg]
  rw [(Coordinates.sp4 m).projection_component_conjugation]

theorem mem_second_iff_displacement (v : V) :
    (v : G) ∈ (flag m S).Vi 1 ↔
      ∀ p : pointSylow S m,
        (p.val.val : G) * v * (p.val.val : G)⁻¹ * (v : G)⁻¹ ∈ (flag m S).Vi 0 := by
  change (v : G) ∈ (Coordinates.sp4 m).preimage _ ↔ _
  rw [(Coordinates.sp4 m).mem_preimage]
  let x : Vector S.field.Carrier := ((Coordinates.sp4 m).projection v).toAdd
  change x ∈ ModelFlag.movedStage (alignment m) (1 : Fin 3).succ ↔ _
  rw [ModelFlag.mem_movedStage_succ_iff (alignment m) (1 : Fin 3),
    ← modelSylow_coe S m, ← pointSylow_image S m]
  constructor
  · intro h p
    let l : L := ⟨p.val.val,(localResidual_le _ p.val.property).1⟩
    apply ((Coordinates.sp4 m).mem_preimage _
      (V.normalizerMonoidHom (inclusion D.normalizes l) v * v⁻¹)).mpr
    change ((Coordinates.sp4 m).projection
      (V.normalizerMonoidHom (inclusion D.normalizes l) v * v⁻¹)).toAdd ∈ _
    rw [projection_displacement]
    exact h _ (mem_map_of_mem _ p.property)
  · rintro h _ ⟨p,hp,rfl⟩
    let l : L := ⟨p.val,(localResidual_le _ p.property).1⟩
    have hd := ((Coordinates.sp4 m).mem_preimage _
      (V.normalizerMonoidHom (inclusion D.normalizes l) v * v⁻¹)).mp (h ⟨p,hp⟩)
    change ((Coordinates.sp4 m).projection
      (V.normalizerMonoidHom (inclusion D.normalizes l) v * v⁻¹)).toAdd ∈ _ at hd
    rw [projection_displacement] at hd
    exact hd

theorem mem_first_iff_model_fixed (v : V) :
    (v : G) ∈ (flag m S).Vi 0 ↔
      ∀ p : pointSylow S m,
        (Coordinates.sp4 m).modelAction (pointMap S m p.val)
          ((Coordinates.sp4 m).projection v).toAdd = ((Coordinates.sp4 m).projection v).toAdd := by
  change (v : G) ∈ (Coordinates.sp4 m).preimage _ ↔ _
  rw [(Coordinates.sp4 m).mem_preimage]
  let x : Vector S.field.Carrier := ((Coordinates.sp4 m).projection v).toAdd
  change x ∈ ModelFlag.movedStage (alignment m) (0 : Fin 3).succ ↔
    ∀ p : pointSylow S m, (pointMap S m p.val) • x = x
  rw [ModelFlag.mem_movedStage_succ_iff (alignment m) (0 : Fin 3),
    ← modelSylow_coe S m, ← pointSylow_image S m]
  simp only [Fin.castSucc_zero,ModelFlag.movedStage_zero,Submodule.mem_bot,sub_eq_zero]
  constructor
  · intro h p
    exact h _ (mem_map_of_mem _ p.property)
  · rintro h _ ⟨p,hp,rfl⟩
    exact h ⟨p,hp⟩

/-- Fixed lifting retains the entire original central kernel. -/
theorem pointSylow_fixed :
    (flag m S).Vi 0 = V ⊓ centralizer
      (((pointSylow S m : Subgroup ((flag m S).Li 0))).map ((flag m S).Li 0).subtype : Set G) := by
  ext v
  constructor
  · intro hv
    have hvV := D.centralQuotientPreimage_le _ hv
    refine ⟨hvV,?_⟩
    rintro _ ⟨p,hp,rfl⟩
    have he := PlaneAction.component_fixed_of_projection_fixed S m
      ⟨p.val,(localResidual_le _ p.property).1⟩ ⟨v,hvV⟩
      ((mem_first_iff_model_fixed S m ⟨v,hvV⟩).mp hv ⟨p,hp⟩)
    exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)
  · rintro ⟨hv,hc⟩
    apply (mem_first_iff_model_fixed S m ⟨v,hv⟩).mpr
    intro p
    let l : L := ⟨p.val.val,(localResidual_le _ p.val.property).1⟩
    have he : V.normalizerMonoidHom (inclusion D.normalizes l) ⟨v,hv⟩ = ⟨v,hv⟩ := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hc _ (mem_map_of_mem _ p.property))
    have hh := (Coordinates.sp4 m).projection_component_conjugation l ⟨v,hv⟩
    rw [he] at hh
    exact hh.symm

theorem pointSylow_fixed_third :
    (flag m S).Vi 0 = (flag m S).Vi 2 ⊓ centralizer
      (((pointSylow S m : Subgroup ((flag m S).Li 0))).map ((flag m S).Li 0).subtype : Set G) := by
  apply le_antisymm
  · exact le_inf ((flag m S).Vi_mono (by decide))
      ((pointSylow_fixed S m).le.trans inf_le_right)
  · exact (inf_le_inf_right _ (D.centralQuotientPreimage_le _)).trans_eq
      (pointSylow_fixed S m).symm

/-- The literal fixed subgroup is the point, so it cannot be the plane. -/
theorem plane_ne_pointSylow_fixed_third :
    (flag m S).Vi 1 ≠ (flag m S).Vi 2 ⊓ centralizer
      (((pointSylow S m : Subgroup ((flag m S).Li 0))).map ((flag m S).Li 0).subtype : Set G) := by
  rw [← pointSylow_fixed_third S m]
  intro h
  have he := (Coordinates.sp4 m).preimage_injective h
  have hd := congrArg (fun U : Submodule S.field.Carrier (Coordinates.sp4 m).Space =>
    Module.finrank S.field.Carrier U) he
  rw [(flag m S).dimension 1,(flag m S).dimension 0] at hd
  contradiction

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Sp4.Orbits
