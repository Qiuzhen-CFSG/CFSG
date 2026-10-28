module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.Assembly
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology.PointGeometry.Sp4Core.RootPlacement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Preliminary.Cover
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedLifting
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Geometry

/-!
# Fixed vectors through the original symplectic central kernel

Restrict the marked central cover to the derived symplectic group; perfectness
of the actual quotient makes this a surjective reindexing. Universal-cover
fixed lifting then says that every fixed vector in the natural quotient has
all its original lifts fixed. No splitting of C_V(L) is introduced.

Source: Aschbacher–Smith I.2.3(1), applied in 11.1.5, printed pp.413,765–766.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped IsMulCommutative
open Matrix Subgroup Theory.GroupTheory Representation Representation.OneCohomology
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

include m in
private theorem derived_surjective : Function.Surjective
    (commutator (Sp S.field.Carrier)).subtype := by
  let := S.source.quasisimple
  let : Group.IsPerfect (Sp S.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective
  exact fun g => ⟨⟨g,Group.IsPerfect.mem_commutator⟩,rfl⟩

private def derivedProjection :
    Representation.IntertwiningMap
      ((Preliminary.markedAction D m).comp (commutator (Sp S.field.Carrier)).subtype)
      (binaryNatural (K := S.field.Carrier)) where
  toLinearMap := (Preliminary.markedProjection D m).toLinearMap
  isIntertwining' g := (Preliminary.markedProjection D m).isIntertwining' g.val

private theorem derivedProjection_cover : IsCover (derivedProjection D S m) := by
  have hp := Preliminary.markedProjection_isCover D m
  refine ⟨hp.1,fun w hw g => hp.2.1 hw g.val,?_⟩
  apply top_unique
  rw [←hp.2.2]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨g,w⟩,rfl⟩
  obtain ⟨g,rfl⟩ := derived_surjective D S m g
  exact Coinvariants.sub_mem_ker
    (ρ := (Preliminary.markedAction D m).comp (commutator (Sp S.field.Carrier)).subtype) g w

/-- Fixed vectors of each actual component element lift through the entire central kernel. -/
theorem projection_fixed_iff (l : L) (v : V) :
    (Coordinates.sp4 m).modelAction ((Coordinates.sp4 m).quotientMap l)
        ((Coordinates.sp4 m).projection v).toAdd = ((Coordinates.sp4 m).projection v).toAdd ↔
      V.normalizerMonoidHom (inclusion D.normalizes l) v = v := by
  constructor
  · intro hv
    let w : D.space := (D.spaceEquiv.symm v).toAdd
    have hpw : derivedProjection D S m w = ((Coordinates.sp4 m).projection v).toAdd := rfl
    have hg : binaryNatural (SymplecticModel.actor D S m l) (derivedProjection D S m w) =
        derivedProjection D S m w := by
      rw [hpw]
      change (SymplecticModel.actor D S m l).val.val *ᵥ _ = _
      rw [SymplecticModel.actor_val]
      exact hv
    have hw := cover_fixed_of_projection_fixed (derivedProjection D S m)
      (derivedProjection_cover D S m) (SymplecticModel.actor D S m l) w hg
    change Preliminary.markedAction D m (SymplecticModel.actor D S m l).val w = w at hw
    rw [SymplecticModel.actor_val] at hw
    change Preliminary.markedAction D m
      (m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l)) w = w at hw
    rw [Preliminary.markedAction_mk] at hw
    have hwv : (w.val.toMul.val : G) = (v : G) :=
      (D.spaceEquiv_apply w).symm.trans
        (congrArg Subtype.val (D.spaceEquiv.apply_symm_apply v))
    have he : D.spaceEquiv (Multiplicative.ofAdd (D.chosenAction l w)) =
        V.normalizerMonoidHom (inclusion D.normalizes l) v := by
      apply Subtype.ext
      rw [D.spaceEquiv_apply]
      change (l : G) * (w.val.toMul.val : G) * (l : G)⁻¹ = _
      rw [hwv]
      rfl
    rw [←he,hw]
    exact D.spaceEquiv.apply_symm_apply v
  · intro hv
    rw [←(Coordinates.sp4 m).projection_component_conjugation,hv]

/-- The marked local two-core fixes precisely the caller's actual point. -/
theorem model_core_fixed_iff (f : InvariantFlag (Coordinates.sp4 m))
    (x : Vector S.field.Carrier) :
    (∀ g ∈ modelImage D S m ((f.Li 0).pCoreIn 2), g.val *ᵥ x = x) ↔ x ∈ f.space 0 := by
  have hf : f.space 0 = Sp4.space m 1 :=
    Sp4.space_inner_unique m 0 (f.space 0) (f.dimension 0)
      (inf_le_left.trans (f.invariant 0))
  rw [modelImage_core D S m (f.Li 0) ((localResidual_le _).trans inf_le_left),
    modelImage_point,←map_pCoreIn_of_injective 2 _ _ (MulAut.conj (Sp4.alignment m)).injective]
  change (∀ g ∈ ((pCore 2 (pointLocal (F := S.field.Carrier))).map pointLocal.subtype).map
    (MulAut.conj (Sp4.alignment m)).toMonoidHom, g.val *ᵥ x = x) ↔ _
  rw [pointLocal_core_eq S.field.card_eq S.nonbinary,hf]
  change _ ↔ x ∈ Sp4.ModelFlag.movedStage (Sp4.alignment m) 1
  rw [Sp4.ModelFlag.mem_movedStage]
  change _ ↔ (Sp4.alignment m)⁻¹ • x ∈ point S.field.Carrier
  rw [←PointRadicalAction.radical_fixedSpace]
  constructor
  · intro hx r hr
    have hh := hx ((Sp4.alignment m)*r*(Sp4.alignment m)⁻¹) ⟨r,hr,rfl⟩
    change ((Sp4.alignment m)*r*(Sp4.alignment m)⁻¹) • x = x at hh
    have he := congrArg (fun w => (Sp4.alignment m)⁻¹ • w) hh
    simpa only [mul_smul,inv_smul_smul] using he
  · rintro hx _ ⟨r,hr,rfl⟩
    change ((Sp4.alignment m)*r*(Sp4.alignment m)⁻¹) • x = x
    rw [mul_smul,mul_smul,hx r hr,smul_inv_smul]

/-- The literal point-core fixed space includes every nonsplit central lift. -/
theorem local_core_fixed (f : InvariantFlag (Coordinates.sp4 m)) :
    V ⊓ centralizer ((f.Li 0).pCoreIn 2 : Set G) = f.Vi 0 := by
  ext v
  constructor
  · rintro ⟨hv,hfix⟩
    let v' : V := ⟨v,hv⟩
    apply ((Coordinates.sp4 m).mem_preimage (f.space 0) v').mpr
    apply (model_core_fixed_iff D S m f _).mp
    rintro g ⟨l,hl,rfl⟩
    apply (projection_fixed_iff D S m l v').mpr
    apply Subtype.ext
    change (l : G)*v*(l : G)⁻¹ = v
    rw [hfix l hl,mul_inv_cancel_right]
  · intro hv
    have hvV : v ∈ V := D.centralQuotientPreimage_le _ hv
    let v' : V := ⟨v,hvV⟩
    refine ⟨hvV,?_⟩
    intro l hl
    have hlL : l ∈ L := (pCoreIn_le _ _).trans ((localResidual_le _).trans inf_le_left) hl
    let l' : L := ⟨l,hlL⟩
    have hx := (model_core_fixed_iff D S m f _).mpr
      (((Coordinates.sp4 m).mem_preimage (f.space 0) v').mp hv)
    have he := congrArg Subtype.val ((projection_fixed_iff D S m l' v').mp
      (hx _ ⟨l',hl,rfl⟩))
    change l*v*l⁻¹=v at he
    exact (mul_inv_eq_iff_eq_mul).mp he

/-- The original symplectic center calculation now needs only its point-core product.
The consolidated owner retains that remaining outer-Sylow comparison. -/
theorem center_eq_of_core_product
    (f : InvariantFlag (Coordinates.sp4 m))
    (hb : ChapterC.IsSL3EvenBlock L S.field.degree ∨ ChapterC.IsSp4FourBlock L)
    (hprod : f.Ri 0 = (f.Li 0).pCoreIn 2 ⊔ (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L :=
  center_eq_of_core_calculations D S f hb hprod (local_core_fixed D S m f)

end PointGeometry.Sp4Core
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.PointCohomology
