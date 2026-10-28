module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Transport

/-!
# Field scalars on the literal first flag subgroup

The given coordinate projection restricts to a surjection V₁ → f.space 0.
When C_V(L)=1 it is injective, so it transports field scalars to actual
binary automorphisms of V₁. The compatibility equation is the original
SL₃, Sp₄ or G₂ marking on L, with no projective quotient of the SL₃ center.
Every L-element normalizing V₁ acts by a scalar since the field space has
dimension one. The full transported scalar group is cyclic and regular;
its equality with the Cartan image is proved in ScalarGeometry.lean.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.0.2 and 11.2.3, printed pp.759--760,768--769.
-/

open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {F : BinaryField}
    {c : Coordinates D F} (f : InvariantFlag c)

/-- Restriction of the original coordinate projection to the literal first flag subgroup. -/
def lineProjection : Additive (f.Vi 0) →ₗ[ZMod 2] f.space 0 :=
  ((c.projection.comp (inclusion (D.centralQuotientPreimage_le _))).toAdditive.toZModLinearMap 2).codRestrict
    (f.space 0 |>.restrictScalars (ZMod 2)) (by
      intro v
      exact (c.mem_preimage _ _).mp v.toMul.property)

theorem lineProjection_surjective : Function.Surjective (lineProjection f) := by
  intro w
  obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd w.val)
  have hm : v.val ∈ f.Vi 0 := (c.mem_preimage _ v).mpr (by
    change (c.projection v).toAdd ∈ f.space 0
    rw [hv]
    exact w.property)
  exact ⟨Additive.ofMul ⟨v,hm⟩, Subtype.ext (congrArg Multiplicative.toAdd hv)⟩

theorem lineProjection_injective (hz : V ⊓ centralizer (L : Set G) = ⊥) :
    Function.Injective (lineProjection f) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have hp : c.projection (inclusion (D.centralQuotientPreimage_le _) v.toMul) = 1 :=
    congrArg Multiplicative.ofAdd (congrArg Subtype.val hv)
  have hc := (c.projection_eq_one_iff _).mp hp
  apply Additive.toMul.injective
  apply Subtype.ext
  exact mem_bot.mp (hz ▸ (show v.toMul.val ∈ V ⊓ centralizer (L : Set G) from
    ⟨D.centralQuotientPreimage_le _ v.toMul.property,hc⟩))

/-- When C_V(L)=1 the given quotient marking is an actual binary line isomorphism. -/
def lineCoordinates (hz : V ⊓ centralizer (L : Set G) = ⊥) :
    Additive (f.Vi 0) ≃ₗ[ZMod 2] f.space 0 :=
  LinearEquiv.ofBijective (lineProjection f)
    ⟨lineProjection_injective f hz, lineProjection_surjective f⟩

/-- Compatibility uses the full supplied model marking, including the SL₃ center. -/
theorem lineProjection_component (l : L) (hl : (l : G) ∈ normalizer (f.Vi 0 : Set G))
    (v : Additive (f.Vi 0)) :
    (lineProjection f (lineAction f ⟨l,hl⟩ v)).val =
      c.modelAction (c.quotientMap l) (lineProjection f v).val := by
  exact c.projection_component_conjugation l
    (inclusion (D.centralQuotientPreimage_le _) v.toMul)

/-- Field multiplication transported to the original subgroup, through its given marking. -/
def lineScalars (hz : V ⊓ centralizer (L : Set G) = ⊥) :
    F.Carrierˣ →* (Additive (f.Vi 0) ≃ₗ[ZMod 2] Additive (f.Vi 0)) where
  toFun a := ((lineCoordinates f hz).trans
    ((LinearEquiv.smulOfUnit a : f.space 0 ≃ₗ[F.Carrier] f.space 0).restrictScalars (ZMod 2))).trans
      (lineCoordinates f hz).symm
  map_one' := by ext v; simp [LinearEquiv.smulOfUnit]
  map_mul' a b := by ext v; simp [LinearEquiv.smulOfUnit, mul_smul]

theorem lineScalars_apply (hz : V ⊓ centralizer (L : Set G) = ⊥)
    (a : F.Carrierˣ) (v : Additive (f.Vi 0)) :
    lineCoordinates f hz (lineScalars f hz a v) = (a : F.Carrier) • lineCoordinates f hz v := by
  simp [lineScalars, LinearEquiv.smulOfUnit, Units.smul_def]

theorem lineScalars_isCyclic (hz : V ⊓ centralizer (L : Set G) = ⊥) :
    IsCyclic (lineScalars f hz).range :=
  isCyclic_of_surjective (lineScalars f hz).rangeRestrict (lineScalars f hz).rangeRestrict_surjective

theorem lineImage_le_scalars (hz : V ⊓ centralizer (L : Set G) = ⊥)
    {H : Subgroup G} (hHL : H ≤ L) : lineImage f H ≤ (lineScalars f hz).range := by
  rintro _ ⟨l,hl,rfl⟩
  let l' : L := ⟨l,hHL hl⟩
  let a : f.space 0 →ₗ[F.Carrier] f.space 0 :=
    ((c.modelAction (c.quotientMap l')).comp (f.space 0).subtype).codRestrict _ (by
      intro v
      exact ((c.mem_normalizer_preimage_iff _ l').mp l.property v.val).mpr v.property)
  obtain ⟨r,hr,_⟩ := a.existsUnique_eq_smul_id_of_finrank_eq_one (f.dimension 0)
  have he (v : Additive (f.Vi 0)) :
      lineCoordinates f hz (lineAction f l v) = r • lineCoordinates f hz v := by
    apply Subtype.ext
    exact (lineProjection_component f l' l.property v).trans
      (congrArg Subtype.val (LinearMap.congr_fun hr (lineCoordinates f hz v)))
  have hr0 : r ≠ 0 := by
    intro h
    obtain ⟨v,hv⟩ := ((Submodule.ne_bot_iff _).mp (f.space_ne_bot 0))
    obtain ⟨w,hw⟩ := (lineCoordinates f hz).surjective ⟨v,hv.1⟩
    have hh := he ((lineAction f l).symm w)
    rw [LinearEquiv.apply_symm_apply, h, zero_smul, hw] at hh
    exact hv.2 (congrArg Subtype.val hh)
  refine ⟨Units.mk0 r hr0, ?_⟩
  apply LinearEquiv.ext
  intro v
  apply (lineCoordinates f hz).injective
  rw [lineScalars_apply, he]
  rfl
/-- The transported full scalar group acts regularly on the nonzero original vectors. -/
theorem lineScalars_regular (hz : V ⊓ centralizer (L : Set G) = ⊥) :
    LinearGroup.IsRegularOnNonzero (lineScalars f hz).range := by
  let e := lineCoordinates f hz
  intro v w hv hw
  have hev : e v ≠ 0 := fun h => hv (e.injective (h.trans e.map_zero.symm))
  obtain ⟨r,hr⟩ := exists_smul_eq_of_finrank_eq_one (f.dimension 0) hev (e w)
  have hr0 : r ≠ 0 := by
    intro h
    rw [h,zero_smul] at hr
    exact hw (e.injective (hr.symm.trans e.map_zero.symm))
  let a := Units.mk0 r hr0
  have ha : lineScalars f hz a v = w := by
    apply e.injective
    exact (lineScalars_apply f hz a v).trans hr
  refine ⟨⟨lineScalars f hz a, MonoidHom.mem_range.mpr ⟨a,rfl⟩⟩,ha,?_⟩
  rintro ⟨b,b',rfl⟩ hb
  apply Subtype.ext
  have he : (b' : F.Carrier) = r := by
    apply (smul_left_injective F.Carrier hev)
    exact (lineScalars_apply f hz b' v).symm.trans ((congrArg e hb).trans hr.symm)
  exact congrArg (lineScalars f hz) (Units.ext he)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
