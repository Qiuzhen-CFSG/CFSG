module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame.Alignment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame.Lift
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame.Weyl
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Geometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Torus

/-!
# Alignment of the original Cartan and point

The actual source Cartan image is Hall in the marked inner Sylow normalizer.
Full SL₃ Hall alignment and Sylow flag uniqueness identify the given point.
Exact normalizer lifting then produces the two Weyl matrices in N_L(X),
using the original quotient map and preserving right conjugation.
Source: Aschbacher–Smith 11.5.7, printed p.781.
-/

open Subgroup Theory.GroupTheory Representation Matrix
open scoped IsMulCommutative MatrixGroups
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.SpecialLinearGroup.FrameGeometry
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)
    (m : ActionEquiv D.centralQuotientAction (linearNatural E.input.field 3))

/-- The actual Cartan image is Hall in the actual full SL₃ Sylow normalizer. -/
theorem cartan_image_hall (hX : IsCartan T L E.X) :
    let c := Coordinates.sl3 m
    let C := (E.X.subgroupOf L).map c.quotientMap
    C ≤ normalizer (c.modelSylow : Set c.ModelGroup) ∧
      IsHallSubgroup OddHall.oddPrimes
        (C.subgroupOf (normalizer (c.modelSylow : Set c.ModelGroup))) := by
  let c := Coordinates.sl3 m
  let N := normalizer (c.modelSylow : Set c.ModelGroup)
  let Y := (E.X.subgroupOf (cartanNormalizer T L)).map c.cartanProjection
  have hY : IsHallSubgroup OddHall.oddPrimes Y := by
    refine ⟨fun p hp => hX.2.p_in_pi_of_p_dvd_card p
      (hp.trans ((E.X.subgroupOf (cartanNormalizer T L)).card_map_dvd c.cartanProjection)), ?_⟩
    intro p hp
    exact hX.2.p_in_pi_of_p_dvd_index p
      (hp.trans (index_map_dvd _ c.cartanProjection_surjective))
  have he : Y.map N.subtype = (E.X.subgroupOf L).map c.quotientMap := by
    ext z
    constructor
    · rintro ⟨y, ⟨x,hx,rfl⟩, rfl⟩
      exact ⟨⟨x,x.property.1⟩,hx,(c.cartanProjection_coe x).symm⟩
    · rintro ⟨x,hx,rfl⟩
      let u : cartanNormalizer T L := ⟨x, hX.1 hx⟩
      exact ⟨c.cartanProjection u,⟨u,hx,rfl⟩,c.cartanProjection_coe u⟩
  change (E.X.subgroupOf L).map c.quotientMap ≤ N ∧ _
  rw [← he]
  refine ⟨map_subtype_le _, ?_⟩
  change IsHallSubgroup OddHall.oddPrimes ((Y.map N.subtype).comap N.subtype)
  rw [comap_map_eq_self_of_injective N.subtype_injective]
  exact hY

/-- The given field line is the first member of the simultaneously aligned flag. -/
theorem point_eq_aligned_line
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hdim : Module.finrank E.input.field.Carrier P = 1)
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace P)
    (hT : (T : Subgroup G) ≤ E.G₁)
    (g : SL(3,E.input.field.Carrier))
    (hg : (unipotentSL E.input.field.Carrier).map (MulAut.conj g).toMonoidHom =
      (Coordinates.sl3 m).modelSylow.toSubgroup) :
    P = (coordinateLine 0).map (specialLinearNatural 3 g) := by
  have hpre : E.V₁ = (Coordinates.sl3 m).preimage P :=
    congrArg D.centralQuotientPreimage hpoint
  have hu : ∀ p ∈ (Coordinates.sl3 m).modelSylow.toSubgroup,
      ∀ v ∈ P, specialLinearNatural 3 p v ∈ P := by
    intro p hp v hv
    obtain ⟨l,hl,rfl⟩ := hp
    have hlT : (l : G) ∈ T := by
      change l ∈ (Coordinates.sl3 m).innerSylow.toSubgroup at hl
      rw [(Coordinates.sl3 m).innerSylow_coe] at hl
      exact hl
    have hlN : (l : G) ∈ normalizer ((Coordinates.sl3 m).preimage P : Set G) := by
      rw [← hpre]
      exact hT hlT
    exact ((Coordinates.sl3 m).mem_normalizer_preimage_iff P l).mp hlN v |>.mpr hv
  have hp := LocalGeometry.SL3.Model.flagFor_unique g _ hg 0 P hdim hu
  simpa only [LocalGeometry.SL3.Model.flagFor, LocalGeometry.SL3.Model.flag,
    Matrix.cons_val_zero, coordinateLine_eq_model_point] using hp

/-- Weyl lifts in the original Cartan normalizer with exactly their prescribed matrices. -/
theorem exists_aligned_lifts
    (P : Submodule E.input.field.Carrier (Fin 3 → E.input.field.Carrier))
    (hdim : Module.finrank E.input.field.Carrier P = 1)
    (hpoint : E.point = (Coordinates.sl3 m).binarySubspace P)
    (hT : (T : Subgroup G) ≤ E.G₁) (hX : IsCartan T L E.X) :
    ∃ (g : SL(3,E.input.field.Carrier)) (x y : L),
      (x : G) ∈ normalizer (E.X : Set G) ∧
      (y : G) ∈ normalizer (E.X : Set G) ∧
      (Coordinates.sl3 m).quotientMap x⁻¹ = g * cycleSL * g⁻¹ ∧
      (Coordinates.sl3 m).quotientMap y⁻¹ = g * reversalSL E.input.field.Carrier * g⁻¹ ∧
      P = (coordinateLine 0).map (specialLinearNatural 3 g) := by
  let c := Coordinates.sl3 m
  let C : Subgroup SL(3,E.input.field.Carrier) := (E.X.subgroupOf L).map c.quotientMap
  obtain ⟨hCN,hHall⟩ := cartan_image_hall E m hX
  obtain ⟨g,hgS,hgC⟩ := exists_sylow_cartan_alignment E.input.field.degree_pos
    E.input.field.card_eq c.modelSylow C hCN hHall
  have hsol : Group.IsSolvable C := by
    let U := (torusSL E.input.field.Carrier).range
    let : Group.IsSolvable U :=
      Group.isSolvable_of_surjective (torusSL E.input.field.Carrier).rangeRestrict_surjective
    let e := (U.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr hgC)
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hk : IsPGroup 2 c.quotientMap.ker := by
    have he : c.quotientMap.ker = pCore 2 L := by
      ext l
      change m.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ l ∈ pCore 2 L
      rw [← m.groupEquiv.map_one, m.groupEquiv.injective.eq_iff]
      exact QuotientGroup.eq_one_iff l
    rw [he]
    exact pCore_isPGroup
  have ho : Odd (Nat.card (E.X.subgroupOf L)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (hX.1.trans inf_le_left)).toEquiv]
    exact hX.odd
  have hw (w : SL(3,E.input.field.Carrier))
      (hw : w ∈ normalizer ((torusSL E.input.field.Carrier).range : Set _)) :
      g * w * g⁻¹ ∈ normalizer (C : Set _) := by
    rw [← hgC, ← Subgroup.map_equiv_normalizer_eq]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom hw
  obtain ⟨a,haN,ha⟩ := exists_normalizer_lift c.quotientMap c.quotientMap_surjective
    (E.X.subgroupOf L) ho hk hsol (hw cycleSL cycle_normalizes_torus)
  obtain ⟨b,hbN,hb⟩ := exists_normalizer_lift c.quotientMap c.quotientMap_surjective
    (E.X.subgroupOf L) ho hk hsol (hw _ reversal_normalizes_torus)
  have hn (a : L) (haN : a ∈ normalizer (E.X.subgroupOf L : Set L)) :
      (a : G)⁻¹ ∈ normalizer (E.X : Set G) := by
    apply (normalizer (E.X : Set G)).inv_mem
    have he := subgroupOf_normalizer_eq (hX.1.trans inf_le_left)
    rw [← he] at haN
    exact haN
  refine ⟨g,a⁻¹,b⁻¹,hn a haN,hn b hbN,?_,?_,
    point_eq_aligned_line E m P hdim hpoint hT g hgS⟩
  · change c.quotientMap (a⁻¹)⁻¹ = _
    rw [inv_inv]
    exact ha
  · change c.quotientMap (b⁻¹)⁻¹ = _
    rw [inv_inv]
    exact hb
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Generation.Frame
