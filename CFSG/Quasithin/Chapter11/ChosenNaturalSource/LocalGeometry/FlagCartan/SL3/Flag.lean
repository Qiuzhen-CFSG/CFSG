module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Normalization

/-!
# The original T-invariant SL₃ flag

Map the actual Sylow intersection T intersect L through the supplied quotient
marking and align it with the upper unitriangular group. Intrinsic fixed and
second fixed spaces prove invariance under ambient T-conjugation. Root
calculations give uniqueness already under T intersect L, which discharges
the independent Cartan normalizer theorem without a field-linearity premise.

Source: Aschbacher--Smith, opening of §11.1, printed pp.760--761.
-/

open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open Matrix.PSL3.LinearThree
open scoped MatrixGroups
@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

/-- The supplied full SL₃ action marking, with its original central quotient. -/
abbrev coordinates : Coordinates D S.field := .sl3 m

/-- The marked image of the literal intersection T intersect L. -/
def innerSylow : Sylow 2 SL(3,S.field.Carrier) :=
  (NormalSylowQuotientAction.intersection_sylow T L D.sylow_normalizes_component).choose.mapSurjective
    (coordinates D S m).quotientMap_surjective

theorem innerSylow_eq : (innerSylow D S m : Subgroup SL(3,S.field.Carrier)) =
    ((T : Subgroup G).subgroupOf L).map (coordinates D S m).quotientMap := by
  change (NormalSylowQuotientAction.intersection_sylow T L D.sylow_normalizes_component).choose.toSubgroup.map _ = _
  rw [(NormalSylowQuotientAction.intersection_sylow T L D.sylow_normalizes_component).choose_spec]
  rfl

/-- One common change of basis for both members of the marked Sylow flag. -/
def alignment : SL(3,S.field.Carrier) :=
  (Matrix.PSL3.CartanActions.BorelQuotient.sylowSL_normalizer_conjugate S.field.Carrier
    S.field.degree_pos S.field.card_eq (innerSylow D S m)).choose

theorem alignment_sylow :
    (unipotentSL S.field.Carrier).map (MulAut.conj (alignment D S m)).toMonoidHom =
      (innerSylow D S m : Subgroup SL(3,S.field.Carrier)) :=
  (Matrix.PSL3.CartanActions.BorelQuotient.sylowSL_normalizer_conjugate S.field.Carrier
    S.field.degree_pos S.field.card_eq (innerSylow D S m)).choose_spec.1

private theorem action_compatibility (t : T) (l : L) (v : (coordinates D S m).Space) :
    (coordinates D S m).sylowAction S t
      ((coordinates D S m).modelAction ((coordinates D S m).quotientMap l) v) =
    (coordinates D S m).modelAction ((coordinates D S m).quotientMap
      (L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t) l))
      ((coordinates D S m).sylowAction S t v) := by
  let c := coordinates D S m
  obtain ⟨w,hw⟩ := c.projection_surjective (Multiplicative.ofAdd v)
  have hv : (c.projection w).toAdd = v := congrArg Multiplicative.toAdd hw
  change c.conjugationAction D.sylow_normalizes_component S.sylow_normalizes t
    (c.modelAction (c.quotientMap l) v) =
      c.modelAction (c.quotientMap (L.normalizerMonoidHom
        (inclusion D.sylow_normalizes_component t) l))
        (c.conjugationAction D.sylow_normalizes_component S.sylow_normalizes t v)
  rw [← hv, ← c.projection_component_conjugation,
    c.conjugationAction_projection D.sylow_normalizes_component S.sylow_normalizes,
    c.conjugationAction_projection D.sylow_normalizes_component S.sylow_normalizes,
    ← c.projection_component_conjugation]
  congr 2
  apply Subtype.ext
  change (t : G) * ((l : G) * (w : G) * (l : G)⁻¹) * (t : G)⁻¹ =
    ((t : G) * (l : G) * (t : G)⁻¹) * ((t : G) * (w : G) * (t : G)⁻¹) *
      ((t : G) * (l : G) * (t : G)⁻¹)⁻¹
  group

private theorem sylow_moves_inner (t : T) (p : SL(3,S.field.Carrier))
    (hp : p ∈ (innerSylow D S m : Subgroup _)) :
    ∃ q ∈ (innerSylow D S m : Subgroup _), ∀ v,
      specialLinearNatural 3 p ((coordinates D S m).sylowAction S t v) =
        (coordinates D S m).sylowAction S t (specialLinearNatural 3 q v) := by
  rw [innerSylow_eq] at hp
  obtain ⟨l,hl,rfl⟩ := hp
  let l' := L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t⁻¹) l
  have hl' : l' ∈ (T : Subgroup G).subgroupOf L := by
    change (t : G)⁻¹ * (l : G) * ((t : G)⁻¹)⁻¹ ∈ (T : Subgroup G)
    exact T.mul_mem (T.mul_mem (T.inv_mem t.property) hl) (T.inv_mem (T.inv_mem t.property))
  refine ⟨(coordinates D S m).quotientMap l', ?_, ?_⟩
  · rw [innerSylow_eq]
    exact mem_map_of_mem _ hl'
  · intro v
    have he : L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t) l' = l := by
      change L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t)
        (L.normalizerMonoidHom (inclusion D.sylow_normalizes_component t⁻¹) l) = l
      rw [map_inv, map_inv]
      exact MulEquiv.apply_symm_apply _ l
    have h := (action_compatibility D S m t l' v).symm
    rw [he] at h
    exact h

/-- The original T-invariant flag, in the given quotient coordinates. -/
def flag : InvariantFlag (coordinates D S m) where
  space := Model.flagFor (alignment D S m)
  dimension := Model.flagFor_dim _
  nested := Model.flagFor_mono _
  invariant i := by
    apply ((coordinates D S m).sylow_normalizes_preimage_iff S _).mpr
    intro t v hv
    exact Model.flagFor_preserved _ _ (alignment_sylow D S m)
      ((coordinates D S m).sylowAction S t).toAddMonoidHom
      (sylow_moves_inner D S m t) i v hv

/-- Each dimension is unique already under the inner Sylow intersection. -/
theorem flag_inner_unique : (flag D S m).IsInnerUnique := by
  intro i U hd hU
  apply Model.flagFor_unique _ _ (alignment_sylow D S m) i U hd
  intro p hp v hv
  rw [innerSylow_eq] at hp
  obtain ⟨l,hl,rfl⟩ := hp
  exact ((coordinates D S m).mem_normalizer_preimage_iff U l).mp
    (hU ⟨hl,l.property⟩) v |>.mpr hv

/-- In particular the flag is unique for the actual full Sylow action. -/
theorem flag_unique : (flag D S m).IsUnique :=
  fun i U hd hU => flag_inner_unique D S m i U hd (inf_le_left.trans hU)

/-- The original third preimage is V, with its given ambient inclusion. -/
theorem flag_top : (flag D S m).Vi 2 = V := InvariantFlag.sl3_top m _

/-- The independent Cartan consumer now has its inner-uniqueness premise. -/
theorem cartan_normalizes {X : Subgroup G} (hX : IsCartan T L X) (i : Fin 3) :
    X ≤ normalizer ((flag D S m).Vi i : Set G) :=
  (flag D S m).cartan_normalizes (flag_inner_unique D S m) hX i

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.SL3
