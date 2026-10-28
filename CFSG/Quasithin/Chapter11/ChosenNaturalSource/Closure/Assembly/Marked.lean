module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Nonabelian.PointModels.Residual
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.RadicalGeometryTransport
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.PlaneGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.PointModel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.Orbits.Normalizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.Sp4.PlaneAction.Natural

/-!
# Original point orbits and simultaneous symplectic closure coordinates

Transitivity on the nonidentity vectors induces transitivity on each field
line under its actual stabilizer: linearity transports the span of a nonzero
vector onto the span of its image. This supplies the point-orbit premise of
11.5.8, using the literal projection and retaining its fixed-space kernel
until the preceding trivial-centralizer conclusion is applied.

Uniqueness of the invariant symplectic flag identifies all three original
preimages in one basis. Surjectivity of the two local projections then
identifies both solvable residual images under the same conjugated quotient
map. The point-normalizer decomposition supplies the parabolic image, with
its two-core removed only after applying the quotient. The existing corrected
plane-orbit theorem supplies normalizer control from the genuine unique
noncentral-component premise.

These transports are applied to both Chapter12 closure branches in
Closure/Assembly.lean. No closure abelianness or K=L₁ is assumed here.
Source: Aschbacher--Smith, 11.1.4, 11.5.2--8, printed pp.765,779--784.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} {E : Geometry D}

namespace Nonabelian.MarkedFlag
theorem point_orbit (m : Nonabelian.MarkedFlag E)
    (hc : V ⊓ centralizer (L : Set G) = ⊥)
    (hz : E.z ∈ E.V₁) (hz1 : E.z ≠ 1)
    (ht : ∀ u ∈ V, u ≠ 1 → ∀ v ∈ V, v ≠ 1 →
      ∃ l ∈ L, (MulAut.conj l) u = v) :
    ∀ u ∈ E.V₁, u ≠ 1 → ∃ l ∈ L ⊓ E.G₁, (MulAut.conj l) E.z = u := by
  intro u hu hu1
  obtain ⟨l, hl, he⟩ := ht E.z (E.V₁_le hz) hz1 u (E.V₁_le hu) hu1
  let c := m.action.coordinates
  let z : V := ⟨E.z, E.V₁_le hz⟩
  let v : V := ⟨u, E.V₁_le hu⟩
  let w := (c.projection z).toAdd
  let w' := (c.projection v).toAdd
  have hline : E.V₁ = c.preimage (m.flag.space 0) := by
    change D.centralQuotientPreimage E.point = _
    rw [m.point_eq]
    rfl
  have hw : w ∈ m.flag.space 0 := (c.mem_preimage _ z).mp (hline ▸ hz)
  have hw' : w' ∈ m.flag.space 0 := (c.mem_preimage _ v).mp (hline ▸ hu)
  have hw0 : w ≠ 0 := by
    intro h
    apply hz1
    exact congrArg Subtype.val (PointModels.projection_injective c hc
      (show c.projection z = c.projection 1 from h.trans (map_one c.projection).symm))
  have hw0' : w' ≠ 0 := by
    intro h
    apply hu1
    exact congrArg Subtype.val (PointModels.projection_injective c hc
      (show c.projection v = c.projection 1 from h.trans (map_one c.projection).symm))
  have hs := eq_span_singleton_of_mem_of_finrank_eq_one (m.flag.dimension 0) hw hw0
  have hs' := eq_span_singleton_of_mem_of_finrank_eq_one (m.flag.dimension 0) hw' hw0'
  have ha : c.modelAction (c.quotientMap ⟨l, hl⟩) w = w' := by
    rw [← c.projection_component_conjugation]
    exact congrArg (fun x : V => (c.projection x).toAdd) (Subtype.ext he)
  refine ⟨l, ⟨hl, ?_⟩, he⟩
  change l ∈ normalizer (E.V₁ : Set G)
  rw [hline]
  apply (c.mem_normalizer_preimage_iff _ ⟨l, hl⟩).mpr
  intro x
  constructor
  · intro hx
    obtain ⟨a, ha'⟩ := Submodule.mem_span_singleton.mp (hs' ▸ hx)
    rw [hs]
    apply Submodule.mem_span_singleton.mpr
    refine ⟨a, ?_⟩
    have hh : c.modelAction (c.quotientMap ⟨l, hl⟩) (a • w) =
        c.modelAction (c.quotientMap ⟨l, hl⟩) x := by rw [map_smul, ha, ha']
    have hi := congrArg (c.modelAction (c.quotientMap ⟨l, hl⟩)⁻¹) hh
    simpa only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel,
      map_one, Module.End.one_apply] using hi
  · intro hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp (hs ▸ hx)
    rw [map_smul, ha]
    exact (m.flag.space 0).smul_mem a hw'
end Nonabelian.MarkedFlag

namespace Symplectic.MarkedFlag
open Theory.SpecificGroups.SymplecticFour

theorem space_eq (m : Symplectic.MarkedFlag E) (i : Fin 3) :
    m.flag.space i = Sp4.space m.action i.succ :=
  Sp4.flag_unique m.action E.input i _ (m.flag.dimension i) (m.flag.invariant i)

theorem preimage_eq (m : Symplectic.MarkedFlag E) (i : Fin 3) :
    m.flag.Vi i = (Sp4.flag m.action E.input).Vi i := by
  change (Coordinates.sp4 m.action).preimage (m.flag.space i) = _
  rw [m.space_eq i]
  rfl

theorem local_eq (m : Symplectic.MarkedFlag E) (i : Fin 2) :
    m.flag.Li i = (Sp4.flag m.action E.input).Li i := by
  change localResidual L (m.flag.Vi i.castSucc) = _
  rw [m.preimage_eq i.castSucc]
  rfl

theorem point_coordinates (m : Symplectic.MarkedFlag E) :
    m.flag.space 0 = (point E.input.field.Carrier).map
      (toLinear (Sp4.alignment m.action)).toLinearMap := m.space_eq 0

theorem three_coordinates (m : Symplectic.MarkedFlag E) :
    m.flag.space 2 = ((form E.input.field.Carrier).orthogonal
      (point E.input.field.Carrier)).map (toLinear (Sp4.alignment m.action)).toLinearMap :=
  m.space_eq 2

theorem plane_membership (m : Symplectic.MarkedFlag E) (x : V) :
    (x : G) ∈ E.V₂ ↔
      (Symplectic.Terminal.markedProjection E m (Sp4.alignment m.action)⁻¹ x).toAdd ∈
        plane E.input.field.Carrier := by
  rw [m.plane_preimage]
  change (x : G) ∈ (Coordinates.sp4 m.action).preimage (m.flag.space 1) ↔ _
  rw [Coordinates.mem_preimage, m.space_eq]
  exact Sp4.ModelFlag.mem_movedStage _ 2 _

theorem three_membership (m : Symplectic.MarkedFlag E) (x : V) :
    (x : G) ∈ E.V₃ ↔
      (Symplectic.Terminal.markedProjection E m (Sp4.alignment m.action)⁻¹ x).toAdd (.inr 0) = 0 := by
  rw [m.threeSpace_preimage]
  change (x : G) ∈ (Coordinates.sp4 m.action).preimage (m.flag.space 2) ↔ _
  rw [Coordinates.mem_preimage, m.space_eq]
  exact (Sp4.ModelFlag.mem_movedStage _ 3 _).trans (Sp4.ModelFlag.mem_hyperplane _)

theorem local_image (m : Symplectic.MarkedFlag E) (i : Fin 2) :
    ((m.flag.Li i).subgroupOf L).map
      ((MulAut.conj (Sp4.alignment m.action)⁻¹).toMonoidHom.comp
        (Symplectic.Terminal.RadicalGeometry.componentQuotient m)) =
      Sp4.standardLocal (F := E.input.field) i := by
  rw [m.local_eq i]
  have hq (l : L) : (Coordinates.sp4 m.action).quotientMap l =
      Symplectic.Terminal.RadicalGeometry.componentQuotient m l := by rfl
  have he (l : (Sp4.flag m.action E.input).Li i) :
      (Sp4.PlaneAction.localProjection E.input m.action i l).val =
      ((MulAut.conj (Sp4.alignment m.action)⁻¹).toMonoidHom.comp
        (Symplectic.Terminal.RadicalGeometry.componentQuotient m))
          ⟨l.val,(localResidual_le _ l.property).1⟩ := by
    rw [Sp4.PlaneAction.localProjection_coe, hq]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  ext a
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hp := (Sp4.PlaneAction.localProjection E.input m.action i ⟨l,hl⟩).property
    rw [he] at hp
    exact hp
  · intro ha
    obtain ⟨l,hl⟩ := Sp4.PlaneAction.localProjection_surjective E.input m.action i ⟨a,ha⟩
    refine ⟨⟨l.val,(localResidual_le _ l.property).1⟩,l.property,?_⟩
    exact (he l).symm.trans (congrArg Subtype.val hl)

theorem point_local_image (m : Symplectic.MarkedFlag E) :
    (E.L₁.subgroupOf L).map
      ((MulAut.conj (Sp4.alignment m.action)⁻¹).toMonoidHom.comp
        (Symplectic.Terminal.RadicalGeometry.componentQuotient m)) = pointLocal := by
  change ((localResidual L E.V₁).subgroupOf L).map _ = _
  rw [m.point_preimage]
  exact m.local_image 0

theorem plane_local_image (m : Symplectic.MarkedFlag E) :
    (E.L₂.subgroupOf L).map
      ((MulAut.conj (Sp4.alignment m.action)⁻¹).toMonoidHom.comp
        (Symplectic.Terminal.RadicalGeometry.componentQuotient m)) = planeLocal := by
  change ((localResidual L E.V₂).subgroupOf L).map _ = _
  rw [m.plane_preimage]
  exact m.local_image 1

theorem normalizer_control (m : Symplectic.MarkedFlag E)
    (hu : Source.UniqueNoncentralComponent (normalizer (E.V₂ : Set G)) E.V₂ E.L₂) :
    normalizer (E.V₃ : Set G) ⊓ normalizer (E.L₁ : Set G) ≤ E.M := by
  have hp : E.V₁ = (Sp4.flag m.action E.input).Vi 0 :=
    m.point_preimage.trans (m.preimage_eq 0)
  have hv : E.V₂ = (Sp4.flag m.action E.input).Vi 1 :=
    m.plane_preimage.trans (m.preimage_eq 1)
  have ht : E.V₃ = (Sp4.flag m.action E.input).Vi 2 :=
    m.threeSpace_preimage.trans (m.preimage_eq 2)
  have hl : E.L₁ = (Sp4.flag m.action E.input).Li 0 := by
    change localResidual L E.V₁ = _
    rw [hp]
    rfl
  have hl' : E.L₂ = (Sp4.flag m.action E.input).Li 1 := by
    change localResidual L E.V₂ = _
    rw [hv]
    rfl
  rw [hv, hl'] at hu
  rw [ht, hl]
  exact (Sp4.Orbits.source_normalizerControl E.input m.action hu).2

theorem cartan_image (m : Symplectic.MarkedFlag E) (hX : E.X ≤ L)
    (hsplit : L ⊓ E.G₁ = (E.L₁ ⊔ L.pCoreIn 2) ⊔ E.X) :
    Symplectic.PointModel.image m (E.L₁ ⊔ E.X) =
      pointParabolic.map (MulAut.conj (Sp4.alignment m.action)).toMonoidHom := by
  let c := Coordinates.sp4 m.action
  have hn : Symplectic.PointModel.image m (L ⊓ E.G₁) =
      c.modelStabilizer (m.flag.space 0) := by
    ext a
    constructor
    · rintro ⟨l, hl, rfl⟩
      apply (c.mem_normalizer_preimage_iff _ l).mp
      have hh : (l : G) ∈ normalizer (E.V₁ : Set G) := hl.2
      rw [m.point_preimage] at hh
      exact hh
    · intro ha
      obtain ⟨l,hl⟩ := c.normalizerProjection_surjective (m.flag.space 0) ⟨a,ha⟩
      refine ⟨⟨l,l.property.1⟩,⟨l.property.1,?_⟩,congrArg Subtype.val hl⟩
      change (l : G) ∈ normalizer (E.V₁ : Set G)
      rw [m.point_preimage]
      exact l.property.2
  have hcore : Symplectic.PointModel.image m (L.pCoreIn 2) = ⊥ := by
    change ((L.pCoreIn 2).subgroupOf L).map (Symplectic.PointModel.quotientMap m) = ⊥
    rw [Subgroup.map_eq_bot_iff, Symplectic.PointModel.quotientMap_ker]
    rintro l ⟨k,hk,hkl⟩
    exact (show k = l from Subtype.ext hkl) ▸ hk
  have hsup (A B : Subgroup G) (hA : A ≤ L) (hB : B ≤ L) :
      Symplectic.PointModel.image m (A ⊔ B) =
        Symplectic.PointModel.image m A ⊔ Symplectic.PointModel.image m B := by
    unfold Symplectic.PointModel.image
    rw [subgroupOf_sup hA hB, Subgroup.map_sup]
  rw [hsplit, hsup _ _ (sup_le E.L₁_le (pCoreIn_le 2 L)) hX,
    hsup _ _ E.L₁_le (pCoreIn_le 2 L), hcore, sup_bot_eq,
    ← hsup _ _ E.L₁_le hX] at hn
  rw [hn, m.space_eq]
  exact Sp4.modelStabilizer_space m.action 0

end Symplectic.MarkedFlag
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure
