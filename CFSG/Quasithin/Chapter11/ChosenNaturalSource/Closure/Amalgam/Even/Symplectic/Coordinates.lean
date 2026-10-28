module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic.Forward
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.FullAction
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.LocalIdentification

/-!
# The literal point coordinates from the ambient radical comparison

The marked point identifies the original local residual with the conjugate
matrix point local. Its actual two-core is the explicit three-parameter
radical. Transporting the full action image through the original quotient
therefore gives the required radical matrices, and surjectivity on the
point local supplies every Levi lift in the original L₁.

This conditional adapter retains the ambient comparison explicitly. The
unconditional original radical construction is now in Radical.lean. The point,
plane and hyperplane coordinate identities are earlier flag geometry, produced
by qt-d-1222-natural-flag-cartan. The matrix equations and Levi lifts below are
constructed from the displayed comparison.
Source: Aschbacher--Smith, 11.5.7--8, printed pp.782--784.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic
open Closure.Symplectic Closure.Symplectic.Terminal LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} {E : Geometry D} (m : MarkedFlag E)

private theorem model_projection (t : Sp E.input.field.Carrier) (x : V) :
    ((Coordinates.sp4 m.action).projection (FullAction.modelHom m t x)).toAdd =
      (toLinear t) ((Coordinates.sp4 m.action).projection x).toAdd := by
  obtain ⟨l, rfl⟩ := (Coordinates.sp4 m.action).quotientMap_surjective t
  rw [show (Coordinates.sp4 m.action).quotientMap l = PointModel.quotientMap m l from rfl,
    FullAction.modelHom_quotientMap]
  exact (Coordinates.sp4 m.action).projection_component_conjugation l x

private theorem realizes_model (s r : Sp E.input.field.Carrier)
    (a : normalizer (V : Set G))
    (ha : V.normalizerMonoidHom a = FullAction.modelHom m (s⁻¹*r*s)) :
    Realizes (markedProjection E m s) a r := by
  intro x
  change (toLinear s) ((Coordinates.sp4 m.action).projection (V.normalizerMonoidHom a x)).toAdd =
    (toLinear r) ((toLinear s) ((Coordinates.sp4 m.action).projection x).toAdd)
  rw [ha, model_projection]
  have he (w : Vector E.input.field.Carrier) :
      s • ((s⁻¹*r*s) • w) = r • (s • w) := by
    simp only [mul_smul, smul_inv_smul]
  exact he _

/-- The original radical and Levi actions, from the explicit ambient image bound. -/
def pointCoordinates_of_radical_image (s : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear s⁻¹).toLinearMap)
    (hplane : ∀ x : V, (x : G) ∈ E.V₂ ↔
      (markedProjection E m s x).toAdd ∈ plane E.input.field.Carrier)
    (hthree : ∀ x : V, (x : G) ∈ E.V₃ ↔
      (markedProjection E m s x).toAdd (.inr 0) = 0)
    (hr : actionImage (V := V) E.R₁ ≤ actionImage (V := V) (E.L₁.pCoreIn 2)) :
    PointCoordinates E m := by
  have hlocal := PointModel.local_identification m s⁻¹ hp
  have hcore : PointModel.image m (E.L₁.pCoreIn 2) =
      ((pointRadical (F := E.input.field.Carrier)).map pointLocal.subtype).map
        (MulAut.conj s⁻¹).toMonoidHom := by
    rw [PointModel.image_core m E.L₁ E.L₁_le, hlocal,
      ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj s⁻¹).injective,
      PointRadicalAction.core_eq_radical E.input.field.card_eq E.input.nonbinary]
  refine ⟨s, ?_, hplane, hthree, ?_, ?_⟩
  · intro x
    rw [m.point_preimage]
    change (x : G) ∈ (Coordinates.sp4 m.action).preimage (m.flag.space 0) ↔ _
    rw [(Coordinates.sp4 m.action).mem_preimage, hp]
    change ((Coordinates.sp4 m.action).projection x).toAdd ∈
      (point E.input.field.Carrier).map (toLinear s⁻¹).toLinearMap ↔
      (toLinear s) ((Coordinates.sp4 m.action).projection x).toAdd ∈ point E.input.field.Carrier
    constructor
    · rintro ⟨y, hy, he⟩
      rw [← he]
      change s • (s⁻¹ • y) ∈ point E.input.field.Carrier
      rw [smul_inv_smul]
      exact hy
    · intro hx
      refine ⟨(toLinear s) ((Coordinates.sp4 m.action).projection x).toAdd, hx, ?_⟩
      exact inv_smul_smul s _
  · intro a
    let aN : normalizer (V : Set G) := ⟨a,radical_normalizes_seed E a.property⟩
    have ha : V.normalizerMonoidHom aN ∈ actionImage (V := V) (E.L₁.pCoreIn 2) :=
      hr (mem_map_of_mem V.normalizerMonoidHom (show aN ∈ E.R₁.subgroupOf _ from a.property))
    rw [← FullAction.image_eq m _ ((pCoreIn_le 2 E.L₁).trans E.L₁_le), hcore] at ha
    obtain ⟨t, ⟨r, ⟨q, hq, rfl⟩, rfl⟩, he⟩ := ha
    have hqeq := pointRadical_eq_element q hq
    obtain ⟨u,v,z,hqeq⟩ : ∃u v z, q.val = PlaneModel.radical u v z :=
      ⟨_,_,_,congrArg Subtype.val hqeq⟩
    refine ⟨u,v,z,realizes_model m s (PlaneModel.radical u v z) aN ?_⟩
    rw [← hqeq]
    have ht : (MulAut.conj s⁻¹).toMonoidHom (pointLocal.subtype q) = s⁻¹*q.val*s := by
      change s⁻¹*q.val*(s⁻¹)⁻¹ = _
      rw [inv_inv]
    rw [ht] at he
    exact he.symm
  · intro b
    have hb : s⁻¹ * (PlaneModel.levi b) * s ∈ PointModel.image m E.L₁ := by
      rw [hlocal]
      exact ⟨(pointLevi b).val, (pointLevi b).property, by simp⟩
    obtain ⟨l, hl, he⟩ := hb
    refine ⟨⟨l,hl⟩,realizes_model m s (PlaneModel.levi b)
      ⟨l,D.normalizes (E.L₁_le hl)⟩ ?_⟩
    rw [← he, FullAction.modelHom_quotientMap]
    rfl

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic
