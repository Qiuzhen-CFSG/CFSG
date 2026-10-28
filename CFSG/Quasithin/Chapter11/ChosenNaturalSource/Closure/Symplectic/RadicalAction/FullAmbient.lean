module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic.Radical
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.FullAutomizer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.Branches

/-!
# The actual ambient radical action on the full chosen module

The original normalizer acts faithfully on V/C_V(L), because V=[V,L].
Thus the natural-normalizer calculation, which retains the odd scalar
kernel, lifts from the original quotient to equality of automorphisms of V.
This places the actual R₁ image in the actual local radical image without
assuming O₂(L)=V or discarding the central attachment.

For the closure consumer it suffices to bound the local R₁ hyperplane
fixer. Its actors now lie in the marked symplectic image, where the native
hyperplane calculation identifies the fixer with the long-root center.
No normal symplectic subgroup of all Aut(V), centricity, or innerness of
all ambient actors is assumed.

Source: Aschbacher--Smith 11.5.7, assertion (!), printed pp.782--783.
Final source assembly belongs to qt-d-1222-natural-closure-sp4.
-/

public noncomputable section
open Subgroup Representation
open Theory.SpecificGroups.SymplecticFour
open SymplecticNaturalNormalizer
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.FullAmbient
open LocalGeometry
open Closure.Amalgam.Even.Symplectic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} {E : Geometry D} (m : MarkedFlag E)

/-- Equality on the original central quotient detects equality of actual
ambient automorphisms, since V=[V,L]. -/
theorem full_action_eq_of_projection_eq (a b : normalizer (V : Set G))
    (h : ∀ x : V, (Coordinates.sp4 m.action).projection (V.normalizerMonoidHom a x) =
      (Coordinates.sp4 m.action).projection (V.normalizerMonoidHom b x)) :
    V.normalizerMonoidHom a = V.normalizerMonoidHom b := by
  let := D.elementary
  let c := Coordinates.sp4 m.action
  obtain ⟨ρ,hρ,he,_⟩ := WeakClosure.Parameters.FullAutomizer.exists_faithful_quotient_action
    D E.input c
  have hr : V.normalizerMonoidHom.rangeRestrict a =
      V.normalizerMonoidHom.rangeRestrict b := by
    apply hρ
    apply LinearMap.ext
    intro w
    obtain ⟨v,rfl⟩ := WeakClosure.Parameters.FullAutomizer.projectionLinear_surjective
      D E.input c w
    rw [← he, ← he]
    change (c.projection (V.normalizerMonoidHom a v.toMul)).toAdd =
      (c.projection (V.normalizerMonoidHom b v.toMul)).toAdd
    exact congrArg Multiplicative.toAdd (h v.toMul)
  exact congrArg Subtype.val hr

/-- The actual R₁-image is contained in the actual local core image. The
natural-normalizer computation retains its odd scalar kernel. -/
theorem radical_image_le (g : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap) :
    actionImage (V := V) E.R₁ ≤ actionImage (V := V) (E.L₁.pCoreIn 2) := by
  rintro a ⟨r,hr,rfl⟩
  obtain ⟨u,v,z,hn⟩ := radical_realizes m g⁻¹ (by simpa only [inv_inv] using hp) ⟨r,hr⟩
  let q := (pointRadicalElement u v z).val
  have hq : q ∈ pointLocal.pCoreIn 2 := by
    rw [PointRadicalAction.core_eq_radical E.input.field.card_eq E.input.nonbinary]
    exact mem_map_of_mem pointLocal.subtype (pointRadicalElement_mem u v z)
  have hlocal := PointModel.local_identification m g hp
  have him : PointModel.image m (E.L₁.pCoreIn 2) =
      (pointLocal.pCoreIn 2).map (MulAut.conj g).toMonoidHom := by
    rw [PointModel.image_core m E.L₁ E.L₁_le,hlocal,
      ← map_pCoreIn_of_injective 2 _ _ (MulAut.conj g).injective]
  have hq' : g * q * g⁻¹ ∈ PointModel.image m (E.L₁.pCoreIn 2) := by
    rw [him]
    exact mem_map_of_mem _ hq
  obtain ⟨l,hl,hle⟩ := hq'
  have heq : V.normalizerMonoidHom r = V.normalizerMonoidHom (inclusion D.normalizes l) := by
    apply full_action_eq_of_projection_eq m
    intro x
    apply Multiplicative.toAdd.injective
    apply (toLinear g⁻¹).injective
    have hx := hn x
    change (toLinear g⁻¹) ((Coordinates.sp4 m.action).projection (V.normalizerMonoidHom r x)).toAdd =
      (toLinear q) ((toLinear g⁻¹) ((Coordinates.sp4 m.action).projection x).toAdd) at hx
    rw [hx]
    have hlx := (Coordinates.sp4 m.action).projection_component_conjugation l x
    change ((Coordinates.sp4 m.action).projection (V.normalizerMonoidHom
      (inclusion D.normalizes l) x)).toAdd = (toLinear (PointModel.quotientMap m l))
        ((Coordinates.sp4 m.action).projection x).toAdd at hlx
    rw [hlx,hle]
    have hlin : toLinear g⁻¹ * toLinear (g * q * g⁻¹) = toLinear q * toLinear g⁻¹ := by
      rw [← map_mul, ← map_mul]
      congr 1
      simp only [mul_assoc,inv_mul_cancel_left]
    exact (congrArg (fun f : Vector E.input.field.Carrier ≃ₗ[E.input.field.Carrier]
      Vector E.input.field.Carrier => f ((Coordinates.sp4 m.action).projection x).toAdd) hlin).symm
  rw [heq]
  exact mem_map_of_mem V.normalizerMonoidHom
    (show inclusion D.normalizes l ∈ (E.L₁.pCoreIn 2).subgroupOf (normalizer (V : Set G)) from hl)

/-- Only the local core image is needed in the closure argument. Its full
three-space fixer is the local center, without any claim that all ambient
actors are inner. -/
theorem local_fixer_bound (g : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear g).toLinearMap)
    (hthree : m.flag.space 2 =
      ((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap) :
    actionImage (V := V) E.R₁ ⊓
      fixingSubgroup (MulAut V) (E.V₃.subgroupOf V : Set V) ≤
        (center (actionImage (V := V) E.L₁)).map (actionImage (V := V) E.L₁).subtype := by
  intro a ha
  have ha' := radical_image_le m g hp ha.1
  rw [← FullAction.image_eq m _ ((pCoreIn_le 2 E.L₁).trans E.L₁_le)] at ha'
  obtain ⟨q,hq,rfl⟩ := ha'
  obtain ⟨l,hl,rfl⟩ := hq
  have hfix := ha.2
  rw [FullAction.modelHom_quotientMap] at hfix
  have hqfix : PointModel.quotientMap m l ∈ fixingSubgroup (Sp E.input.field.Carrier)
      (((form E.input.field.Carrier).orthogonal (point E.input.field.Carrier)).map
        (toLinear g).toLinearMap : Set (Vector E.input.field.Carrier)) := by
    apply (mem_fixingSubgroup_iff _).mpr
    intro w hw
    let c := Coordinates.sp4 m.action
    obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd w)
    have hv3 : (v : G) ∈ E.V₃ := by
      rw [m.threeSpace_preimage]
      apply (c.mem_preimage (m.flag.space 2) v).mpr
      change (c.projection v).toAdd ∈ m.flag.space 2
      rw [hv,hthree]
      exact hw
    have he : V.normalizerMonoidHom (inclusion D.normalizes l) v = v :=
      (mem_fixingSubgroup_iff _).mp hfix v hv3
    have hh := c.projection_component_conjugation l v
    rw [he,hv] at hh
    exact hh.symm
  rw [PointModel.hyperplane_fixer m g (PointModel.local_identification m g hp)] at hqfix
  rw [← FullAction.center_image m]
  exact mem_map_of_mem _ hqfix

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.FullAmbient
