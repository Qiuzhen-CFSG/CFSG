module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic.Action
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic.NormalizerCore
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic.Coordinates

/-!
# The original Sp₄ radical action

The actual seed normalizer acts on the marked quotient through the natural
normalizer. Conjugating by the preceding flag basis identifies the image of
L₁ with the literal matrix point local. Relative normality of L₁ in L₁T and
the normalizer core calculation then put the image of R₁ = O₂(L₁T) inside
its three-parameter radical. The scalar kernel is retained throughout.

Evaluation on the original quotient constructs the radical matrices and
Levi lifts required by PointCoordinates. No radical image, alignment, or
critical-pair conclusion is assumed. Only the compatible point, plane and
hyperplane coordinates remain explicit; their earlier source producer is
qt-d-1222-natural-flag-cartan. The applications to the quadratic alternatives
and odd distance are in the Symplectic umbrella.
Source: Aschbacher--Smith, §11.1 and 11.5.8, printed pp.760–761 and 784.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Representation
open Theory.SpecificGroups.SymplecticFour
open SymplecticConjugatePair.Ambient SymplecticConjugatePair.Ambient.Normalizer
open SymplecticNaturalNormalizer
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic
open Closure.Symplectic LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} {E : Geometry D} (m : MarkedFlag E)

theorem field_large : 2 < Nat.card E.input.field.Carrier := by
  rw [E.input.field.card_eq]
  simpa using (Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) E.input.nonbinary)

private theorem normalizerAction_component (l : L) (w : (Coordinates.sp4 m.action).Space) :
    normalizerAction m.action (inclusion D.normalizes l) w =
      symplecticNatural 2 ((Coordinates.sp4 m.action).quotientMap l) w := by
  let c := Coordinates.sp4 m.action
  obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd w)
  have he : (c.projection v).toAdd = w := congrArg Multiplicative.toAdd hv
  rw [← he]
  change c.conjugationAction _ _ _ _ = c.modelAction _ _
  rw [c.conjugationAction_projection, ← c.projection_component_conjugation]
  rfl

private theorem operator_mem (a : normalizer (V : Set G)) :
    linearAction (normalizerAction m.action) a ∈ naturalNormalizer := by
  let H := normalizer (V : Set G)
  let J := L.subgroupOf H
  let e : J ≃* L := subgroupOfEquivOfLe D.normalizes
  let q := (Coordinates.sp4 m.action).quotientMap.comp e.toMonoidHom
  let : J.Normal := normal_subgroupOf_of_le_normalizer
    (WeakClosure.seed_normalizer_le D E.input)
  apply NormalizerCore.operator_mem_of_quotient (field_large (E := E)) J q
    ((Coordinates.sp4 m.action).quotientMap_surjective.comp e.surjective)
    (normalizerAction m.action)
  intro j w
  exact normalizerAction_component m (e j) w

/-- The actual seed normalizer, retaining the scalar kernel. -/
def naturalOperator : normalizer (V : Set G) →* naturalNormalizer (F := E.input.field.Carrier) :=
  (linearAction (normalizerAction m.action)).codRestrict naturalNormalizer (operator_mem m)

theorem naturalOperator_component (l : L) :
    naturalOperator m (inclusion D.normalizes l) =
      naturalElement (field_large (E := E)) ((Coordinates.sp4 m.action).quotientMap l) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  exact normalizerAction_component m l

/-- Conjugate the same operator by the supplied symplectic basis. -/
def alignedOperator (s : Sp E.input.field.Carrier) :
    normalizer (V : Set G) →* naturalNormalizer (F := E.input.field.Carrier) :=
  (MulAut.conj (naturalElement (field_large (E := E)) s)).toMonoidHom.comp (naturalOperator m)

theorem alignedOperator_component (s : Sp E.input.field.Carrier) (l : L) :
    alignedOperator m s (inclusion D.normalizes l) =
      naturalElement (field_large (E := E))
        (s * (show Sp E.input.field.Carrier from (Coordinates.sp4 m.action).quotientMap l) * s⁻¹) := by
  change (naturalElement _ s) * naturalOperator m (inclusion D.normalizes l) *
    (naturalElement _ s)⁻¹ = _
  rw [naturalOperator_component,map_mul,map_mul,map_inv]

private theorem join_normalizes_seed : E.L₁ ⊔ (T : Subgroup G) ≤ normalizer (V : Set G) :=
  sup_le (E.L₁_le.trans D.normalizes) E.input.sylow_normalizes

include m in
private theorem sylow_normalizes_local :
    (T : Subgroup G) ≤ normalizer (E.L₁ : Set G) :=
  sylow_normalizes_localResidual D E.V₁ (MarkedFlag.sylow_le_point_normalizer m)

private theorem local_operator_image (s : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear s⁻¹).toLinearMap) :
    (E.L₁.subgroupOf (E.L₁ ⊔ (T : Subgroup G))).map
        ((alignedOperator m s).comp (inclusion (join_normalizes_seed (E := E)))) =
      pointLocal.map (naturalElement (field_large (E := E))) := by
  let c := Coordinates.sp4 m.action
  have hlocal := PointModel.local_identification m s⁻¹ hp
  apply le_antisymm
  · rintro _ ⟨l,hl,rfl⟩
    let l' : L := ⟨l,E.L₁_le hl⟩
    have hq : c.quotientMap l' ∈ PointModel.image m E.L₁ := ⟨l',hl,rfl⟩
    rw [hlocal] at hq
    obtain ⟨q,hq,he⟩ := hq
    change alignedOperator m s (inclusion D.normalizes l') ∈ _
    rw [alignedOperator_component, ← he]
    have hcancel : s * (MulAut.conj s⁻¹).toMonoidHom q * s⁻¹ = q := by
      simp [mul_assoc]
    rw [hcancel]
    exact mem_map_of_mem _ hq
  · rintro _ ⟨q,hq,rfl⟩
    have hq' : s⁻¹ * q * s ∈ PointModel.image m E.L₁ := by
      rw [hlocal]
      exact ⟨q,hq,by simp⟩
    obtain ⟨l,hl,he⟩ := hq'
    refine ⟨⟨l,(le_sup_left : E.L₁ ≤ E.L₁ ⊔ (T : Subgroup G)) hl⟩,hl,?_⟩
    change alignedOperator m s (inclusion D.normalizes l) = _
    rw [alignedOperator_component]
    change naturalElement _ (s * PointModel.quotientMap m l * s⁻¹) = _
    rw [he]
    simp [mul_assoc]

/-- The literal original radical acts in the native point core. -/
theorem radical_operator_mem (s : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear s⁻¹).toLinearMap)
    (r : E.R₁) :
    alignedOperator m s ⟨r,Terminal.radical_normalizes_seed E r.property⟩ ∈
      (pointLocal.map (naturalElement (field_large (E := E)))).pCoreIn 2 := by
  let J := E.L₁ ⊔ (T : Subgroup G)
  let A := E.L₁.subgroupOf J
  let B := (T : Subgroup G).subgroupOf J
  let ρ := (alignedOperator m s).comp (inclusion (join_normalizes_seed (E := E)))
  let K := pointLocal.map (naturalElement (field_large (E := E)))
  have hA : A.map ρ = K := local_operator_image m s hp
  have hnA : A.Normal := normal_subgroupOf_of_le_normalizer
    (sup_le E.L₁.le_normalizer (sylow_normalizes_local m))
  let := hnA
  have hnB : B.map ρ ≤ normalizer (K : Set _) := by
    rw [← hA]
    rintro _ ⟨b,hb,rfl⟩
    exact A.le_normalizer_map ρ (mem_map_of_mem ρ (A.normalizer_eq_top ▸ mem_top b))
  have hjoin : A ⊔ B = ⊤ := by
    rw [← subgroupOf_sup (show E.L₁ ≤ J from le_sup_left)
      (show (T : Subgroup G) ≤ J from le_sup_right)]
    exact subgroupOf_self J
  have hrange : ρ.range = K ⊔ B.map ρ := by
    rw [← hA, ← Subgroup.map_sup, hjoin, ← MonoidHom.range_eq_map]
  have hcore : (pCore 2 J).map ρ ≤ K.pCoreIn 2 := by
    have hC : (pCore 2 J).map ρ.rangeRestrict ≤ pCore 2 ρ.range :=
      le_sSup ⟨(inferInstance : (pCore 2 J).Normal).map
        ρ.rangeRestrict ρ.rangeRestrict_surjective,
        pCore_isPGroup.map ρ.rangeRestrict⟩
    have hC' := map_mono (f := ρ.range.subtype) hC
    rw [Subgroup.map_map] at hC'
    change (pCore 2 J).map ρ ≤ ρ.range.pCoreIn 2 at hC'
    rw [hrange] at hC'
    have he := NormalizerCore.pointLocal_join_core_eq (field_large (E := E))
      E.input.field.card_eq E.input.nonbinary (B.map ρ) hnB
    exact hC'.trans_eq he
  obtain ⟨j,hj,he⟩ := r.property
  have hmem := hcore (mem_map_of_mem ρ hj)
  convert hmem using 1
  apply congrArg (alignedOperator m s)
  exact Subtype.ext he.symm

open Closure.Symplectic.Terminal

private theorem realizes_of_operator (s q : Sp E.input.field.Carrier)
    (a : normalizer (V : Set G))
    (he : alignedOperator m s a = naturalElement (field_large (E := E)) q) :
    Realizes (markedProjection E m s) a q := by
  intro x
  have h := congrArg (fun y : naturalNormalizer (F := E.input.field.Carrier) =>
    y.val ((markedProjection E m s x).toAdd)) he
  change (toLinear s) (normalizerAction m.action a
    ((toLinear s⁻¹) ((toLinear s) ((Coordinates.sp4 m.action).projection x).toAdd))) =
      (toLinear q) ((markedProjection E m s x).toAdd) at h
  have hinv : (toLinear s⁻¹) ((toLinear s)
      ((Coordinates.sp4 m.action).projection x).toAdd) =
      ((Coordinates.sp4 m.action).projection x).toAdd := inv_smul_smul s _
  rw [hinv] at h
  change (toLinear s) ((Coordinates.sp4 m.action).conjugationAction _ _ a
    ((Coordinates.sp4 m.action).projection x).toAdd) = _ at h
  rw [(Coordinates.sp4 m.action).conjugationAction_projection] at h
  exact h

/-- The radical matrices follow from the original normal two-core, with no
radical-image or extension-data hypothesis. -/
theorem radical_realizes (s : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear s⁻¹).toLinearMap)
    (r : E.R₁) : ∃ u v z : E.input.field.Carrier,
      Realizes (markedProjection E m s)
        ⟨r,radical_normalizes_seed E r.property⟩ (PlaneModel.radical u v z) := by
  have hr := radical_operator_mem m s hp r
  rw [← map_pCoreIn_of_injective 2 pointLocal
    (naturalElement (field_large (E := E)))
    (NormalizerCore.naturalElement_injective (field_large (E := E))),
    PointRadicalAction.core_eq_radical E.input.field.card_eq E.input.nonbinary] at hr
  obtain ⟨q,⟨a,ha,rfl⟩,he⟩ := hr
  have haeq := pointRadical_eq_element a ha
  obtain ⟨u,v,z,haeq⟩ : ∃u v z, a.val = PlaneModel.radical u v z :=
    ⟨_,_,_,congrArg Subtype.val haeq⟩
  refine ⟨u,v,z,?_⟩
  rw [← haeq]
  exact realizes_of_operator m s a.val _ he.symm

/-- The exact source flag coordinates now construct the original point-radical
and Levi actions. These coordinate identities are preceding flag geometry. -/
def pointCoordinates (s : Sp E.input.field.Carrier)
    (hp : m.flag.space 0 = (point E.input.field.Carrier).map (toLinear s⁻¹).toLinearMap)
    (hplane : ∀ x : V, (x : G) ∈ E.V₂ ↔
      (markedProjection E m s x).toAdd ∈ plane E.input.field.Carrier)
    (hthree : ∀ x : V, (x : G) ∈ E.V₃ ↔
      (markedProjection E m s x).toAdd (.inr 0) = 0) : PointCoordinates E m := by
  refine ⟨s,?_,hplane,hthree,radical_realizes m s hp,?_⟩
  · intro x
    rw [m.point_preimage]
    change (x : G) ∈ (Coordinates.sp4 m.action).preimage (m.flag.space 0) ↔ _
    rw [(Coordinates.sp4 m.action).mem_preimage,hp]
    change ((Coordinates.sp4 m.action).projection x).toAdd ∈
      (point E.input.field.Carrier).map (toLinear s⁻¹).toLinearMap ↔
      (toLinear s) ((Coordinates.sp4 m.action).projection x).toAdd ∈ point E.input.field.Carrier
    constructor
    · rintro ⟨y,hy,he⟩
      rw [← he]
      change s • (s⁻¹ • y) ∈ point E.input.field.Carrier
      rw [smul_inv_smul]
      exact hy
    · intro hx
      refine ⟨(toLinear s) ((Coordinates.sp4 m.action).projection x).toAdd,hx,?_⟩
      exact inv_smul_smul s _
  · intro b
    have hlocal := PointModel.local_identification m s⁻¹ hp
    have hb : s⁻¹ * PlaneModel.levi b * s ∈ PointModel.image m E.L₁ := by
      rw [hlocal]
      exact ⟨(pointLevi b).val,(pointLevi b).property,by simp⟩
    obtain ⟨l,hl,he⟩ := hb
    refine ⟨⟨l,hl⟩,realizes_of_operator m s (PlaneModel.levi b) _ ?_⟩
    change alignedOperator m s (inclusion D.normalizes l) = _
    rw [alignedOperator_component]
    change naturalElement _ (s * PointModel.quotientMap m l * s⁻¹) = _
    rw [he]
    simp [mul_assoc]

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic
