module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.RootCoordinates
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.NonFrattini
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.XDecomposition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.XMovement

/-!
# The whole central-omega decomposition at the original field degree

In the failed whole-core branch, both critical indices equal the original
field order. The marked critical root bounds movement of the entire X-layer
by that order. Four root conjugates generate the component, and their
fixed-codimension budget is attained by the natural moving cover. Thus
X = U C_X(Ltilde), retaining the complete fixed factor.

The coordinates here extend the actual replacement quotient to the whole
central omega subgroup. All cover and root premises are constructed from
the original input and the non-Frattini assumption. No field-four or
center-freeness hypothesis is added.

Source: MS93 (3.3)(ii)(2), printed p.867, applied in (3.6), pp.870--871.
The secondary-orbit contradiction needed to remove the non-Frattini case
remains separate.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

set_option maxHeartbeats 400000 in
/-- Literal coordinates on the entire X-layer extend any marking of the
canonical natural cover, with the same quotient and conjugation action. -/
theorem replacement_fullX_coordinates_at_vertex
    {a : Vertex d.radical} (ha : color d.radical a = false) :
    let s := replacementMovedSection h d
    ∀ (E : BinaryField)
      (e : ActionEquiv (s.action.comp (replacementComponent d).subtype)
          (binaryNatural (K := E.Carrier))),
      ∃ j : Multiplicative (Additive (omegaCenterIn (pCore 2 d.overgroup))) →* FreeAmalgam d.radical,
        Function.Injective j ∧ j.range = X d.radical a ∧
        (j.comp s.space.toSubmodule.subtype.toAddMonoidHom.toMultiplicative).range = U d.radical a ∧
      ∃ κ : stabilizer d.radical a →* (d.overgroup ⧸ pCore 2 d.overgroup), Function.Surjective κ ∧
        κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        κ.ker.map (stabilizer d.radical a).subtype = C d.radical a ∧
        ((Ltilde d.radical a).subgroupOf (stabilizer d.radical a)).map κ = replacementComponent d ∧
        (∀ (g : stabilizer d.radical a) (v : Additive (omegaCenterIn (pCore 2 d.overgroup))),
          j (Multiplicative.ofAdd (replacementRepresentation h d (κ g) v)) =
            (g : FreeAmalgam d.radical) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam d.radical)⁻¹) ∧
      ∃ f : Ltilde d.radical a →* L (K := E.Carrier), Function.Surjective f ∧
        (∀ (g : Ltilde d.radical a) (v : Additive (omegaCenterIn (pCore 2 d.overgroup))),
          j (Multiplicative.ofAdd
            (replacementRepresentation h d ((replacementComponent d).subtype (e.groupEquiv.symm (f g))) v)) =
            (g : FreeAmalgam d.radical) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam d.radical)⁻¹) := by
  dsimp only
  let : (replacementComponent d).Normal := replacementComponent_normal h d
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let hq := QuotientGroup.mk'_surjective (pCore 2 d.overgroup)
  let : ((K.subgroupOf d.overgroup).map q).Normal := replacementComponent_normal h d
  let hk := (QuotientGroup.ker_mk' _).trans (replacement_centralOmega_centralizer h d).symm
  let ρ := NormalElementaryQuotient.representation (omegaCenterIn (pCore 2 d.overgroup)) q hq hk
  let s := replacementMovedSection h d
  intro E e
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := vertex_coordinates_with_kernel d.radical
    (replacement_isPGroup h d) (replacement_core_le h d) ha
  rw [replacement_residual h d] at hiL
  let j₀ : Multiplicative (Additive (omegaCenterIn (pCore 2 d.overgroup))) →* d.overgroup :=
    { toFun := fun v => v.toAdd.toMul.val
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let j := i.comp j₀
  have hj₀ : Function.Injective j₀ := by
    intro x y h
    exact Multiplicative.toAdd.injective (Additive.toMul.injective (Subtype.ext h))
  have hj₀r : j₀.range = omegaCenterIn (pCore 2 d.overgroup) := by
    ext x
    constructor
    · rintro ⟨v,rfl⟩
      exact v.toAdd.toMul.property
    · intro hx
      exact ⟨Multiplicative.ofAdd (Additive.ofMul ⟨x,hx⟩),rfl⟩
  let κ := ElementaryMovedCover.embeddedQuotient q i hi (stabilizer d.radical a) hir
  have hkQ : κ.ker.map (stabilizer d.radical a).subtype = Q d.radical a := by
    rw [ElementaryMovedCover.embeddedQuotient_kernel,QuotientGroup.ker_mk' _]
    exact hiQ
  refine ⟨j,hi.comp hj₀,?_,?_,κ,
    ElementaryMovedCover.embeddedQuotient_surjective q i hi _ hir hq,hkQ,?_,?_,?_,?_⟩
  · rw [MonoidHom.range_comp,hj₀r]
    change (omegaCenter (pCore 2 d.overgroup)).map i = omegaCenter (Q d.radical a)
    rw [←hiQ,omegaCenter_map _ _ hi]
  · change (i.comp (ElementaryMovedCover.embedding (omegaCenterIn (pCore 2 d.overgroup))
      (K.subgroupOf d.overgroup) q hq hk)).range = U d.radical a
    rw [MonoidHom.range_comp,ElementaryMovedCover.embedding_range,←replacement_initialCore_eq h d]
    simpa only [Sp4Four.LocalPackage.initialLayer,replacement_residual h d] using hiU
  · exact hkQ.trans (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) a ha).symm
  · rw [←hiL]
    exact ElementaryMovedCover.embeddedQuotient_subgroup q i hi _ hir _
  · intro g v
    let vtx := (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hir)
    have hd : i (vtx.symm g) = (g : FreeAmalgam d.radical) :=
      congrArg Subtype.val (vtx.apply_symm_apply g)
    have hh := congrArg i (NormalElementaryQuotient.representation_apply
      (omegaCenterIn (pCore 2 d.overgroup)) q hq hk (vtx.symm g) v)
    change i ((ρ (q (vtx.symm g)) v).toMul.val) =
      (g : FreeAmalgam d.radical) * i v.toMul.val * (g : FreeAmalgam d.radical)⁻¹
    simpa only [map_mul,map_inv,hd] using hh
  · let vtx : K.subgroupOf d.overgroup ≃* Ltilde d.radical a :=
      ((K.subgroupOf d.overgroup).equivMapOfInjective i hi).trans (MulEquiv.subgroupCongr hiL)
    let f : Ltilde d.radical a →* L (K := E.Carrier) := e.groupEquiv.toMonoidHom.comp
      ((q.subgroupMap (K.subgroupOf d.overgroup)).comp vtx.symm.toMonoidHom)
    refine ⟨f,e.groupEquiv.surjective.comp
      ((q.subgroupMap_surjective _).comp vtx.symm.surjective),?_⟩
    intro g v
    have hmark : (e.groupEquiv.symm (f g)).val = q (vtx.symm g) :=
      congrArg Subtype.val (e.groupEquiv.symm_apply_apply
        (q.subgroupMap (K.subgroupOf d.overgroup) (vtx.symm g)))
    have hd : i (vtx.symm g) = (g : FreeAmalgam d.radical) :=
      congrArg Subtype.val (vtx.apply_symm_apply g)
    have hh := congrArg i (NormalElementaryQuotient.representation_apply
      (omegaCenterIn (pCore 2 d.overgroup)) q hq hk (vtx.symm g) v)
    have hh' : j (Multiplicative.ofAdd (ρ (q (vtx.symm g)) v)) =
        (g : FreeAmalgam d.radical) * j (Multiplicative.ofAdd v) * (g : FreeAmalgam d.radical)⁻¹ := by
      change i ((ρ (q (vtx.symm g)) v).toMul.val) =
        (g : FreeAmalgam d.radical) * i v.toMul.val * (g : FreeAmalgam d.radical)⁻¹
      simpa only [map_mul,map_inv,hd] using hh
    exact (congrArg (fun x => j (Multiplicative.ofAdd (ρ x v))) hmark).trans hh'

/-- At the original field degree, failure of the whole-core bound bounds
movement of the whole central omega layer by the field order. -/
theorem replacement_nonfrattini_X_movement
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex (X d.radical a) ≤ 2^n := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  have hsmall := replacement_critical_index_lt_field_sq_of_nonfrattini h d path hb hlarge
  obtain ⟨he,ha⟩ := replacement_critical_indices_eq_field_of_small h d path (by omega) hsmall
  obtain ⟨⟨E,hE,e,hecov,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.end_color
  have hFcard : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  let δ := κ.comp (inclusion hAZ)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (quotient_image_card _ _ _ hAZ κ hκQ).trans (he.trans hFcard.symm)
  have hδ : ∀ x : Z d.radical a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hconj (inclusion hAZ x) v
  have hCa := MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) a path.start_color
  obtain ⟨β,hβcard,hβmark,hβ,hd,hquad⟩ := inner_root_actor_of_field_index path (by omega)
    hCa h.nonbinary hFcard s e hecov (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ hδ hδcard (ha.trans hFcard.symm)
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFcard]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hh := critical_X_movement_bound_of_vertex_coordinates path (by omega)
    (MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)) hCa hcard
    s e hecov (replacement_component_image_structure h d).2.2.2.2 j hj hjr κ hκC hconj β hβ hd
  rwa [hFcard] at hh

/-- The source X-decomposition at the original degree, including its entire
component-fixed attachment. This supplies the whole-layer part of MS93 (3.3)
in the non-Frattini branch of (3.6). -/
theorem replacement_nonfrattini_X_decomposition
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hlarge : ¬ core d.radical a ≤
      (frattini (Q d.radical a)).map (Q d.radical a).subtype ⊔ X d.radical a) :
    X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) := by
  let := replacementComponent_normal h d
  let ρ := replacementRepresentation h d
  let s := replacementMovedSection h d
  obtain ⟨E,hE,e,he⟩ := replacement_centralOmega_initial_cover h d
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  obtain ⟨j,hj,hjr,hjUr,κ,hκ,hκQ,hκC,hκL,hfull,f,hf,hfconj⟩ :=
    replacement_fullX_coordinates_at_vertex h d path.start_color E e
  let jU := j.comp s.space.toSubmodule.subtype.toAddMonoidHom.toMultiplicative
  have hjU : Function.Injective jU := by
    intro x y hh
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (hj hh)
  obtain ⟨haq,hzq⟩ := replacement_critical_indices_eq_field_of_small h d path (by omega)
    (replacement_critical_index_lt_field_sq_of_nonfrattini h d path hb hlarge)
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have hZA : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZA)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (quotient_image_card _ _ _ hZA κ hκQ).trans (hzq.trans hFc.symm)
  have hδ : ∀ x : Z d.radical z, ∀ v : s.space.toSubmodule,
      jU (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam d.radical)*jU (Multiplicative.ofAdd v)*(x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hfull (inclusion hZA x) v.val
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d) (replacement_core_le h d)
      (replacement_omegaOrbit_centralizer h d) z path.end_color)
    h.nonbinary hFc s e he (replacement_component_image_structure h d).2.2.2.2
    jU hjU hjUr δ hδ hδcard (haq.trans hFc.symm)
  let σ : Representation (ZMod 2) (L (K := E.Carrier))
      (Additive (omegaCenterIn (pCore 2 d.overgroup))) :=
    ρ.comp ((replacementComponent d).subtype.comp e.groupEquiv.symm.toMonoidHom)
  let W : Subrepresentation σ :=
    { toSubmodule := s.space.toSubmodule
      apply_mem_toSubmodule _g _v hv := s.space.apply_mem_toSubmodule _ hv }
  have hβfull (x : Z d.radical z) (v : Additive (omegaCenterIn (pCore 2 d.overgroup))) :
      j (Multiplicative.ofAdd (σ (β x) v)) =
        (x : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam d.radical)⁻¹ := by
    change j (Multiplicative.ofAdd (ρ (e.groupEquiv.symm (β x)) v)) = _
    rw [hβmark]
    exact hfull (inclusion hZA x) v
  have hbound := replacement_nonfrattini_X_movement h d path hb hlarge
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  exact X_eq_moving_sup_centralizer_of_movement hcard σ W
    (MovedSection.coverProjection s e) he (Z d.radical z) β hβcard
    hβdim hβquad j hj hjr hjUr hβfull (by rwa [hFc]) f hfconj

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
