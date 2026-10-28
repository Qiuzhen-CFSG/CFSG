module

public import Theory.SpecificGroups.Rudvalis.Model.CoveringIncidence.Max4Geometry.Assembly
public import Theory.Frattini.OmegaProducts

/-!
# The special core and its modules in actual max4 conjugates

Ambient conjugation carries the intrinsic two-core, its center, derived and
Frattini subgroups, and both literal quotients to those of the chosen conjugate.
The natural and Steinberg coordinates use this same conjugation and the same
actor equivalence. Their action formulas agree with ambient conjugation and
with the original quotient projections on every representative.

Together with `exists_marked_conjugateMax4_over_sylow`, these results supply
the special-group geometry for the conjugate containing a prescribed Sylow.
All structural and involution-marking premises have been discharged by the
fixed-subgroup assembly. Source: Aschbacher--Smith I.2.2(7), pp.412--413,
and J.2.6(2), pp.434--435; GLS3 Table 5.3r, pp.291--292.
-/

open Subgroup Rudvalis Rudvalis.SylowOvergroups

namespace Rudvalis.CoveringIncidence.Max4Geometry

/-- The group equivalence on the literal conjugate, with its ambient formula. -/
public def conjugateGroupEquiv (g : Model) : max4 ≃* conjugateMax4 g :=
  (MulAut.conj g).subgroupMap max4

@[simp] public theorem conjugateGroupEquiv_apply (g : Model) (h : max4) :
    (conjugateGroupEquiv g h : Model) = g * (h : Model) * g⁻¹ := by rfl

/-- Conjugation identifies the two literal actor quotients. -/
public noncomputable def conjugateActorQuotientEquiv (g : Model) :
    (max4 ⧸ pCore 2 max4) ≃*
      (conjugateMax4 g ⧸ pCore 2 (conjugateMax4 g)) :=
  QuotientGroup.congr _ _ (conjugateGroupEquiv g)
    (pCore_map_iso 2 (conjugateGroupEquiv g))

@[simp] public theorem conjugateActorQuotientEquiv_mk (g : Model) (h : max4) :
    conjugateActorQuotientEquiv g (QuotientGroup.mk' (pCore 2 max4) h) =
      QuotientGroup.mk' (pCore 2 (conjugateMax4 g)) (conjugateGroupEquiv g h) := by rfl

public noncomputable def conjugateActor (g : Model) :
    (conjugateMax4 g ⧸ pCore 2 (conjugateMax4 g)) ≃* BinaryLinearThree.Group :=
  (conjugateActorQuotientEquiv g).symm.trans max4NaturalActor

public abbrev ConjugateCentralQuotient (g : Model) :=
  conjugateMax4Core g ⧸ center (conjugateMax4Core g)

/-- The center quotient is transported through the same ambient conjugation. -/
public noncomputable def conjugateCentralQuotientEquiv (g : Model) :
    Max4CentralQuotient ≃* ConjugateCentralQuotient g :=
  QuotientGroup.congr _ _ (conjugateMax4CoreEquiv g)
    (center_map_equiv (conjugateMax4CoreEquiv g))

@[simp] public theorem conjugateCentralQuotientEquiv_mk (g : Model) (x : max4Core) :
    conjugateCentralQuotientEquiv g (QuotientGroup.mk' (center max4Core) x) =
      QuotientGroup.mk' (center (conjugateMax4Core g)) (conjugateMax4CoreEquiv g x) := by rfl

public theorem conjugateCore_card (g : Model) : Nat.card (conjugateMax4Core g) = 2048 :=
  (Nat.card_congr (conjugateMax4CoreEquiv g).toEquiv).symm.trans max4Core_card

public theorem conjugateCore_commutator_eq_center (g : Model) :
    _root_.commutator (conjugateMax4Core g) = center (conjugateMax4Core g) := by
  have h := congrArg (Subgroup.map (conjugateMax4CoreEquiv g).toMonoidHom)
    max4Core_commutator_eq_center
  rwa [map_commutator_eq, MonoidHom.range_eq_top.mpr (conjugateMax4CoreEquiv g).surjective,
    ← _root_.commutator_def, center_map_equiv] at h

public theorem conjugateCore_frattini_eq_center (g : Model) :
    frattini (conjugateMax4Core g) = center (conjugateMax4Core g) := by
  have h := congrArg (Subgroup.map (conjugateMax4CoreEquiv g).toMonoidHom)
    max4Core_frattini_eq_center
  rwa [frattini_map_equiv, center_map_equiv] at h

public theorem conjugateCore_mapped_commutator_eq_center (g : Model) :
    (_root_.commutator (conjugateMax4Core g)).map (conjugateMax4Core g).subtype =
      conjugateMax4CoreCenter g := by
  rw [conjugateCore_commutator_eq_center]
  rfl

public theorem conjugateCore_mapped_frattini_eq_center (g : Model) :
    (frattini (conjugateMax4Core g)).map (conjugateMax4Core g).subtype =
      conjugateMax4CoreCenter g := by
  rw [conjugateCore_frattini_eq_center]
  rfl

public theorem conjugateCore_center_card (g : Model) :
    Nat.card (center (conjugateMax4Core g)) = 8 :=
  (Nat.card_congr (centerCongr (conjugateMax4CoreEquiv g)).toEquiv).symm.trans
    max4Core_center_card

public theorem conjugateCentralQuotient_card (g : Model) :
    Nat.card (ConjugateCentralQuotient g) = 256 :=
  (Nat.card_congr (conjugateCentralQuotientEquiv g).toEquiv).symm.trans max4CentralQuotient_card

public instance conjugateCentralQuotient_elementary (g : Model) :
    IsElementaryAbelian 2 (ConjugateCentralQuotient g) :=
  IsElementaryAbelian.of_surjective (conjugateCentralQuotientEquiv g).toMonoidHom
    (conjugateCentralQuotientEquiv g).surjective

public noncomputable def conjugateNaturalCoordinates (g : Model) :
    center (conjugateMax4Core g) ≃* Multiplicative BinaryLinearThree.Vector :=
  (centerCongr (conjugateMax4CoreEquiv g)).symm.trans naturalCoordinates

public noncomputable def conjugateSteinbergCoordinates (g : Model) :
    ConjugateCentralQuotient g ≃* Multiplicative BinaryLinearThree.Steinberg :=
  (conjugateCentralQuotientEquiv g).symm.trans steinbergCoordinates

public noncomputable def conjugateNaturalAction (g : Model) :
    (conjugateMax4 g ⧸ pCore 2 (conjugateMax4 g)) →*
      MulAut (center (conjugateMax4Core g)) :=
  (MulAut.congr (centerCongr (conjugateMax4CoreEquiv g))).toMonoidHom.comp
    (naturalAction.comp (conjugateActorQuotientEquiv g).symm.toMonoidHom)

public noncomputable def conjugateSteinbergAction (g : Model) :
    (conjugateMax4 g ⧸ pCore 2 (conjugateMax4 g)) →*
      MulAut (ConjugateCentralQuotient g) :=
  (MulAut.congr (conjugateCentralQuotientEquiv g)).toMonoidHom.comp
    (steinbergAction.comp (conjugateActorQuotientEquiv g).symm.toMonoidHom)

/-- On representatives, this is the original core-center action conjugated in Ru. -/
public theorem conjugateNaturalAction_mk (g : Model) (h : max4) (x : center max4Core) :
    conjugateNaturalAction g
        (QuotientGroup.mk' (pCore 2 (conjugateMax4 g)) (conjugateGroupEquiv g h))
        (centerCongr (conjugateMax4CoreEquiv g) x) =
      centerCongr (conjugateMax4CoreEquiv g) (max4CenterAction h x) := by
  rw [← conjugateActorQuotientEquiv_mk]
  simp only [conjugateNaturalAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, naturalAction_mk, MulAut.congr_apply, MulEquiv.trans_apply]

/-- The transported natural action is literal conjugation, including ambient embeddings. -/
public theorem conjugateNaturalAction_apply (g : Model) (h : conjugateMax4 g)
    (x : center (conjugateMax4Core g)) :
    ((conjugateNaturalAction g (QuotientGroup.mk' (pCore 2 (conjugateMax4 g)) h) x :
      conjugateMax4Core g) : Model) =
      (h : Model) * ((x : conjugateMax4Core g) : Model) * (h : Model)⁻¹ := by
  obtain ⟨h, rfl⟩ := (conjugateGroupEquiv g).surjective h
  obtain ⟨x, rfl⟩ := (centerCongr (conjugateMax4CoreEquiv g)).surjective x
  rw [conjugateNaturalAction_mk]
  change (conjugateMax4CoreEquiv g (max4CenterAction h x) : Model) =
    (conjugateGroupEquiv g h : Model) * (conjugateMax4CoreEquiv g (x : max4Core) : Model) *
      (conjugateGroupEquiv g h : Model)⁻¹
  simp only [conjugateMax4CoreEquiv_apply, conjugateGroupEquiv_apply, max4CenterAction_apply]
  group

/-- The Steinberg action commutes with both the actual core projection and conjugation. -/
public theorem conjugateSteinbergAction_mk (g : Model) (h : max4) (x : max4Core) :
    conjugateSteinbergAction g
        (QuotientGroup.mk' (pCore 2 (conjugateMax4 g)) (conjugateGroupEquiv g h))
        (QuotientGroup.mk' (center (conjugateMax4Core g)) (conjugateMax4CoreEquiv g x)) =
      QuotientGroup.mk' (center (conjugateMax4Core g))
        (conjugateMax4CoreEquiv g (max4CoreAction h x)) := by
  rw [← conjugateActorQuotientEquiv_mk, ← conjugateCentralQuotientEquiv_mk,
    ← conjugateCentralQuotientEquiv_mk]
  simp only [conjugateSteinbergAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, steinbergAction_mk, MulAut.congr_apply, MulEquiv.trans_apply,
    max4CentralQuotientAction_mk]

public theorem conjugate_natural_intertwines (g : Model)
    (q : conjugateMax4 g ⧸ pCore 2 (conjugateMax4 g)) (x : center (conjugateMax4Core g)) :
    (conjugateNaturalCoordinates g (conjugateNaturalAction g q x)).toAdd =
      BinaryLinearThree.W (conjugateActor g q) (conjugateNaturalCoordinates g x).toAdd := by
  simpa only [conjugateNaturalCoordinates, conjugateNaturalAction, conjugateActor,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using
      natural_intertwines ((conjugateActorQuotientEquiv g).symm q)
        ((centerCongr (conjugateMax4CoreEquiv g)).symm x)

public theorem conjugate_steinberg_intertwines (g : Model)
    (q : conjugateMax4 g ⧸ pCore 2 (conjugateMax4 g)) (x : ConjugateCentralQuotient g) :
    (conjugateSteinbergCoordinates g (conjugateSteinbergAction g q x)).toAdd =
      BinaryLinearThree.S (conjugateActor g q) (conjugateSteinbergCoordinates g x).toAdd := by
  simpa only [conjugateSteinbergCoordinates, conjugateSteinbergAction, conjugateActor,
    MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.symm_apply_apply] using
      steinberg_intertwines ((conjugateActorQuotientEquiv g).symm q)
        ((conjugateCentralQuotientEquiv g).symm x)



/-- Conjugation on the intrinsic core of the chosen max4 conjugate. -/
public noncomputable def conjugateCoreAction (g : Model) :
    conjugateMax4 g →* MulAut (conjugateMax4Core g) :=
  (MulAut.congr (conjugateMax4CoreEquiv g)).toMonoidHom.comp
    (max4CoreAction.comp (conjugateGroupEquiv g).symm.toMonoidHom)

public theorem conjugateCoreAction_transport (g : Model) (h : max4) (x : max4Core) :
    conjugateCoreAction g (conjugateGroupEquiv g h) (conjugateMax4CoreEquiv g x) =
      conjugateMax4CoreEquiv g (max4CoreAction h x) := by
  simp only [conjugateCoreAction, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply, MulAut.congr_apply, MulEquiv.trans_apply]

@[simp] public theorem conjugateCoreAction_apply (g : Model)
    (h : conjugateMax4 g) (x : conjugateMax4Core g) :
    (conjugateCoreAction g h x : Model) = (h : Model) * (x : Model) * (h : Model)⁻¹ := by
  obtain ⟨h, rfl⟩ := (conjugateGroupEquiv g).surjective h
  obtain ⟨x, rfl⟩ := (conjugateMax4CoreEquiv g).surjective x
  rw [conjugateCoreAction_transport]
  simp only [conjugateMax4CoreEquiv_apply, conjugateGroupEquiv_apply, max4CoreAction_apply]
  group

/-- On every quotient representative, the transported action is actual conjugation. -/
public theorem conjugateSteinbergAction_apply_mk (g : Model)
    (h : conjugateMax4 g) (x : conjugateMax4Core g) :
    conjugateSteinbergAction g (QuotientGroup.mk' (pCore 2 (conjugateMax4 g)) h)
        (QuotientGroup.mk' (center (conjugateMax4Core g)) x) =
      QuotientGroup.mk' (center (conjugateMax4Core g)) (conjugateCoreAction g h x) := by
  obtain ⟨h, rfl⟩ := (conjugateGroupEquiv g).surjective h
  obtain ⟨x, rfl⟩ := (conjugateMax4CoreEquiv g).surjective x
  rw [conjugateSteinbergAction_mk, conjugateCoreAction_transport]

/-- Both transported representations act through the literal subgroup quotient. -/
public theorem conjugateActor_mk (g : Model) (h : max4) :
    conjugateActor g
        (QuotientGroup.mk' (pCore 2 (conjugateMax4 g)) (conjugateGroupEquiv g h)) =
      max4NaturalActor (QuotientGroup.mk' (pCore 2 max4) h) := by
  rw [← conjugateActorQuotientEquiv_mk]
  exact congrArg max4NaturalActor ((conjugateActorQuotientEquiv g).symm_apply_apply _)

end Rudvalis.CoveringIncidence.Max4Geometry
