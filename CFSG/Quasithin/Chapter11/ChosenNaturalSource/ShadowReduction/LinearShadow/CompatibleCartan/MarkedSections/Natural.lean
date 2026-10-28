module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.SourceFields
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.SL3.PlaneAction

/-!
# The original natural action and its marked plane

Transport the original chosen coordinates to V and retain the actual L-action.
Uniqueness of the Sylow flag identifies its literal plane, whose local residual
maps onto SL₂. The same coordinates prove scalar-linearity of the inclusion.
Faithfulness gives the centralizer identity needed to align the two fields,
and the actual Cartan has an invariant one-dimensional complement in V.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), the geometry
preceding 11.3.8 and its first complement, printed pp.774–775.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections
open LocalGeometry
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) {F : BinaryField} (c : Coordinates D F)
    [IsMulCommutative V] (hfixed : V ⊓ centralizer (L : Set G) = ⊥)

omit [IsMulCommutative V] in
private theorem originalCoordinates_projection (v : Additive V) :
    originalCoordinates D c hfixed v = (c.projection v.toMul).toAdd := rfl

/-- The original field-linear representation of L on V, with its given scalars. -/
def originalRepresentation :
    let := originalModule D c hfixed
    Representation F.Carrier L (Additive V) := by
  let := originalModule D c hfixed
  exact ((originalCoordinates D c hfixed).linearEquiv F.Carrier).symm.conjRingEquiv.toMonoidHom.comp
    (c.modelAction.comp c.quotientMap)

/-- The transported representation is actual conjugation, on every original vector. -/
theorem originalRepresentation_conj (l : L) (v : Additive V) :
    ((originalRepresentation D c hfixed l v).toMul : G) =
      MulAut.conj (l : G) (v.toMul : G) := by
  let := originalModule D c hfixed
  have he : originalRepresentation D c hfixed l v =
      Additive.ofMul (V.normalizerMonoidHom (inclusion D.normalizes l) v.toMul) := by
    apply (originalCoordinates D c hfixed).injective
    change originalCoordinates D c hfixed
      ((originalCoordinates D c hfixed).symm
        (c.modelAction (c.quotientMap l) (originalCoordinates D c hfixed v))) = _
    rw [AddEquiv.apply_symm_apply]
    exact (c.projection_component_conjugation l v.toMul).symm
  exact congrArg (fun w : Additive V => (w.toMul : G)) he

/-- Restrict the same representation to the source Cartan inside L. -/
def cartanRepresentation {X : Subgroup G} (hX : IsCartan T L X) :
    let := originalModule D c hfixed
    Representation F.Carrier X (Additive V) :=
  (originalRepresentation D c hfixed).comp (inclusion (hX.1.trans inf_le_left))

theorem cartanRepresentation_conj {X : Subgroup G} (hX : IsCartan T L X)
    (x : X) (v : Additive V) :
    ((cartanRepresentation D c hfixed hX x v).toMul : G) =
      MulAut.conj (x : G) (v.toMul : G) :=
  originalRepresentation_conj D c hfixed _ v

variable (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))

omit [IsMulCommutative V] in
/-- Every supplied invariant flag is the one obtained from the same SL₃ marking. -/
theorem flag_eq (f : InvariantFlag (.sl3 m)) : f = SL3.flag D S m := by
  have hs : f.space = (SL3.flag D S m).space := by
    funext i
    exact SL3.flag_unique D S m i (f.space i) (f.dimension i) (f.invariant i)
  have extFlag (a b : InvariantFlag (.sl3 m)) (h : a.space = b.space) : a = b := by
    cases a
    cases b
    cases h
    rfl
  exact extFlag _ _ hs

omit [IsMulCommutative V] in
/-- In particular the source Cartan preserves the actual plane for any supplied flag. -/
theorem cartan_normalizes_plane (f : InvariantFlag (.sl3 m)) {X : Subgroup G}
    (hX : IsCartan T L X) : X ≤ normalizer (f.Vi 1 : Set G) := by
  rw [flag_eq D S m f]
  exact SL3.cartan_normalizes D S m hX 1

/-- Actual X-invariance over the original, specified field on V. -/
theorem originalPlane_invariant (f : InvariantFlag (.sl3 m)) {X : Subgroup G}
    (hX : IsCartan T L X) :
    let := originalModule D (.sl3 m) hfixed
    ∀ (x : X) (v : Additive V), v ∈ originalPlane D (.sl3 m) hfixed f →
      cartanRepresentation D (.sl3 m) hfixed hX x v ∈ originalPlane D (.sl3 m) hfixed f := by
  let := originalModule D (.sl3 m) hfixed
  dsimp only
  intro x v hv
  rw [mem_originalPlane] at hv ⊢
  rw [cartanRepresentation_conj]
  exact (mem_normalizer_iff.mp (cartan_normalizes_plane D S m f hX x.property) _).mp hv

/-- The whole original V is three-dimensional over its original field. -/
theorem original_finrank :
    let := originalModule D (.sl3 m) hfixed
    Module.finrank S.field.Carrier (Additive V) = 3 := by
  let := originalModule D (.sl3 m) hfixed
  exact ((originalCoordinates D (.sl3 m) hfixed).linearEquiv S.field.Carrier).finrank_eq.trans
    (Module.finrank_fin_fun S.field.Carrier)

/-- Coordinates on the literal intersection, obtained from the original SL₃ flag. -/
def planeCoordinates (f : InvariantFlag (.sl3 m)) (P : Subgroup G)
    (hPV : P ⊓ V = f.Vi 1) : Additive (P ⊓ V : Subgroup G) ≃+ (Fin 2 → S.field.Carrier) :=
  (MulEquiv.subgroupCongr (hPV.trans (congrArg (fun q : InvariantFlag (.sl3 m) => q.Vi 1)
    (flag_eq D S m f)))).toAdditive.trans (SL3.PlaneAction.planeEquiv D S m).toAddEquiv

omit [IsMulCommutative V] in
private theorem planeCoordinates_symm_val (f : InvariantFlag (.sl3 m)) (P : Subgroup G)
    (hPV : P ⊓ V = f.Vi 1) (w : Fin 2 → S.field.Carrier) :
    (((planeCoordinates D S m f P hPV).symm w).toMul : G) =
      (((SL3.PlaneAction.planeEquiv D S m).symm w).toMul : G) :=
  MulEquiv.subgroupCongr_symm_apply
    (hPV.trans (congrArg (fun q : InvariantFlag (.sl3 m) => q.Vi 1) (flag_eq D S m f)))
    ((SL3.PlaneAction.planeEquiv D S m).symm w).toMul

/-- The same literal L₂, projected onto its actual natural SL₂ action. -/
def planeActors (f : InvariantFlag (.sl3 m)) :
    f.Li 1 →* Matrix.SpecialLinearGroup (Fin 2) S.field.Carrier :=
  (SL3.PlaneAction.planeProjection D S m).comp
    (MulEquiv.subgroupCongr (congrArg (fun q : InvariantFlag (.sl3 m) => q.Li 1)
      (flag_eq D S m f))).toMonoidHom

omit [IsMulCommutative V] in
theorem planeActors_surjective (f : InvariantFlag (.sl3 m)) :
    Function.Surjective (planeActors D S m f) :=
  (SL3.PlaneAction.planeProjection_surjective D S m).comp (MulEquiv.surjective _)

omit [IsMulCommutative V] in
/-- Intertwining is equality in G, with the original conjugating element. -/
theorem planeCoordinates_conj (f : InvariantFlag (.sl3 m)) (P : Subgroup G)
    (hPV : P ⊓ V = f.Vi 1) (g : f.Li 1) (v : Fin 2 → S.field.Carrier) :
    ((planeCoordinates D S m f P hPV).symm ((planeActors D S m f g).val.mulVec v)).toMul.val =
      MulAut.conj (g : G) (((planeCoordinates D S m f P hPV).symm v).toMul : G) := by
  have hf := flag_eq D S m f
  subst f
  let e := SL3.PlaneAction.planeEquiv D S m
  have he := SL3.PlaneAction.planeEquiv_intertwines D S m g (e.symm v)
  rw [LinearEquiv.apply_symm_apply] at he
  have hi := congrArg (fun w => ((e.symm w).toMul : G)) he
  have hg : planeActors D S m (SL3.flag D S m) g =
      SL3.PlaneAction.planeProjection D S m g := by
    change SL3.PlaneAction.planeProjection D S m
      ((MulEquiv.subgroupCongr (congrArg (fun q : InvariantFlag (.sl3 m) => q.Li 1)
        (flag_eq D S m (SL3.flag D S m)))) g) = _
    congr 1
  rw [hg, planeCoordinates_symm_val, planeCoordinates_symm_val]
  simpa [e, Components.flagAction, specialLinearNatural_apply] using hi.symm

/-- Embedding the marked plane into V preserves its original field scalars. -/
theorem planeCoordinates_linear (f : InvariantFlag (.sl3 m)) (P : Subgroup G)
    (hPV : P ⊓ V = f.Vi 1) :
    let := originalModule D (.sl3 m) hfixed
    ∀ (a : S.field.Carrier) v,
      (inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive
        ((planeCoordinates D S m f P hPV).symm (a • v)) =
      a • (inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive
        ((planeCoordinates D S m f P hPV).symm v) := by
  let := originalModule D (.sl3 m) hfixed
  dsimp only
  intro a v
  have hf := flag_eq D S m f
  subst f
  let e := SL3.PlaneAction.planeEquiv D S m
  let b := SL3.PlaneAction.alignedPlaneEquiv (SL3.alignment D S m)
  let z := (SL3.Model.planeEquiv (F := S.field.Carrier)).symm
  have hcoord (w : Fin 2 → S.field.Carrier) :
      originalCoordinates D (.sl3 m) hfixed
        ((inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive
          ((planeCoordinates D S m (SL3.flag D S m) P hPV).symm w)) =
        (b.symm (z w)).val := by
    have hh := congrArg (fun u => (b.symm (z u)).val) (e.apply_symm_apply w)
    change (b.symm (z (SL3.Model.planeEquiv (b
      ((SL3.subspaceEquiv D S m ((SL3.flag D S m).space 1))
        (e.symm w).toMul).toAdd)))).val = _ at hh
    simp only [z, LinearEquiv.symm_apply_apply] at hh
    rw [SL3.subspaceEquiv_apply] at hh
    rw [originalCoordinates_projection]
    have hi : ((inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive
        ((planeCoordinates D S m (SL3.flag D S m) P hPV).symm w)).toMul =
        (⟨(e.symm w).toMul, D.centralQuotientPreimage_le _ (e.symm w).toMul.property⟩ : V) := by
      apply Subtype.ext
      exact planeCoordinates_symm_val D S m (SL3.flag D S m) P hPV w
    rw [hi]
    exact hh
  apply (originalCoordinates D (.sl3 m) hfixed).injective
  rw [originalCoordinates_smul, hcoord, hcoord, map_smul, map_smul]
  rfl

omit [IsMulCommutative V] in
include D S m in
/-- The faithful marked action puts every element of C_L(V) in O₂(L). -/
theorem centralizer_le_core : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2 := by
  rintro l ⟨hl,hc⟩
  let c : Coordinates D S.field := .sl3 m
  let l' : L := ⟨l,hl⟩
  have hq : c.quotientMap l' = 1 := by
    apply Subtype.ext
    apply Matrix.mulVec_injective
    funext w
    obtain ⟨v,hv⟩ := c.projection_surjective (Multiplicative.ofAdd w)
    have he := c.projection_component_conjugation l' v
    have hcv : V.normalizerMonoidHom (inclusion D.normalizes l') v = v := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hc _ v.property).symm
    rw [hcv,hv] at he
    exact he.symm.trans (Matrix.one_mulVec w).symm
  have hk : l' ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff _).mp
    apply c.groupEquiv.injective
    exact hq.trans c.groupEquiv.map_one.symm
  exact ⟨l',hk,rfl⟩

/-- The source core identity and the marked action derive C_P(V)=P∩V. -/
theorem fixed_plane (f : InvariantFlag (.sl3 m)) (P : Subgroup G)
    (hP : P = (f.Li 1).pCoreIn 2) (hcore : L.pCoreIn 2 = V) :
    P ⊓ centralizer (V : Set G) = P ⊓ V := by
  have hPL : P ≤ L := hP ▸ (pCoreIn_le 2 (f.Li 1)).trans
    ((localResidual_le _).trans inf_le_left)
  apply le_antisymm
  · intro p hp
    exact ⟨hp.1,hcore ▸ centralizer_le_core D S m ⟨hPL hp.1,hp.2⟩⟩
  · exact inf_le_inf_left P (le_centralizer_iff_isMulCommutative.mpr inferInstance)

/-- The specified original plane has exactly field dimension two. -/
theorem originalPlane_finrank (f : InvariantFlag (.sl3 m)) :
    let := originalModule D (.sl3 m) hfixed
    Module.finrank S.field.Carrier (originalPlane D (.sl3 m) hfixed f) = 2 := by
  let := originalModule D (.sl3 m) hfixed
  exact (((originalCoordinates D (.sl3 m) hfixed).linearEquiv S.field.Carrier).ofSubmodule'
    (f.space 1)).finrank_eq.trans (f.dimension 1)

/-- Every field complement to the original plane is one-dimensional. -/
theorem original_complement_finrank (f : InvariantFlag (.sl3 m)) :
    let := originalModule D (.sl3 m) hfixed
    ∀ W : Submodule S.field.Carrier (Additive V),
      IsCompl (originalPlane D (.sl3 m) hfixed f) W → Module.finrank S.field.Carrier W = 1 := by
  let := originalModule D (.sl3 m) hfixed
  dsimp only
  intro W hW
  have h := Submodule.finrank_add_eq_of_isCompl hW
  rw [originalPlane_finrank D hfixed S m f, original_finrank D hfixed S m] at h
  omega

/-- The first source complement is constructed on the literal V₂ inside V. -/
theorem exists_original_line_complement (f : InvariantFlag (.sl3 m))
    {X : Subgroup G} (hX : IsCartan T L X) :
    let := originalModule D (.sl3 m) hfixed
    ∃ W : Submodule S.field.Carrier (Additive V),
      IsCompl (originalPlane D (.sl3 m) hfixed f) W ∧
      Module.finrank S.field.Carrier W = 1 ∧
      Disjoint (f.Vi 1) (ambientSubgroup W) ∧
      f.Vi 1 ⊔ ambientSubgroup W = V ∧
      X ≤ normalizer (ambientSubgroup W : Set G) := by
  let := originalModule D (.sl3 m) hfixed
  obtain ⟨W,hW,hd,hs,hn⟩ := exists_ambient_field_complement hX.odd
    (cartanRepresentation D (.sl3 m) hfixed hX)
    (cartanRepresentation_conj D (.sl3 m) hfixed hX)
    (originalPlane D (.sl3 m) hfixed f) (originalPlane_invariant D hfixed S m f hX)
  exact ⟨W,hW,original_complement_finrank D hfixed S m f W hW,
    ambient_originalPlane D (.sl3 m) hfixed f ▸ hd,
    ambient_originalPlane D (.sl3 m) hfixed f ▸ hs,hn⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan.MarkedSections
