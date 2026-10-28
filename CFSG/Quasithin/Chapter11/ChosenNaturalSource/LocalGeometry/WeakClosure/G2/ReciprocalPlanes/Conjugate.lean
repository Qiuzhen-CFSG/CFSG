module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalPlanes.Transfer
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalRoots.Source
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ResidualIncidence.Marked

/-!
# Reciprocal full planes on the actual conjugate module

Transport the root action back by the literal ambient conjugation map, apply
the full-preimage identity, and transport it forward again. The center remains
C_(Vᵍ)(Lᵍ). The reciprocal corank 2n proves the actor nontrivial. Lifting the
model conjugator through the original quotient realizes the recovered plane
as an Lᵍ-conjugate of the full original flag plane V₂ᵍ.

The Source application constructs all these actors from the preceding source
family. This does not identify the two covering centers or yet establish the
common-plane comparison required for weak closure.
Source: Aschbacher--Smith 11.2.2(5), printed p.768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalPlanes
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k:=ZMod 2) (g2Natural S.field.Carrier)))

/-- Every rotated full natural plane is an actual L-conjugate of the original
flag plane; the literal quotient map supplies its ambient conjugator. -/
theorem preimage_plane_conjugate (f : InvariantFlag (Coordinates.g2 m))
    (u : Model S.field.Carrier) : ∃ l : L,
    (Coordinates.g2 m).preimage ((naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier u)) =
      (f.Vi 1).map (MulAut.conj (l : G)).toMonoidHom := by
  let b := (LocalGeometry.G2.ResidualIncidence.alignment S m).val
  have hf : f.space 1 = (naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier b) := by
    exact (LocalGeometry.G2.flag_unique S m 1 _ (f.dimension 1) (f.invariant 1)).trans
      (LocalGeometry.G2.ResidualIncidence.flag_space_eq S m 1)
  obtain ⟨l,hl⟩ := (Coordinates.g2 m).quotientMap_surjective (u*b⁻¹)
  refine ⟨l,?_⟩
  rw [InvariantFlag.Vi,(Coordinates.g2 m).preimage_conjugate,hl]
  change _ = (Coordinates.g2 m).preimage ((f.space 1).map (Natural.action S.field.Carrier (u*b⁻¹)))
  rw [hf,←Submodule.map_comp]
  have he : (Natural.action S.field.Carrier (u*b⁻¹)).comp (Natural.action S.field.Carrier b) =
      Natural.action S.field.Carrier u := by
    ext x
    simp only [LinearMap.comp_apply,map_mul,Module.End.mul_apply,
      (Natural.action S.field.Carrier).inv_self_apply]
  rw [he]

omit [Finite G] in
private theorem conjugate_cancel (U : Subgroup G) (g : G) :
    (U.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = U := by
  rw [map_map]
  have he : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom = MonoidHom.id G := by
    ext x
    simp [MulAut.conj_apply,mul_assoc]
  rw [he,map_id]

/-- The reciprocal action reconstructs a full plane of the conjugate module,
retaining its own central kernel, rather than replacing it by the original one. -/
theorem conjugate_root_commutator_sup_center (g : G) (E : Subgroup G)
    (b : E →* Model S.field.Carrier) (u : Model S.field.Carrier)
    (hact : ∀ (x : E) (v : D.space),
      MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (b x) v)) : G) =
        (x : G) * MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹)
    (hb : b.range ≤ LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom)
    (hne : b.range ≠ ⊥) :
    ⁅V.map (MulAut.conj g).toMonoidHom,E⁆ ⊔
        (V ⊓ centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
      ((Coordinates.g2 m).preimage ((naturalPlane S.field.Carrier).map
        (Natural.action S.field.Carrier u))).map (MulAut.conj g).toMonoidHom := by
  let e := MulAut.conj g⁻¹
  let E' := E.map e.toMonoidHom
  let b' : E' →* Model S.field.Carrier := b.comp (e.subgroupMap E).symm.toMonoidHom
  have hbe : b'.range = b.range := by
    rw [MonoidHom.range_comp,MonoidHom.range_eq_top.mpr (e.subgroupMap E).symm.surjective,
      ←MonoidHom.range_eq_map]
  have hact' (x : E') (v : D.space) :
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (b' x) v)) : G) =
        (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹ := by
    have hh := congrArg e (hact ((e.subgroupMap E).symm x) v)
    have hcancel (y : G) : e (MulAut.conj g y) = y := by simp [e,MulAut.conj_apply,mul_assoc]
    change e (MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd
      (Preliminary.markedAction D m (b' x) v)) : G)) =
        e ((((e.subgroupMap E).symm x : E) : G) *
          MulAut.conj g (D.spaceEquiv (Multiplicative.ofAdd v) : G) *
          (((e.subgroupMap E).symm x : E) : G)⁻¹) at hh
    rw [hcancel,map_mul,map_mul,map_inv,hcancel] at hh
    have hex : e (((e.subgroupMap E).symm x : E) : G) = (x : G) :=
      congrArg Subtype.val ((e.subgroupMap E).apply_symm_apply x)
    rw [hex] at hh
    exact hh
  have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom)
    (root_commutator_sup_center D S m E' b' u hact' (hbe.symm ▸ hb) (hbe.symm ▸ hne))
  rw [Subgroup.map_sup,map_commutator] at hh
  have hE : E'.map (MulAut.conj g).toMonoidHom = E := by
    simpa only [inv_inv] using conjugate_cancel E g⁻¹
  rwa [hE] at hh

/-- The reciprocal root supplied by the original construction is nontrivial:
its exact fixed corank is 2n>0. -/
theorem rootData_actor_ne_bot (g : G)
    (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier)
    (Z : Subgroup (Model S.field.Carrier)) (r : ReciprocalRoots.RootData D S m g a Z) :
    r.actor.range ≠ ⊥ := by
  intro hbot
  have hEC : V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G) ≤
      centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) := by
    intro x hx
    have hx1 : r.actor ⟨x,hx⟩ = 1 := mem_bot.mp (hbot ▸ (show r.actor ⟨x,hx⟩ ∈ r.actor.range from ⟨⟨x,hx⟩,rfl⟩))
    have hk : (⟨x,hx⟩ : (V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G) : Subgroup G)) ∈ r.actor.ker := hx1
    rw [r.kernel] at hk
    exact hk
  have he : (V.map (MulAut.conj g).toMonoidHom) ⊓ centralizer
      (V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G) : Set G) =
        V.map (MulAut.conj g).toMonoidHom := inf_eq_left.mpr (le_centralizer_iff.mp hEC)
  have hc := r.corank
  rw [he] at hc
  norm_num [ChapterE.subgroupCorank] at hc
  have hn := S.nonbinary
  omega

/-- Each original reciprocal root constructs an actual full conjugate flag plane.
The center adjoined is C_(Vᵍ)(Lᵍ), with its literal ambient conjugation map. -/
theorem rootData_plane (f : InvariantFlag (Coordinates.g2 m)) (g : G)
    (a : (V.map (MulAut.conj g).toMonoidHom) →* Model S.field.Carrier)
    (Z : Subgroup (Model S.field.Carrier)) (r : ReciprocalRoots.RootData D S m g a Z) :
    ∃ l : L, ⁅V.map (MulAut.conj g).toMonoidHom,
        V ⊓ centralizer (RootPullback.rootPreimage _ a Z : Set G)⁆ ⊔
        (V ⊓ centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
      ((f.Vi 1).map (MulAut.conj (l : G)).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨l,hl⟩ := preimage_plane_conjugate D S m f r.conjugator
  refine ⟨l,?_⟩
  rw [←hl]
  exact conjugate_root_commutator_sup_center D S m g _ r.actor r.conjugator
    r.action r.root_image (rootData_actor_ne_bot D S m g a Z r)
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalPlanes
