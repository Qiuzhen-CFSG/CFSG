module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CompatibleCartan.Restriction
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Compatible scalars on the literal common subgroup

SeparatePlaneActions retains the actual additive plane in P intersect V,
its natural L₂ action, and the independent field structure on P. The
constructor ofFixedPlane obtains scalar stability from C_P(V) = P intersect V
and the specified linear action on P. Restriction then constructs a new
field structure on P agreeing with V on each actual element of the
intersection. Every linear action, including Y, is preserved pointwise.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 11.3.8,
printed p.775. This leaf proves the transport step. Extracting the separate
plane coordinates from the full natural and orthogonal markings and the
subsequent Cartan eigenspaces are separate obligations. The chosen-source
application is in SourceFields.
-/

@[expose] public noncomputable section
open Subgroup Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
variable {G : Type*} [Group G] {E F : Type*} [Field E] [Field F]
  {P V A : Subgroup G} [IsMulCommutative P] [IsMulCommutative V]
  [Module E (Additive P)] [Module F (Additive V)]

/-- Separate markings of the common plane; no comparison of the scalar fields. -/
structure SeparatePlaneActions (P V A : Subgroup G)
    [IsMulCommutative P] [IsMulCommutative V]
    [Module E (Additive P)] [Module F (Additive V)] where
  plane : Additive (P ⊓ V : Subgroup G) ≃+ (Fin 2 → F)
  linear_in_V : ∀ (a : F) v,
    (Subgroup.inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive (plane.symm (a • v)) =
      a • (Subgroup.inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive (plane.symm v)
  plane_in_P : Submodule E (Additive P)
  plane_in_P_mem : ∀ p : Additive P, p ∈ plane_in_P ↔ (p.toMul : G) ∈ V
  action : Representation E A (Additive P)
  action_eq_conj : ∀ (g : A) (p : Additive P),
    ((action g p).toMul : G) = (MulAut.conj (g : G)) (p.toMul : G)
  natural : A →* Matrix.SpecialLinearGroup (Fin 2) F
  natural_surjective : Function.Surjective natural
  natural_eq_conj : ∀ (g : A) (v : Fin 2 → F),
    ((plane.symm ((natural g).val.mulVec v)).toMul : G) =
      (MulAut.conj (g : G)) ((plane.symm v).toMul : G)

namespace SeparatePlaneActions

/-- The fixed-space description of P intersect V makes it an E-submodule;
no stability under the other field is imposed. -/
def fixedPlane {Y : Subgroup G} (ρ : Representation E Y (Additive P)) :
    Submodule E (Additive P) := Representation.invariants (ρ.comp (V.subgroupOf Y).subtype)

omit [IsMulCommutative V] in
theorem mem_fixedPlane {Y : Subgroup G} (ρ : Representation E Y (Additive P))
    (hρ : ∀ (g : Y) (p : Additive P),
      ((ρ g p).toMul : G) = (MulAut.conj (g : G)) (p.toMul : G))
    (hVY : V ≤ Y) (hfixed : P ⊓ centralizer (V : Set G) = P ⊓ V)
    (p : Additive P) : p ∈ fixedPlane (V := V) ρ ↔ (p.toMul : G) ∈ V := by
  constructor
  · intro hp
    have hc : (p.toMul : G) ∈ centralizer (V : Set G) := by
      intro v hv
      let a : V.subgroupOf Y := ⟨⟨v, hVY hv⟩, hv⟩
      have he := congrArg (fun w : Additive P => (w.toMul : G)) (hp a)
      rw [MonoidHom.comp_apply, hρ] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    exact (hfixed ▸ (show (p.toMul : G) ∈ P ⊓ centralizer (V : Set G) from
      ⟨p.toMul.property, hc⟩)).2
  · intro hp v
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [MonoidHom.comp_apply, hρ]
    have hc : (p.toMul : G) ∈ centralizer (V : Set G) :=
      (hfixed.symm ▸ (show (p.toMul : G) ∈ P ⊓ V from ⟨p.toMul.property, hp⟩)).2
    exact mul_inv_eq_iff_eq_mul.mpr (hc _ v.property)

/-- Construct the separate plane datum from the actual fixed-plane geometry
and the natural L₂ action, without a field-stability or compatibility premise. -/
def ofFixedPlane {Y : Subgroup G} (ρ : Representation E Y (Additive P))
    (hρ : ∀ (g : Y) (p : Additive P),
      ((ρ g p).toMul : G) = (MulAut.conj (g : G)) (p.toMul : G))
    (hVY : V ≤ Y) (hAY : A ≤ Y)
    (hfixed : P ⊓ centralizer (V : Set G) = P ⊓ V)
    (e : Additive (P ⊓ V : Subgroup G) ≃+ (Fin 2 → F))
    (he : ∀ (a : F) v,
      (Subgroup.inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive (e.symm (a • v)) =
        a • (Subgroup.inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive (e.symm v))
    (α : A →* Matrix.SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α)
    (ha : ∀ (g : A) (v : Fin 2 → F),
      ((e.symm ((α g).val.mulVec v)).toMul : G) =
        (MulAut.conj (g : G)) ((e.symm v).toMul : G)) :
    SeparatePlaneActions (E := E) (F := F) P V A where
  plane := e
  linear_in_V := he
  plane_in_P := fixedPlane (V := V) ρ
  plane_in_P_mem := mem_fixedPlane ρ hρ hVY hfixed
  action := ρ.comp (Subgroup.inclusion hAY)
  action_eq_conj g p := hρ (Subgroup.inclusion hAY g) p
  natural := α
  natural_surjective := hα
  natural_eq_conj := ha
variable (d : SeparatePlaneActions (E := E) (F := F) P V A)

/-- Inclusion of the literal intersection, composed with its natural coordinates. -/
def inclusion : (Fin 2 → F) →+ Additive P :=
  (Subgroup.inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive.comp d.plane.symm.toAddMonoidHom

private theorem inclusion_injective : Function.Injective d.inclusion := by
  intro v w h
  apply d.plane.symm.injective
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun p : Additive P => (p.toMul : G)) h

/-- Scalar stability follows from the separately marked P-submodule. -/
private theorem scalar_closed (a : E) (v : Fin 2 → F) :
    ∃ w, d.inclusion w = a • d.inclusion v := by
  have hv : d.inclusion v ∈ d.plane_in_P :=
    (d.plane_in_P_mem _).mpr (d.plane.symm v).toMul.property.2
  have hV := (d.plane_in_P_mem _).mp (d.plane_in_P.smul_mem a hv)
  let b : Additive (P ⊓ V : Subgroup G) := Additive.ofMul
    ⟨((a • d.inclusion v).toMul : G), (a • d.inclusion v).toMul.property, hV⟩
  refine ⟨d.plane b, ?_⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((d.plane.symm (d.plane b)).toMul : G) = _
  rw [d.plane.symm_apply_apply]
  rfl

/-- The actual L₂ actors give the natural-plane restriction datum. -/
def restrictionDatum : NaturalPlane (E := E) (F := F) (A := Additive P) where
  inclusion := d.inclusion
  injective := by exact inclusion_injective d
  scalar_closed := by exact scalar_closed d
  actor g := d.action ((d.natural_surjective g).choose)
  intertwines g v := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change ((d.plane.symm (g.val.mulVec v)).toMul : G) = _
    rw [d.action_eq_conj]
    have h := d.natural_eq_conj ((d.natural_surjective g).choose) v
    rw [(d.natural_surjective g).choose_spec] at h
    exact h

variable [Finite F]

/-- A new F-structure on P, constructed from the two independent markings. -/
@[instance_reducible] def compatibleModule (hc : Nat.card E = Nat.card F) :
    Module F (Additive P) := d.restrictionDatum.compatibleModule hc

/-- The new P-scalars and the original V-scalars agree on every actual vector
of P intersect V; their equality takes place in the ambient group. -/
theorem common_smul (hc : Nat.card E = Nat.card F) (a : F) (b : Additive (P ⊓ V : Subgroup G)) :
    letI := d.compatibleModule hc
    ((a • (Subgroup.inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b).toMul : G) =
      ((a • (Subgroup.inclusion (inf_le_right : P ⊓ V ≤ V)).toAdditive b).toMul : G) := by
  let := d.compatibleModule hc
  have hp := d.restrictionDatum.compatible_smul hc a (d.plane b)
  change a • d.inclusion (d.plane b) = d.inclusion (a • d.plane b) at hp
  have hv := d.linear_in_V a (d.plane b)
  simp only [AddEquiv.symm_apply_apply] at hv
  have hi : d.inclusion (d.plane b) =
      (Subgroup.inclusion (inf_le_left : P ⊓ V ≤ P)).toAdditive b := by
    change (Subgroup.inclusion _).toAdditive (d.plane.symm (d.plane b)) = _
    rw [d.plane.symm_apply_apply]
  rw [hi] at hp
  rw [hp, ← hv]
  rfl

end SeparatePlaneActions

namespace NaturalPlane
variable {E F M H : Type*} [Field E] [Field F] [AddCommGroup M] [Module E M]
  [Finite F] [Monoid H] (N : NaturalPlane (E := E) (F := F) (A := M))

/-- Changing coefficients preserves the complete action of every linear actor. -/
def compatibleRepresentation (hc : Nat.card E = Nat.card F) (ρ : Representation E H M) :
    letI := N.compatibleModule hc
    Representation F H M := by
  letI := N.compatibleModule hc
  exact {
    toFun := fun h => N.compatibleEnd hc (ρ h)
    map_one' := by
      apply LinearMap.ext
      intro v
      change ρ 1 v = v
      rw [map_one]
      rfl
    map_mul' := by
      intro g h
      apply LinearMap.ext
      intro v
      change ρ (g * h) v = ρ g (ρ h v)
      rw [map_mul]
      rfl }

theorem compatibleRepresentation_apply (hc : Nat.card E = Nat.card F)
    (ρ : Representation E H M) (h : H) (v : M) :
    N.compatibleRepresentation hc ρ h v = ρ h v := rfl
end NaturalPlane

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
