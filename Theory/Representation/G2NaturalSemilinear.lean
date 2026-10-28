module

public import Theory.Representation.G2.RestrictedModules.NaturalFieldTransport
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.FieldAction
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# The binary natural representation of the inner-field extension of G₂

The coefficient field automorphisms and the six-dimensional natural action
combine into a representation of the actual semidirect product. Restricting
scalars to F₂ makes the coefficient action linear. We transport this action
back to the trace-zero split-octonion quotient, and prove its compatibility
with both the inner group and the field subgroup.

For F₄ the quotient has binary dimension twelve, and coefficient squaring is
an involution. These are the ambient representation and field action required
for the Hall--Janko restriction in Aschbacher--Smith, K.4.5, printed p.460.
No embedding or recognition of J₂ is assumed or asserted here. The underlying
octonion conventions and licensed ATLAS attribution remain in the imports.
-/

@[expose] public section

open Atlas.G2
namespace Atlas.G2.Natural.BinarySemilinear
open Restricted.NaturalCoordinates LieAutomorphismExtensions
variable (F : Type*) [Field F] [CharP F 2] [Algebra (ZMod 2) F]

/-- The actual inner-field extension of the split-octonion group. -/
abbrev Actor := Model F ⋊[fieldAction] (F ≃+* F)
abbrev Coordinates := Fin 6 → F

/-- Coefficient transport, regarded as a binary linear equivalence. -/
def fieldLinear (e : F ≃+* F) : Coordinates F ≃ₗ[ZMod 2] Coordinates F where
  toFun v i := e (v i)
  invFun v i := e.symm (v i)
  left_inv v := by ext i; exact e.symm_apply_apply _
  right_inv v := by ext i; exact e.apply_symm_apply _
  map_add' v w := by ext i; exact map_add e _ _
  map_smul' a v := by ext i; exact ZMod.map_smul e a (v i)

omit [CharP F 2] in
@[simp] theorem fieldLinear_apply (e : F ≃+* F) (v : Coordinates F) (i : Fin 6) :
    fieldLinear F e v i = e (v i) := rfl

/-- The natural semilinear action in the six nonscalar coordinates. -/
def coordinateRepresentation : Representation (ZMod 2) (Actor F) (Coordinates F) where
  toFun z := ((Restricted.NaturalCoordinates.action F) z.left).restrictScalars (ZMod 2) ∘ₗ
    (fieldLinear F z.right).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro v
    change Restricted.NaturalCoordinates.action F 1 v = v
    rw [map_one]
    rfl
  map_mul' x y := by
    apply LinearMap.ext
    intro v
    change Restricted.NaturalCoordinates.action F
      (x.left * fieldEquiv x.right y.left) (fun i => x.right (y.right (v i))) =
      Restricted.NaturalCoordinates.action F x.left
        (fun i => x.right (Restricted.NaturalCoordinates.action F y.left
          (fun j => y.right (v j)) i))
    rw [map_mul, Module.End.mul_apply, action_fieldEquiv]

@[simp] theorem coordinateRepresentation_apply (z : Actor F) (v : Coordinates F) :
    coordinateRepresentation F z v = Restricted.NaturalCoordinates.action F z.left
      (fun i => z.right (v i)) := rfl

/-- Binary coordinates on the actual trace-zero quotient. -/
def coordinatesEquiv : Natural.Space F ≃ₗ[ZMod 2] Coordinates F :=
  (Restricted.NaturalCoordinates.equiv F).restrictScalars (ZMod 2)

/-- The action on the actual natural quotient, including the field subgroup. -/
def representation : Representation (ZMod 2) (Actor F) (Natural.Space F) :=
  (coordinatesEquiv F).symm.conjRingEquiv.toMonoidHom.comp (coordinateRepresentation F)

theorem coordinates_representation (z : Actor F) (v : Natural.Space F) :
    coordinatesEquiv F (representation F z v) =
      coordinateRepresentation F z (coordinatesEquiv F v) := by
  change coordinatesEquiv F ((coordinatesEquiv F).symm _) = _
  exact (coordinatesEquiv F).apply_symm_apply _

theorem representation_inner (g : Model F) (v : Natural.Space F) :
    representation F (SemidirectProduct.inl g) v = Natural.action F g v := by
  apply (coordinatesEquiv F).injective
  rw [coordinates_representation]
  exact (LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' g) v).symm

/-- Restriction to the linear factor is the actual natural action. -/
def innerRepresentation : Representation (ZMod 2) (Model F) (Natural.Space F) :=
  (representation F).comp SemidirectProduct.inl

/-- Binary field transport on the actual octonion quotient. -/
def fieldEquivalence (e : F ≃+* F) : Natural.Space F ≃ₗ[ZMod 2] Natural.Space F :=
  (coordinatesEquiv F).trans ((fieldLinear F e).trans (coordinatesEquiv F).symm)

theorem representation_field (e : F ≃+* F) (v : Natural.Space F) :
    representation F (SemidirectProduct.inr e) v = fieldEquivalence F e v := by
  apply (coordinatesEquiv F).injective
  rw [coordinates_representation]
  change Restricted.NaturalCoordinates.action F 1 _ = _
  rw [map_one]
  change _ = coordinatesEquiv F ((coordinatesEquiv F).symm _)
  rw [LinearEquiv.apply_symm_apply]
  rfl

/-- Field transport intertwines the genuine coefficient automorphism of G₂. -/
theorem fieldEquivalence_action (e : F ≃+* F) (g : Model F) (v : Natural.Space F) :
    fieldEquivalence F e (Natural.action F g v) =
      Natural.action F (fieldEquiv e g) (fieldEquivalence F e v) := by
  apply (coordinatesEquiv F).injective
  have h (x : Natural.Space F) : coordinatesEquiv F (fieldEquivalence F e x) =
      fieldLinear F e (coordinatesEquiv F x) := by
    exact (coordinatesEquiv F).apply_symm_apply _
  have ha (g : Model F) (x : Natural.Space F) :
      coordinatesEquiv F (Natural.action F g x) =
        Restricted.NaturalCoordinates.action F g (coordinatesEquiv F x) :=
    LinearMap.congr_fun ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' g) x
  rw [h, ha, ha, h]
  exact (action_fieldEquiv F e g _).symm

/-- The six coordinates identify the whole binary semilinear representation. -/
def coordinateEquivalence : Representation.RepEquiv (representation F)
    (coordinateRepresentation F) where
  toLinearEquiv := coordinatesEquiv F
  isIntertwining' z := LinearMap.ext (coordinates_representation F z)

section Four
abbrev Four := GaloisField 2 2

theorem finrank_four : Module.finrank (ZMod 2) (Natural.Space Four) = 12 := by
  rw [(coordinatesEquiv Four).finrank_eq]
  change Module.finrank (ZMod 2) (Fin 6 → Four) = 12
  rw [Module.finrank_pi_fintype]
  simp [GaloisField.finrank 2 (by decide : 2 ≠ 0)]

/-- The distinguished nontrivial coefficient involution of F₄. -/
noncomputable def fourFrobenius : Four ≃+* Four := frobeniusEquiv Four 2

@[simp] theorem fourFrobenius_apply (a : Four) : fourFrobenius a = a ^ 2 := rfl

theorem fourFrobenius_involutive : Function.Involutive fourFrobenius := by
  intro a
  change (a ^ 2) ^ 2 = a
  rw [← pow_mul]
  have hcard : Nat.card Four = 4 := GaloisField.card 2 2 (by decide)
  let := Fintype.ofFinite Four
  have h := FiniteField.pow_card a
  rw [← Nat.card_eq_fintype_card, hcard] at h
  exact h

theorem fieldEquivalence_fourFrobenius_involutive :
    Function.Involutive (fieldEquivalence Four fourFrobenius) := by
  intro v
  apply (coordinatesEquiv Four).injective
  change coordinatesEquiv Four ((coordinatesEquiv Four).symm _) = _
  simp only [LinearEquiv.apply_symm_apply]
  change (fun i => fourFrobenius ((coordinatesEquiv Four)
    ((coordinatesEquiv Four).symm (fun j => fourFrobenius (coordinatesEquiv Four v j))) i)) = _
  simp only [LinearEquiv.apply_symm_apply]
  funext i
  exact fourFrobenius_involutive _
end Four
end Atlas.G2.Natural.BinarySemilinear
