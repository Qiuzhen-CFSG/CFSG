module

public import Theory.Representation.SL2NaturalOffenders.Semilinear
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.Algebra.Module.End

/-!
# Restricting the two scalar fields to the common natural plane

An injective copy of the natural SL₂(F) plane lies in an E-module. The old
E-scalars preserve this copy and the natural actors are E-linear. Pulling
scalars back along the injection gives a ring homomorphism to the additive
endomorphisms of the plane. The additive SL₂ commutant calculation makes
these endomorphisms F-scalars. When the field orders agree, this constructs
an actual field isomorphism, identifies both restriction images, and
transports the E-module so its scalars agree with the original plane.
Every previously linear actor stays linear after this transport.

This is the restriction argument of Aschbacher--Smith, combined manuscript
(1 March 2004), Lemma 11.3.8, printed p.775. The application to the literal
P intersect V is in `CompatibleCartan/SourceFields`. No field compatibility
or equality of endomorphism rings is a hypothesis here.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
variable {E F A : Type*} [Field E] [Field F] [AddCommGroup A] [Module E A]

/-- A natural plane inside a separately marked module, before identifying fields. -/
structure NaturalPlane where
  inclusion : (Fin 2 → F) →+ A
  injective : Function.Injective inclusion
  scalar_closed : ∀ a : E, ∀ v, ∃ w, inclusion w = a • inclusion v
  actor : Matrix.SpecialLinearGroup (Fin 2) F → Module.End E A
  intertwines : ∀ g v, inclusion (g.val.mulVec v) = actor g (inclusion v)

namespace NaturalPlane
variable (N : NaturalPlane (E := E) (F := F) (A := A))

def restrictScalar (a : E) : AddMonoid.End (Fin 2 → F) where
  toFun v := (N.scalar_closed a v).choose
  map_zero' := by
    apply N.injective
    rw [(N.scalar_closed a 0).choose_spec, map_zero, smul_zero]
  map_add' v w := by
    apply N.injective
    rw [(N.scalar_closed a (v + w)).choose_spec, map_add, map_add,
      (N.scalar_closed a v).choose_spec, (N.scalar_closed a w).choose_spec, smul_add]

theorem inclusion_restrictScalar (a : E) (v : Fin 2 → F) :
    N.inclusion (N.restrictScalar a v) = a • N.inclusion v :=
  (N.scalar_closed a v).choose_spec

/-- Restriction is a ring map, not merely an identification of equal orders. -/
def restriction : E →+* AddMonoid.End (Fin 2 → F) where
  toFun := N.restrictScalar
  map_one' := by
    apply AddMonoidHom.ext
    intro v
    apply N.injective
    change N.inclusion (N.restrictScalar 1 v) = N.inclusion v
    rw [inclusion_restrictScalar, one_smul]
  map_mul' a b := by
    apply AddMonoidHom.ext
    intro v
    apply N.injective
    change N.inclusion (N.restrictScalar (a * b) v) =
      N.inclusion (N.restrictScalar a (N.restrictScalar b v))
    rw [inclusion_restrictScalar, inclusion_restrictScalar, inclusion_restrictScalar, mul_smul]
  map_zero' := by
    apply AddMonoidHom.ext
    intro v
    apply N.injective
    change N.inclusion (N.restrictScalar 0 v) = N.inclusion 0
    rw [inclusion_restrictScalar, zero_smul, map_zero]
  map_add' a b := by
    apply AddMonoidHom.ext
    intro v
    apply N.injective
    change N.inclusion (N.restrictScalar (a + b) v) =
      N.inclusion (N.restrictScalar a v + N.restrictScalar b v)
    rw [inclusion_restrictScalar, map_add, inclusion_restrictScalar,
      inclusion_restrictScalar, add_smul]

theorem restriction_commutes (a : E) (g : Matrix.SpecialLinearGroup (Fin 2) F)
    (v : Fin 2 → F) :
    N.restriction a (g.val.mulVec v) = g.val.mulVec (N.restriction a v) := by
  apply N.injective
  change N.inclusion (N.restrictScalar a (g.val.mulVec v)) =
    N.inclusion (g.val.mulVec (N.restrictScalar a v))
  rw [inclusion_restrictScalar, N.intertwines, N.intertwines,
    inclusion_restrictScalar, map_smul]

private theorem restriction_scalar (a : E) :
    ∃ b : F, ∀ v, N.restriction a v = b • v :=
  Representation.SL2NaturalOffenders.centralizer_scalar _ (N.restriction_commutes a)

/-- Read the coefficient of the restricted endomorphism on a nonzero vector. -/
def coefficient (a : E) : F := N.restriction a ![1, 0] 0

theorem restriction_eq_smul (a : E) (v : Fin 2 → F) :
    N.restriction a v = N.coefficient a • v := by
  obtain ⟨b, hb⟩ := N.restriction_scalar a
  have hc : N.coefficient a = b := by simp [coefficient, hb]
  rw [hc]
  exact hb v

/-- The scalar on the common plane depends homomorphically on the old scalar. -/
def coefficientHom : E →+* F where
  toFun := N.coefficient
  map_one' := by simp [coefficient]
  map_mul' a b := by
    change N.restriction (a * b) ![1, 0] 0 = N.coefficient a * N.coefficient b
    rw [map_mul]
    change N.restriction a (N.restriction b ![1, 0]) 0 = _
    rw [restriction_eq_smul, restriction_eq_smul]
    simp
  map_zero' := by simp [coefficient]
  map_add' a b := by
    change N.restriction (a + b) ![1, 0] 0 = _
    rw [map_add]
    rfl

/-- The literal restriction diagram commutes with scalar multiplication. -/
theorem inclusion_coefficient (a : E) (v : Fin 2 → F) :
    N.inclusion (N.coefficientHom a • v) = a • N.inclusion v := by
  change N.inclusion (N.coefficient a • v) = _
  rw [← restriction_eq_smul]
  exact N.inclusion_restrictScalar a v

variable [Finite F]

/-- Equal field orders turn the constructed restriction map into an isomorphism. -/
def fieldEquiv (hc : Nat.card E = Nat.card F) : E ≃+* F :=
  RingEquiv.ofBijective N.coefficientHom (by
    exact (Nat.bijective_iff_injective_and_card _).mpr ⟨N.coefficientHom.injective, hc⟩)

/-- The image of restriction is exactly the field of scalar endomorphisms. -/
theorem restriction_range (hc : Nat.card E = Nat.card F) :
    N.restriction.range = (Module.toAddMonoidEnd F (Fin 2 → F)).range := by
  ext f
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨N.coefficientHom a, ?_⟩
    apply AddMonoidHom.ext
    intro v
    exact (N.restriction_eq_smul a v).symm
  · rintro ⟨b, rfl⟩
    obtain ⟨a, ha⟩ := (N.fieldEquiv hc).surjective b
    refine ⟨a, ?_⟩
    apply AddMonoidHom.ext
    intro v
    change N.restriction a v = b • v
    rw [N.restriction_eq_smul]
    exact congrArg (fun c : F => c • v) ha

/-- Transport the old scalars by the inverse restriction isomorphism. -/
@[instance_reducible] def compatibleModule (hc : Nat.card E = Nat.card F) : Module F A :=
  Module.compHom A (N.fieldEquiv hc).symm.toRingHom

/-- With the transported structure, the common plane has its original scalars. -/
theorem compatible_smul (hc : Nat.card E = Nat.card F) (a : F) (v : Fin 2 → F) :
    letI := N.compatibleModule hc
    a • N.inclusion v = N.inclusion (a • v) := by
  change (N.fieldEquiv hc).symm a • N.inclusion v = _
  rw [← N.inclusion_coefficient]
  exact congrArg (fun b : F => N.inclusion (b • v)) ((N.fieldEquiv hc).apply_symm_apply a)

/-- Every old linear actor is linear for the transported field structure. -/
def compatibleEnd (hc : Nat.card E = Nat.card F) (f : Module.End E A) :
    letI := N.compatibleModule hc
    Module.End F A := by
  letI := N.compatibleModule hc
  exact { f.toAddMonoidHom with
    map_smul' := fun a v => f.map_smul ((N.fieldEquiv hc).symm a) v }

end NaturalPlane
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CompatibleCartan
