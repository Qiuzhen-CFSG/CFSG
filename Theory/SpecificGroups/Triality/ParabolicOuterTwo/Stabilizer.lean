module
public import Theory.SpecificGroups.Triality.ParabolicOuterTwo.Actions
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# The actual triality local stabilizer and its quotient action

Restrict automorphisms preserving the root-defined local factor, then descend
through its intrinsic two-core. The action agrees with the shared cubic
coefficient action and takes conjugation by a local element to conjugation by
its actual quotient image. This is the action on which local innerness is tested
in Aschbacher–Smith F.1.12, printed p.264; see also GLS3 §§2.5–2.6.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.ParabolicOuterTwo
open Parabolics OuterOdd
open scoped Pointwise

/-- Actual automorphisms preserving the root-defined local factor. -/
def localStabilizer (P : Parameters) (a : Node) : Subgroup (MulAut (Carrier P)) :=
  MulAction.stabilizer (MulAut (Carrier P)) (localFactor P a)

theorem mem_localStabilizer (P : Parameters) (a : Node) (σ : MulAut (Carrier P)) :
    σ ∈ localStabilizer P a ↔ (localFactor P a).map σ.toMonoidHom = localFactor P a := Iff.rfl

/-- Restriction of these literal automorphisms to the local factor. -/
def localRestriction (P : Parameters) (a : Node) :
    localStabilizer P a →* MulAut (localFactor P a) where
  toFun σ := restrictCoefficientSubgroup σ.val _ σ.property
  map_one' := by ext x; rfl
  map_mul' σ τ := by ext x; rfl

@[simp] theorem localRestriction_val (P : Parameters) (a : Node)
    (σ : localStabilizer P a) (x : localFactor P a) :
    (localRestriction P a σ x).val = σ.val x := rfl

/-- The actual quotient action used to test local innerness. -/
def localQuotientAction (P : Parameters) (a : Node) :
    localStabilizer P a →* MulAut (LocalTwoQuotient P a) :=
  (Subgroup.quotientAut (pCore 2 (localFactor P a))).comp (localRestriction P a)

@[simp] theorem localQuotientAction_mk (P : Parameters) (a : Node)
    (σ : localStabilizer P a) (x : localFactor P a) :
    localQuotientAction P a σ (QuotientGroup.mk' (pCore 2 (localFactor P a)) x) =
      QuotientGroup.mk' (pCore 2 (localFactor P a)) (localRestriction P a σ x) :=
  Subgroup.quotientAut_apply_mk _ _ _

/-- The shared cubic coefficient action takes values in this actual stabilizer. -/
def coefficientStabilizer (P : Parameters) (a : Node) :
    CoefficientAut P →* localStabilizer P a :=
  (coefficientAction P).codRestrict _ (fun e => coefficient_localFactor P e a)

theorem localQuotientAction_coefficient (P : Parameters) (a : Node) (e : CoefficientAut P) :
    localQuotientAction P a (coefficientStabilizer P a e) =
      coefficientLocalTwoQuotient P e a := by
  ext x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (localFactor P a)) x
  rw [localQuotientAction_mk, coefficientLocalTwoQuotient_mk]
  apply congrArg (QuotientGroup.mk' (pCore 2 (localFactor P a)))
  apply Subtype.ext
  rfl

/-- Conjugation by local-factor elements, retaining their embedding in the carrier. -/
def localInner (P : Parameters) (a : Node) :
    localFactor P a →* localStabilizer P a :=
  (MulAut.conj.comp (localFactor P a).subtype).codRestrict _ (by
    intro x
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((localFactor P a).le_normalizer x.property))

theorem localQuotientAction_localInner (P : Parameters) (a : Node)
    (x : localFactor P a) :
    localQuotientAction P a (localInner P a x) =
      MulAut.conj (QuotientGroup.mk' (pCore 2 (localFactor P a)) x) := by
  ext z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 (localFactor P a)) z
  rw [localQuotientAction_mk]
  change QuotientGroup.mk' (pCore 2 (localFactor P a)) (x * g * x⁻¹) = _
  simp only [map_mul, map_inv, MulAut.conj_apply]

end Triality.Standard.ParabolicOuterTwo
