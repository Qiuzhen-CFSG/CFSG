module
public import Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.CubicAction
public import Theory.GroupTheory.ExtraspecialSquare
public import Mathlib.RepresentationTheory.Basic

/-!
# The literal twelve-dimensional orthogonal core action

The faithful H/Q action on Q/Z(Q) is linear over GF(2). Squaring gives
its invariant quadratic form, whose polar form is alternating and
nondegenerate. Singular vectors retain their exact interpretation as
squares equal to one in Q. These statements use the original core quotient
and conjugation maps, rather than a choice of coordinates or model module.

Source: Aschbacher–Segev, *The uniqueness of groups of type J₄*, Invent.
Math. 105 (1991), introduction to §4 and (4.1–2), printed p.597,
DOI 10.1007/BF01232280. This supplies the orthogonal action used in the
source's module identification, without assuming irreducibility.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
open Subgroup
variable {G : Type*} [Group G] [Finite G] {z : G} (h : IsTypeJ4 z)

variable [IsExtraspecial 2 (core z)]

/-- The source module is the additive form of the original central quotient. -/
abbrev CoreSpace := ExtraspecialSquare.Space (core z)

noncomputable def coreBinaryRepresentation :
    Representation (ZMod 2) (centralizer z ⧸ core z) (CoreSpace (z := z)) where
  toFun g := ((coreQuotientAction h g).toMonoidHom.toAdditive).toZModLinearMap 2
  map_one' := by ext v; exact congrArg Additive.ofMul (MulEquiv.congr_fun (map_one (coreQuotientAction h)) v.toMul)
  map_mul' a b := by
    ext v
    exact congrArg Additive.ofMul (MulEquiv.congr_fun ((coreQuotientAction h).map_mul a b) v.toMul)

@[simp] theorem coreBinaryRepresentation_apply (g : centralizer z ⧸ core z)
    (v : CoreSpace (z := z)) :
    coreBinaryRepresentation h g v = Additive.ofMul (coreQuotientAction h g v.toMul) := rfl

theorem coreBinaryRepresentation_injective : Function.Injective (coreBinaryRepresentation h) := by
  intro a b hab
  apply coreQuotientAction_injective h
  ext v
  exact congrArg Additive.toMul (LinearMap.congr_fun hab (Additive.ofMul v))

include h in
theorem coreSpace_finrank : Module.finrank (ZMod 2) (CoreSpace (z := z)) = 12 :=
  ExtraspecialSquare.space_finrank (core z) 12 h.core_card

noncomputable def coreQuadraticForm : QuadraticForm (ZMod 2) (CoreSpace (z := z)) :=
  ExtraspecialSquare.form (core z)

theorem coreQuadraticForm_invariant (g : centralizer z ⧸ core z)
    (v : CoreSpace (z := z)) :
    coreQuadraticForm (z := z) (coreBinaryRepresentation h g v) = coreQuadraticForm (z := z) v := by
  obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective (core z) g
  exact ExtraspecialSquare.form_invariant (core z) (MulAut.conjNormal g) v.toMul

omit [Finite G] in
theorem coreQuadraticForm_nondegenerate : (coreQuadraticForm (z := z)).polarBilin.Nondegenerate :=
  ExtraspecialSquare.polar_nondegenerate (core z)

omit [Finite G] in
theorem coreQuadraticForm_polar_alt : (coreQuadraticForm (z := z)).polarBilin.IsAlt := by
  intro v
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self]
  rw [two_nsmul]
  exact (show ∀ c : ZMod 2, c + c = 0 by decide) _

theorem coreQuadraticForm_polar_invariant (g : centralizer z ⧸ core z)
    (v w : CoreSpace (z := z)) :
    (coreQuadraticForm (z := z)).polarBilin (coreBinaryRepresentation h g v) (coreBinaryRepresentation h g w) =
      (coreQuadraticForm (z := z)).polarBilin v w := by
  simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar,
    ← map_add (coreBinaryRepresentation h g), coreQuadraticForm_invariant]

omit [Finite G] in
/-- Singular vectors correspond to elements whose square is the identity,
with the original quotient map. -/
theorem coreQuadraticForm_mk_eq_zero (q : core z) :
    coreQuadraticForm (z := z) (Additive.ofMul (QuotientGroup.mk' (center (core z)) q)) = 0 ↔ q^2=1 :=
  ExtraspecialSquare.form_mk_eq_zero (core z) q

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition
end
