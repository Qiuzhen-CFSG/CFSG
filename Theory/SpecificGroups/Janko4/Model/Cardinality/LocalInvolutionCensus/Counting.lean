module

public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalInvolutionCensus.Representatives
public import Mathlib.Tactic.Group

/-!
# Bounding a local conjugacy class by one quotient fiber

Conjugators in the actual image Q lift to H. Choosing one lift for each image
of a conjugacy class gives a surjection from the product of the image class
and the class's fiber over its representative. Thus their cardinalities
multiply to an upper bound, without any distinctness or splitting premise.

This is the counting step needed for the local orbit certificates motivated
by Aschbacher--Smith, `refs/quasithin.pdf`, pp.64--65, A.6.1--4.
-/

@[expose] public section
namespace Janko4.Cardinality.LocalInvolutionCensus

/-- Conjugacy inside the actual row quotient image. -/
def quotientClass (v : Q) : Set Q := {w | IsConj v w}

/-- The part of a local class lying over the representative's quotient image. -/
def classFiber (r : H) : Set H := {u | IsConj r u ∧ q u = q r}

/-- A single quotient fiber bounds the whole local conjugacy class. -/
theorem localClass_card_le_quotient_mul_fiber (r : H) :
    Nat.card (localClass r) ≤
      Nat.card (quotientClass (q r)) * Nat.card (classFiber r) := by
  classical
  have hchoose (v : quotientClass (q r)) :
      ∃ g : H, q g * q r * (q g)⁻¹ = v.val := by
    obtain ⟨c, hc⟩ := isConj_iff.mp v.property
    obtain ⟨g, rfl⟩ := q_surjective c
    exact ⟨g, hc⟩
  choose g hg using hchoose
  let f : quotientClass (q r) × classFiber r → localClass r := fun p =>
    ⟨g p.1 * p.2.val * (g p.1)⁻¹,
      p.2.property.1.trans (isConj_iff.mpr ⟨g p.1, rfl⟩)⟩
  have hsurj : Function.Surjective f := by
    intro u
    let v : quotientClass (q r) := ⟨q u.val, q.map_isConj u.property⟩
    let w : H := (g v)⁻¹ * u.val * g v
    have hwc : IsConj r w := u.property.trans (isConj_iff.mpr ⟨(g v)⁻¹, by
      simp only [w, inv_inv]⟩)
    have hwq : q w = q r := by
      change q ((g v)⁻¹ * u.val * g v) = q r
      rw [map_mul, map_mul, map_inv]
      have hv : q (g v) * q r * (q (g v))⁻¹ = q u.val := hg v
      rw [← hv]
      group
    refine ⟨(v, ⟨w, hwc, hwq⟩), ?_⟩
    apply Subtype.ext
    change g v * ((g v)⁻¹ * u.val * g v) * (g v)⁻¹ = u.val
    group
  have hle := Nat.card_le_card_of_surjective f hsurj
  rwa [Nat.card_prod] at hle

/-- A quotient bound and a single representative's fiber bound suffice for
that representative's local class bound. -/
theorem representative_class_bound_of_quotient_and_fiber
    (i : Fin 11)
    (hquotient : Nat.card (quotientClass (q (lift (fiberIndex i)))) ≤
      quotientBound (fiberIndex i))
    (hfiber : Nat.card (classFiber (representative i)) ≤ fiberBound i) :
    Nat.card (localClass (representative i)) ≤
      quotientBound (fiberIndex i) * fiberBound i := by
  apply (localClass_card_le_quotient_mul_fiber (representative i)).trans
  rw [q_representative]
  exact Nat.mul_le_mul hquotient hfiber

end Janko4.Cardinality.LocalInvolutionCensus
