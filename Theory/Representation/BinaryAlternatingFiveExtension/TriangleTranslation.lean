module
public import Theory.Representation.BinaryAlternatingFiveExtension.CubicFixedDecomposition
public import Theory.Representation.BinaryAlternatingFiveExtension.BorelModel

/-!
# A translation aligning the actual cubic inverter

An involution in the binary affine A₅ group that inverts a standard cubic
has a translation part fixed by that cubic and its quotient inverter. The
fixed-vector difference theorem chooses a correcting translation that
centralizes the entire A₄ point stabilizer. Conjugating the full complement
by this translation therefore retains the point section and contains the
original involution.
-/

public section
open Subgroup
namespace BinaryPermutation.AlternatingFiveExtension.TriangleTranslation
open AlternatingFiveBorel

/-- The actual alternating action on the binary five-point core. -/
abbrev action : alternatingGroup (Fin 5) →* MulAut V :=
  coreAction.comp (alternatingGroup (Fin 5)).subtype

/-- The binary affine group with its original alternating quotient. -/
abbrev Model := V ⋊[action] alternatingGroup (Fin 5)

private theorem vector_neg (v : core (Fin 5)) : -v = v := by
  apply Subtype.ext
  funext i
  exact CharTwo.neg_eq _

/-- The correcting translation centralizes the full standard A₄ and puts the
literal cubic-inverting involution into that same conjugated A₅ complement. -/
theorem inverter_translation (s : alternatingGroup (Fin 5))
    (hs : orderOf s = 3) (hB : s ∈ B) (y : Model) (hy : y ^ 2 = 1)
    (hi : y * SemidirectProduct.inr s * y⁻¹ = SemidirectProduct.inr s⁻¹) :
    ∃ b : V,
      (∀ g : alternatingGroup (Fin 5), g ∈ B →
        Commute (SemidirectProduct.inl b : Model) (SemidirectProduct.inr g)) ∧
      y = SemidirectProduct.inl b * SemidirectProduct.inr y.right *
        (SemidirectProduct.inl b : Model)⁻¹ ∧
      y ∈ (SemidirectProduct.inr : alternatingGroup (Fin 5) →* Model).range.map
        (MulAut.conj (SemidirectProduct.inl b)).toMonoidHom := by
  let t := y.right
  let v := y.left.toAdd
  have ht : t ^ 2 = 1 := by
    simpa only [pow_two, SemidirectProduct.mul_right, SemidirectProduct.one_right]
      using congrArg SemidirectProduct.right hy
  have hit : t * s * t⁻¹ = s⁻¹ := by
    simpa only [SemidirectProduct.mul_right, SemidirectProduct.inv_right,
      SemidirectProduct.right_inr] using congrArg SemidirectProduct.right hi
  have htfix : coreRepresentation (Fin 5) t.val v = v := by
    have hh := congrArg (fun x : Model => x.left.toAdd) hy
    rw [pow_two] at hh
    change v + coreRepresentation (Fin 5) t.val v = 0 at hh
    exact (eq_neg_of_add_eq_zero_right hh).trans (vector_neg v)
  have hsfix : coreRepresentation (Fin 5) s.val v = v := by
    have hm : y * SemidirectProduct.inr s = SemidirectProduct.inr s⁻¹ * y :=
      mul_inv_eq_iff_eq_mul.mp hi
    have hh := congrArg (fun x : Model => x.left.toAdd) hm
    change v + coreRepresentation (Fin 5) t.val 0 =
      0 + coreRepresentation (Fin 5) (s⁻¹).val v at hh
    rw [map_zero, add_zero, zero_add] at hh
    apply Subtype.ext
    funext i
    change v.val (s.val.symm i) = v.val i
    have he := congrArg (fun w : core (Fin 5) => w.val (s.val.symm i)) hh
    change v.val (s.val.symm i) = v.val (s.val (s.val.symm i)) at he
    simpa only [Equiv.apply_symm_apply] using he
  obtain ⟨w, hw, hdiff⟩ := cubic_inverter_fixed_difference s t hs hB ht hit v hsfix htfix
  let b : V := Multiplicative.ofAdd (-w)
  have hcomm (g : alternatingGroup (Fin 5)) (hg : g ∈ B) :
      Commute (SemidirectProduct.inl b : Model) (SemidirectProduct.inr g) := by
    apply SemidirectProduct.ext
    · change -w + coreRepresentation (Fin 5) 1 0 =
        0 + coreRepresentation (Fin 5) g.val (-w)
      rw [map_zero, add_zero, zero_add, map_neg, hw g hg]
    · simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl,
        SemidirectProduct.right_inr, one_mul, mul_one]
  have he : y = SemidirectProduct.inl b * SemidirectProduct.inr t *
      (SemidirectProduct.inl b : Model)⁻¹ := by
    apply SemidirectProduct.ext
    · change v = (-w + coreRepresentation (Fin 5) 1 0) +
        coreRepresentation (Fin 5) t.val (coreRepresentation (Fin 5) 1 (- -w))
      rw [map_zero, add_zero, neg_neg, map_one, Module.End.one_apply]
      simpa only [sub_eq_add_neg, add_comm] using hdiff
    · simp only [SemidirectProduct.mul_right, SemidirectProduct.right_inl,
        SemidirectProduct.right_inr, SemidirectProduct.inv_right, one_mul, inv_one, mul_one]
      rfl
  exact ⟨b, hcomm, he, ⟨SemidirectProduct.inr t, ⟨t,rfl⟩, he.symm⟩⟩

end BinaryPermutation.AlternatingFiveExtension.TriangleTranslation
