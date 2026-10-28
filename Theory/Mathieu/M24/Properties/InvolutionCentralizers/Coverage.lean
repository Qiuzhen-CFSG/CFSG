module

public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.FusionData
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Order
public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Reduction
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Exhaustive involution coverage in the Witt-design M₂₄

Every involution is conjugate into the certified subgroup of order 1024,
which is Sylow by the established order of M₂₄. The checked words fuse all
involutions in that subgroup to the two marked representatives. This proves
coverage without assuming any centralizer table or structural classification.

Source: Aschbacher–Smith 16.1.5(7), printed p.1171; GLS3, Table 5.3e.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24InvolutionCentralizers
open M24LocalGeometry.SylowNormalizer

namespace FusionData

theorem letter_mem (i : Fin 3) : letterPerm i ∈ M24 := by
  fin_cases i
  · exact m24GeneratorA_mem
  · exact m24GeneratorB_mem
  · exact M24.inv_mem m24GeneratorB_mem

noncomputable def letter (i : Fin 3) : M24 := ⟨letterPerm i, letter_mem i⟩

noncomputable def evaluate : List (Fin 3) → M24
  | [] => 1
  | i :: w => letter i * evaluate w

theorem evaluate_apply (w : List (Fin 3)) (x : Fin 24) :
    (evaluate w).val x = wordPoint w x := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change letterPerm i ((evaluate w).val x) = _
    rw [letterPoint_spec, ih]
    rfl

noncomputable def base (a : Bool) : M24 :=
  if a then involution2A else involution2B

theorem base_apply (a : Bool) (x : Fin 24) : (base a).val x = basePoint a x := by
  cases a
  · change m24Involution2B x = _
    exact basePoint_spec false x
  · change m24Involution2A x = _
    exact basePoint_spec true x

/-- The exact fusion of every involution in the certified enumeration. -/
theorem element_fusion (i : Fin 1024)
    (hsq : (OrderEnumeration.element i).val ^ 2 = 1)
    (hne : (OrderEnumeration.element i).val ≠ 1) :
    IsConj involution2A (OrderEnumeration.element i).val ∨
      IsConj involution2B (OrderEnumeration.element i).val := by
  have hi : i ≠ 0 := by
    rintro rfl
    exact hne (congrArg Subtype.val OrderEnumeration.element_identity)
  have hp : OrderEnumeration.point i (OrderEnumeration.point i (badPoint i)) = badPoint i := by
    have hh := congrArg (fun x : M24 => x.val (badPoint i)) hsq
    simpa only [pow_two, Subgroup.coe_mul, Equiv.Perm.mul_apply,
      OrderEnumeration.element_apply, Subgroup.coe_one, Equiv.Perm.one_apply] using hh
  let g := evaluate (word i)
  have hg : g * base (tag i) = (OrderEnumeration.element i).val * g := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    change g.val ((base (tag i)).val x) = (OrderEnumeration.element i).val.val (g.val x)
    rw [base_apply, evaluate_apply, evaluate_apply, OrderEnumeration.element_apply]
    exact fusion_check i hi hp x
  have hc : IsConj (base (tag i)) (OrderEnumeration.element i).val :=
    isConj_iff.mpr ⟨g, (mul_inv_eq_iff_eq_mul).mpr hg⟩
  cases h : tag i
  · exact Or.inr (by simpa only [base, h, Bool.false_eq_true, ↓reduceIte] using hc)
  · exact Or.inl (by simpa only [base, h, ↓reduceIte] using hc)

end FusionData

/-- Every involution of the actual Witt-design M₂₄ is conjugate to a marked representative. -/
theorem involution_classes (x : M24) (hx : orderOf x = 2) :
    IsConj involution2A x ∨ IsConj involution2B x := by
  have hind : ¬ 2 ∣ candidate.index := by
    have hc := candidate.card_mul_index
    rw [candidate_card, m24_order] at hc
    have he : candidate.index = 239085 := by omega
    rw [he]
    decide
  let S : Sylow 2 M24 := (IsPGroup.of_card (p := 2) (n := 10) candidate_card).toSylow hind
  obtain ⟨y, hy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow
    (hx.trans (pow_one 2).symm)
  obtain ⟨i, hi⟩ := OrderEnumeration.element_surjective y
  obtain ⟨g, hg⟩ := isConj_iff.mp hy
  have he : (MulAut.conj g) x = (OrderEnumeration.element i).val :=
    hg.trans (congrArg Subtype.val hi).symm
  have hsq : (OrderEnumeration.element i).val ^ 2 = 1 := by
    rw [← he, ← map_pow, (orderOf_eq_prime_iff.mp hx).1, map_one]
  have hne : (OrderEnumeration.element i).val ≠ 1 := by
    intro h
    exact (orderOf_eq_prime_iff.mp hx).2
      ((MulAut.conj g).injective (he.trans (h.trans (map_one _).symm)))
  have hc : IsConj x (OrderEnumeration.element i).val := isConj_iff.mpr ⟨g, he⟩
  rcases FusionData.element_fusion i hsq hne with h | h
  · exact Or.inl (h.trans hc.symm)
  · exact Or.inr (h.trans hc.symm)

end Sporadic.Mathieu.M24InvolutionCentralizers
