module

public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Order.Enumeration
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Order of the marked subgroup of M₂₄

The checked list contains 1024 distinct positive words in the four marked
Witt-design permutations and is stable under left multiplication by every
generator. Each such transition is injective, hence surjective on the finite
list, so the list is also stable under multiplication by inverse generators.
Closure induction proves that it exhausts `candidate`.

This establishes the cardinality input to the Sylow normalizer calculation;
the source context is Aschbacher–Smith, printed p.511, and GLS3, Table 5.3e.
-/

public section
namespace Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.OrderEnumeration

noncomputable def evaluate : List (Fin 4) → M24
  | [] => 1
  | a :: w => generator a * evaluate w

theorem evaluate_mem (w : List (Fin 4)) : evaluate w ∈ candidate := by
  induction w with
  | nil => exact candidate.one_mem
  | cons a w ih => exact candidate.mul_mem (generator_mem a) ih

theorem evaluate_apply (w : List (Fin 4)) (x : Fin 24) :
    (evaluate w).val x = evaluatePoint w x := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    change generatorPerm a ((evaluate w).val x) = _
    rw [generatorPerm_apply, ih]
    rfl

noncomputable def element (i : Fin 1024) : candidate :=
  ⟨evaluate (words i), evaluate_mem (words i)⟩

theorem element_apply (i : Fin 1024) (x : Fin 24) :
    (element i).val.val x = point i x := evaluate_apply _ _

theorem element_injective : Function.Injective element := by
  intro i j h
  apply (Fin.strictMono_iff_lt_succ.mpr key_lt_succ).injective
  have hp (x : Fin 24) : point i x = point j x := by
    rw [← element_apply, ← element_apply, h]
  simp only [key, hp]

theorem element_identity : element identityIndex = 1 := by
  apply Subtype.ext
  change evaluate (words identityIndex) = 1
  rw [words_identityIndex]
  rfl

theorem element_step (a : Fin 4) (i : Fin 1024) :
    element (step a i) = markedGenerator a * element i := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (element (step a i)).val.val x = generatorPerm a ((element i).val.val x)
  rw [element_apply, generatorPerm_apply, element_apply, point_step]

theorem element_coe_step (a : Fin 4) (i : Fin 1024) :
    (element (step a i) : M24) = generator a * (element i : M24) :=
  congrArg Subtype.val (element_step a i)

theorem step_surjective (a : Fin 4) : Function.Surjective (step a) := by
  apply Finite.surjective_of_injective
  intro i j h
  apply element_injective
  apply mul_left_cancel (a := markedGenerator a)
  rw [← element_step, ← element_step, h]

theorem element_surjective : Function.Surjective element := by
  intro x
  have hex : ∃ i, (element i : M24) = x := by
    apply Subgroup.closure_induction_left (s := Set.range generator)
      (p := fun y _ => ∃ i, (element i : M24) = y) ?_ ?_ ?_ x.property
    · exact ⟨identityIndex, congrArg Subtype.val element_identity⟩
    · intro g hg y _ hy
      obtain ⟨a, rfl⟩ := hg
      obtain ⟨i, rfl⟩ := hy
      exact ⟨step a i, element_coe_step a i⟩
    · intro g hg y _ hy
      obtain ⟨a, rfl⟩ := hg
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨j, hj⟩ := step_surjective a i
      refine ⟨j, ?_⟩
      rw [← hj, element_coe_step, inv_mul_cancel_left]
  obtain ⟨i, hi⟩ := hex
  exact ⟨i, Subtype.ext hi⟩

end Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer.OrderEnumeration

namespace Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer

theorem candidate_card : Nat.card candidate = 1024 := by
  rw [← Nat.card_congr (Equiv.ofBijective OrderEnumeration.element
    ⟨OrderEnumeration.element_injective, OrderEnumeration.element_surjective⟩), Nat.card_fin]

end Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer
