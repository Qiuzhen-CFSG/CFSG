module

public import Theory.Character.NilpotentBrauerIdeal
public import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Maximal ideals of the character ring

Every maximal ideal of the character ring is the inverse image of a maximal
ideal of the algebraic integers under evaluation at a group element.

Embed the character ring into the finite product of copies of the algebraic
integers. This is an integral extension because the product is integral over
the integers. Lying over gives a maximal ideal of the product. One coordinate
idempotent survives in its residue field, so membership is detected by that
coordinate, followed by reduction modulo a maximal ideal of the algebraic integers.

Source: the character-ring proof of Brauer induction in Serre,
*Linear Representations of Finite Groups*, Chapter 10; lying over for integral
extensions and the description of prime ideals of a finite product.
-/

public section

open scoped BigOperators
noncomputable section
namespace BrauerInduction
variable {G : Type*} [Group G] [Fintype G]

private abbrev A := integralClosure ℤ ℂ
private def evaluations : characterRing G →+* (G → A) :=
  RingHom.pi fun g => characterEvaluation g

private theorem evaluations_injective : Function.Injective (evaluations (G := G)) := by
  intro f h heq
  apply Subtype.ext
  funext g
  exact congrArg Subtype.val (congrFun heq g)

/-- A maximal ideal of the character ring is evaluation modulo a maximal ideal
of the algebraic integers. -/
theorem exists_maximal_evaluation (M : Ideal (characterRing G)) [M.IsMaximal] :
    ∃ (g : G) (P : Ideal (integralClosure ℤ ℂ)),
      P.IsMaximal ∧ M = P.comap (characterEvaluation g) := by
  classical
  let : Algebra (characterRing G) (G → A) := (evaluations (G := G)).toAlgebra
  let : Algebra.IsIntegral ℤ (G → A) := Algebra.IsIntegral.trans A
  let : Algebra.IsIntegral (characterRing G) (G → A) := Algebra.IsIntegral.tower_top ℤ
  have hker : RingHom.ker (algebraMap (characterRing G) (G → A)) ≤ M := by
    have heq : RingHom.ker (evaluations (G := G)) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp evaluations_injective
    change RingHom.ker (evaluations (G := G)) ≤ M
    rw [heq]
    exact bot_le
  obtain ⟨Q, hQ, hQM⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral M hker
  let := hQ
  obtain ⟨g, hg⟩ : ∃ g : G, Pi.single g (1 : A) ∉ Q := by
    by_contra! h
    have hone : (1 : G → A) ∈ Q := by
      rw [← Finset.univ_sum_single (1 : G → A)]
      exact Q.sum_mem fun g _ => h g
    exact hQ.ne_top (Ideal.eq_top_of_isUnit_mem Q hone isUnit_one)
  let P : Ideal A := Q.comap (algebraMap A (G → A))
  have hP : P.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  have heval (f : G → A) : f ∈ Q ↔ (fun _ : G => f g) ∈ Q := by
    have hzero : Pi.single g (1 : A) * (f - fun _ : G => f g) = 0 := by
      ext x
      by_cases hx : x = g
      · subst x; simp
      · simp [hx]
    have hdiff : (f - fun _ : G => f g) ∈ Q :=
      (hQ.isPrime.mem_or_mem (hzero ▸ Q.zero_mem)).resolve_left hg
    constructor
    · intro hf
      simpa only [sub_sub_cancel] using Q.sub_mem hf hdiff
    · intro hf
      simpa only [sub_add_cancel] using Q.add_mem hdiff hf
  refine ⟨g, P, hP, ?_⟩
  rw [← hQM]
  ext f
  exact heval (evaluations f)
end BrauerInduction
