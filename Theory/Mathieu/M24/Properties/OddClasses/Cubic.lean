module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.Representatives
public import Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.SylowThree
public import Theory.GroupTheory.SylowElementConjugacy
import all Theory.Representation.Mathieu.M24DegreeSpectrum.ElevenTrace.SylowThree
import all Theory.Mathieu.M24.Properties.Sylow3

/-!
# Two cubic classes cover native M₂₄

Sylow conjugacy places every order-three element in the certified subgroup of
order 27. Its nonidentity coordinates are fused to the fifth power of the
marked element of order 15 or the seventh power of the marked element of order
21. Three ambient words and short words in the existing Sylow normalizer
certify this finite calculation. Every point identity is checked by the kernel.

The internal `import all` edges deliberately reuse the existing coordinate and
normalizer evaluators without changing their public boundaries. Public results
refer only to native group elements and the published marked representatives.
The class-bound consumer is `OddClasses.lean`.

Source: the ATLAS M24 conjugacy data,
https://brauer.maths.qmul.ac.uk/Atlas/v3/spor/M24/ (classes 3A and 3B).
GAP is only an untrusted witness finder; `source/` retains the reproducer.
-/

namespace Sporadic.Mathieu.M24OddClasses
open M24OddCyclic

/-- Marked representatives of the two cubic classes. -/
@[expose] public noncomputable def cubicRepresentative (i : Fin 2) : M24 :=
  if i = 0 then representative 0 ^ 5 else representative 1 ^ 7

private def bridgePerm : Fin 3 → Equiv.Perm (Fin 24)
  | 0 =>
    { toFun := ![15, 22, 13, 17, 11, 3, 23, 2, 12, 5, 9, 4, 6, 1, 18, 10, 0, 19, 14, 20, 16, 7, 8, 21]
      invFun := ![16, 13, 7, 5, 11, 9, 12, 21, 22, 10, 15, 4, 8, 2, 18, 0, 20, 3, 14, 17, 19, 23, 1, 6]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  | 1 =>
    { toFun := ![21, 8, 3, 23, 22, 6, 4, 20, 18, 2, 7, 1, 19, 14, 16, 17, 15, 9, 12, 5, 13, 11, 0, 10]
      invFun := ![22, 11, 9, 2, 6, 19, 5, 10, 1, 17, 23, 21, 18, 20, 13, 16, 14, 15, 8, 12, 7, 0, 4, 3]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  | _ =>
    { toFun := ![3, 18, 14, 2, 8, 4, 13, 0, 6, 12, 20, 19, 15, 16, 9, 23, 1, 17, 22, 7, 5, 21, 10, 11]
      invFun := ![7, 16, 3, 0, 5, 20, 8, 19, 4, 14, 22, 23, 9, 6, 2, 12, 13, 17, 1, 11, 10, 21, 18, 15]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }

private def bridgeWord : Fin 3 → List (Fin 3)
  | 0 => [1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1]
  | 1 => [1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2]
  | _ => [0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 2, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 1, 0, 1, 0, 2, 0, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2]

private theorem bridge_word (i : Fin 3) :
    bridgePerm i = (Words.evaluate (bridgeWord i)).val := by
  have h : ∀ i x, bridgePerm i x = Words.wordPoint (bridgeWord i) x := by
    decide +kernel
  apply Equiv.ext
  intro x
  rw [Words.evaluate_apply]
  exact h i x

private noncomputable def bridge (i : Fin 3) : M24 :=
  ⟨bridgePerm i, (bridge_word i).symm ▸ (Words.evaluate (bridgeWord i)).property⟩

private def bridgeIndex : (Fin 3 × Fin 3 × Fin 3) → Fin 3
  | (0, 0, 0) => 0
  | (0, 0, 1) => 0
  | (0, 0, 2) => 0
  | (0, 1, 0) => 1
  | (0, 1, 1) => 1
  | (0, 1, 2) => 1
  | (0, 2, 0) => 1
  | (0, 2, 1) => 1
  | (0, 2, 2) => 1
  | (1, 0, 0) => 1
  | (1, 0, 1) => 1
  | (1, 0, 2) => 1
  | (1, 1, 0) => 2
  | (1, 1, 1) => 2
  | (1, 1, 2) => 2
  | (1, 2, 0) => 2
  | (1, 2, 1) => 2
  | (1, 2, 2) => 2
  | (2, 0, 0) => 1
  | (2, 0, 1) => 1
  | (2, 0, 2) => 1
  | (2, 1, 0) => 2
  | (2, 1, 1) => 2
  | (2, 1, 2) => 2
  | (2, 2, 0) => 2
  | (2, 2, 1) => 2
  | (2, 2, 2) => 2

private def fusionWord : (Fin 3 × Fin 3 × Fin 3) → List (Fin 4)
  | (0, 0, 0) => []
  | (0, 0, 1) => []
  | (0, 0, 2) => [3, 0, 3, 1, 3, 3, 1, 2, 0, 2, 0, 3, 3]
  | (0, 1, 0) => []
  | (0, 1, 1) => [3, 1, 3, 3, 3, 0, 3, 3, 3]
  | (0, 1, 2) => [3, 1, 3, 3, 3, 3, 3, 1, 2, 0, 2, 0, 3, 3]
  | (0, 2, 0) => [3, 3, 1, 3, 1, 2]
  | (0, 2, 1) => [3, 3, 1, 3, 1, 3, 3, 3]
  | (0, 2, 2) => [3, 3, 1, 3, 1, 1, 3, 3, 1, 2, 0, 2, 0, 3, 3]
  | (1, 0, 0) => [2, 0, 3, 3, 3]
  | (1, 0, 1) => [1, 3, 1, 3, 3, 3, 0, 3]
  | (1, 0, 2) => [2, 0]
  | (1, 1, 0) => []
  | (1, 1, 1) => [1, 2, 0, 2, 0, 3, 3]
  | (1, 1, 2) => [3, 0, 2]
  | (1, 2, 0) => [3, 0, 3, 3]
  | (1, 2, 1) => [1, 3, 3, 1, 3, 1, 3, 3]
  | (1, 2, 2) => [2, 2, 0, 2, 1, 3, 3, 1, 2, 0, 2, 0, 3, 3]
  | (2, 0, 0) => [3, 3, 0, 3, 3, 3]
  | (2, 0, 1) => [2, 2, 0, 3]
  | (2, 0, 2) => [2, 2, 1, 3, 1, 3, 0, 2, 2, 0, 3, 0, 2, 0, 2, 2, 0, 2]
  | (2, 1, 0) => [2, 2, 0, 2]
  | (2, 1, 1) => [1, 3, 3, 1, 3, 1, 2, 2, 1, 3, 3, 1, 2, 0, 2, 0, 3, 3]
  | (2, 1, 2) => [3, 3, 3, 1, 2, 0, 2, 0, 3, 3]
  | (2, 2, 0) => [2, 2, 0, 2, 2]
  | (2, 2, 1) => [1, 3, 3, 1, 3, 1, 3, 3, 3, 1, 3, 3, 1, 2, 0, 2, 0, 3, 3]
  | (2, 2, 2) => [3, 0, 3, 3, 3, 1, 3, 3, 1, 2, 0, 2, 0, 3, 3]

private def targetIndex : Fin 3 → Fin 2 := ![0, 0, 1]

private def conjugatorPoint (t : Fin 3 × Fin 3 × Fin 3) (x : Fin 24) : Fin 24 :=
  bridgePerm (bridgeIndex t) (M24OddCyclic.localPoint (fusionWord t) x)

private noncomputable def fusionConjugator (t : Fin 3 × Fin 3 × Fin 3) : M24 :=
  bridge (bridgeIndex t) * M24OddCyclic.localEvaluate (fusionWord t)

private theorem fusionConjugator_apply (t : Fin 3 × Fin 3 × Fin 3) (x : Fin 24) :
    (fusionConjugator t).val x = conjugatorPoint t x := by
  change bridgePerm (bridgeIndex t) ((M24OddCyclic.localEvaluate (fusionWord t)).val x) = _
  rw [M24OddCyclic.localEvaluate_apply]
  rfl

private def cubicPoint (i : Fin 2) : Fin 24 → Fin 24 :=
  if i = 0 then (representativePerm 0 ^ 5 : Equiv.Perm (Fin 24))
  else (representativePerm 1 ^ 7 : Equiv.Perm (Fin 24))

private theorem cubicRepresentative_apply (i : Fin 2) (x : Fin 24) :
    (cubicRepresentative i).val x = cubicPoint i x := by
  fin_cases i <;> simp [cubicRepresentative, cubicPoint]

private theorem fusion_check : ∀ (t : Fin 3 × Fin 3 × Fin 3), t ≠ (0, 0, 0) →
    ∀ x : Fin 24,
      conjugatorPoint t (M24OddCyclic.point t x) =
        cubicPoint (targetIndex (bridgeIndex t)) (conjugatorPoint t x) := by
  decide +kernel

private theorem conjugacy_of_points (g h c : M24)
    (he : ∀ x : Fin 24, c.val (g.val x) = h.val (c.val x)) : IsConj g h := by
  refine isConj_iff.mpr ⟨c, ?_⟩
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  exact Equiv.ext he

/-- Every nonidentity element of the literal Sylow subgroup has one of two classes. -/
public theorem sylowThree_cubic_coverage (g : M24)
    (hg : g ∈ m24Sylow3Subgroup) (hne : g ≠ 1) :
    ∃ i : Fin 2, IsConj g (cubicRepresentative i) := by
  obtain ⟨t, rfl⟩ := hg
  have ht : t ≠ (0, 0, 0) := by
    rintro rfl
    exact hne Sporadic.Mathieu.evaluate_one
  refine ⟨targetIndex (bridgeIndex t), ?_⟩
  apply conjugacy_of_points _ _ (fusionConjugator t)
  intro x
  rw [fusionConjugator_apply, fusionConjugator_apply,
    M24OddCyclic.point_spec, cubicRepresentative_apply]
  exact fusion_check t ht x

/-- The two marked cubic classes cover every native element of order three. -/
public theorem order_three_coverage (g : M24) (hg : orderOf g = 3) :
    ∃ i : Fin 2, IsConj g (cubicRepresentative i) := by
  obtain ⟨y, hy⟩ := m24Sylow3.exists_isConj_of_orderOf_eq_prime_pow
    (hg.trans (pow_one 3).symm)
  have hne : (y : M24) ≠ 1 := by
    intro he
    have ho : g = 1 := isConj_one_left.mp (he ▸ hy)
    rw [ho, orderOf_one] at hg
    omega
  obtain ⟨i, hi⟩ := sylowThree_cubic_coverage y y.property hne
  exact ⟨i, hy.trans hi⟩

end Sporadic.Mathieu.M24OddClasses
