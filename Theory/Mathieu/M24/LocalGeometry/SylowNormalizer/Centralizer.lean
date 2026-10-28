module

public import Theory.Mathieu.M24.LocalGeometry.SylowNormalizer.Generators
public import Mathlib.GroupTheory.PGroup

/-!
# The centralizer of the marked M₂₄ subgroup has exponent two

Every point is reached from point 1 or point 3 by a short word in the four
marked generators. A commuting permutation is therefore determined by its
images of those two points. Short words fixing the representatives restrict
their images to {1,20} and {3,19}. The four resulting maps have square one,
as checked in the kernel. This proves the two-group bound without assuming a centralizer
table, the order of the marked subgroup, or a Sylow assertion.

Source context: the Sylow-normalizer calculation supporting Aschbacher–Smith,
printed p.511, and the concrete degree-24 model in GLS3, Table 5.3e.
-/

@[expose] public section
namespace Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer
set_option maxRecDepth 100000

def orbitBase : Fin 24 → Fin 24 := ![3,1,1,3,3,1,1,1,3,3,1,3,1,1,1,1,1,1,1,3,1,3,1,1]

def orbitWord : Fin 24 → List (Fin 4)
  | 0 => [1,2]
  | 1 => []
  | 2 => [3,0,2,0]
  | 3 => []
  | 4 => [0,0]
  | 5 => [1,0]
  | 6 => [0,0,0]
  | 7 => [1,0,0,0]
  | 8 => [3,0]
  | 9 => [0]
  | 10 => [1,2,0]
  | 11 => [1]
  | 12 => [3,0,1,0]
  | 13 => [0,1,2,0]
  | 14 => [2,0]
  | 15 => [0]
  | 16 => [2,0,1,0]
  | 17 => [3,2,0]
  | 18 => [0,1,0]
  | 19 => [2]
  | 20 => [0,0]
  | 21 => [1,0]
  | 22 => [0,2,0]
  | _ => [2,0,0,0]

theorem orbitWord_reaches : ∀ x, evaluatePoint (orbitWord x) (orbitBase x) = x := by
  decide +kernel

def reconstruct (a b x : Fin 24) : Fin 24 :=
  evaluatePoint (orbitWord x) (if orbitBase x = 1 then a else b)

private theorem fixed_one : ∀ x, evaluatePoint [1,2] x = x →
    generatorPoint 3 x = x → x = 1 ∨ x = 20 := by decide +kernel

private theorem fixed_three : ∀ x, evaluatePoint [0,1] x = x →
    x = 3 ∨ x = 19 := by decide +kernel

private theorem reconstruct_square (a b : Fin 24) (ha : a = 1 ∨ a = 20)
    (hb : b = 3 ∨ b = 19) : ∀ x, reconstruct a b (reconstruct a b x) = x := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide +kernel

private theorem commute_evaluatePoint (g : Equiv.Perm (Fin 24))
    (h : ∀ i x, g (generatorPoint i x) = generatorPoint i (g x))
    (w : List (Fin 4)) (x : Fin 24) :
    g (evaluatePoint w x) = evaluatePoint w (g x) := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [evaluatePoint, h, ih, evaluatePoint]

private theorem eq_reconstruct (g : Equiv.Perm (Fin 24))
    (h : ∀ i x, g (generatorPoint i x) = generatorPoint i (g x)) (x : Fin 24) :
    g x = reconstruct (g 1) (g 3) x := by
  have hb : g (orbitBase x) = if orbitBase x = 1 then g 1 else g 3 := by
    fin_cases x <;> rfl
  calc
    g x = g (evaluatePoint (orbitWord x) (orbitBase x)) := by rw [orbitWord_reaches]
    _ = evaluatePoint (orbitWord x) (g (orbitBase x)) := commute_evaluatePoint g h _ _
    _ = reconstruct (g 1) (g 3) x := by rw [hb]; rfl

/-- Every permutation commuting with the four marked generators has square one. -/
theorem square_eq_one_of_commute (g : Equiv.Perm (Fin 24))
    (h : ∀ i, Commute g (generatorPerm i)) : g ^ 2 = 1 := by
  have hc : ∀ i x, g (generatorPoint i x) = generatorPoint i (g x) := by
    intro i x
    simpa only [Equiv.Perm.mul_apply, generatorPerm_apply] using
      congrArg (fun p : Equiv.Perm (Fin 24) => p x) (h i).eq
  have he := eq_reconstruct g hc
  have ha : g 1 = 1 ∨ g 1 = 20 := by
    apply fixed_one
    · have h := commute_evaluatePoint g hc [1,2] 1
      rw [show evaluatePoint [1,2] 1 = 1 by decide +kernel] at h
      exact h.symm
    · have h := hc 3 1
      rw [show generatorPoint 3 1 = 1 by decide +kernel] at h
      exact h.symm
  have hb : g 3 = 3 ∨ g 3 = 19 := by
    apply fixed_three
    have h := commute_evaluatePoint g hc [0,1] 3
    rw [show evaluatePoint [0,1] 3 = 3 by decide +kernel] at h
    exact h.symm
  apply Equiv.ext
  intro x
  simp only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
  rw [he (g x), he x, reconstruct_square _ _ ha hb]

/-- The centralizer in the actual M₂₄ carrier is a two-group. -/
theorem centralizer_isPGroup :
    IsPGroup 2 (Subgroup.centralizer (candidate : Set M24)) := by
  intro g
  refine ⟨1, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change (g.val.val : Equiv.Perm (Fin 24)) ^ 2 = 1
  apply square_eq_one_of_commute
  intro i
  have hc := (Subgroup.mem_centralizer_iff.mp g.property) (generator i) (generator_mem i)
  exact (congrArg (fun x : M24 => (x : Equiv.Perm (Fin 24))) hc).symm

end Sporadic.Mathieu.M24LocalGeometry.SylowNormalizer
