module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.LinearCoordinates
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.Parameters
public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.PairRigidity.BlockParameters.FieldRecovery.SuzukiCoordinates.SplitBlock

/-!
# Complete coordinates on both signed Suzuki fixed blocks

The four-root collection and matrix-entry uniqueness in `SplitBlock` describe
all elements of the positive middle block. The supplied twist's scalar fixed
equations give exactly the literal type V word
`x_α(t) x_β(θ(t)) x_(α+2β)(u) x_(α+β)(t*θ(t)+θ(u))`.
Collecting products gives `(t+v, u+w+θ(t)^2*v)`. The fixed opposition
representative transports the coordinates and all their properties to the
negative block. No global split-factorization or semilinearity hypothesis is
used, and every calculation includes `m = 0`.

Source: GLS3, Table 2.4 type V and §2.4,
`refs/KGroup/GLS3/chapter2.tex`. The four-root collection and the initial
coordinate assembly were recovered from the retained Suzuki-coordinate attempt.
-/

@[expose] public noncomputable section
namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery.SuzukiChart
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open LargeLocalSeeds Subgroup Parabolics RadicalCoordinates FixedCoordinates
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
variable {m : ℕ}
def parameters (t u : CoefficientField m) : Fin 4 → CoefficientField m :=
  ![t, theta m t, t * theta m t + theta m u, u]

theorem positive_roots :
    suzukiRoots true = ![roots 0, roots 1, roots 3, roots 2] := by
  simp only [suzukiRoots, roots, signedRoot, ↓reduceIte,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons]

private theorem quartetWord_swap_last (r : Fin 4 → F4Chevalley.Root)
    (p : Fin 4 → CoefficientField m)
    (h : Commute (rootGeneratorInGroup m (r 3) (p 3))
      (rootGeneratorInGroup m (r 2) (p 2))) :
    quartetWord m ![r 0, r 1, r 3, r 2] ![p 0, p 1, p 3, p 2] =
      quartetWord m r p := h.right_comm _

theorem word_eq (t u : CoefficientField m) :
    suzukiWord m true t u = splitWord m (parameters t u) := by
  calc
    _ = quartetWord m (suzukiRoots true)
        ![t, theta m t, u, t * theta m t + theta m u] := rfl
    _ = quartetWord m ![roots 0, roots 1, roots 3, roots 2]
        ![t, theta m t, u, t * theta m t + theta m u] :=
      congrArg (fun r => quartetWord m r ![t, theta m t, u, t * theta m t + theta m u])
        positive_roots
    _ = _ := quartetWord_swap_last roots (parameters t u) (commute23 _ _).symm

theorem theta_eq_halfFrobenius : theta m = halfFrobenius m := rfl

theorem parameters_fixed (t u : CoefficientField m) :
    quartetTwist m (parameters t u) = parameters t u := by
  apply (quartetTwist_fixed_iff m _).mpr
  ext i
  fin_cases i <;>
    simp [parameters, quartetSolution, Matrix.cons_val_two, Matrix.cons_val_three,
      theta_eq_halfFrobenius, titsEnd_halfFrobenius, map_add, map_mul,
      CharTwo.add_self_eq_zero, add_comm, add_left_comm, mul_comm]

theorem positive_fixed (d : LocalBlockInput m) (t u : CoefficientField m) :
    suzukiWord m true t u ∈ d.fixedGroup := by
  rw [d.mem_fixedGroup, word_eq, twist_splitWord, parameters_fixed]

theorem positive_mem (t u : CoefficientField m) :
    suzukiWord m true t u ∈ splitSimpleBlock m .suzuki true := by
  rw [word_eq]
  exact splitWord_mem _

theorem positive_injective : Function.Injective
    (fun p : CoefficientField m × CoefficientField m => suzukiWord m true p.1 p.2) := by
  intro p q h
  change suzukiWord m true p.1 p.2 = suzukiWord m true q.1 q.2 at h
  rw [word_eq, word_eq] at h
  have he := splitWord_injective h
  exact Prod.ext (congrFun he 0) (congrFun he 3)

theorem positive_cover (d : LocalBlockInput m) (x : d.fixedGroup)
    (hx : x ∈ simpleBlock d .suzuki true) :
    ∃ t u, suzukiWord m true t u = x.val := by
  obtain ⟨p, hp⟩ := splitWord_cover hx
  change splitWord m p = x.val at hp
  have hf : quartetTwist m p = p := by
    apply splitWord_injective
    rw [← twist_splitWord d, hp]
    exact x.property
  have hb : theta m (p 0) = p 1 := congrFun hf 1
  have hc : titsEnd m (p 1) * theta m (p 0) + theta m (p 3) = p 2 := congrFun hf 2
  rw [← hb, show theta m = halfFrobenius m from rfl, titsEnd_halfFrobenius] at hc
  refine ⟨p 0, p 3, ?_⟩
  rw [word_eq, ← hp]
  congr 1
  ext i
  fin_cases i
  · rfl
  · exact hb
  · exact hc
  · rfl

theorem positive_mul (t u v w : CoefficientField m) :
    suzukiWord m true t u * suzukiWord m true v w =
      suzukiWord m true (t + v) (u + w + (theta m t) ^ 2 * v) := by
  rw [word_eq, word_eq, splitWord_mul, word_eq]
  congr 1
  ext i
  fin_cases i
  · rfl
  · exact (map_add (theta m) t v).symm
  · change t * theta m t + theta m u + (v * theta m v + theta m w) + v * theta m t =
      (t + v) * theta m (t + v) + theta m (u + w + theta m t ^ 2 * v)
    have hf : theta m (theta m t ^ 2) = t := by
      change halfFrobenius m (halfFrobenius m t ^ 2) = t
      rw [halfFrobenius_sq, halfFrobenius_titsEnd]
    rw [map_add, map_add, map_add, map_mul, hf]
    linear_combination (norm := ring_nf) -(CharTwo.add_self_eq_zero (t * theta m v))
  · change u + w + v * theta m t ^ 2 = u + w + theta m t ^ 2 * v
    rw [mul_comm v]



/-- Opposition preserves the scalar parameters in the literal type V word. -/
theorem opposition_word (t u : CoefficientField m) :
    MulAut.conj (PairNormalization.splitOpposition m) (suzukiWord m true t u) =
      suzukiWord m false t u := by
  simp only [suzukiWord, map_mul, MulAut.conj_apply,
    PairNormalization.splitOpposition_conj_root]
  rfl

theorem negative_fixed (d : LocalBlockInput m) (t u : CoefficientField m) :
    suzukiWord m false t u ∈ d.fixedGroup := by
  rw [← opposition_word]
  exact d.fixedGroup.mul_mem
    (d.fixedGroup.mul_mem (PairNormalization.opposition d).property (positive_fixed d t u))
    (d.fixedGroup.inv_mem (PairNormalization.opposition d).property)

theorem negative_mem (t u : CoefficientField m) :
    suzukiWord m false t u ∈ splitSimpleBlock m .suzuki false := by
  rw [← opposition_word, ← splitOpposition_map_simpleBlock .suzuki]
  exact ⟨suzukiWord m true t u, positive_mem t u, rfl⟩

theorem negative_injective : Function.Injective
    (fun p : CoefficientField m × CoefficientField m => suzukiWord m false p.1 p.2) := by
  intro p q h
  change suzukiWord m false p.1 p.2 = suzukiWord m false q.1 q.2 at h
  rw [← opposition_word, ← opposition_word] at h
  exact positive_injective ((MulAut.conj (PairNormalization.splitOpposition m)).injective h)

theorem negative_cover (d : LocalBlockInput m) (x : d.fixedGroup)
    (hx : x ∈ simpleBlock d .suzuki false) :
    ∃ t u, suzukiWord m false t u = x.val := by
  rw [← opposition_map_simpleBlock d .suzuki] at hx
  obtain ⟨y, hy, he⟩ := hx
  obtain ⟨t, u, hw⟩ := positive_cover d y hy
  refine ⟨t, u, ?_⟩
  rw [← opposition_word, hw]
  exact congrArg Subtype.val he

theorem negative_mul (t u v w : CoefficientField m) :
    suzukiWord m false t u * suzukiWord m false v w =
      suzukiWord m false (t + v) (u + w + (theta m t) ^ 2 * v) := by
  rw [← opposition_word, ← opposition_word, ← map_mul, positive_mul, opposition_word]

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery.SuzukiChart

namespace ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery


/-- The literal type V coordinates cover both complete signed fixed intersections,
with the source product law, for every supplied Ree twist, including `m = 0`. -/
theorem suzukiCoordinates {m : ℕ} (d : LocalBlockInput m) : SuzukiCoordinates d where
  suzuki_fixed positive := by
    cases positive
    · exact SuzukiChart.negative_fixed d
    · exact SuzukiChart.positive_fixed d
  suzuki_mem positive := by
    cases positive
    · exact SuzukiChart.negative_mem
    · exact SuzukiChart.positive_mem
  suzuki_injective positive := by
    cases positive
    · exact SuzukiChart.negative_injective
    · exact SuzukiChart.positive_injective
  suzuki_cover positive := by
    cases positive
    · exact SuzukiChart.negative_cover d
    · exact SuzukiChart.positive_cover d
  suzuki_mul positive := by
    cases positive
    · exact SuzukiChart.negative_mul
    · exact SuzukiChart.positive_mul

end ReeF4.LocalBlockInput.PairRigidity.BlockParameters.FieldRecovery
