module

public import Theory.SpecificGroups.G2.PRegularClasses.Torus
public import Theory.AtlasPort.LinearGroups.G2.WeylMaps

/-!
# Separation of split G₂ torus elements by their characteristic polynomials

The octonion torus weights are two reciprocal triples, each of product one.
The coefficients of degrees seven and six determine the two triple sums as an
unordered pair. If the sums match in order, evaluation of their common cubic
matches one weight; cancellation then matches the other two, even when roots
repeat. The explicit octonion Weyl maps realize the required permutations.
Swapping the two triple sums is also realized by a Weyl map.

Thus equality of characteristic polynomials gives conjugacy within the actual
split-octonion automorphism group for torus elements. A torus-normal-form
hypothesis then gives the same conclusion for arbitrary odd-order elements.
There is no rational-descent assertion in this module.

Source context: the semisimple geometry behind GLS III, Section 2.8
(`refs/KGroup/GLS3/chapter2.tex`), used in Aschbacher--Smith G.9.3,
printed pp.356–357. The concrete Weyl maps are from the licensed ATLAS port
`Theory.AtlasPort.LinearGroups.G2.WeylMaps`; see `LICENSES/ATLAS.txt`.
-/

public section

open Atlas.SplitOctonion Polynomial

namespace Atlas.G2.PRegularClasses.RationalFusion

variable {F : Type*} [Field F]

private theorem conjR (l m : Fˣ) : IsConj (torus l m) (torus l (l * m⁻¹)) := by
  apply isConj_iff.mpr
  refine ⟨weylR, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;>
    simp [weylR, weylREquiv, weylRLinear, weylRApply,
      torus, torusEquiv, torusLinear, torusWeights]
  all_goals field_simp
  all_goals simp

private theorem conjS (l m : Fˣ) : IsConj (torus l m) (torus m l) := by
  apply isConj_iff.mpr
  refine ⟨weylS, ?_⟩
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;>
    simp [weylS, weylSEquiv, weylSLinear, weylSApply,
      torus, torusEquiv, torusLinear, torusWeights]
  all_goals field_simp
  all_goals simp

private theorem conjRS (l m : Fˣ) : IsConj (torus l m) (torus (l * m⁻¹) l) :=
  (conjR l m).trans (conjS l (l * m⁻¹))

private theorem conjCycle (l m : Fˣ) : IsConj (torus l m) (torus m⁻¹ (l * m⁻¹)) := by
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    (conjRS l m).trans (conjRS (l * m⁻¹) l)

private theorem same_first (l m n : Fˣ) (h : torusA l m = torusA l n) :
    n = m ∨ n = l * m⁻¹ := by
  have hz : ((n : F) - (m : F)) * ((n : F) * (m : F) - (l : F)) = 0 := by
    have h' := h
    simp only [torusA, Units.val_mul, Units.val_inv_eq_inv_val] at h'
    field_simp at h'
    linear_combination -h'
  rcases mul_eq_zero.mp hz with h₁ | h₂
  · exact Or.inl (Units.ext (sub_eq_zero.mp h₁))
  · right
    apply eq_mul_inv_iff_mul_eq.mpr
    exact Units.ext (sub_eq_zero.mp h₂)

private theorem torusA_cycle (l m : Fˣ) :
    torusA m⁻¹ (l * m⁻¹) = torusA l m := by
  simp [torusA]
  ring

private theorem cubic (l m : Fˣ) (x : F) :
    (x - (l : F)) * (x - (↑(l⁻¹ * m) : F)) * (x - (↑m⁻¹ : F)) =
      x ^ 3 - torusA l m * x ^ 2 + torusB l m * x - 1 := by
  simp only [torusA, torusB, Units.val_mul, Units.val_inv_eq_inv_val]
  field_simp
  ring

private theorem conj_of_AB (l m a b : Fˣ)
    (hA : torusA l m = torusA a b) (hB : torusB l m = torusB a b) :
    IsConj (torus l m) (torus a b) := by
  have hz : ((a : F) - (l : F)) * ((a : F) - (↑(l⁻¹ * m) : F)) *
      ((a : F) - (↑m⁻¹ : F)) = 0 := by
    rw [cubic, hA, hB, ← cubic a b]
    simp
  have hf (u v : Fˣ) (hc : IsConj (torus l m) (torus u v))
      (hu : torusA u v = torusA a b) (ha : a = u) :
      IsConj (torus l m) (torus a b) := by
    subst a
    rcases same_first u v b hu with rfl | rfl
    · exact hc
    · exact hc.trans (conjR u v)
  rcases mul_eq_zero.mp hz with hz | hz
  · rcases mul_eq_zero.mp hz with hz | hz
    · exact hf l m (IsConj.refl _) hA (Units.ext (sub_eq_zero.mp hz))
    · have hc := (conjCycle l m).trans (conjCycle m⁻¹ (l * m⁻¹))
      have ha : a = (l * m⁻¹)⁻¹ := by
        apply Units.ext
        simpa [mul_comm] using sub_eq_zero.mp hz
      exact hf _ _ hc (by rw [torusA_cycle, torusA_cycle]; exact hA) ha
  · exact hf _ _ (conjCycle l m) (by rw [torusA_cycle]; exact hA)
      (Units.ext (sub_eq_zero.mp hz))

private theorem unordered_pair {a b c d : F} (hs : a + b = c + d)
    (hp : a * b = c * d) : (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hz : (a - c) * (a - d) = 0 := by
    linear_combination a * hs - hp
  rcases mul_eq_zero.mp hz with hc | hd
  · left
    have hc := sub_eq_zero.mp hc
    exact ⟨hc, by linear_combination hs - hc⟩
  · right
    have hd := sub_eq_zero.mp hd
    exact ⟨hd, by linear_combination hs - hd⟩

/-- Characteristic polynomials separate split torus elements inside the actual G₂ model. -/
theorem torus_isConj_of_charpoly_eq [CharP F 2] (l m a b : Fˣ)
    (hp : charpoly (torus l m) = charpoly (torus a b)) :
    IsConj (torus l m) (torus a b) := by
  rw [charpoly_torus, charpoly_torus] at hp
  have hs : torusA l m + torusB l m = torusA a b + torusB a b := by
    simpa only [classPolynomial_coeff_seven] using
      congrArg (fun p : F[X] => p.coeff 7) hp
  have ht : torusA l m * torusB l m + torusA l m + torusB l m + 1 =
      torusA a b * torusB a b + torusA a b + torusB a b + 1 := by
    simpa only [classPolynomial_coeff_six] using
      congrArg (fun p : F[X] => p.coeff 6) hp
  have hm : torusA l m * torusB l m = torusA a b * torusB a b := by
    linear_combination ht - hs
  rcases unordered_pair hs hm with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · exact conj_of_AB l m a b hA hB
  · have hswapA : torusA b a = torusB a b := by simp [torusA, torusB, mul_comm]
    have hswapB : torusB b a = torusA a b := by simp [torusA, torusB, mul_comm]
    exact (conj_of_AB l m b a (hA.trans hswapA.symm) (hB.trans hswapB.symm)).trans
      (conjS b a)

/-- Torus normal form and the concrete Weyl maps separate all odd-order classes
over the field on which normal form is available. -/
theorem isConj_of_charpoly_eq_of_torus_normal_form [CharP F 2]
    (hgeom : ∀ x : Model F, ¬ 2 ∣ orderOf x → ∃ l m : Fˣ, IsConj x (torus l m))
    (g h : Model F) (hg : ¬ 2 ∣ orderOf g) (hh : ¬ 2 ∣ orderOf h)
    (hp : charpoly g = charpoly h) : IsConj g h := by
  obtain ⟨l, m, hc⟩ := hgeom g hg
  obtain ⟨a, b, hd⟩ := hgeom h hh
  apply hc.trans
  apply IsConj.trans _ hd.symm
  apply torus_isConj_of_charpoly_eq
  exact (charpoly_eq_of_isConj _ _ hc).symm.trans (hp.trans (charpoly_eq_of_isConj _ _ hd))

end Atlas.G2.PRegularClasses.RationalFusion
