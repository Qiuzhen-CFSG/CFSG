module

public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine.TensorEmbedding
public import Theory.Representation.SL3.BinaryDefiningFactors.Classification.TensorSimplicity.FixedLine.FlagInterpolation
public import Theory.SpecificGroups.PSL3.RootPlaneGeometry
public import Mathlib.RepresentationTheory.Invariants

/-!
# Root-plane fixed spaces of binary SL₃ tensor words

For a word occupying at most one finite-field Frobenius period, the common
fixed space of either root plane has dimension at most `2^(a+b)`, where `a`
counts natural and dual factors and `b` counts adjoint factors.

Restrict the concrete orbit-coefficient polynomial to the complementary simple
root: the y-axis for the point radical and the x-axis for the line radical.
A fixed vector's coefficient on the whole upper group is determined by this
restriction. Finite-grid flag interpolation and the injective polynomial model
therefore make restriction injective on the common fixed space. Each restricted
factor is constant or linear, and the tail variables are squared at every
Frobenius position. A recursive coefficient space consequently has dimension
at most two to the number of nontrivial factors. Trivial positions retain their
Frobenius shift without increasing this dimension bound.

The argument uses the literal root planes and tensor action, works for either
orientation and any coefficient embedding, and includes the field of order two.
It does not identify the two radicals by inner conjugacy or assert a half-degree
bound for arbitrary irreducible modules.

Source: the SL₃ tensor-degree step of Guralnick–Malle, *Classification of
2F-modules II*, author manuscript Proposition 4.7, pp.25–26, as used in
Aschbacher–Smith K.3.2, printed pp.454–456. The polynomial model implements
GLS III, 2.8.6(a), 2.8.9 and 2.8.10(c).
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct MatrixGroups
open MvPolynomial Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3.RootPlaneGeometry
namespace Representation.SL3.BinaryDefiningFactors.ParabolicFixed
open TensorSimplicity.FixedLine
variable (K : Type*) [Field K]

/-- Retain the complementary simple-root coordinate. -/
def restrictAxis (side : Bool) : MvPolynomial (Fin 3) K →ₐ[K] MvPolynomial (Fin 3) K :=
  MvPolynomial.aeval fun i => if i = (if side then 1 else 0) then X i else 0

private def shift (side : Bool) : MvPolynomial (Fin 3) K →ₗ[K] MvPolynomial (Fin 3) K :=
  LinearMap.mulLeft K (X (if side then 1 else 0)) ∘ₗ (squareVariables K).toLinearMap

private def coefficientSpace (side : Bool) : List Factor → Submodule K (MvPolynomial (Fin 3) K)
  | [] => (Algebra.ofId K (MvPolynomial (Fin 3) K)).toLinearMap.range
  | a :: w => if a = .trivial then
      (coefficientSpace side w).map (squareVariables K).toLinearMap
    else (coefficientSpace side w).map (squareVariables K).toLinearMap ⊔
      (coefficientSpace side w).map (shift K side)

private instance coefficientSpace_finite (side : Bool) (w : List Factor) :
    FiniteDimensional K (coefficientSpace K side w) := by
  induction w with
  | nil => dsimp [coefficientSpace]; infer_instance
  | cons a w ih =>
    by_cases ha : a = .trivial
    · rw [coefficientSpace, if_pos ha]; infer_instance
    · rw [coefficientSpace, if_neg ha]; infer_instance

private theorem coefficientSpace_finrank (side : Bool) (w : List Factor) :
    Module.finrank K (coefficientSpace K side w) ≤
      2 ^ (naturalCount w + adjointCount w) := by
  induction w with
  | nil =>
    simpa [coefficientSpace, naturalCount, adjointCount] using
      (LinearMap.finrank_range_le (Algebra.ofId K (MvPolynomial (Fin 3) K)).toLinearMap)
  | cons a w ih =>
    have h₀ := Submodule.finrank_map_le (squareVariables K).toLinearMap (coefficientSpace K side w)
    have h₁ := Submodule.finrank_map_le (shift K side) (coefficientSpace K side w)
    have hs := Submodule.finrank_add_le_finrank_add_finrank
      ((coefficientSpace K side w).map (squareVariables K).toLinearMap)
      ((coefficientSpace K side w).map (shift K side))
    have hh := hs.trans (Nat.add_le_add (h₀.trans ih) (h₁.trans ih))
    cases a with
    | trivial => simpa [coefficientSpace, naturalCount, adjointCount] using h₀.trans ih
    | natural =>
      simpa [coefficientSpace, naturalCount, adjointCount, Nat.add_right_comm,
        pow_succ, mul_two] using hh
    | dual =>
      simpa [coefficientSpace, naturalCount, adjointCount, Nat.add_right_comm,
        pow_succ, mul_two] using hh
    | adjoint =>
      simpa [coefficientSpace, naturalCount, adjointCount, ← Nat.add_assoc,
        pow_succ, mul_two] using hh

private theorem restrictAxis_square (side : Bool) (p : MvPolynomial (Fin 3) K) :
    restrictAxis K side (squareVariables K p) =
      squareVariables K (restrictAxis K side p) := by
  have h : (restrictAxis K side).comp (squareVariables K) =
      (squareVariables K).comp (restrictAxis K side) := by
    ext i
    simp only [AlgHom.comp_apply, squareVariables, restrictAxis, aeval_X, map_pow]
    split_ifs <;> simp
  exact AlgHom.congr_fun h p

private theorem restricted_factor_linear (side : Bool) (a : Factor) (v : Space K a) :
    ∃ c d : K, restrictAxis K side (factorPolynomial K a v) =
      C c + C d * X (if side then 1 else 0) := by
  cases side <;> cases a
  · change K at v
    refine ⟨v, 0, ?_⟩
    change restrictAxis K false (C v) = C v + C 0 * X 0
    simp [restrictAxis]
  · change (Fin 3 → K) at v
    refine ⟨v 0, v 1, ?_⟩
    change restrictAxis K false (∑ i : Fin 3, v i • leftRow K i) = _
    simp [leftRow, restrictAxis, Fin.sum_univ_three, Algebra.smul_def]
  · change Module.Dual K (Fin 3 → K) at v
    refine ⟨dualEntry K 2 v, 0, ?_⟩
    change restrictAxis K false (∑ i : Fin 3, dualEntry K i v • rightColumn K i) = _
    simp [rightColumn, restrictAxis, Fin.sum_univ_three, Algebra.smul_def]
  · change AdjointSpace K at v
    refine ⟨adjointEntry K 0 2 v, adjointEntry K 1 2 v, ?_⟩
    change restrictAxis K false (∑ i : Fin 3, ∑ j : Fin 3,
      adjointEntry K i j v • (leftRow K i * rightColumn K j)) = _
    simp [leftRow, rightColumn, restrictAxis, Fin.sum_univ_three, Algebra.smul_def]
  · change K at v
    refine ⟨v, 0, ?_⟩
    change restrictAxis K true (C v) = C v + C 0 * X 1
    simp [restrictAxis]
  · change (Fin 3 → K) at v
    refine ⟨v 0, 0, ?_⟩
    change restrictAxis K true (∑ i : Fin 3, v i • leftRow K i) = _
    simp [leftRow, restrictAxis, Fin.sum_univ_three, Algebra.smul_def]
  · change Module.Dual K (Fin 3 → K) at v
    refine ⟨dualEntry K 2 v, dualEntry K 1 v, ?_⟩
    change restrictAxis K true (∑ i : Fin 3, dualEntry K i v • rightColumn K i) = _
    simp [rightColumn, restrictAxis, Fin.sum_univ_three, Algebra.smul_def]
    exact add_comm _ _
  · change AdjointSpace K at v
    refine ⟨adjointEntry K 0 2 v, adjointEntry K 0 1 v, ?_⟩
    change restrictAxis K true (∑ i : Fin 3, ∑ j : Fin 3,
      adjointEntry K i j v • (leftRow K i * rightColumn K j)) = _
    simp [leftRow, rightColumn, restrictAxis, Fin.sum_univ_three, Algebra.smul_def]
    exact add_comm _ _

private theorem restricted_word_mem (side : Bool) (w : List Factor) (v : WordSpace K w) :
    restrictAxis K side (wordPolynomial K w v) ∈ coefficientSpace K side w := by
  induction w with
  | nil =>
    change K at v
    refine ⟨v, ?_⟩
    change C v = restrictAxis K side (C v)
    simp [restrictAxis]
  | cons a w ih =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | tmul v z =>
      rw [wordPolynomial_tmul, map_mul, restrictAxis_square]
      have hz : squareVariables K (restrictAxis K side (wordPolynomial K w z)) ∈
          (coefficientSpace K side w).map (squareVariables K).toLinearMap :=
        ⟨_, ih z, rfl⟩
      by_cases ha : a = .trivial
      · subst a
        change K at v
        change restrictAxis K side (C v) * _ ∈ _
        rw [show restrictAxis K side (C v) = C v by simp [restrictAxis]]
        simpa only [Algebra.smul_def, algebraMap_eq] using
          (coefficientSpace K side (.trivial :: w)).smul_mem v hz
      · obtain ⟨c,d,hd⟩ := restricted_factor_linear K side a v
        rw [hd]
        have hz' : X (if side then 1 else 0) *
            squareVariables K (restrictAxis K side (wordPolynomial K w z)) ∈
            (coefficientSpace K side w).map (shift K side) := ⟨_, ih z, rfl⟩
        rw [coefficientSpace, if_neg ha]
        have hh := ((coefficientSpace K side w).map (squareVariables K).toLinearMap ⊔
          (coefficientSpace K side w).map (shift K side)).add_mem
            (Submodule.smul_mem _ c (Submodule.mem_sup_left hz))
            (Submodule.smul_mem _ d (Submodule.mem_sup_right hz'))
        simpa only [Algebra.smul_def, algebraMap_eq, add_mul, mul_assoc] using hh

variable {K} {F : Type*} [Field F] [Finite F] [CharP K 2]

private def complement (side : Bool) (u : U F) : U F :=
  if side then ⟨0,u.y,0⟩ else ⟨u.x,0,0⟩

omit [Finite F] [CharP K 2] in
private theorem eval_restrictAxis (ι : F →+* K) (side : Bool) (u : U F)
    (p : MvPolynomial (Fin 3) K) :
    MvPolynomial.eval (point ι u) (restrictAxis K side p) =
      MvPolynomial.eval (point ι (complement side u)) p := by
  have h : (MvPolynomial.aeval (point ι u)).comp (restrictAxis K side) =
      MvPolynomial.aeval (point ι (complement side u)) := by
    ext i
    cases side <;> fin_cases i <;> simp [restrictAxis, point, complement]
  exact AlgHom.congr_fun h p

omit [Finite F] in
private theorem orbit_eq_complement (ι : F →+* K) (w : List Factor) (side : Bool)
    (v : WordSpace K w)
    (hv : v ∈ invariants ((wordRep ι w).comp (rootPlaneSL F side).subtype))
    (u : U F) :
    wordRep ι w (specialLinear F u) v =
      wordRep ι w (specialLinear F (complement side u)) v := by
  have hfix (r : U F) (hr : specialLinear F r ∈ rootPlaneSL F side) :
      wordRep ι w (specialLinear F r) v = v := hv ⟨_,hr⟩
  have hmul (c r : U F) (he : c * r = u)
      (hr : specialLinear F r ∈ rootPlaneSL F side) :
      wordRep ι w (specialLinear F u) v = wordRep ι w (specialLinear F c) v := by
    rw [← he, map_mul, map_mul, Module.End.mul_apply, hfix r hr]
  cases side
  · apply hmul (complement false u) ⟨0,u.y,u.c - u.x * u.y⟩
    · apply U.ext <;> simp [complement]
    · exact (mem_rootPlaneSL_line F _).mpr ⟨_,_,rfl⟩
  · apply hmul (complement true u) ⟨u.x,0,u.c⟩
    · apply U.ext <;> simp [complement]
    · exact (mem_rootPlaneSL_point F _).mpr ⟨_,_,rfl⟩

/-- Restricting the orbit coefficient to the complementary simple root detects
all root-plane-fixed vectors, with the literal finite-field action. -/
theorem eq_zero_of_restrictAxis_eq_zero (ι : F →+* K) (n : ℕ)
    (hcard : Nat.card F = 2 ^ n) (w : List Factor) (hlen : w.length = n)
    (side : Bool) (v : WordSpace K w)
    (hv : v ∈ invariants ((wordRep ι w).comp (rootPlaneSL F side).subtype))
    (hz : restrictAxis K side (wordPolynomial K w v) = 0) : v = 0 := by
  have hp : wordPolynomial K w v = 0 := by
    have hw := wordWeight_lt w
    rw [hlen] at hw
    apply eq_zero_of_flagSpace_eval_eq_zero ι n _ _ hcard hw.1 hw.2 _
      (wordPolynomial_mem_flagSpace K w v)
    intro u
    rw [wordPolynomial_eval, orbit_eq_complement ι w side v hv,
      ← wordPolynomial_eval, ← eval_restrictAxis, hz, map_zero]
  apply wordPolynomial_injective K w
  simpa only [map_zero] using hp

/-- The common fixed dimension on either root plane is bounded by two choices
per nontrivial binary tensor factor. -/
theorem finrank_invariants_le (ι : F →+* K) (n : ℕ)
    (hcard : Nat.card F = 2 ^ n) (w : List Factor) (hlen : w.length = n)
    (side : Bool) :
    Module.finrank K (invariants ((wordRep ι w).comp (rootPlaneSL F side).subtype)) ≤
      2 ^ (naturalCount w + adjointCount w) := by
  let T := invariants ((wordRep ι w).comp (rootPlaneSL F side).subtype)
  let f : T →ₗ[K] coefficientSpace K side w :=
    (((restrictAxis K side).toLinearMap ∘ₗ wordPolynomial K w).comp T.subtype).codRestrict
      (coefficientSpace K side w) (fun v => restricted_word_mem K side w v.val)
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro v hv
    apply Subtype.ext
    apply eq_zero_of_restrictAxis_eq_zero ι n hcard w hlen side v.val v.property
    exact congrArg Subtype.val hv
  exact (LinearMap.finrank_le_finrank_of_injective hf).trans
    (coefficientSpace_finrank K side w)

end Representation.SL3.BinaryDefiningFactors.ParabolicFixed
