module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Data.Finset.Max
public import Theory.Representation.ZeroHecke.TypeA4Eigenvector.Words

/-!
# Simultaneous eigenvectors for type-A₄ zero-Hecke operators

The zero-Hecke proof uses operators indexed by permutations. Among the nonzero
word operators choose one of maximal Coxeter length. Multiplication on the left
by a simple generator either fixes that operator or gives an operator of greater
length, which must vanish. The resulting nonzero image vector is simultaneously
fixed or killed by every generator. The finite word model is supplied by a
kernel-checked calculation from the idempotent type-A₄ Coxeter presentation in
`TypeA4Eigenvector.Words`.

This proves the split one-dimensional-submodule property directly over every
field, with no finite-dimensionality assumption. It includes the binary case
needed by the upper-unitriangular-invariant highest-vector construction.
-/

namespace ZeroHecke

/-- The linear-algebra step in the finite zero-Hecke argument. The finite word
model supplies `word`, `step`, and `height`; no braid relations are needed here. -/
public theorem exists_common_zero_or_fixed_of_finite_words
    {F W I M : Type*} [Field F] [AddCommGroup W] [Module F W]
    [Fintype M] (T : I → Module.End F W)
    (word : M → Module.End F W) (seed : M) (hseed : word seed ≠ 0)
    (step : I → M → M) (height : M → ℕ)
    (hstep : ∀ i m, T i * word m = word (step i m))
    (hrise : ∀ i m, step i m = m ∨ height m < height (step i m)) :
    ∃ v : W, v ≠ 0 ∧ ∀ i, T i v = v ∨ T i v = 0 := by
  classical
  let support : Finset M := Finset.univ.filter (fun m => word m ≠ 0)
  have hsupport : support.Nonempty := by
    refine ⟨seed, ?_⟩
    simp [support, hseed]
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image support height hsupport
  have hmne : word m ≠ 0 := (Finset.mem_filter.mp hm).2
  have hvector : ∃ v : W, word m v ≠ 0 := by
    by_contra h
    apply hmne
    ext v
    exact not_ne_iff.mp (not_exists.mp h v)
  obtain ⟨v, hv⟩ := hvector
  refine ⟨word m v, hv, ?_⟩
  intro i
  rcases hrise i m with hsame | hgreater
  · left
    have h := congrArg (fun f : Module.End F W => f v) (hstep i m)
    simpa [Module.End.mul_apply, hsame] using h
  · right
    have hzero : word (step i m) = 0 := by
      by_contra hne
      have hmem : step i m ∈ support := by simp [support, hne]
      exact (not_lt_of_ge (hmax (step i m) hmem)) hgreater
    have h := congrArg (fun f : Module.End F W => f v) (hstep i m)
    simpa [Module.End.mul_apply, hzero] using h

/-- Four type-A₄ zero-Hecke operators have a common nonzero vector that each
operator fixes or kills. This holds over any field, without a dimension bound. -/
public theorem exists_common_zero_or_fixed
    {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [Nontrivial W]
    (T : Fin 4 → Module.End F W) (h : TypeA4Relations T) :
    ∃ v : W, v ≠ 0 ∧ ∀ i, T i v = v ∨ T i v = 0 := by
  obtain ⟨word, step, height, hunit, hstep, hrise⟩ := typeA4_finite_word_model T h
  exact exists_common_zero_or_fixed_of_finite_words T word 0 (by rw [hunit]; exact one_ne_zero)
    step height hstep hrise

/-- The simultaneous eigenvalues of type-A₄ zero-Hecke operators can be chosen
in `{0, 1}`. In particular this applies to every nonzero finite-dimensional
vector space over `ZMod 2`. -/
public theorem exists_common_eigenvector
    {F W : Type*} [Field F] [AddCommGroup W] [Module F W] [Nontrivial W]
    (T : Fin 4 → Module.End F W) (h : TypeA4Relations T) :
    ∃ (v : W) (ε : Fin 4 → F), v ≠ 0 ∧
      (∀ i, ε i = 0 ∨ ε i = 1) ∧ ∀ i, T i v = ε i • v := by
  classical
  obtain ⟨v, hv, he⟩ := exists_common_zero_or_fixed T h
  refine ⟨v, fun i => if T i v = v then 1 else 0, hv, ?_, ?_⟩
  · intro i
    by_cases hi : T i v = v <;> simp [hi]
  · intro i
    by_cases hi : T i v = v
    · simpa only [if_pos hi, one_smul] using hi
    · simpa only [if_neg hi, zero_smul] using (he i).resolve_left hi

end ZeroHecke
