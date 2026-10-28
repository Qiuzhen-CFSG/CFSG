module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The singular-subspace reduction in Section 12.1

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), Lemma 12.1.2, printed p. 789. In the natural-plus-dual module,
Lemma H.9.1 supplies a nondegenerate quadratic form and Lemma 12.1.1 puts the
centralizer of each nonsingular vector inside `M`. A subgroup centralizing a
subspace but escaping `M` therefore forces that subspace to be totally singular.
The polar form gives the resulting codimension bound. The action below is the
conjugation action on the elementary abelian subgroup in the source application.
-/

namespace CFSG.Quasithin.Chapter12.Section01

open Module

/-- The group-action portion of Lemma 12.1.2(1): an element outside `M` that
fixes every vector of `U` rules out nonsingular vectors in `U`. -/
public theorem singular_of_pointwise_stabilizer_escape
    {G E : Type*} [Group G] [AddCommGroup E] [MulAction G E]
    (M : Subgroup G) (Q : E → Prop) (U : Set E)
    (hcentral : ∀ v : E, ¬ Q v → ∀ g : G, g • v = v → g ∈ M)
    (hescape : ∃ g : G, g ∉ M ∧ ∀ u ∈ U, g • u = u) :
    ∀ u ∈ U, Q u := by
  obtain ⟨g, hgM, hgU⟩ := hescape
  intro u hu
  by_contra hq
  exact hgM (hcentral u hq g (hgU u hu))

/-- For a nondegenerate quadratic form, a totally singular subspace has at most
half the dimension of the ambient space. This is the linear-algebra step in
Lemma 12.1.2(2). -/
public theorem twice_finrank_le_of_totally_singular
    {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [FiniteDimensional K E] (Q : QuadraticForm K E)
    (hQ : Q.polarBilin.Nondegenerate) (U : Submodule K E)
    (hU : ∀ u ∈ U, Q u = 0) :
    2 * finrank K U ≤ finrank K E := by
  let B : LinearMap.BilinForm K E := Q.polarBilin
  have horth : U ≤ B.orthogonal U := by
    intro u hu
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    apply QuadraticMap.isOrtho_polarBilin.mpr
    change Q (v + u) = Q v + Q u
    rw [hU v hv, hU u hu, hU (v + u) (U.add_mem hv hu)]
    simp
  have hdim : finrank K U ≤ finrank K (B.orthogonal U) :=
    Submodule.finrank_mono horth
  rw [B.finrank_orthogonal hQ U] at hdim
  omega

/-- In the `2n`-dimensional natural-plus-dual setting, every centralizer-escape
subspace has codimension at least `n`. This is the bound used to obtain
`r(G,V) ≥ n` in Lemma 12.1.2(2), once the weak-closure parameter is instantiated. -/
public theorem codimension_ge_of_pointwise_stabilizer_escape
    {G E : Type*} [Group G] [AddCommGroup E] [MulAction G E]
    [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (M : Subgroup G) (Q : QuadraticForm (ZMod 2) E)
    (hQ : Q.polarBilin.Nondegenerate) (n : ℕ)
    (hdim : finrank (ZMod 2) E = 2 * n)
    (U : Submodule (ZMod 2) E)
    (hcentral : ∀ v : E, Q v ≠ 0 → ∀ g : G, g • v = v → g ∈ M)
    (hescape : ∃ g : G, g ∉ M ∧ ∀ u ∈ U, g • u = u) :
    n ≤ finrank (ZMod 2) (E ⧸ U) := by
  have hsing : ∀ u ∈ U, Q u = 0 :=
    singular_of_pointwise_stabilizer_escape M (fun v => Q v = 0) U hcentral hescape
  have hbound := twice_finrank_le_of_totally_singular Q hQ U hsing
  have hquot := Submodule.finrank_quotient_add_finrank U
  omega

end CFSG.Quasithin.Chapter12.Section01
