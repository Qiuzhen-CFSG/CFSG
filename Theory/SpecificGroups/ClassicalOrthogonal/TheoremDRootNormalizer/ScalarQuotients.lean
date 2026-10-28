module

public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd
public import Theory.SpecificGroups.ClassicalOrthogonal.Minus
public import Mathlib.Algebra.CharP.Two

/-!
# Scalar quotients of orthogonal groups in characteristic two

A scalar quadratic isometry has square-one multiplier as soon as the form
represents a nonzero value. In characteristic two that multiplier is one.
Thus projectivization is injective on both actual Omega constructions used
here: the elementary Siegel subgroup and the orthogonal commutator subgroup.
The chosen minus form represents one on its anisotropic plane at every rank.

The equivalences below are induced by the literal quotient maps. They supply
the projective step for the odd/symplectic and minus/linear comparisons, and
allow root and torus embeddings to survive the same projective quotients.
Source: GLS3 §2.7 (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public noncomputable section
universe u
namespace ClassicalOrthogonal.TheoremDRootNormalizer
variable {F : Type u} [Field F] [CharP F 2]

/-- In characteristic two, elementary projectivization kills no element. -/
theorem elementaryProjective_injective {V : Type u} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) : Function.Injective (projectiveElementaryMap Q) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨c, hc, hcg⟩ := (projectiveElementaryMap_eq_one_iff Q g).mp hg
  have hc1 : c = 1 := by
    rcases sq_eq_one_iff.mp hc with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val.val x = x
  simpa only [hc1, one_smul] using hcg x

/-- In characteristic two, the elementary carrier equals its scalar quotient. -/
def elementaryProjectiveEquiv {V : Type u} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) : elementarySubgroup Q ≃* ProjectiveElementary Q :=
  MulEquiv.ofBijective (projectiveElementaryMap Q)
    ⟨elementaryProjective_injective Q, projectiveElementaryMap_surjective Q⟩

@[simp] theorem elementaryProjectiveEquiv_apply {V : Type u} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (g : elementarySubgroup Q) :
    elementaryProjectiveEquiv Q g = projectiveElementaryMap Q g := rfl

/-- A scalar isometry of a nonzero form in characteristic two is the identity;
this applies to the actual orthogonal commutator subgroup. -/
theorem omegaProjective_injective {V : Type u} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (hQ : ∃ v, Q v ≠ 0) :
    Function.Injective (QuotientGroup.mk' (Minus.scalarSubgroup F V Q)) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  obtain ⟨c, hcg⟩ := (Minus.projectiveOmega_mk_eq_one_iff F V Q g).mp hg
  obtain ⟨v, hv⟩ := hQ
  have hs : (c : F) ^ 2 = 1 := by
    have h := (Theory.AlgebraicGroup.mem_quadraticIsometrySubgroup Q g.val.val).mp
      g.val.property v
    rw [hcg] at h
    apply mul_right_cancel₀ hv
    simpa only [Q.map_smul, smul_eq_mul, pow_two, one_mul] using h
  have hc1 : (c : F) = 1 := by
    rcases sq_eq_one_iff.mp hs with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h
  apply Subtype.ext
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change g.val.val x = x
  simpa only [hc1, one_smul] using hcg x

/-- Projectivization of an orthogonal commutator group over a binary field. -/
def omegaProjectiveEquiv {V : Type u} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (hQ : ∃ v, Q v ≠ 0) :
    Minus.Omega F V Q ≃* Minus.ProjectiveOmega F V Q :=
  MulEquiv.ofBijective (QuotientGroup.mk' (Minus.scalarSubgroup F V Q))
    ⟨omegaProjective_injective Q hQ, QuotientGroup.mk'_surjective _⟩

@[simp] theorem omegaProjectiveEquiv_apply {V : Type u} [AddCommGroup V] [Module F V]
    (Q : QuadraticForm F V) (hQ : ∃ v, Q v ≠ 0) (g : Minus.Omega F V Q) :
    omegaProjectiveEquiv Q hQ g = QuotientGroup.mk' (Minus.scalarSubgroup F V Q) g := rfl

/-- The actual minus form represents one on its final plane, so its projective
quotient also has trivial kernel, at every rank. -/
def minusOmegaEquivProjective [Finite F] (r : ℕ) :
    Minus.Omega F (Minus.Space F (r - 1)) (Minus.quadraticForm F r) ≃*
      ClassicalGroup.POmegaMinus r F :=
  omegaProjectiveEquiv (Minus.quadraticForm F r)
    ⟨(0, (1, 0)), by simp [Minus.quadraticForm]⟩

end ClassicalOrthogonal.TheoremDRootNormalizer
