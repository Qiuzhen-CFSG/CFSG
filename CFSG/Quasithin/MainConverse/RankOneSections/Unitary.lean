module

public import CFSG.Quasithin.MainConverse.RankOneSections.Linear
public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveLinearEmbedding
public import Mathlib.Algebra.Group.ULift

/-!
# Reduction of the unitary proper-K clause to the linear clause

The genuine PSU₃(q) matrix model embeds in PSL₃(q²). An injective
homomorphism sends every proper subgroup to a proper subgroup; K-group
inheritance along the restricted injection then proves the unitary clause
from the linear one. A universe lift retains the caller's catalogue K.

This is a conditional reduction, not the completed unitary converse.
The separate proper-K theorem for PSL₃(q²) must discharge its explicit
premise. In the binary family q = 2^f, the linear field exponent is 2f.
Source: Aschbacher–Smith, Main Hypothesis 0.1.1(K) and Theorem 0.1.2,
printed p.4, repeated on p.482; the embedding uses the defining matrix images.
-/

namespace CFSG.Quasithin.MainConverse

universe u

private theorem properK_of_injective {G H : Type u} [Group G] [Group H]
    {K : GroupClass} (hH : HasProperKSubgroups K H)
    (i : G →* H) (hi : Function.Injective i) : HasProperKSubgroups K G := by
  intro U hU
  have hproper : U.map i ≠ ⊤ := by
    intro htop
    apply hU
    apply top_unique
    intro x _
    have hx : i x ∈ U.map i := by rw [htop]; trivial
    obtain ⟨y, hy, hxy⟩ := hx
    exact hi hxy ▸ hy
  let e := Subgroup.equivMapOfInjective U i hi
  exact (hH _ hproper).of_injective e.toMonoidHom e.injective

/-- An explicit reduction to the independently required PSL₃ proper-K theorem.
The coefficient field is of order q². This conditional result does not assert
the unitary proper-K theorem until the linear premise is discharged. -/
public theorem psu3_properK_of_psl3 {G : Type u} [Group G] {K : GroupClass} {q : ℕ}
    (hlinear : ∀ (H : Type u) [Group H] [Finite H],
      ClassicalGroup.IsPSL H 3 (q ^ 2) → HasProperKSubgroups K H)
    (hmodel : ClassicalGroup.IsPSU G 3 q) : HasProperKSubgroups K G := by
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  obtain ⟨j, hj⟩ := J.exists_injective_projectiveSpecialLinear
  let H := ULift.{u} (Matrix.ProjectiveSpecialLinearGroup (Fin 3) F)
  let lift : Matrix.ProjectiveSpecialLinearGroup (Fin 3) F ≃* H := MulEquiv.ulift.symm
  let i : G →* H := lift.toMonoidHom.comp (j.comp e.toMonoidHom)
  have hi : Function.Injective i := lift.injective.comp (hj.comp e.injective)
  have hH : ClassicalGroup.IsPSL H 3 (q ^ 2) :=
    ⟨F, hF, hfin, hcard, ⟨lift.symm⟩⟩
  exact properK_of_injective (hlinear H hH) i hi

end CFSG.Quasithin.MainConverse
