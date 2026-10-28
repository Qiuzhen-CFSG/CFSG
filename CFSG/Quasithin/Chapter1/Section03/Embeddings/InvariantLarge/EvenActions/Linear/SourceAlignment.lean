module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Linear.SourceAlignment.Configuration
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.EvenActions.Linear.SourceAlignment.BorelGeometry
public import CFSG.Quasithin.Defs
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# Aligning the raw linear Cartan configuration in A.3.15(5)

For finite SQTK J with F*(J) = D nonabelian simple, restrict the actual
Sylow two-subgroup S to D. Given the full raw field–Cartan configuration,
field/inner-diagonal disjointness proves that B lies in H and hence
normalizes U = S ∩ D. Sylow conjugacy followed by a fixed-coset argument
inside the concrete Borel produces one actual equivalence D ≃ PSL₃(E)
sending U onto the standard unipotent group and B into the published torus.

The raw record includes the source field-coordinate realization, all F/H/I
clauses and their relative normalizer convention. It includes neither the
aligned equivalence nor torus containment. Normality of D is derived from
F*(J) = D, and all hypotheses of the simultaneous alignment theorem are
discharged below. Coverage of the full automorphism group by standard
linear/field/graph automorphisms is unnecessary for this alignment step.

This is the alignment helper for the A₂ branch of Proposition 1.3.4;
normalizer-action factorization and final source assembly belong to its
parent. The helper also permits B = 1, so no three-residual nontriviality
premise is required beyond the supplied raw configuration.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Lemma A.3.15(5),
printed pp.50–51 (PDF pp.61–62), and Proposition 1.3.4, printed p.511
(PDF p.528).
-/

public section

open scoped MatrixGroups Pointwise
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions

universe u v

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear.SourceAlignment

variable {J : Type u} [Group J]

/-- The ambient source hypotheses in the inside-D prime-subgroup branch. -/
structure AmbientInput (κ : GroupClass.{u}) (D B : Subgroup J) (S : Sylow 2 J)
    (p : ℕ) : Prop where
  sqtk : IsSQTK κ J
  fitting : generalizedFitting J = D
  simple : IsSimpleGroup D
  nonabelian : ¬ IsMulCommutative D
  prime : p.Prime
  large : 3 < p
  p_group : IsPGroup p B
  inside : B ≤ D
  permutes : (B : Set J) * (S : Set J) = (S : Set J) * (B : Set J)

variable (E : Type v) [Field E] [Finite E]

/-- Simultaneous alignment after the Sylow subgroup has been restricted to D. -/
theorem exists_alignment_of_raw {D : Type*} [Group D] [Finite D]
    {n p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (T : Sylow 2 D)
    (B : Subgroup D) (hB : IsPGroup p B)
    (c : RawConfiguration E n (T : Subgroup D) B) :
    ∃ e' : D ≃* PSL(3,E), (T : Subgroup D).map e'.toMonoidHom = unipotent E ∧
      B.map e'.toMonoidHom ≤ torus E := by
  exact exists_simultaneous_alignment E c.model (by have := c.degree; omega)
    c.field_card hp T B hB c.subgroup_le_normalizer

/-- The requested actual equivalence, from the ambient source hypotheses and
all clauses of the raw A.3.15(5) configuration. -/
theorem exists_alignment [Finite J] {κ : GroupClass.{u}}
    {D B : Subgroup J} {S : Sylow 2 J} {p n : ℕ}
    (h : AmbientInput κ D B S p)
    (c : RawConfiguration E n ((S : Subgroup J).subgroupOf D) (B.subgroupOf D)) :
    ∃ e' : D ≃* PSL(3,E),
      ((S : Subgroup J).subgroupOf D).map e'.toMonoidHom = unipotent E ∧
      (B.subgroupOf D).map e'.toMonoidHom ≤ torus E := by
  let : Fact p.Prime := ⟨h.prime⟩
  let : D.Normal := by rw [← h.fitting]; infer_instance
  obtain ⟨T,hT⟩ := S.exists_subgroupOf_eq_of_normal D
  have c' : RawConfiguration E n (T : Subgroup D) (B.subgroupOf D) := by
    rwa [hT]
  obtain ⟨e',hU,hB⟩ := exists_alignment_of_raw E (by have := h.large; omega)
    T (B.subgroupOf D) h.p_group.comap_subtype c'
  exact ⟨e',by rwa [hT] at hU,hB⟩

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.EvenActions.Linear.SourceAlignment
