module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Reduction
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.OddClassical.LinearThree.Split.Elementary.Nontrivial.InvolutionCentralizer
public import Theory.SpecificGroups.SL3.SplitMonomial

/-!
# Position contracts for the elementary split PSL₃ intersection

An involution centralizer containing R and centralizing Z(S) suffices: its
cyclic abelianization forces the noncyclic R to meet its derived subgroup.
The alternative contract places the entire product in the actual projective
split monomial subgroup. The position dichotomy is not asserted here.

The map lemmas transport the intrinsic center, its centralizer and its
derived subgroup under an arbitrary group equivalence. They let the owner
combine a concrete monomial calculation with the original ambient Sylow.

Source: Aschbacher–Smith, proof of Proposition 1.3.4, printed p.511
(PDF p.528 of refs/quasithin.pdf); GLS3, Theorem 6.5.3(a–d).
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial

private theorem nontrivial_of_cyclic_abelianization {Q : Type*} [Group Q]
    (R C D : Subgroup Q) (hR : ¬ IsCyclic R) (hRC : R ≤ C)
    (hCD : ⁅C, C⁆ ≤ D) [IsCyclic (Abelianization C)] : D.subgroupOf R ≠ ⊥ := by
  intro hbot
  let f : R →* Abelianization C := Abelianization.of.comp (inclusion hRC)
  have hf : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxcomm : inclusion hRC x ∈ commutator C := by
      rw [← Abelianization.ker_of C]
      exact hx
    have hxD : (x : Q) ∈ D := by
      apply hCD
      rw [← C.map_subtype_commutator]
      exact mem_map_of_mem C.subtype hxcomm
    have hxbot : x ∈ D.subgroupOf R := hxD
    rwa [hbot] at hxbot
  exact hR (isCyclic_of_injective f hf)

variable {Q : Type*} [Group Q]

/-- An actual involution centralizer contains R and centralizes the entire
intrinsic center of S. This is a position predicate, not an asserted theorem. -/
@[expose] def InvolutionPosition (S R : Subgroup Q) : Prop :=
  ∃ z : Q, orderOf z = 2 ∧ R ≤ centralizer ({z} : Set Q) ∧
    centralizer ({z} : Set Q) ≤ centralizer ((center S).map S.subtype : Set Q)

/-- An actual projective model sends the whole product into the split
monomial subgroup. The choice of equivalence includes a change of basis. -/
@[expose] def MonomialPosition (p : ℕ) (S R : Subgroup Q) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = p ∧
    ∃ e : Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) F,
      (R ⊔ S).map e.toMonoidHom ≤ Matrix.SL3.SplitMonomial.projective F

/-- The involution-position branch is complete: a noncyclic subgroup cannot
embed in the cyclic abelianization of its containing centralizer. -/
theorem intersection_ne_bot_of_involutionPosition
    {S R : Subgroup Q} (hR : ¬ IsCyclic R)
    {p : ℕ} (hp : p.Prime) (hlarge : 3 < p)
    (hm : ClassicalGroup.IsPSL Q 3 p) (hpos : InvolutionPosition S R) :
    (centralizerDerived S).subgroupOf R ≠ ⊥ := by
  obtain ⟨z, hz, hRC, hC⟩ := hpos
  let _ := involutionCentralizer_abelianization_isCyclic hp hlarge hm z hz
  apply nontrivial_of_cyclic_abelianization R (centralizer ({z} : Set Q)) _ hR hRC
  rw [centralizerDerived_eq_center]
  exact commutator_mono hC hC

private theorem map_centralizer_equiv {G : Type*} [Group G]
    (E : Subgroup Q) (e : Q ≃* G) :
    (centralizer (E : Set Q)).map e.toMonoidHom =
      centralizer (E.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

/-- The intrinsic derived centralizer transports through an actual group
isomorphism, including an isomorphism to the projective matrix model. -/
theorem centralizerDerived_map_equiv {G : Type*} [Group G]
    (S : Subgroup Q) (e : Q ≃* G) :
    (centralizerDerived S).map e.toMonoidHom = centralizerDerived (S.map e.toMonoidHom) := by
  unfold centralizerDerived
  rw [map_commutator, map_centralizer_equiv, map_inf _ _ _ e.injective,
    map_centralizer_equiv]

/-- Nontriviality in an isomorphic model pulls back to the original pair. -/
theorem intersection_ne_bot_of_map {G : Type*} [Group G]
    (S R : Subgroup Q) (e : Q ≃* G)
    (hne : (centralizerDerived (S.map e.toMonoidHom)).subgroupOf (R.map e.toMonoidHom) ≠ ⊥) :
    (centralizerDerived S).subgroupOf R ≠ ⊥ := by
  intro hbot
  apply hne
  apply subgroupOf_eq_bot.mpr
  rw [← centralizerDerived_map_equiv]
  exact disjoint_map e.injective (subgroupOf_eq_bot.mp hbot)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.OddClassical.LinearThree.Split.ElementaryNontrivial
