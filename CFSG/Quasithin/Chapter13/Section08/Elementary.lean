module

public import Theory.GroupTheory.IntersectingConjugateFusion
public import Theory.GroupTheory.NormalGenerationFixedQuotient

/-!
# Intersecting conjugates and noncentral generation in §13.8

These are the elementary arguments in Aschbacher–Smith, *The Classification
of Quasithin Groups*, combined manuscript (1 March 2004), 13.8.3 and
13.8.9(1), printed pp.946 and 949. Transitivity moves an intersection
point to the distinguished point, where the abelian conjugate closure
forces commutation. Normal generation propagates trivial action on a
quotient to the whole vertex stabilizer.

The earlier transitivity, abelian-closure and local-generation results
remain explicit inputs; these lemmas do not establish Theorem 13.8.1.
-/

namespace CFSG.Quasithin.Chapter13.Section08

open Subgroup

/-- The inference of 13.8.3 from transitivity of `L` on `V` minus the
identity and the abelian closure established in 13.8.2. Conjugation here
is left conjugation; taking the inverse conjugator gives the source convention. -/
public theorem intersecting_conjugates_commute
    {G : Type*} [Group G] (L V : Subgroup G) {z : G} (hz : z ≠ 1)
    (hLV : L ≤ normalizer (V : Set G))
    (htrans : ∀ x ∈ V, x ≠ 1 → ∃ l ∈ L, MulAut.conj l z = x)
    [IsMulCommutative (centralizerConjugateClosure V z)]
    (g : G) (hinter : V ⊓ V.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ⁅V, V.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
  refine commutator_conjugate_eq_bot_of_intersection_fusion V z g ?_ hinter ?_
  · intro a ha
    have hane : MulAut.conj a z ≠ 1 :=
      fun h => hz ((MulAut.conj a).injective (h.trans (map_one _).symm))
    obtain ⟨l, hl, hlz⟩ := htrans _ ha hane
    exact ⟨l, hLV hl, hlz⟩
  · intro x hx hxne
    obtain ⟨l, hl, hlx⟩ := htrans x hx.1 hxne
    refine ⟨l⁻¹, hLV (L.inv_mem hl), ?_⟩
    rw [← hlx]
    simp [MulAut.conj_apply, mul_assoc]

/-- The noncentrality argument of 13.8.9(1). Work inside the vertex
stabilizer `J = Gγ`, with `V = Vγ`, `U = Uγ`, `W = Vγ_{b-1}`, and
`E = Gγ,γ_{b-1}`. The seed is centralized modulo `U` by the edge
stabilizer, and 13.8.4(5) supplies its normal generation and noncentrality. -/
public theorem commutator_not_le_of_noncentral_generated_quotient
    {J : Type*} [Group J] (F E W V U : Subgroup J) [U.Normal]
    (hV : V = normalClosure (W : Set J))
    (hgen : normalClosure (F : Set J) ⊔ E = ⊤)
    (hEW : ⁅E, W⁆ ≤ U) (hnoncentral : ¬ ⁅(⊤ : Subgroup J), V⁆ ≤ U) :
    ¬ ⁅F, V⁆ ≤ U := by
  intro hFV
  exact hnoncentral (commutator_le_of_normal_generation F E W V U hV hgen hFV hEW)

end CFSG.Quasithin.Chapter13.Section08
