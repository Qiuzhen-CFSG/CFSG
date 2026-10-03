module

public import Theory.ElementaryAbelian.Extraspecial
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.GroupTheory.PGroup.CentralProductCore
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Binary symplectic type and Hall's central-product factors

The conclusion of Philip Hall's theorem is an internal central product of a
trivial or extraspecial subgroup and a cyclic, generalized quaternion, dihedral,
or semidihedral subgroup. The first three alternatives use existing group
models. The last uses the generating presentation with the group order fixed;
these are the same relations used by the semidihedral recognition theorem.

`BinaryHallCore` records the intermediate reduction in Gorenstein, *Finite
Groups*, Lemma 5.4.7: the remaining factor has a cyclic self-centralizing
subgroup characteristic in the whole group. It does not assert that this
reduction exists. The structural conclusion is GLS2, Chapter C, Theorem 10.3.
-/

open Subgroup

/-- The four possible second factors in the binary case of Hall's theorem. -/
@[expose] public def IsBinaryHallFactor (P : Type*) [Group P] : Prop :=
  IsCyclic P ∨
    (∃ n : ℕ, 3 ≤ n ∧ Nonempty (P ≃* QuaternionGroup (2 ^ (n - 2)))) ∨
    (∃ m : ℕ, Nonempty (P ≃* DihedralGroup m)) ∨
    (∃ n : ℕ, 4 ≤ n ∧ Nat.card P = 2 ^ n ∧
      ∃ a b : P, orderOf a = 2 ^ (n - 1) ∧ orderOf b = 2 ∧
        b * a * b⁻¹ = a ^ (2 ^ (n - 2) - 1) ∧
        closure ({a, b} : Set P) = ⊤)

/-- An actual internal central-product decomposition of binary symplectic type. -/
@[expose] public def IsBinarySymplecticType (P : Type*) [Group P] : Prop :=
  ∃ E D : Subgroup P, (E = ⊥ ∨ IsExtraspecial 2 E) ∧ IsBinaryHallFactor D ∧
    D ≤ centralizer (E : Set P) ∧ E ⊔ D = ⊤

/-- The intermediate conclusion of the critical-subgroup argument. The cyclic
subgroup `Z` is characteristic in the ambient group and self-centralizing in `D`. -/
public structure BinaryHallCore {P : Type*} [Group P] (E D Z : Subgroup P) : Prop where
  extraspecial_or_bot : E = ⊥ ∨ IsExtraspecial 2 E
  centralizes : D ≤ centralizer (E : Set P)
  sup_eq_top : E ⊔ D = ⊤
  cyclic : IsCyclic Z
  characteristic : Z.Characteristic
  le_tail : Z ≤ D
  selfCentralizing : D ⊓ centralizer (Z : Set P) = Z

/-- The list of Hall factors is invariant under group isomorphism. -/
public theorem IsBinaryHallFactor.of_mulEquiv
    {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (h : IsBinaryHallFactor P) : IsBinaryHallFactor Q := by
  rcases h with h | h | h | ⟨n, hn, hcard, a, b, ha, hb, hrel, hgen⟩
  · exact Or.inl (e.isCyclic.mp h)
  · obtain ⟨n, hn, ⟨f⟩⟩ := h
    exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩)
  · obtain ⟨m, ⟨f⟩⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨m, ⟨e.symm.trans f⟩⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨n, hn, ?_, e a, e b, ?_, ?_, ?_, ?_⟩))
    · rw [← Nat.card_congr e.toEquiv, hcard]
    · simpa using ha
    · simpa using hb
    · simpa using congrArg e hrel
    · have hm := congrArg (fun H : Subgroup P => H.map e.toMonoidHom) hgen
      simpa [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton] using hm

/-- A Hall factor itself gives the decomposition with trivial extraspecial factor. -/
public theorem IsBinaryHallFactor.isBinarySymplecticType
    {P : Type*} [Group P] (h : IsBinaryHallFactor P) : IsBinarySymplecticType P := by
  refine ⟨⊥, ⊤, Or.inl rfl, h.of_mulEquiv Subgroup.topEquiv.symm, ?_, by simp⟩
  simp

/-- Transport the embedded central-product factors along a group equivalence. -/
public theorem IsBinarySymplecticType.of_mulEquiv
    {P Q : Type*} [Group P] [Group Q] (e : P ≃* Q)
    (h : IsBinarySymplecticType P) : IsBinarySymplecticType Q := by
  obtain ⟨E, D, hE, hD, hc, hgen⟩ := h
  refine ⟨E.map e.toMonoidHom, D.map e.toMonoidHom, ?_,
    hD.of_mulEquiv (e.subgroupMap D), ?_, ?_⟩
  · rcases hE with rfl | hE
    · exact Or.inl (map_bot _)
    · exact Or.inr (hE.of_mulEquiv (e.subgroupMap E))
  · rintro d ⟨x, hx, rfl⟩ y ⟨z, hz, rfl⟩
    exact (map_mul e z x).symm.trans
      ((congrArg e (hc hx z hz)).trans (map_mul e x z))
  · rw [← Subgroup.map_sup, hgen, map_top_of_surjective _ e.surjective]

/-- Both embedded factors in the decomposition are normal. -/
public theorem IsBinarySymplecticType.exists_normal_factors
    {P : Type*} [Group P] (h : IsBinarySymplecticType P) :
    ∃ E D : Subgroup P, E.Normal ∧ D.Normal ∧
      (E = ⊥ ∨ IsExtraspecial 2 E) ∧ IsBinaryHallFactor D ∧
      D ≤ centralizer (E : Set P) ∧ E ⊔ D = ⊤ := by
  obtain ⟨E, D, hE, hD, hc, hgen⟩ := h
  exact ⟨E, D, normal_of_centralizing_sup_eq_top E D hgen hc,
    normal_of_centralizing_sup_eq_top D E (sup_comm E D ▸ hgen)
      (le_centralizer_iff.mp hc), hE, hD, hc, hgen⟩

/-- Classifying the remaining factor finishes the central-product reduction. -/
public theorem BinaryHallCore.isBinarySymplecticType
    {P : Type*} [Group P] {E D Z : Subgroup P} (h : BinaryHallCore E D Z)
    (hD : IsBinaryHallFactor D) : IsBinarySymplecticType P :=
  ⟨E, D, h.extraspecial_or_bot, hD, h.centralizes, h.sup_eq_top⟩
