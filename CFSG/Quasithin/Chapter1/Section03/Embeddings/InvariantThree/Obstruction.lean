module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.Obstruction.Action
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder
public import Theory.Mathieu.M11.Properties.Order

/-!
# Counterexample to the proposed intrinsic invariant-three contract

`Action` constructs the actual E₉:C₄ subgroup of A₆ and proves every
local and component hypothesis in the proposed contract. This module
rules out all its proposed conclusions. Determinant and scalar-center
counts distinguish (S)L₃(3), L₄(2), and L₅(2) from order 360; the known
M₁₁ order does the same. For Sp₄(2ⁿ), the field has at least two elements,
so 16 divides the group order, whereas 16 does not divide 360.

`counterexample` includes all the hypotheses and the negation of the
entire requested conclusion. `sqtk_of_catalogue` shows that enlarging the
constructed catalogue does not remove the obstruction. Thus the input
contract needs a substantive repair before an invariant-three sieve can
be proved; adding model computations cannot discharge this obstruction.

Source under investigation: Aschbacher–Smith, Proposition 1.3.4,
printed pp.509–511, especially the A₆ exclusion on p.511, and the
remark on p.1052 of `refs/quasithin.pdf` (1 March 2004 manuscript).
The latter does not supply a standalone theorem erasing all the original
standing hypotheses. No replacement for the source proposition is asserted.
-/

@[expose] public section

open Subgroup Theory.GroupTheory Equiv
open scoped Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.Obstruction

theorem not_psl_of_card_360 {Q : Type*} [Group Q] (hQ : Nat.card Q = 360)
    {n q : ℕ} (hnq : (n = 3 ∧ q = 3) ∨ (n = 4 ∧ q = 2) ∨ (n = 5 ∧ q = 2)) :
    ¬ ClassicalGroup.IsPSL Q n q := by
  rintro ⟨F, _, _, hF, ⟨e⟩⟩
  have hc := (Nat.card_congr e.toEquiv).symm.trans hQ
  rcases hnq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    rw [hc, hF] at hh
    norm_num [Fin.prod_univ_succ] at hh
  · have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 4
    rw [hc, hF] at hh
    norm_num [Fin.prod_univ_succ] at hh
  · have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 5
    rw [hc, hF] at hh
    norm_num [Fin.prod_univ_succ] at hh

theorem not_linear_of_card_360 {Q : Type*} [Group Q] (hQ : Nat.card Q = 360) :
    ¬ LinearThreeModel 3 Q := by
  rintro (⟨F, _, _, hF, ⟨e⟩⟩ | hpsl)
  · have hc := (Nat.card_congr e.toEquiv).symm.trans hQ
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center (Matrix.SpecialLinearGroup (Fin 3) F)), Atlas.ExceptionalSupport.card_sl_center,
      Fintype.card_fin, hF] at hc
    norm_num at hc
    have hh := Atlas.ExceptionalSupport.card_psl_mul (F := F) 3
    rw [hc, hF] at hh
    norm_num [Fin.prod_univ_succ] at hh
  · exact not_psl_of_card_360 hQ (Or.inl ⟨rfl, rfl⟩) hpsl

theorem not_symplectic_of_card_360 {Q : Type*} [Group Q] (hQ : Nat.card Q = 360) :
    ¬ SymplecticModel 3 Q := by
  rintro ⟨n, _, _, F, _, _, hF, ⟨e⟩⟩
  have hn : 0 < n := by
    have hcard : 1 < Nat.card F := Finite.one_lt_card
    by_contra hn
    have hn0 : n = 0 := by omega
    simp [hn0] at hF
    omega
  have hd : 16 ∣ (Nat.card F) ^ 4 := by
    rw [hF, ← pow_mul]
    exact pow_dvd_pow 2 (by omega : 4 ≤ n * 4)
  have hc := (Nat.card_congr e.toEquiv).symm.trans hQ
  rw [Theory.SpecificGroups.SymplecticFour.card_sp] at hc
  have hh : 16 ∣ 360 := hc ▸ (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _)
  norm_num at hh

theorem not_exceptional_of_card_360 {Q : Type*} [Group Q] (hQ : Nat.card Q = 360) :
    ¬ ExceptionalModel Q := by
  intro h
  rcases h with h11 | h4 | h5
  · obtain ⟨e⟩ := h11
    have hh := Nat.card_congr e.toEquiv
    rw [hQ, Sporadic.Mathieu.m11_order] at hh
    omega
  · exact not_psl_of_card_360 hQ (Or.inr (Or.inl ⟨rfl, rfl⟩)) h4
  · exact not_psl_of_card_360 hQ (Or.inr (Or.inr ⟨rfl, rfl⟩)) h5

theorem no_invariant_alternative :
    ¬ (Nonempty (P ≃* Plane 3) ∧
      (LinearThreeModel 3 (XiQuotient (⊤ : Subgroup A6)) ∨
        (SymplecticModel 3 (XiQuotient (⊤ : Subgroup A6)) ∧ IsCyclic (automizer T P)) ∨
        ExceptionalModel (XiQuotient (⊤ : Subgroup A6)))) := by
  have hc : Nat.card (XiQuotient (⊤ : Subgroup A6)) = 360 :=
    (Nat.card_congr component_quotient_equiv.toEquiv).trans a6_card
  rintro ⟨_, hl | ⟨hs, _⟩ | he⟩
  · exact not_linear_of_card_360 hc hl
  · exact not_symplectic_of_card_360 hc hs
  · exact not_exceptional_of_card_360 hc he


/-- Every hypothesis of the requested intrinsic invariant-three contract holds,
but its entire disjunctive conclusion fails. -/
theorem counterexample :
    IsSQTK CFSG.KnownSimple.IsConstructedCarrier (⊤ : Subgroup A6) ∧
    LocalInput 3 T P P ⊤ ∧
    (⊤ : Subgroup A6) ∈ cComponentsIn ⊤ ∧
    ((⊤ : Subgroup A6).subgroupOf ⊤).Normal ∧
    IsQuasisimple (XiQuotient (⊤ : Subgroup A6)) ∧
    T ≤ normalizer (⊤ : Subgroup A6) ∧
    P ≤ (⊤ : Subgroup A6) ∧
    ⁅(⊤ : Subgroup A6), P⁆ = ⊤ ∧
    ¬ (Nonempty (P ≃* Plane 3) ∧
      (LinearThreeModel 3 (XiQuotient (⊤ : Subgroup A6)) ∨
        (SymplecticModel 3 (XiQuotient (⊤ : Subgroup A6)) ∧ IsCyclic (automizer T P)) ∨
        ExceptionalModel (XiQuotient (⊤ : Subgroup A6)))) := by
  exact ⟨a6_sqtk.subgroup ⊤, local_input, top_cComponent, inferInstance,
    component_quotient_quasisimple, le_normalizer_of_normal, le_top,
    component_commutator, no_invariant_alternative⟩

/-- The same input obstruction persists on enlarging the constructed catalogue. -/
theorem sqtk_of_catalogue {κ : GroupClass}
    (hκ : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S],
      CFSG.KnownSimple.IsConstructedCarrier S → κ S) : IsSQTK κ (⊤ : Subgroup A6) := by
  have h := a6_sqtk.subgroup ⊤
  refine ⟨h.stronglyQuasithin, ?_⟩
  intro S _ hS U f hf
  let := hS
  let : Finite S := Finite.of_surjective f hf
  exact hκ S (h.isKGroup S hS U f hf)

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.Obstruction
