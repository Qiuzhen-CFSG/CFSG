module

public import Theory.Representation.BinaryOffender.DisplacementFaithfulness
public import Theory.GroupTheory.GeneralizedFitting.Defs

/-!
# Reductions for component normalization, B.1.5(4)

The intended theorem says that best offenders on a faithful finite binary
module normalize every subnormal quasisimple component. The source refers to
GLS vol. 2, Theorem 26.24, whose proof uses Timmesfeld replacement and the
quadratic four-group theorem, GLS 25.14.

Here finite minimization supplies the offender-minimality dichotomy used in
that proof. The generated-subgroup equivalence records the final passage from
individual offenders to `J(G,V)`. The imported displacement-centralizer and
abelian-orbit results supply elementary parts of the construction and Step 3.
These are reductions only: the component permutation obstruction and the
faithfulness reduction have not yet been discharged, so B.1.5(4) is not claimed.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, printed p. 69; GLS vol. 2, Theorem 26.24.
-/

public section
namespace CFSG.Quasithin.ChapterB

open Representation.BinaryOffender Theory.GroupTheory

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Containment of the offender-generated subgroup is exactly containment of
all of its best-offender generators. -/
theorem offenderSubgroup_le_iff (H : Subgroup G) :
    offenderSubgroup ρ ≤ H ↔ ∀ A, IsBestOffender ρ A → A ≤ H := by
  unfold offenderSubgroup generatedBy
  simp only [iSup_le_iff]
  constructor
  · intro h A hA
    exact h A ⟨hA, le_top⟩
  · intro h A hA
    exact h A hA.1

/-- A failure of component normalization has an offender-minimal witness.
Every best offender inside that witness either is the witness or normalizes
the same actual component. No ambient normality of the component is assumed. -/
theorem exists_minimal_component_counterexample [Finite G]
    (h : ∃ (A L : Subgroup G), IsBestOffender ρ A ∧ IsComponent G L ∧
      ¬ A ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (A L : Subgroup G), IsBestOffender ρ A ∧ IsComponent G L ∧
      ¬ A ≤ Subgroup.normalizer (L : Set G) ∧
      ∀ C ≤ A, IsBestOffender ρ C → C = A ∨ C ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨A₀, L, hA₀, hL, hfail⟩ := h
  let S : Set (Subgroup G) := {A | IsBestOffender ρ A ∧ ¬ A ≤ Subgroup.normalizer (L : Set G)}
  obtain ⟨A, hA, hmin⟩ := Set.exists_min_image S (fun A => Nat.card A)
    (Set.toFinite S) ⟨A₀, hA₀, hfail⟩
  refine ⟨A, L, hA.1, hL, hA.2, fun C hCA hC => ?_⟩
  by_cases hn : C ≤ Subgroup.normalizer (L : Set G)
  · exact Or.inr hn
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hCA (hmin C ⟨hC, hn⟩))

end CFSG.Quasithin.ChapterB
