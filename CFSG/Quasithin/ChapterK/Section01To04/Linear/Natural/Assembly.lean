module
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.Transport
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Natural.Context

/-!
# Assembly after the outer-field actor calculation

The constructed best offenders already generate L. Once elementary actors
outside L have strictly larger displacement than rank, best offenders stay
inside L and the inner lower bound becomes the ambient quadratic lower bound.
The hyperplane witness attains it, giving the actual B.4.2(3),(9) clauses.

These are conditional assembly lemmas. The outer-field estimate is not proved
in this module and cannot be assumed in the final K.3.2.1 theorem.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), K.3.2.1,
printed pp.454–455.
-/

public section

open Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped ENNReal
namespace CFSG.Quasithin.ChapterK.Linear.Natural

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) (F : BinaryField) (n : ℕ)

/-- The remaining field-actor estimate feeds the actual global infimum and
best-offender-generated subgroup. Its premise must be discharged before this
conditional calculation is the source theorem. -/
theorem conclusions_of_outer_actor_bound
    (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F n)) (hn : 2 ≤ n)
    (houter : ∀ A : Subgroup G, IsElementaryTwo A → ¬ A ≤ L →
      rank A < fixedCodim ρ A) :
    quadraticRatio ρ = 1 / (n - 1 : ℕ) ∧
    (∀ A, IsBestOffender ρ A → A ≤ L) ∧ offenderSubgroup ρ = L := by
  have hbest : ∀ A, IsBestOffender ρ A → A ≤ L := by
    intro A hA
    by_contra hAL
    exact Nat.not_lt_of_ge (hA.isOffender ρ).2 (houter A hA.1 hAL)
  refine ⟨le_antisymm (quadraticRatio_le ρ L F n e hn) ?_, hbest,
    le_antisymm ?_ (component_le_offenderSubgroup ρ L F n e hn)⟩
  · apply le_iInf
    intro A
    apply le_iInf
    rintro ⟨hA, hq⟩
    by_cases hAL : A ≤ L
    · exact inner_actionRatio_ge ρ L F n e hn hA hq hAL
    · have hone : 1 ≤ actionRatio ρ A := by
        unfold actionRatio
        apply (ENNReal.le_div_iff_mul_le
          (Or.inl (by exact_mod_cast Nat.ne_of_gt hA.rank_pos)) (Or.inl (by simp))).mpr
        simp only [one_mul]
        exact_mod_cast (houter A hA hAL).le
      apply le_trans _ hone
      have hden : (1 : ℝ≥0∞) ≤ (n - 1 : ℕ) := by exact_mod_cast (show 1 ≤ n - 1 by omega)
      simpa only [div_one] using ENNReal.div_le_div_left hden 1
  · apply iSup_le
    intro A
    apply iSup_le
    rintro ⟨hA, _⟩
    exact hbest A hA

/-- The literal B.4.2 linear-three clause, conditional only on the missing
outer-actor calculation; the model ratio and generation are proved here. -/
theorem linearThree_of_outer_actor_bound
    (e : ActionEquiv (ρ.comp L.subtype) (linearNatural F 3))
    (houter : ∀ A : Subgroup G, IsElementaryTwo A → ¬ A ≤ L →
      rank A < fixedCodim ρ A) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  obtain ⟨hq, _, hg⟩ := conclusions_of_outer_actor_bound ρ L F 3 e (by decide) houter
  exact .linearThree F hg e (by simpa using hq)

/-- The literal B.4.2 binary degree-four/five clause. Both use the same
recognized action as the hyperplane-centralizer construction. -/
theorem binaryLinear_of_outer_actor_bound (hd : n = 4 ∨ n = 5)
    (e : ActionEquiv (ρ.comp L.subtype) (linearNatural BinaryField.two n))
    (houter : ∀ A : Subgroup G, IsElementaryTwo A → ¬ A ≤ L →
      rank A < fixedCodim ρ A) :
    ChapterB.SourceInduction.ProjectiveLine.IrreducibleActionCase ρ L (offenderSubgroup ρ) := by
  have hn : 2 ≤ n := by rcases hd with rfl | rfl <;> omega
  obtain ⟨hq, _, hg⟩ := conclusions_of_outer_actor_bound ρ L BinaryField.two n e hn houter
  exact .binaryLinear n hd hg e hq

end CFSG.Quasithin.ChapterK.Linear.Natural
