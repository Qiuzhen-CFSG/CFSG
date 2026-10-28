module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockContract

/-!
# Earlier-source inputs for the factor argument in 1.3.8

These are universally quantified theorem parameters, not asserted results.
A.1.15 retains directly indecomposable factors and an actual internal product
isomorphism. Its conclusion enlarges factors by the center of its ambient
group. C.1.9 retains the additional fitting-group hypothesis when an A₃-block
is present. The subgroup O₂,₃ is the preimage of O₃ modulo O₂.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.1.15,
printed p.23; C.1.9, printed p.123; proof of 1.3.8, printed p.514.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.BlockRigidity

universe u

/-- A nontrivial group has no internal product decomposition into two
nontrivial commuting factors. Normality follows from commutation and generation. -/
def DirectlyIndecomposable (D : Type u) [Group D] : Prop :=
  Nontrivial D ∧ ∀ A B : Subgroup D, Disjoint A B → ⁅A, B⁆ = ⊥ →
    A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥

/-- The full finite-family assertion of A.1.15. The coordinate equations
identify the factors with the specified actual subgroups of D. Quantifying
over every automorphism also gives the reverse setwise inclusion. -/
def SourceA115 : Prop :=
  ∀ (D : Type u) [Group D] [Finite D] (n : ℕ) (F : Fin n → Subgroup D),
    (∀ i, DirectlyIndecomposable (F i)) →
    (∃ e : (∀ i, F i) ≃* D, ∀ i (x : F i), e (Pi.mulSingle i x) = (x : D)) →
    ∀ a : MulAut D, ∀ i, ∃ j,
      (F i ⊔ center D).map a.toMonoidHom = F j ⊔ center D

/-- O₂,₃(D), with the order of the core series explicit. -/
def twoThreeCore (D : Type u) [Group D] : Subgroup D :=
  (pCore 3 (D ⧸ pCore 2 D)).comap (QuotientGroup.mk' (pCore 2 D))

instance twoThreeCore_normal (D : Type u) [Group D] : (twoThreeCore D).Normal :=
  inferInstanceAs ((pCore 3 (D ⧸ pCore 2 D)).comap
    (QuotientGroup.mk' (pCore 2 D))).Normal

/-- The full distinct-block implication C.1.9, including its A₃ clause. -/
def SourceC19 : Prop :=
  ∀ (D : Type u) [Group D] [Finite D],
    ((∃ J : Subgroup D, ChapterC.IsBlock J ∧ ChapterC.IsAlternatingBlock J 3) →
      generalizedFitting (twoThreeCore D) = pCore 2 (twoThreeCore D)) →
    ∀ A B : Subgroup D, ChapterC.IsBlock A → ChapterC.IsBlock B →
      A ≠ B → ⁅A, B⁆ = ⊥

variable {G : Type u} [Group G] [Finite G]

/-- The genuine He bridge discharges the fitting-group premise of C.1.9.
In fact it holds regardless of whether an A₃-block is present. -/
theorem twoThreeCore_fitting_of_global_He {T H₀ : Subgroup G}
    (h114 : HOver G (T : Set G) ⊆ He G) (hH : H₀ ∈ HOver G (T : Set G)) :
    generalizedFitting (twoThreeCore H₀) = pCore 2 (twoThreeCore H₀) := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  exact normal_core_selfCentralizing (mem_He_iff.mp (h114 hH)) (twoThreeCore H₀)

end CFSG.Quasithin.Chapter1.RadicalExclusions.BlockRigidity
