module

public import Theory.SpecificGroups.Triality.CentralCovers.TwoPrimary.SmallField.Adjustments
public import Theory.GroupTheory.Commutator.CentralExtensionPairing

/-!
# Separating commuting defects from higher-root corrections

The normal-form order is a, b, a+b, 2a+b, 3a+b, 3a+2b. Exactly five
unordered pairs can produce positive-root corrections. `CommutingPairs`
asks for exact commutation of the other ten pairs in the covering group.
It is an explicit local proof obligation, not a claim inferred from the
base matrices.

A central extension determines the commutator of two lifts solely from their
images. Consequently additive central changes cannot fix a nontrivial defect
on a commuting pair. This separates that vanishing calculation from the
normalization of the five remaining pairs, while allowing their proofs to
be developed with one common system of root sections.

Source: GLS3 §2.4.5(b), with the actual folded-root marking in `RootRelations`;
the covering calculation used in Aschbacher–Smith I.1.3 (PDF p.418).
-/

@[expose] public section

open Triality.Standard
open scoped commutatorElement
namespace Triality.Standard.CentralCovers.TwoPrimary.SmallField
noncomputable section

/-- The five unordered pairs in which a positive folded-root correction can occur. -/
def interactingPair (i j : Fin 6) : Prop :=
  (min i j, max i j) ∈ ({(0,1), (0,2), (0,3), (1,4), (2,3)} : Finset (Fin 6 × Fin 6))

variable {n : ℕ} {hn : 0 < n} {E : Type*} [Group E] {f : E →* BinaryCarrier n hn}

/-- Exact commuting of the ten noninteracting positive-root pairs in the extension. -/
def CommutingPairs (L : RootSections n hn f) : Prop :=
  ∀ (i j : Fin 6) (a b : PositiveParameters n hn), i ≠ j → ¬ interactingPair i j →
    Commute (L.factor i a) (L.factor j b)

private theorem factor_project_eq (L M : RootSections n hn f)
    (i : Fin 6) (a : PositiveParameters n hn) :
    f (L.factor i a) = f (M.factor i a) := by
  fin_cases i <;> simp [RootSections.factor, L.project_short, L.project_long,
    M.project_short, M.project_long]

/-- The pairwise commutator depends only on the marked base roots. -/
theorem factor_commutator_eq (hk : f.ker ≤ Subgroup.center E)
    (L M : RootSections n hn f) (i j : Fin 6) (a b : PositiveParameters n hn) :
    ⁅L.factor i a, L.factor j b⁆ = ⁅M.factor i a, M.factor j b⁆ :=
  CentralExtension.commutator_eq_of_image_eq f hk
    (factor_project_eq L M i a) (factor_project_eq L M j b)

/-- Changing central root sections cannot repair a nontrivial commuting-pair defect. -/
theorem commutingPairs_iff (hk : f.ker ≤ Subgroup.center E)
    (L M : RootSections n hn f) : CommutingPairs L ↔ CommutingPairs M := by
  have step (L M : RootSections n hn f) (hL : CommutingPairs L) : CommutingPairs M := by
    intro i j a b hij hroot
    apply commutatorElement_eq_one_iff_commute.mp
    rw [← factor_commutator_eq hk L M]
    exact (hL i j a b hij hroot).commutator_eq
  exact ⟨step L M, step M L⟩

/-- The exact central-adjustment operation retains every proved commuting pair. -/
theorem CentralAdjustment.commutingPairs_iff (A : CentralAdjustment f)
    (hk : f.ker ≤ Subgroup.center E) (L : RootSections n hn f) :
    CommutingPairs (A.adjusted hk L) ↔ CommutingPairs L :=
  SmallField.commutingPairs_iff hk _ _


end
end Triality.Standard.CentralCovers.TwoPrimary.SmallField
