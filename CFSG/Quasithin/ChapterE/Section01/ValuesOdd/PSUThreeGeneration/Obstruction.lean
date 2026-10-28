module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.Assembly
public import CFSG.Quasithin.ChapterE.Section01.Inheritance

/-!
# The remaining large-family obstruction for odd PSU₃ generation

When the whole-group E₂ case is available, a family containing a nontrivial
actor of rank at most one generates at once. Otherwise failure of generation
gives a proper Sylow overgroup containing both the weak-closure normalizer
and every rank-one E-member for the family. Every nontrivial actor in that
family has rank greater than one.

The record below describes this residual obstruction, without asserting its
existence or its impossibility in a unitary model. Its exclusion is precisely
the remaining local calculation. Keeping the actual E-members in the record
retains the intrinsic quotients and corrected local tau of E.1.2.

Source: Aschbacher--Smith, E.1.2, E.1.5 and E.1.14(7), printed pp.210, 214.
-/

public section

namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration

open Subgroup
open ValuesEvenClassical.RankOneUpper

variable {G : Type*} [Group G] [Finite G]

/-- A proper subgroup trapping a family after the rank-one actor case has
been excluded. No classification or E-generation conclusion is a field. -/
structure LargeFamilyObstruction (T : Sylow 2 G) where
  family : Set (Subgroup G)
  elementary : IsElementaryFamily family
  overgroup : Subgroup G
  proper : overgroup ≠ ⊤
  sylow_le : (T : Subgroup G) ≤ overgroup
  normalizer_le : normalizer (weakClosure (T : Subgroup G) family : Set G) ≤ overgroup
  members_le : ∀ A ∈ family, A ≤ (T : Subgroup G) →
    ∀ K : Subgroup G, IsEMemberAt 1 (T : Subgroup G) A K → K ≤ overgroup
  large : ∀ A ∈ family, A ≤ (T : Subgroup G) → A ≠ ⊥ → 1 < Group.rank A
  nontrivial_member : ∃ A ∈ family, A ≤ (T : Subgroup G) ∧ A ≠ ⊥

/-- Generation failure produces the literal obstruction, rather than a
presumed maximal-subgroup catalogue or an assumed bound on all actor ranks. -/
theorem exists_large_obstruction_of_not_generated (T : Sylow 2 G)
    (hcomponent : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → A ≠ ⊥ → ECaseComponent (T : Subgroup G) A ⊤)
    (hnot : ¬ IsEGeneratedAt 1 T) : Nonempty (LargeFamilyObstruction T) := by
  classical
  change ¬ ∀ Ω, IsElementaryFamily Ω → _ at hnot
  push Not at hnot
  obtain ⟨Ω, hΩ, hproper⟩ := hnot
  let M := eFamilySubgroup 1 (T : Subgroup G) Ω ⊔
    normalizer (weakClosure (T : Subgroup G) Ω : Set G)
  have hmembers (A : Subgroup G) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G))
      (K : Subgroup G) (hK : IsEMemberAt 1 (T : Subgroup G) A K) : K ≤ M :=
    (show K ≤ eSubgroup 1 (T : Subgroup G) A from le_sSup hK).trans
      ((le_iSup (fun B : {B : Subgroup G // B ∈ Ω ∧ B ≤ (T : Subgroup G)} =>
        eSubgroup 1 (T : Subgroup G) B.1) ⟨A, hA, hAT⟩).trans le_sup_left)
  have hlarge (A : Subgroup G) (hA : A ∈ Ω) (hAT : A ≤ (T : Subgroup G))
      (hne : A ≠ ⊥) : 1 < Group.rank A := by
    apply Nat.lt_of_not_ge
    intro hrank
    exact hproper (top_unique (hmembers A hA hAT ⊤
      (isEMemberAt_top_of_component_and_rank T A (hΩ.1 A hA) hAT
        (hcomponent A (hΩ.1 A hA) hAT hne) hrank)))
  have hex : ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ := by
    by_contra hn
    have hW : weakClosure (T : Subgroup G) Ω = ⊥ :=
      weakClosure_eq_bot_of_members_eq_bot _ _ (fun A hA hAT => by
        by_contra hne
        exact hn ⟨A, hA, hAT, hne⟩)
    exact hproper (by rw [hW, normalizer_eq_top, sup_top_eq])
  exact ⟨{
    family := Ω
    elementary := hΩ
    overgroup := M
    proper := hproper
    sylow_le := (Subgroup.le_normalizer.trans
      (normalizer_le_weakClosure_normalizer (T : Subgroup G) hΩ)).trans le_sup_right
    normalizer_le := le_sup_right
    members_le := hmembers
    large := hlarge
    nontrivial_member := hex }⟩

/-- Separate the remaining calculation by whether the family contains a
nontrivial actor in the normal simple subgroup. The outer branch concerns
all remaining actors, not just elementary subgroups of the socle. -/
theorem isEGenerated_of_large_family_cases (L : Subgroup G) (T : Sylow 2 G)
    (hcomponent : ∀ A : Subgroup G, IsElementaryAbelian 2 A →
      A ≤ (T : Subgroup G) → A ≠ ⊥ → ECaseComponent (T : Subgroup G) A ⊤)
    (hinner : ∀ d : LargeFamilyObstruction T,
      (∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧ A ≤ L) → False)
    (houter : ∀ d : LargeFamilyObstruction T,
      (∀ A ∈ d.family, A ≤ (T : Subgroup G) → A ≠ ⊥ → ¬ A ≤ L) → False) :
    IsEGenerated 1 G := by
  classical
  apply IsEGeneratedAt.isEGenerated (T := T)
  by_contra hn
  obtain ⟨d⟩ := exists_large_obstruction_of_not_generated T hcomponent hn
  by_cases hi : ∃ A ∈ d.family, A ≤ (T : Subgroup G) ∧ A ≠ ⊥ ∧ A ≤ L
  · exact hinner d hi
  · apply houter d
    intro A hA hAT hne hAL
    exact hi ⟨A, hA, hAT, hne, hAL⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration
