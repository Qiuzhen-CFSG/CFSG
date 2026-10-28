module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankOneUpper.SimpleSocle
public import CFSG.Quasithin.ChapterE.Section01.Inheritance
public import Theory.SpecificGroups.PSL3.OddPrimeGraphExtension.GraphLargeStructure

/-!
# Actor-family reduction for the odd PSL₃ graph extension

The actual inner automorphism subgroup is the simple generalized Fitting
subgroup, with a two-group quotient. Thus every nontrivial elementary actor
of rank at most one makes the whole graph extension a genuine E2 member.

For the remaining families, it suffices to construct a rank-one E-member outside
every proper overgroup of the chosen Sylow subgroup containing the weak
closure normalizer. We split these families according to whether they contain
a nontrivial actor in the inner subgroup. These are still explicit local
construction premises; this module does not assert their existence or claim
the completed graph-extension case.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.2, E.1.5 and E.1.14(7), printed pp.209--210, 214; the last result
cites Aschbacher, *GF(2)-representations of finite groups* (1982), Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
private theorem member_le_family {G : Type*} [Group G] [Finite G]
    {T A K : Subgroup G} {Ω : Set (Subgroup G)}
    (hA : A ∈ Ω) (hAT : A ≤ T) (hK : IsEMemberAt 1 T A K) :
    K ≤ eFamilySubgroup 1 T Ω := by
  exact (show K ≤ eSubgroup 1 T A from le_sSup hK).trans
    (le_iSup (fun B : {B : Subgroup G // B ∈ Ω ∧ B ≤ T} =>
      eSubgroup 1 T B.1) ⟨A, hA, hAT⟩)

variable (F : Type*) [Field F] [Finite F] [IsSimpleGroup PSL(3,F)]

/-- The whole graph extension is an actual E2 member for a nontrivial actor
of rank at most one. The quotient and local tau are those of E.1.2. -/
theorem isEMemberAt_top_of_rank_le_one (T : Sylow 2 (graphExtension F))
    (A : Subgroup (graphExtension F)) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup (graphExtension F))) (hne : A ≠ ⊥)
    (hrank : Group.rank A ≤ 1) : IsEMemberAt 1 (T : Subgroup _) A ⊤ := by
  exact ValuesEvenClassical.RankOneUpper.isEMemberAt_top_of_simple_generalizedFitting
    (Group.IsPerfect.not_isMulCommutative (generalizedFitting (graphExtension F)))
    T (generalizedFitting_sup_sylow F T) T A hA hAT hne hrank

/-- The families left after the small-actor argument. Rank is the intrinsic
rank of A here; E-membership still uses its actual quotient-image rank. -/
@[expose] def LargeActors (T : Sylow 2 (graphExtension F))
    (Ω : Set (Subgroup (graphExtension F))) : Prop :=
  ∀ A ∈ Ω, A ≤ (T : Subgroup (graphExtension F)) → A ≠ ⊥ → 1 < Group.rank A

/-- A family has a nontrivial member in the actual inner subgroup. -/
@[expose] def HasInnerActor (T : Sylow 2 (graphExtension F))
    (Ω : Set (Subgroup (graphExtension F))) : Prop :=
  ∃ A ∈ Ω, A ≤ (T : Subgroup (graphExtension F)) ∧ A ≠ ⊥ ∧ A ≤ innerPart F

/-- The concrete local construction required for the remaining families:
an actual rank-one E-member escapes the specified proper overgroup. -/
@[expose] def FamilyEscapes (T : Sylow 2 (graphExtension F))
    (Ω : Set (Subgroup (graphExtension F))) (M : Subgroup (graphExtension F)) : Prop :=
  ∃ A ∈ Ω, A ≤ (T : Subgroup (graphExtension F)) ∧
    ∃ K : Subgroup (graphExtension F), IsEMemberAt 1 (T : Subgroup _) A K ∧ ¬ K ≤ M

/-- Reduction after discharging the entire rank-at-most-one actor branch.
Only the local E-member construction for large-actor families remains. -/
theorem isEGeneratedAt_of_large_family_escape (T : Sylow 2 (graphExtension F))
    (hescape : ∀ Ω, IsElementaryFamily Ω → LargeActors F T Ω →
      ∀ M : Subgroup (graphExtension F), (T : Subgroup (graphExtension F)) ≤ M →
        M ≠ ⊤ → normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M →
          FamilyEscapes F T Ω M) : IsEGeneratedAt 1 T := by
  classical
  intro Ω hΩ
  let M := eFamilySubgroup 1 (T : Subgroup (graphExtension F)) Ω ⊔
    normalizer (weakClosure (T : Subgroup (graphExtension F)) Ω : Set (graphExtension F))
  have hmember : ∀ A ∈ Ω, A ≤ (T : Subgroup (graphExtension F)) →
      ∀ K : Subgroup (graphExtension F), IsEMemberAt 1 (T : Subgroup _) A K → K ≤ M := by
    intro A hA hAT K hK
    exact (member_le_family hA hAT hK).trans le_sup_left
  by_contra hM
  have hlarge : LargeActors F T Ω := by
    intro A hA hAT hne
    apply Nat.lt_of_not_ge
    intro hrank
    exact hM (top_unique (hmember A hA hAT ⊤
      (isEMemberAt_top_of_rank_le_one F T A (hΩ.1 A hA) hAT hne hrank)))
  have hTM : (T : Subgroup (graphExtension F)) ≤ M :=
    (Subgroup.le_normalizer.trans
      (ValuesEvenClassical.RankOneUpper.normalizer_le_weakClosure_normalizer
        (T : Subgroup _) hΩ)).trans le_sup_right
  obtain ⟨A, hA, hAT, K, hK, hKM⟩ := hescape Ω hΩ hlarge M hTM hM le_sup_right
  exact hKM (hmember A hA hAT K hK)

/-- Conditional assembly separating the two remaining geometric branches.
Each premise must be proved in the literal model before this yields the
p>3 source result. No completion of PSL₂ or parameter reduction is assumed. -/
theorem isEGenerated_one_of_inner_and_outer_families
    (hinner : ∀ (T : Sylow 2 (graphExtension F)) Ω,
      IsElementaryFamily Ω → LargeActors F T Ω → HasInnerActor F T Ω →
      ∀ M : Subgroup (graphExtension F), (T : Subgroup (graphExtension F)) ≤ M →
        M ≠ ⊤ → normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M →
          FamilyEscapes F T Ω M)
    (houter : ∀ (T : Sylow 2 (graphExtension F)) Ω,
      IsElementaryFamily Ω → LargeActors F T Ω → ¬ HasInnerActor F T Ω →
      ∀ M : Subgroup (graphExtension F), (T : Subgroup (graphExtension F)) ≤ M →
        M ≠ ⊤ → normalizer (weakClosure (T : Subgroup _) Ω : Set (graphExtension F)) ≤ M →
          FamilyEscapes F T Ω M) : IsEGenerated 1 (graphExtension F) := by
  classical
  intro T
  apply isEGeneratedAt_of_large_family_escape F T
  intro Ω hΩ hlarge
  by_cases hi : HasInnerActor F T Ω
  · exact hinner T Ω hΩ hlarge hi
  · exact houter T Ω hΩ hlarge hi

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge
