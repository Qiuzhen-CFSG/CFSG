module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.ActorGeometry
public import Theory.ElementaryAbelian.RankOneImageCriterion

/-!
# Literal local quotient ranks of outer actors

The order-four actor needs a kernel of order at least two, and the order-eight
actor needs a kernel of order at least four. Both tests use the actor restricted
to the local subgroup and its actual radical or two-core quotient.

In particular, normalizing the inner intersection makes that intersection a
normal two-subgroup of the local group. It therefore lies in the local radical,
and the index-two calculation gives the E.1.5 rank bound for the original actor.
The final consumer keeps E0, the intrinsic Sylow condition, and all of E1/E2
explicit; it does not infer them from an orthogonal embedding or rank bound.

Source: Aschbacher--Smith, E.1.1--2, E.1.5, printed pp.209--210, and the outer
PSL₃ branch of E.1.14(7), p.214. The corrected local tau and the distinction
between O² and O₂ are inherited unchanged from `ECaseComponent`.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open Matrix.PSL3.OddPrimeGraphExtension
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
variable (F : Type*) [Field F] [Finite F]

/-- The exact test for any intrinsic local quotient. -/
theorem local_quotient_rank_le_one_iff
    {A K : Subgroup (graphExtension F)} [IsElementaryAbelian 2 A]
    (hAK : A ≤ K) (N : Subgroup K) [N.Normal] :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' N)) ≤ 1 ↔
      Nat.card A ≤ 2 * Nat.card (A.subgroupOf K ⊓ N : Subgroup K) := by
  let : IsElementaryAbelian 2 (A.subgroupOf K) := IsElementaryAbelian.subgroupOf hAK
  have hc := Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv
  simpa only [hc] using
    IsElementaryAbelian.rank_quotient_image_le_one_iff_card_le_twice_intersection
      (A.subgroupOf K) N

/-- A four-group actor must lose at least an involution in the actual quotient. -/
theorem four_local_quotient_rank_le_one_iff
    {A K : Subgroup (graphExtension F)} [IsElementaryAbelian 2 A]
    (hAK : A ≤ K) (hcard : Nat.card A = 4) (N : Subgroup K) [N.Normal] :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' N)) ≤ 1 ↔
      2 ≤ Nat.card (A.subgroupOf K ⊓ N : Subgroup K) := by
  rw [local_quotient_rank_le_one_iff F hAK, hcard]
  omega

/-- An eight-group actor must lose at least a four-group in the actual quotient. -/
theorem eight_local_quotient_rank_le_one_iff
    {A K : Subgroup (graphExtension F)} [IsElementaryAbelian 2 A]
    (hAK : A ≤ K) (hcard : Nat.card A = 8) (N : Subgroup K) [N.Normal] :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' N)) ≤ 1 ↔
      4 ≤ Nat.card (A.subgroupOf K ⊓ N : Subgroup K) := by
  rw [local_quotient_rank_le_one_iff F hAK, hcard]
  omega

/-- Normality is relative to the actual local group K. -/
theorem inner_intersection_le_radical_of_normalized
    {A K : Subgroup (graphExtension F)} [IsElementaryAbelian 2 A]
    (hK : K ≤ normalizer (A ⊓ innerPart F : Subgroup _)) :
    (A ⊓ innerPart F).subgroupOf K ≤ solvableRadical K := by
  let : ((A ⊓ innerPart F).subgroupOf K).Normal := normal_subgroupOf_of_le_normalizer hK
  have hp : IsPGroup 2 ((A ⊓ innerPart F).subgroupOf K) :=
    ((IsElementaryAbelian.isPGroup 2 A).to_le inf_le_left).comap_subtype
  let : Group.IsSolvable ((A ⊓ innerPart F).subgroupOf K) :=
    @IsNilpotent.to_isSolvable _ _ hp.isNilpotent
  exact le_solvableRadical _ inferInstance inferInstance

/-- Killing the actual inner intersection gives rank at most one for the original actor. -/
theorem radical_rank_le_one_of_inner_intersection
    {A K : Subgroup (graphExtension F)} [IsElementaryAbelian 2 A]
    (hAK : A ≤ K) (hout : ¬ A ≤ innerPart F)
    (hR : (A ⊓ innerPart F).subgroupOf K ≤ solvableRadical K) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (solvableRadical K))) ≤ 1 := by
  apply (local_quotient_rank_le_one_iff F hAK _).mpr
  have hcard := outer_intersection_card F A hout
  have hc : Nat.card ((A ⊓ innerPart F).subgroupOf K) =
      Nat.card (A ⊓ innerPart F : Subgroup _) :=
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_left.trans hAK)).toEquiv
  have hle : Nat.card ((A ⊓ innerPart F).subgroupOf K) ≤
      Nat.card (A.subgroupOf K ⊓ solvableRadical K : Subgroup K) :=
    Nat.card_le_card_of_injective (inclusion (le_inf (comap_mono inf_le_left) hR))
      (inclusion_injective _)
  rw [hc] at hle
  omega

/-- Discharge E.1.5 after an actual E-member normalizing the inner intersection
has been constructed. All component and local-tau clauses are retained. -/
theorem isEMemberAt_one_of_normalizes_inner_intersection
    {T A K : Subgroup (graphExtension F)} (hmember : IsEMember T A K)
    (hout : ¬ A ≤ innerPart F)
    (hK : K ≤ normalizer (A ⊓ innerPart F : Subgroup _)) : IsEMemberAt 1 T A K := by
  let := hmember.1
  refine ⟨hmember, ?_⟩
  rcases hmember.2.2.2.2.2 with hodd | hcomp
  · refine Or.inl ⟨hodd, ?_⟩
    obtain ⟨r, _, _, _, _, _, hrank⟩ := hodd
    exact hrank.le
  · exact Or.inr ⟨hcomp, radical_rank_le_one_of_inner_intersection F hmember.2.2.1 hout
      (inner_intersection_le_radical_of_normalized F hK)⟩

/-- Consumer: a constructed local subgroup gives the literal family escape.
The inner intersection is used only as a quotient kernel, never as a new actor. -/
theorem familyEscapes_of_normalized_local_member
    {T : Sylow 2 (graphExtension F)} {Ω : Set (Subgroup (graphExtension F))}
    {A K M : Subgroup (graphExtension F)} (hA : A ∈ Ω)
    (hmember : IsEMember (T : Subgroup _) A K) (hout : ¬ A ≤ innerPart F)
    (hK : K ≤ normalizer (A ⊓ innerPart F : Subgroup _)) (hKM : ¬ K ≤ M) :
    FamilyEscapes F T Ω M :=
  ⟨A, hA, hmember.2.1, K,
    isEMemberAt_one_of_normalizes_inner_intersection F hmember hout hK, hKM⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies
