module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.LowerObstruction.Family
public import Theory.GroupTheory.PrimeRankFixedJoin

/-!
# Root elements in the literal E-member kernels

Every member of the concrete long-root conjugacy family has order
2^(2*m+1), hence generator rank at least 2*m+1. A quotient of smaller rank
cannot be injective on it. For E1 the source rank is exactly one and the
kernel is O₂(K); for E2 the predecessor bound is 2*m and the kernel is
O∞(K). Both conclusions are intersections inside K, using the literal
quotient maps in the corrected Chapter E definitions.

These facts discharge the kernel-intersection premises for the remaining
geometric confinement in Aschbacher--Smith E.1.14(1), printed p.214,
which cites Aschbacher (1982), Lemma 4.7. They do not assert confinement.
-/

public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
open Subgroup ReeF4 ReeF4.Parabolics

/-- The field degree is a lower bound on the actual generator rank of every
member, obtained from its concrete root-coordinate order. -/
theorem fieldDegree_le_rank {m : ℕ} {A : Subgroup (Model m)}
    (hA : A ∈ rootFamily m) : 2 * m + 1 ≤ Group.rank A := by
  let := (rootFamily_elementary m).1 A hA
  exact IsElementaryAbelian.rank_ge_of_card (p := 2) (card_family_member hA)

private theorem quotient_kernel_ne_bot {G : Type*} [Group G] [Finite G]
    {A K : Subgroup G} (hAK : A ≤ K) (N : Subgroup K) [N.Normal]
    {i : ℕ} (hArank : i < Group.rank A)
    (himage : Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' N)) ≤ i) :
    A.subgroupOf K ⊓ N ≠ ⊥ := by
  intro hzero
  let q := QuotientGroup.mk' N
  let qa := q.subgroupMap (A.subgroupOf K)
  have hinj : Function.Injective qa := by
    apply (injective_iff_map_eq_one qa).mpr
    intro x hx
    have hxN : (x : K) ∈ N := by
      apply (QuotientGroup.eq_one_iff _).mp
      exact congrArg Subtype.val hx
    have hh : (x : K) ∈ A.subgroupOf K ⊓ N := ⟨x.property, hxN⟩
    rw [hzero] at hh
    exact Subtype.ext (mem_bot.mp hh)
  have hr := Group.rank_congr (MulEquiv.ofBijective qa
    ⟨hinj, q.subgroupMap_surjective (A.subgroupOf K)⟩)
  have hrA := Group.rank_congr (subgroupOfEquivOfLe hAK)
  change Group.rank (A.subgroupOf K) =
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' N)) at hr
  omega

/-- E1's rank-one quotient forces a nonidentity root element into O₂(K).
This uses the source E1 condition itself, without any extra rank premise. -/
theorem odd_kernel_meets_root {m : ℕ} (hm : 0 < m)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMember (unipotent m) A K) (hodd : ECaseOdd A K) :
    A.subgroupOf K ⊓ pCore 2 K ≠ ⊥ := by
  obtain ⟨p, _, _, _, _, _, hr⟩ := hodd
  have hArank := fieldDegree_le_rank hA
  exact quotient_kernel_ne_bot hK.2.2.1 (pCore 2 K) (by omega) hr.le

/-- The E2 predecessor-rank condition forces a nonidentity root element into
the solvable radical, rather than into an ambient radical or residual. -/
theorem component_kernel_meets_root {m : ℕ}
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hAK : A ≤ K)
    (hrank : Group.rank ((A.subgroupOf K).map
      (QuotientGroup.mk' (solvableRadical K))) ≤ 2 * m) :
    A.subgroupOf K ⊓ solvableRadical K ≠ ⊥ := by
  have hArank := fieldDegree_le_rank hA
  exact quotient_kernel_ne_bot hAK (solvableRadical K) (by omega) hrank

/-- The exact two kernel intersections needed for geometric confinement,
retaining E1 or the full E2 predicate, including its intrinsic local tau. -/
theorem member_kernel_alternatives {m : ℕ} (hm : 0 < m)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMemberAt (2 * m) (unipotent m) A K) :
    (ECaseOdd A K ∧ A.subgroupOf K ⊓ pCore 2 K ≠ ⊥) ∨
    (ECaseComponent (unipotent m) A K ∧ A.subgroupOf K ⊓ solvableRadical K ≠ ⊥) := by
  rcases hK.2 with hodd | hcomponent
  · exact Or.inl ⟨hodd.1, odd_kernel_meets_root hm hA hK.1 hodd.1⟩
  · exact Or.inr ⟨hcomponent.1, component_kernel_meets_root hA hK.1.2.2.1 hcomponent.2⟩

end CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
