module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRank
public import Theory.SpecificGroups.PSL5Two.UniversalCover
public import Theory.SpecificGroups.BinaryLinear.OuterCyclic
public import Theory.SpecificGroups.BinaryLinear.SmallCubicRank
public import Theory.GroupTheory.CoveringPGroupDescent
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# The two-core kernel of a binary-five component image

A surjection onto PSL5(2) forces cubic rank at least two in the actual
SQTK C-component. Its two-core quotient is therefore quasisimple by
A.3.6. The trivial multiplier of PSL5(2) makes the induced surjection
injective, identifying the exact kernel with the original two-core.
No solvability assumption on the original ambient action kernel is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory PerfectCentralCovering
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}

/-- An actual binary-five image of an SQTK C-component has its intrinsic
two-core as kernel, with the given homomorphism preserved. -/
theorem cComponent_binary_five_kernel
    (hG : IsSQTK κ G) {B : Subgroup G} (hB : B.IsCComponent)
    (f : B →* PSL(5,ZMod 2)) (hf : Function.Surjective f) :
    f.ker = pCore 2 B := by
  let A := PSL(5,ZMod 2)
  let : IsSimpleGroup A := Atlas.psl_simple_high_rank 5 (by decide)
  let : IsQuasisimple A := Theory.SpecificGroups.PSL5Two.UniversalCover.isQuasisimple _
  have hr : 2 ≤ primeRank 3 B := by
    by_contra hn
    have hsmall : primeRank 3 B ≤ 1 := by omega
    let P : Sylow 3 B := Classical.choice inferInstance
    have hA := P.primeRank_le_one_of_surjective
      (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hsmall) f hf
    change primeRank 3 A ≤ 1 at hA
    have hlarge : 2 ≤ primeRank 3 A := by
      rw [primeRank_congr 3 (BinaryLinear.OuterCyclic.projectiveEquivSL (by decide : 0 < 5))]
      exact BinaryLinear.SmallCubicRank.five
    omega
  let : IsQuasisimple (B ⧸ pCore 2 B) :=
    cComponent_twoCore_quasisimple_of_three_rank hG hB hr
  have hk : pCore 2 B ≤ f.ker := by
    let N := (pCore 2 B).map f
    let : N.Normal := (inferInstance : (pCore 2 B).Normal).map f hf
    have hp : IsPGroup 2 N := pCore_isPGroup.map f
    have hb : N = ⊥ := by
      rcases (inferInstance : N.Normal).eq_bot_or_eq_top with hb | ht
      · exact hb
      · let : Group.IsNilpotent N := hp.isNilpotent
        let : Group.IsSolvable A := Group.isSolvable_of_surjective
          (f := N.subtype) (by intro x; exact ⟨⟨x,ht ▸ mem_top x⟩,rfl⟩)
        exact (Group.IsPerfect.not_isSolvable A inferInstance).elim
    exact (Subgroup.map_eq_bot_iff _).mp hb
  let g := QuotientGroup.lift (pCore 2 B) f hk
  have hg : Function.Surjective g := QuotientGroup.lift_surjective_of_surjective _ f hf _
  let c : Covering (B ⧸ pCore 2 B) A := ⟨g,hg⟩
  have hu : IsPGroup 2 (universalProjection A).ker := by
    rw [Theory.SpecificGroups.PSL5Two.UniversalCover.universalProjection_ker_eq_bot]
    exact IsPGroup.of_card (n := 0) (by simp)
  have hi : Function.Injective g :=
    (universalQuasisimpleCover_isUniversal A).injective_of_pGroup_kernel
      hu c (pCore_quotient_pCore_eq_bot 2)
  apply le_antisymm _ hk
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  apply hi
  change f x = g 1
  rw [map_one]
  exact hx
end CFSG.Quasithin.ChapterA.Section03
