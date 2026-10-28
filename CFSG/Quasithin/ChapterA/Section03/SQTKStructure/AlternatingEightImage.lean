module

public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.ThreeRank
public import Theory.SpecificGroups.Alternating.EightQuasisimpleQuotient
public import Theory.SpecificGroups.Alternating.TwoThreeCycles
public import Theory.GroupTheory.OddPrimeRankOneSylow

/-!
# The exact kernel of an SQTK component's alternating-eight image

An A₈ image forces three-rank at least two, so the original component's
intrinsic two-core quotient is quasisimple. Its induced surjection to A₈
is injective by the alternating multiplier calculation. Thus the kernel
is exactly the original two-core, even if the ambient action kernel was
not assumed solvable.

Source: Aschbacher--Smith A.3.6, 1.2.1(4), and the point-centralizer step
in 12.7.16, printed pp.43--45,504,844.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {κ : GroupClass}

/-- An actual A₈ surjection on an SQTK C-component has precisely its
intrinsic two-core as kernel. -/
theorem cComponent_alternating_eight_kernel
    (hG : IsSQTK κ G) {B : Subgroup G} (hB : B.IsCComponent)
    (f : B →* alternatingGroup (Fin 8)) (hf : Function.Surjective f) :
    f.ker = pCore 2 B := by
  let A := alternatingGroup (Fin 8)
  let : IsSimpleGroup A := alternatingGroup.isSimpleGroup (by simp)
  let := hB.perfect
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective hf
  have hr : 2 ≤ primeRank 3 B := by
    by_contra hn
    have hsmall : primeRank 3 B ≤ 1 := by omega
    let P : Sylow 3 B := Classical.choice inferInstance
    have hA := P.primeRank_le_one_of_surjective
      (P.isCyclic_of_odd_of_primeRank_le_one (by decide) hsmall) f hf
    have hlarge := alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide : 6 ≤ 8)
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
  have hi := AlternatingEightQuasisimple.surjection_injective
    (pCore_quotient_pCore_eq_bot 2) g hg
  apply le_antisymm _ hk
  intro b hb
  apply (QuotientGroup.eq_one_iff b).mp
  apply hi
  change f b = g 1
  rw [map_one]
  exact hb

end CFSG.Quasithin.ChapterA.Section03
