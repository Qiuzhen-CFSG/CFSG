module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.LinearThreeInvolutoryLift
public import Theory.SpecificGroups.Alternating.FourPairCore
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Elementary displacement in a binary linear-three point radical

Let a perfect group K have quotient SL₃(2) by its two-core, and let the
point subgroup J map onto A₄ with kernel J ∩ O₂(K). An elementary subgroup
P of O₂(J) satisfies [P,O₂(J)] ≤ U(K). If P lies in O₂(K), this is the
definition of U(K). Otherwise an involution outside O₂(K) excludes the
nontrivial central cover of K/U(K), so O₂(K)=U(K); the Klein-four image
of O₂(J) then supplies the same containment.

The argument retains the possible central cover until the involutory lift
excludes it. Its actual source application is the selected linear-three
branch of Aschbacher–Smith 13.4.15, printed p.912, in
Chapter13/Section04/FixedCoreSource/Nonsolvable/ReciprocalCore.lean.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC
variable {K : Type*} [Group K] [Finite K] [Group.IsPerfect K]

/-- An elementary subgroup of the point radical has all its radical
commutators in the intrinsic block layer, including central-cover cases. -/
theorem linearThree_elementary_point_displacement
    (e : (K ⧸ pCore 2 K) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))
    (J P : Subgroup K) [IsElementaryAbelian 2 P]
    (hP : P ≤ J.pCoreIn 2)
    (f : J →* alternatingGroup (Fin 4)) (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 K).subgroupOf J) :
    ⁅P,J.pCoreIn 2⁆ ≤ blockU K := by
  by_cases hcore : P ≤ pCore 2 K
  · exact commutator_mono hcore le_top
  obtain ⟨x,hx,hxq⟩ := Set.not_subset.mp hcore
  have hQ : pCore 2 K = blockU K := linearThree_core_eq_blockU_of_square_mem e x hxq
    (by rw [elemPow_eq_one_of_isElementaryAbelian x hx]; exact one_mem _)
  have hp : IsPGroup 2 f.ker := by rw [hk]; exact pCore_isPGroup.comap_subtype
  have hmap : pCore 2 J ≤ (pCore 2 (alternatingGroup (Fin 4))).comap f :=
    (f.comap_pCore_of_ker_isPGroup hf hp).ge
  let : IsMulCommutative (pCore 2 (alternatingGroup (Fin 4))) := by
    rw [AlternatingFourPair.twoCore_eq_kleinFour]
    exact (alternatingGroup.kleinFour_isKleinFour (by simp)).isMulCommutative
  have hc : ⁅pCore 2 J,pCore 2 J⁆ ≤ f.ker := by
    apply commutator_le.mpr
    intro a ha b hb
    change f ⁅a,b⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (congrArg Subtype.val (mul_comm (⟨f a,hmap ha⟩ : pCore 2 (alternatingGroup (Fin 4)))
        ⟨f b,hmap hb⟩))
  have hkm : f.ker.map J.subtype ≤ pCore 2 K := by
    rintro x ⟨a,ha,rfl⟩
    have ha' : a ∈ (pCore 2 K).subgroupOf J := hk ▸ ha
    exact ha'
  have hderived := (map_mono (f := J.subtype) hc).trans hkm
  rw [map_commutator,hQ] at hderived
  exact (commutator_mono hP le_rfl).trans hderived
end CFSG.Quasithin.ChapterC
