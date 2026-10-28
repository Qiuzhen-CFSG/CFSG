module

public import Theory.GroupTheory.CComponent.RadicalKernel
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.GeneralizedFitting.PerfectCoreTwoExtension

/-!
# Normalizers of a proper perfect subgroup inside a C-component

Let G be a finite intrinsic C-component, and let A be a nontrivial proper
perfect subgroup whose solvable radical is a two-group. A normal subgroup
N of G normalizing A is central modulo O₂(G). Minimality first makes N
solvable. The commutator [N,A] is a normal solvable subgroup of A and a
normal two-subgroup of N, so it lies in O₂(G). The centralizer of the image
of N then pulls back to a normal subgroup containing A; C-component
minimality forces that pullback to be all of G.

This proves the kernel bound used in Aschbacher--Smith 11.5.8, printed p.784.
It requires only the literal local quotient, rather than a classification
of the larger component or ambient normality in the full simple group.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem normal_solvable (hG : (⊤ : Subgroup G).IsCComponent)
    (N : Subgroup G) [N.Normal] (hne : N ≠ ⊤) : Group.IsSolvable N := by
  have hn : N ≤ solvableRadical G := by
    have hh := kernel_le_solvableRadical_of_top_isCComponent hG
      (QuotientGroup.mk' N) (by simpa only [QuotientGroup.ker_mk'] using hne)
    simpa only [QuotientGroup.ker_mk'] using hh
  exact Group.isSolvable_of_isSolvable_injective (inclusion_injective hn)

theorem normalizer_kernel_le_two_center
    (hG : (⊤ : Subgroup G).IsCComponent) (A N : Subgroup G)
    [Group.IsPerfect A] [N.Normal] (hA : A ≠ ⊥) (hAt : A ≠ ⊤)
    (hrad : IsPGroup 2 (solvableRadical A))
    (hn : N ≤ normalizer (A : Set G)) :
    N ≤ (center (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)) := by
  have hNt : N ≠ ⊤ := by
    intro he
    have hnorm : A.Normal := normalizer_eq_top_iff.mp (top_unique (he ▸ hn))
    exact hAt (top_le_iff.mp (hG.minimal A le_top hA inferInstance hnorm.isSubnormal))
  let : Group.IsSolvable N := normal_solvable hG N hNt
  let C := ⁅N,A⁆
  have hCA : C ≤ A := le_normalizer_iff_commutator_le_right.mp hn
  have hCN : C ≤ N := commutator_le_left N A
  let : (C.subgroupOf A).Normal := normal_subgroupOf_of_le_normalizer
    (normalizer_commutator_ge_right N A)
  let : Group.IsSolvable C := Group.isSolvable_of_isSolvable_injective (inclusion_injective hCN)
  let : Group.IsSolvable (C.subgroupOf A) := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe hCA).toMonoidHom) (subgroupOfEquivOfLe hCA).injective
  have hCR : C.subgroupOf A ≤ solvableRadical A := le_solvableRadical _ inferInstance inferInstance
  have hCp : IsPGroup 2 C := (hrad.to_le hCR).of_equiv (subgroupOfEquivOfLe hCA)
  have hCcore : C ≤ pCore 2 G := by
    have hh := le_pCoreIn_of_normalizes hCp hCN (normalizer_commutator_ge_left N A)
    have hp : N.pCoreIn 2 ≤ pCore 2 G := le_sSup
      ⟨ConjAct.normal_of_characteristic_of_normal, pCore_isPGroup.map N.subtype⟩
    exact hh.trans hp
  let q := QuotientGroup.mk' (pCore 2 G)
  have hq := QuotientGroup.mk'_surjective (pCore 2 G)
  have hcomm : ⁅N.map q, A.map q⁆ = ⊥ := by
    rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hCcore
  let B := (centralizer (N.map q : Set (G ⧸ pCore 2 G))).comap q
  let : (N.map q).Normal := Normal.map inferInstance q hq
  let : B.Normal := inferInstance
  have hAB : A ≤ B := map_le_iff_le_comap.mp
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm))
  have hB : B = ⊤ := by
    by_contra hBt
    let : Group.IsSolvable B := normal_solvable hG B hBt
    let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective (inclusion_injective hAB)
    let : Nontrivial A := (nontrivial_iff_ne_bot A).mpr hA
    exact Group.IsPerfect.not_isSolvable A inferInstance
  intro n hnN
  apply mem_center_iff.mpr
  intro x
  obtain ⟨g,rfl⟩ := hq x
  have hg : g ∈ B := hB ▸ mem_top g
  exact (hg (q n) (mem_map_of_mem q hnN)).symm

/-- A simple quotient by the actual two-core supplies the radical premise. -/
theorem normalizer_kernel_le_two_center_of_simple_quotient
    (hG : (⊤ : Subgroup G).IsCComponent) (A N : Subgroup G)
    [Group.IsPerfect A] [IsSimpleGroup (A ⧸ pCore 2 A)] [N.Normal]
    (hAt : A ≠ ⊤) (hn : N ≤ normalizer (A : Set G)) :
    N ≤ (center (G ⧸ pCore 2 G)).comap (QuotientGroup.mk' (pCore 2 G)) := by
  let : Nontrivial A := (QuotientGroup.mk'_surjective (pCore 2 A)).nontrivial
  exact normalizer_kernel_le_two_center hG A N
    ((nontrivial_iff_ne_bot A).mp inferInstance) hAt
    (by rw [PerfectCoreTwoExtension.radical_eq_core]; exact pCore_isPGroup) hn

end Theory.GroupTheory
