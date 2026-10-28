module
public import Theory.GroupTheory.GeneralizedFitting.SimpleComponentPairKernel
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.Commutator.PerfectLocalReduction
public import Theory.GroupTheory.PGroup.CharacteristicKernel
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Two-core kernels for pairs of C-components

Remove the ambient two-core. The simple intrinsic core quotients become
centerless ordinary components. A normal subgroup avoiding either original
component still avoids its image: perfectness removes any added two-group
supplement. The centerless pair kernel lemma now makes the image a two-group,
and lifting through the original two-core proves the same of the kernel.

Source: Aschbacher--Smith, component calculus used in 13.6.14, p.929.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

private theorem perfect_le_of_le_sup_two (B N Q : Subgroup G)
    [Group.IsPerfect B] [N.Normal] [Q.Normal] (hQ : IsPGroup 2 Q)
    (hB : B ≤ N ⊔ Q) : B ≤ N := by
  let U := N ⊔ Q
  let N' := N.subgroupOf U
  let Q' := Q.subgroupOf U
  let : Group.IsPerfect (B.subgroupOf U) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hB).symm.toMonoidHom) (subgroupOfEquivOfLe hB).symm.surjective
  have hgen : N' ⊔ Q' = ⊤ := by
    rw [← subgroupOf_sup (show N ≤ U from le_sup_left) (show Q ≤ U from le_sup_right)]
    exact subgroupOf_self U
  let : Group.IsNilpotent (U ⧸ N') :=
    (isPGroup_quotient_of_sup_eq_top N' Q' hQ.comap_subtype hgen).isNilpotent
  have hn := le_of_isPerfect_of_solvable_quotient (B.subgroupOf U) N'
  intro b hb
  exact hn (show (⟨b,hB hb⟩ : U) ∈ B.subgroupOf U from hb)

private theorem simple_component_of_core_simple {B : Subgroup G} (hB : B.IsCComponent)
    [IsSimpleGroup (B ⧸ pCore 2 B)] :
    IsComponent (G ⧸ pCore 2 G) (B.map (QuotientGroup.mk' (pCore 2 G))) ∧
      center (B.map (QuotientGroup.mk' (pCore 2 G))) = ⊥ := by
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  have hb := hB.map_quotient (pCore 2 G)
  let := hb.perfect
  let : IsSimpleGroup (B.map (QuotientGroup.mk' (pCore 2 G))) :=
    (cComponentTwoCoreQuotientEquiv hB).symm.isSimpleGroup
  have hz : center (B.map (QuotientGroup.mk' (pCore 2 G))) = ⊥ := by
    exact (inferInstance : (center (B.map (QuotientGroup.mk' (pCore 2 G)))).Normal).eq_bot_or_eq_top.resolve_right
      (fun h => Group.IsPerfect.not_isMulCommutative _ (center_eq_top_iff.mp h))
  exact ⟨⟨hb.subnormal, ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩⟩, hz⟩

/-- A normal kernel missing both simple-core components of a two-extension
is a two-group, without assuming that it contains the ambient two-core. -/
theorem isTwoGroup_of_normal_avoiding_simpleCore_pair
    (B D S N : Subgroup G) (hB : B.IsCComponent) (hD : D.IsCComponent)
    (hne : B ≠ D) [IsSimpleGroup (B ⧸ pCore 2 B)] [IsSimpleGroup (D ⧸ pCore 2 D)]
    [(B ⊔ D).Normal] [N.Normal] (hS : IsPGroup 2 S) (hgen : (B ⊔ D) ⊔ S = ⊤)
    (hBN : ¬ B ≤ N) (hDN : ¬ D ≤ N) : IsPGroup 2 N := by
  let π := QuotientGroup.mk' (pCore 2 G)
  have hπ := QuotientGroup.mk'_surjective (pCore 2 G)
  let : Group.IsNilpotent (pCore 2 G) := pCore_isPGroup.isNilpotent
  let A := B.map π
  let C := D.map π
  let P := N.map π
  let : P.Normal := Normal.map inferInstance π hπ
  have hpair : (A ⊔ C).Normal := by
    rw [show A ⊔ C = (B ⊔ D).map π from (Subgroup.map_sup B D π).symm]
    exact Normal.map inferInstance π hπ
  let := hpair
  have hne' : A ≠ C := fun he => hne (hB.eq_of_map_quotient_eq hD (pCore 2 G) he)
  have hq : IsPGroup 2 ((G ⧸ pCore 2 G) ⧸ (A ⊔ C)) := by
    apply isPGroup_quotient_of_sup_eq_top (A ⊔ C) (S.map π) (hS.map π)
    rw [show A ⊔ C = (B ⊔ D).map π from (Subgroup.map_sup B D π).symm,
      ← Subgroup.map_sup, hgen, map_top_of_surjective π hπ]
  have havoid (E : Subgroup G) (hp : Group.IsPerfect E) (hEN : ¬ E ≤ N) :
      ¬ E.map π ≤ P := by
    intro he
    have he' : E ≤ N ⊔ pCore 2 G := by
      have hh := map_le_iff_le_comap.mp he
      simpa only [P, π, comap_map_eq, QuotientGroup.ker_mk'] using hh
    let := hp
    exact hEN (perfect_le_of_le_sup_two E N (pCore 2 G) pCore_isPGroup he')
  have hA := simple_component_of_core_simple hB
  have hC := simple_component_of_core_simple hD
  have hP : IsPGroup 2 P := isTwoGroup_of_normal_avoiding_component_pair A C P
    hA.1 hC.1 hne' hA.2 hC.2 hq
    (havoid B hB.perfect hBN) (havoid D hD.perfect hDN)
  have hker : IsPGroup 2 π.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  exact (hP.comap_of_ker_isPGroup π hker).to_le (le_comap_map π N)

end Theory.GroupTheory
