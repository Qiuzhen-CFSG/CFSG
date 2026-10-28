module

public import Theory.Representation.G2BinaryNaturalNormalizer
public import Theory.Representation.G2NaturalOffenders
public import Theory.Representation.BinaryOffender.GeneratedCore
public import Theory.Representation.BinaryOffender.EquivariantBest
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.DerivedGroup

/-!
# Generation by binary natural G₂ offenders

The short root C(1) has the nontrivial image in the actual index-two
abelianization. The concrete A–B–C offender normally generates G₂(2):
its A–B plane normally generates the derived subgroup, and C(1) supplies
the other coset. These literal subgroup calculations support the marked
binary endpoint of Aschbacher–Smith B.4.2(4) and B.4.6(13).
-/

public section
namespace Atlas.G2.Natural.BinaryNormalizer
open Representation Representation.BinaryOffender Subgroup NaturalOffenders

theorem rootC_not_mem_derived : rootC (1 : ZMod 2) ∉ Derived := by
  intro h
  have hp : BinaryException.projection (rootC 1) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (BinaryParabolicPair.commutator_eq_longRootClosure ▸ h)
  rw [BinaryException.project_C_eq_D, BinaryException.project_D_eq_F] at hp
  exact BinaryParabolicPair.quotientBit_ne_one hp

theorem eq_top_of_derived_le {B : Subgroup Full} (hDB : Derived ≤ B)
    {c : Full} (hc : c ∈ B) (hcd : c ∉ Derived) : B = ⊤ := by
  have hi : Derived.index = 2 := by
    rw [Derived, BinaryParabolicPair.commutator_eq_longRootClosure]
    exact BinaryException.index_H
  apply top_unique
  intro x _
  by_cases hx : x ∈ Derived
  · exact hDB hx
  · have hxc : x*c ∈ Derived := (Subgroup.mul_mem_iff_of_index_two hi).mpr
      (by simp only [hx,hcd])
    simpa only [mul_inv_cancel_right] using B.mul_mem (hDB hxc) (B.inv_mem hc)

theorem generated_eq_top : offenderSubgroup (Natural.action (ZMod 2)) = ⊤ := by
  let J := offenderSubgroup (Natural.action (ZMod 2))
  let : J.Normal := offenderSubgroup_normal _
  have hA : IsBestOffender (Natural.action (ZMod 2)) (EvenTwoRank.elementary (ZMod 2)) :=
    (natural_bestOffender_iff_conjugate (n := 1) (by norm_num) (by decide) _).mpr
      ⟨1,by change _ = Subgroup.map (MonoidHom.id _) _; rw [Subgroup.map_id]⟩
  have hAJ : EvenTwoRank.elementary (ZMod 2) ≤ J := hA.le_offenderSubgroup _
  have hDJ : Derived ≤ J := by
    rw [Derived, BinaryParabolicPair.commutator_eq_longRootClosure]
    apply Subgroup.normalClosure_le_normal
    rintro _ ⟨p,rfl⟩
    exact J.mul_mem (hAJ (rootA_mem_elementary _)) (hAJ (rootB_mem_elementary _))
  exact eq_top_of_derived_le hDJ (hAJ (rootC_mem_elementary 1)) rootC_not_mem_derived
end Atlas.G2.Natural.BinaryNormalizer
