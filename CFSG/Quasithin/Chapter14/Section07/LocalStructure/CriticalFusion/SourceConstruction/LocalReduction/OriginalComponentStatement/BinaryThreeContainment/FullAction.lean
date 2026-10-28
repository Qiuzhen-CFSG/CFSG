module
public import Theory.SpecificGroups.PSL3Two.Automorphisms.OuterOrder
public import Theory.GroupTheory.NormalQuotientOuterAction

/-!
# The full action on the binary component quotient

The literal component image supplies all inner automorphisms. The outer
automorphism group has order two, so one actual outer actor gives
surjectivity onto the whole automorphism group.
Source: Aschbacher--Smith 14.7.47, printed p.1064, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment
variable {G : Type*} [Group G]

/-- One outer actor and the actual inner component image give the full quotient action. -/
theorem full_action (C : Subgroup G) [C.Normal]
    (e : (C ⧸ pCore 2 C) ≃* Matrix.PSL3Two.SL)
    (x : G) (hx : normalQuotientAction C (pCore 2 C) x ∉
      MulAut.innerSubgroup (C ⧸ pCore 2 C)) :
    Function.Surjective (normalQuotientAction C (pCore 2 C)) := by
  let a := normalQuotientAction C (pCore 2 C)
  let b := (MulAut.congr e).toMonoidHom.comp a
  have hi : MulAut.innerSubgroup Matrix.PSL3Two.SL ≤ b.range := by
    rintro _ ⟨z,rfl⟩
    obtain ⟨c,hc⟩ := QuotientGroup.mk'_surjective (pCore 2 C) (e.symm z)
    refine ⟨c,?_⟩
    change MulAut.congr e (normalQuotientAction C (pCore 2 C) c) = MulAut.conj z
    rw [normalQuotientAction_inner,MulAut.congr_conj,hc,e.apply_symm_apply]
  have ho : b x ∉ MulAut.innerSubgroup Matrix.PSL3Two.SL := by
    intro hh
    rw [←MulAut.map_innerSubgroup_congr e] at hh
    exact hx ((mem_map_iff_mem (MulAut.congr e).injective).mp hh)
  have hb : Function.Surjective b := by
    apply b.range_eq_top.mp
    apply top_unique
    intro z _
    by_cases hz : z ∈ MulAut.innerSubgroup Matrix.PSL3Two.SL
    · exact hi hz
    have hidx : (MulAut.innerSubgroup Matrix.PSL3Two.SL).index = 2 :=
      Matrix.PSL3Two.Automorphisms.card_outer_sl
    have hp : z * b x ∈ MulAut.innerSubgroup Matrix.PSL3Two.SL :=
      (Subgroup.mul_mem_iff_of_index_two hidx).mpr (by simp only [hz,ho])
    have hh := b.range.mul_mem (hi hp) (b.range.inv_mem (show b x ∈ b.range from ⟨x,rfl⟩))
    simpa only [mul_inv_cancel_right] using hh
  intro z
  obtain ⟨g,hg⟩ := hb (MulAut.congr e z)
  exact ⟨g,(MulAut.congr e).injective hg⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.OriginalComponentStatement.BinaryThreeContainment
