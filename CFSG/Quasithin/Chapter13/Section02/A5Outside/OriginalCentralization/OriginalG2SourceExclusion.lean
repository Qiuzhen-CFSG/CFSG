module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalG2Exclusion

/-!
# The original chosen modules exclude G₂ at the source intersection

The original source pair uses the two-core of its overlap as S. Its reduced
endpoint comparison still identifies the original short factor with the
native short local group. The center of that local two-core is fixed, which
contradicts the original chosen module's nontrivial central action.

Both original Contexts and every source inclusion are retained. No equality
of S with the ambient Sylow T or normalized-Borel premise is needed.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source ChapterF.Source
open ChapterF.Source.DGS85.OriginalExtension
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ K W W₁ W₂ W₃ S : Subgroup G}

private theorem not_short_endpoint
    {A : Fin 2 → Subgroup G} (j : Fin 2)
    (d : Context T (A j) V V₁ V₂ V₃)
    (h : HypothesisF11 A S)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (hq : 2 < Nat.card F)
    (e : parabolic A (SuzukiContainment.reducedSylow A S) j ≃*
      parabolic₁ (F := F)) : False := by
  let P := parabolic A (SuzukiContainment.reducedSylow A S) j
  have hAP : A j ≤ P := le_sup_left.trans le_sup_left
  have hcore : pCore 2 (parabolic₁ (F := F)) ≤
      solvableResidual (parabolic₁ (F := F)) := by
    apply (map_le_map_iff_of_injective (parabolic₁ (F := F)).subtype_injective).mp
    rw [HigherFieldResiduals.parabolic₁_residual hq]
    change (parabolic₁ (F := F)).pCoreIn 2 ≤ local₁
    rw [parabolic₁_pCore, ←local₁_pCore]
    exact map_subtype_le _
  have hm := A5PairCatalogue.local_marking_of_reduced_equiv h j d.quotient e hcore
  let a : A j ≃* solvableResidual (parabolic₁ (F := F)) :=
    (subgroupOfEquivOfLe hAP).symm.trans
      ((e.subgroupMap ((A j).subgroupOf P)).trans (MulEquiv.subgroupCongr hm))
  let b : solvableResidual (parabolic₁ (F := F)) ≃* local₁ (F := F) :=
    ((solvableResidual (parabolic₁ (F := F))).equivMapOfInjective
      (parabolic₁ (F := F)).subtype (parabolic₁ (F := F)).subtype_injective).trans
        (MulEquiv.subgroupCongr (HigherFieldResiduals.parabolic₁_residual hq))
  exact original_context_not_g2_short_local_equiv d F (a.trans b)

/-- The actual reduced G₂ comparison is incompatible with two original
chosen modules, for any source intersection S and either orientation. -/
theorem original_pair_not_reduced_g2_of_source
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (h : HypothesisF11 ![L,K] S)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (short : Bool)
    (c : Iso (reducedAmalgam ![L,K] S) (G2Native.amalgam F short)) : False := by
  have hq : 2 < Nat.card F := by
    by_contra hgt
    have htwo : Nat.card F = 2 := by
      have := Finite.one_lt_card (α := F)
      omega
    let := Chapter6.Source.RankOneGeneric.Global.G2Short.parabolic_solvable_of_card_two htwo
    cases short
    · let f : _ ≃* parabolic₁ (F := F) := c.right
      exact A5PairCatalogue.overgroup_not_solvable (L := ![L,K]) 1 e.quotient
        (le_sup_left.trans le_sup_left)
        (Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective)
    · let f : _ ≃* parabolic₁ (F := F) := c.left
      exact A5PairCatalogue.overgroup_not_solvable (L := ![L,K]) 0 d.quotient
        (le_sup_left.trans le_sup_left)
        (Group.isSolvable_of_isSolvable_injective (f := f.toMonoidHom) f.injective)
  cases short
  · exact not_short_endpoint 1 e h F hq c.right
  · exact not_short_endpoint 0 d h F hq c.left

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
