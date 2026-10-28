module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.Reversal
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ReciprocalPlacement
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
/-!
# Quadratic action from the reciprocal critical placement

Reciprocal placement puts U in the normalizer of the critical elementary
abelian subgroup Uα. Thus [Uα,U] lies in Uα and [Uα,[Uα,U]]=1.
The original section coordinates transport this identity to the actual
binary action, supplying the quadratic field of SourceSelection from
RankSelection alone. No replacement quotient or action is introduced.

Source: Aschbacher–Smith Notation 14.7.1 and 14.7.66–69,
printed pp.1043 and 1070–1073.
-/

public section
noncomputable section
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Subgroup Representation Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

theorem Data.critical_quadratic_source (d : Data T L V F W)
    (c : CriticalPath (L := L) F) :
    BinaryOffender.IsQuadratic d.action (c.Uα.subgroupOf F.H) := by
  have hn : F.U ≤ normalizer (c.Uα : Set G) :=
    (d.source_reciprocal_placement c).trans
      ((map_mono d.conjugationSection.normalized).trans (le_normalizer_map _))
  have hAU : ⁅c.Uα,F.U⁆ ≤ c.Uα := le_normalizer_iff_commutator_le_left.mp hn
  let _ : IsElementaryAbelian 2 c.Uα := by
    let _ := d.U_elementary
    exact IsElementaryAbelian.map (MulAut.conj c.conjugator⁻¹).toMonoidHom
  have hdouble : ⁅c.Uα,⁅c.Uα,F.U⁆⁆ ≤ F.Vi 1 := by
    apply (commutator_mono le_rfl hAU).trans
    rw [commutator_self_eq_bot_iff.mpr (inferInstance : IsMulCommutative c.Uα)]
    exact bot_le
  intro a ha b hb v
  apply d.conjugationSection.fixed_on_imageSpace_of_commutator_le c.Uα ⁅c.Uα,F.U⁆
    hdouble a ha
  exact d.conjugationSection.displacement_range_le_imageSpace_of_commutator_le
    c.Uα ⁅c.Uα,F.U⁆ le_rfl b hb ⟨v,rfl⟩

theorem CriticalPath.sourceSelection_of_rank (d : Data T L V F W)
    (c : CriticalPath (L := L) F) (selection : c.RankSelection) : c.SourceSelection d :=
  ⟨selection,d.critical_quadratic_source c⟩
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
