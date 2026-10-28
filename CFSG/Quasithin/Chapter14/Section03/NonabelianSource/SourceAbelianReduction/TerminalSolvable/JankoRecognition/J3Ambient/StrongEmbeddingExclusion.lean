module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.ReturningPair
public import BenderSuzuki.SE.InvolutionsInTwoSubgroups

/-!
# Excluding strong two-embedding from the actual returning pair

The source four-group supplies the required two-rank. The actual minus
extraspecial core contains two noncommuting square-one elements. The full
Bender–Suzuki theorem would force those original elements to commute in
any ambient group with a strongly embedded subgroup. This exclusion uses
neither ambient recognition nor an internal fusion assumption on a join.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
open Janko23.J3Recognition.LocalSixteen

private theorem model_noncommuting_involutions :
    ∃ a b : MinusExtraspecial.Model, a ^ 2 = 1 ∧ b ^ 2 = 1 ∧ a * b ≠ b * a := by
  decide +kernel

/-- The literal returning pair excludes every strongly two-embedded subgroup. -/
theorem literal_not_strongly_embedded
    {G : Type*} [Group G] [Finite G] {D : Seed G}
    (P : ReturningPair D) (M : Subgroup G) : ¬ BenderSuzuki.IsStronglyEmbedded M := by
  intro hM
  let : IsElementaryAbelian 2 P.E := P.E_elementary
  have hr : BenderSuzuki.PFchapter1section1.TwoRankAtLeastTwo G := by
    refine ⟨P.E,?_,?_⟩
    · rw [P.E_card]
    · intro x
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 P.E) x
  let j : MinusExtraspecial.Model →* G :=
    (Janko23.involutionCentralizer D.z).subtype.comp
      ((Janko23.localCore D.z).subtype.comp D.localType.core_equiv.some.symm.toMonoidHom)
  have hj : Function.Injective j :=
    (Janko23.involutionCentralizer D.z).subtype_injective.comp
      ((Janko23.localCore D.z).subtype_injective.comp D.localType.core_equiv.some.symm.injective)
  have hp : IsPGroup 2 MinusExtraspecial.Model :=
    IsPGroup.of_card (n := 5) MinusExtraspecial.card_model
  obtain ⟨a,b,ha,hb,hab⟩ := model_noncommuting_involutions
  have hc := hM.squares_commute_in_twoSubgroup hr ((⊤ : Subgroup MinusExtraspecial.Model).map j)
    ((hp.to_subgroup ⊤).map j) (j a) (j b)
    (mem_map_of_mem _ (mem_top _)) (mem_map_of_mem _ (mem_top _))
    (by rw [←map_pow,ha,map_one]) (by rw [←map_pow,hb,map_one])
  exact hab (hj (by simpa only [map_mul] using hc.eq))

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.J3Ambient
