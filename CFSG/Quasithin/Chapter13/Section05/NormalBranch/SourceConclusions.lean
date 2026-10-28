module
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSix
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceSevenNine
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceBarred
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.SixMaximality.Original
public import CFSG.Quasithin.Chapter13.Section05.NormalBranch.TypeU4.Recognition

/-!
# All nine conclusions in the original normal A₆ branch

The original natural datum, F.9 hypothesis, seed identity and normality of
L₁ in H now supply the full conclusion structure of 13.5.15. The source
pair is chosen internally. Original maximality is proved by the earlier
upper-component exclusion, and its genuine Hypothesis 12.2.1 is passed to
the exceptional-component and centralizer arguments. No maximality, core
equality, block, quaternion or centralizer conclusion remains an input.

The existing returning-plane construction and Asc94 recognition then give
the actual U₄(3) model in the M=L branch of 13.5.16. Excluding the separate
S₆ extension alternative remains the subsequent transfer argument.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.5.15 and the first branch of 13.5.16, printed pp.919–921.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceConclusions
open Section08.SourceCompletion
variable {G : Type*} [Group G] [Finite G] {D : ChapterF.Section09.Setup G}
  {V₂ M : Subgroup G}
  (d : NaturalSetup D.T D.L D.V D.V₁ V₂ D.Vplus M D.Gz)
  (h : D.Hypothesis) (e : (D.L ⧸ pCore 2 D.L) ≃* alternatingGroup (Fin 6))
  (hseed : D.Vplus = ⁅D.V,D.L₁⁆) (hn : (D.L₁.subgroupOf D.H).Normal)
  (hU : ¬IsMulCommutative D.UH)
include d h e hseed hn hU

/-- All nine original conclusions in the ordinary normal A₆ branch,
with the source pair selected internally. -/
theorem source13_5_15 :
    ∃ g : D.L, g.val ∉ D.Gz ∧ Conclusions D M 6 g.val := by
  have hmax := Section03.SourceCompletion.SixMaximality.Original.original_hypothesis1221
    d h e hseed hn hU
  obtain ⟨g,hgn,_,hK,_,_,hB,_,hcore,hquat⟩ :=
    SourceFiveBlock.exists_original_block d h e hseed hn hU
  refine ⟨g,hgn,{
    one := SourceStar.source13_5_15_one d h e hseed hn
    two := SourceBarred.source13_5_15_two d h e hseed hn hU
    three := ⟨hB,hK⟩
    four := ⟨fun hh => by omega,fun _ => (SourceSixBlock.source13_5_15_four d h e hseed hn hU).1⟩
    five := ⟨hcore,hquat⟩
    six := SourceSix.source13_5_15_six d h e hseed hn hU hmax
    seven := SourceSevenNine.source13_5_15_seven d hmax h e hseed hn hU
    eight := fun hh => by omega
    nine := fun _ => SourceSevenNine.source13_5_15_nine d hmax h e hseed hn hU
  }⟩

/-- The full source lemma supplies the existing returning-plane and Asc94
recognition consumer in the M=L branch of 13.5.16. -/
theorem modelConclusion_of_local_eq (hM : M = D.L) : ModelConclusion G 6 := by
  obtain ⟨g,_,b⟩ := source13_5_15 d h e hseed hn hU
  exact TypeU4.modelConclusion_of_natural_normal_branch d h b hM

end CFSG.Quasithin.Chapter13.Section05.NormalBranch.SourceConclusions
