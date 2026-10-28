module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.C2Presentation.Input
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.MarkedLocal

/-!
# Positive C₂ collection on the original F.1.1 Sylow subgroup

An original/geometric amalgam marking places the original S in the same
finite quotient X/D as the eight root maps. Their positive relations give a
surjective homomorphism from the concrete symplectic U onto that original S,
commuting with the original Sylow map on every element. This also gives
ordered coordinates in the literal quotient and the bound |S| ≤ |F|⁴.
The numerator may be the infinite universal completion. There is no descent
from that completion to an actual generated ambient source group.

This is a conditional application of the supplied eight-root relations,
not a Lie-model recognition theorem. Global presentation faithfulness,
full Borel and both oriented parabolic comparisons remain to be proved.
Source: DGS, Theorem D, p.224; Aschbacher–Smith F.1.1, pp.259–260;
Steinberg §6, Lemma 36, p.69.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticFourPresentation
variable {G X F : Type*} [Group G] [Group X] [Field F] [Finite F] [CharP F 2]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)
  (d : C2Presentation.RootData (F := F) Q split)
include d

/-- The actual original S has four-root coordinates after its given marking. -/
theorem original_sylow_normal_form (s : S) :
    ∃ b k w v : F, d.x 6 (.ofAdd b) * d.x 0 (.ofAdd k) *
      d.x 4 (.ofAdd w) * d.x 2 (.ofAdd v) = MarkedLocal.sylowMap Q e h s := by
  apply d.positive_normal_form
  rw [← MarkedLocal.sylow_range Q e h split]
  exact ⟨s,rfl⟩

omit d in
private theorem sylowMap_injective : Function.Injective (MarkedLocal.sylowMap Q e h) := by
  exact Q.tits.B.subtype_injective.comp
    (((MulEquiv.subgroupCongr (lemma_F_1_3_6 h).symm).trans e.middle).injective.comp
      (inclusion_injective _))

/-- Positive collection reaches the original S with its entire prescribed
quotient map retained; this makes no assertion of global recognition. -/
theorem exists_original_sylow_cover :
    ∃ f : unipotent (F := F) →* S, Function.Surjective f ∧
      (MarkedLocal.sylowMap Q e h).comp f = d.unipotentMap := by
  let a : S ≃* split.U := (MonoidHom.ofInjective (sylowMap_injective Q e h)).trans
    (MulEquiv.subgroupCongr (MarkedLocal.sylow_range Q e h split))
  let j : unipotent (F := F) →* split.U := d.unipotentMap.codRestrict split.U
    (fun u => d.unipotentMap_range ▸ (show d.unipotentMap u ∈ d.unipotentMap.range from ⟨u,rfl⟩))
  have hj : Function.Surjective j := by
    intro u
    have hu : (u : X ⧸ Q.D) ∈ d.unipotentMap.range := d.unipotentMap_range.symm ▸ u.property
    obtain ⟨v,hv⟩ := hu
    exact ⟨v,Subtype.ext hv⟩
  refine ⟨a.symm.toMonoidHom.comp j, a.symm.surjective.comp hj, ?_⟩
  apply MonoidHom.ext
  intro u
  exact congrArg (fun v : split.U => (v : X ⧸ Q.D)) (a.apply_symm_apply (j u))

include e h in
/-- A bound for the original Sylow, not just an unconnected matrix group. -/
theorem original_sylow_card_le : Nat.card S ≤ Nat.card F ^ 4 := by
  obtain ⟨f,hf,_⟩ := exists_original_sylow_cover Q e h split d
  simpa only [card_unipotent] using Nat.card_le_card_of_surjective f hf

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.SymplecticFourPresentation
