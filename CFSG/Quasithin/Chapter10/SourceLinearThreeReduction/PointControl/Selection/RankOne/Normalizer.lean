module
public import CFSG.Quasithin.Chapter10.SourceBaumannBlocks
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.PointControl.Selection.RankOne.Parabolic

/-!
# Baumann normalizer control outside A₅

The actual minimal parabolic has the E.2.3 alternatives. If normalizer
control fails, the exceptional alternative constructs a genuine generating
alternating-five block. Component conjugacy identifies the original L with
that block, contradicting the absence of an actual A₅ quotient isomorphism.
The rank-one parabolic theorem discharges the only additional premise.
Source: Aschbacher--Smith, 10.2.1, printed p.742.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The genuine E.2.3 exception forces an actual A₅ quotient. -/
theorem baumann_normalizer_le_of_minimal_parabolic
    (hnotA5 : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hP : ChapterB.IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤
      localJoin T L from le_sup_right)) ⊤) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal := by
  by_contra hout
  have hfive := (source_local_baumann_normalizer_or_five_action D hP).resolve_left hout
  obtain ⟨K,hK,hb,ha,hgen⟩ := source_five_action_generating_block D hP hfive hout
  have hAlt := (original_L_block_of_generating_block D K hK hgen hb ha).2.2
  obtain ⟨ρ,⟨c⟩,_⟩ := hAlt.2.2
  exact hnotA5 ⟨c.quotientIso⟩

/-- The rank-one source branch of Baumann normalizer control. -/
theorem baumann_normalizer_le
    (hnotA5 : ¬ Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)))
    (hmodel : RankOneNatural D)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal :=
  baumann_normalizer_le_of_minimal_parabolic D hnotA5
    (minimal_parabolic_of_rankOneNatural D hmodel hn)

end CFSG.Quasithin.Chapter10.PointControl.Selection.RankOne
