module

public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.NaturalAt
public import CFSG.Quasithin.Chapter14.Section08.SourceCases

/-!
# The actual L₃(2) branch of D from ambient-local Chapter12 inputs

The earlier 13.3.2 naturality implication is needed only for the original G,T.
Its maximality and quotient conclusions give 12.2.3. Independent structural
assembly chooses an actual Irr⁺ module, and naturality marks that same module.
The full action then constructs its flag and omitted-point conjugator.

The abelian/nonabelian split is on the original flag's U. Both recognition
inputs retain the actual multiple-overgroup premise. This completes a
conditional D branch, not either recognition source or final D assembly.
Source: Aschbacher--Smith, 13.3.2(2--4), 14.3.1(1), 14.4.14, 14.7.75
and 14.8.2, printed pp.884--885,990,1009,1077--1079.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02
open Section08 Section08.InvariantFlag
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The genuine earlier naturality implication at the same ambient G,T.
The coordinates retain the literal projection L → L/O₂(L). -/
def Earlier1332CaseOneAt (T : Sylow 2 G) : Prop :=
  ∀ L : Subgroup G,
    Counterexample T L → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2 →
      FaithfulMaximalLocal T L ∧ IsQuasisimple (L ⧸ pCore 2 L) ∧
      ∀ (V : Subgroup G) (chosen : ChosenModule T L V),
        letI := chosen.elementary
        Nonempty (AmbientNaturalMarking L chosen.normalizes 3)

namespace SourceAssembly.At
variable {T : Sylow 2 G} {L V : Subgroup G}

/-- Form the original higher-rank source hypothesis from the same chosen V. -/
def higherRankHypothesis (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (chosen : ChosenModule T L V) :
    HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3 := by
  obtain ⟨hmax, hqs, hnat⟩ := earlier L d hq
  letI := chosen.elementary
  let A := Classical.choice (hnat V chosen)
  exact {
    source := Chapter14.Section03.CaseOneSource.hypothesis1223 d hmax hqs
    chosen := chosen
    rank := by decide
    quotient_model := hq
    natural := ⟨A.quotientEquiv, A.coordinates, A.equivariant⟩
    no_nextLinear := d.no_linear 4 (Or.inl rfl)
    no_A9 := d.no_alternating_nine
    no_M24 := d.no_sporadic .m24 (by simp) }

/-- Existence precedes the marking, so no normalization is inferred from
an assumed chosen module when constructing that very module. -/
theorem exists_higherRankHypothesis (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) :
    ∃ V : Subgroup G, Nonempty (HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3) := by
  have hs := earlier L d hq
  obtain ⟨V, ⟨chosen⟩⟩ :=
    (structural L (Chapter14.Section03.CaseOneSource.hypothesis1223 d hs.1 hs.2.1)).2.1
  exact ⟨V, ⟨higherRankHypothesis d earlier hq chosen⟩⟩

/-- The same original point normalizer has escape and H_z membership.
Recognition is the separate four-alternative 12.2.13 input at G,T. -/
theorem exists_source_flag (d : Counterexample T L)
    (earlier : Earlier1332CaseOneAt T)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (recognition : Theorem12213At KnownSimple.IsKnownSimple T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) :
    ∃ (V : Subgroup G) (_h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
      (F : InvariantFlag T V 3) (z g : G),
      z ≠ 1 ∧ F.Vi 1 = zpowers z ∧ g ∈ F.P L ∧ g ∉ F.H ∧
      F.H = centralizer ({z} : Set G) ∧ ¬ F.H ≤ normalizer (L : Set G) ∧
      F.H ∈ F.Hz L (normalizer (L : Set G)) := by
  obtain ⟨V, ⟨h⟩⟩ := exists_higherRankHypothesis d earlier structural hq
  obtain ⟨_, F, _, z, hz, he, g, hgP, hgH⟩ := h.exists_flag_geometry_at structural
  exact ⟨V, h, F, z, g, hz, he, hgP, hgH, F.H_eq_centralizer (by decide) z he,
    h.flag_escape_at F recognition, h.point_mem_Hz_at F recognition⟩

/-- The actual D branch with only local structural/naturality inputs.
The final D owner supplies the two independent recognition implications. -/
theorem theoremDModel_of_linearThree
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (earlier : Earlier1332CaseOneAt T)
    (nonabelian : Chapter14.Section08.SourceCases.NonabelianRecognition G)
    (abelian : Chapter14.Section08.SourceCases.AbelianRecognition G)
    (d : Counterexample T L) (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard) :
    ClassificationModels.IsTheoremDModel G := by
  classical
  obtain ⟨V, ⟨h⟩⟩ := exists_higherRankHypothesis d earlier structural hq
  obtain ⟨_, F, _⟩ := h.exists_flag_geometry_at structural
  by_cases hU : IsMulCommutative F.U
  · exact .exceptional (.sporadic .ru (by simp) (abelian T L V hmany d h F hU))
  · rcases nonabelian T L V hmany d h F hU with hG2 | hHS
    · exact .exceptional (.g2_three hG2)
    · exact .exceptional (.sporadic .hs (by simp) hHS)

end SourceAssembly.At
end CFSG.Quasithin.Chapter12.Section02
