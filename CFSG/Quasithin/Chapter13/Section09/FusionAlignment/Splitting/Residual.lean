module
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.Splitting.Source

/-!
# Full original Lemma 13.9.10

The literal split identifies O²(C_K(t)) with O²(S₄)=A₄ while the original
terminal four-group centralizes this same embedded residual. Both clauses
now follow from the original QTKE configuration, without a model or
alignment premise.
Source: Aschbacher–Smith 13.9.10, printed p.973.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup FusionAlignment
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

/-- The original embedded normalizer-centralizer residual is A₄. -/
theorem normalizer_residual_alternating {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    Nonempty (normalizerCentralizerResidual m.B m.t≃*alternatingGroup (Fin 4)) := by
  obtain ⟨R,X,split,eR,eX,hcoord,_,_,_,_,_,_,_⟩:=
    m.exists_marked_centralizer_split_with_core hG
  have hp:IsPGroup 2 R :=
    (IsPGroup.of_card (by rw [DihedralGroup.nat_card];norm_num : Nat.card (DihedralGroup 4)=2^3)).of_equiv eR
  exact ⟨normalizerCentralizerResidualEquiv m.B R X m.t split hp eX.symm⟩

/-- Lemma 13.9.10, with both the centralization and actual A₄ residual clauses. -/
theorem source13_9_10 {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    m.terminalFour≤centralizer (normalizerCentralizerResidual m.B m.t:Set G) ∧
      Nonempty (normalizerCentralizerResidual m.B m.t≃*alternatingGroup (Fin 4)) :=
  ⟨m.terminalFour_centralizes_normalizer_residual hG,m.normalizer_residual_alternating hG⟩

end CFSG.Quasithin.Chapter13.Section09.Marking
