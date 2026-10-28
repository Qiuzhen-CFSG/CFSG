module
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.Splitting.Placement
public import CFSG.Quasithin.Chapter13.Section09.FusionAlignment.SourceAlignment
public import CFSG.Quasithin.Chapter13.Section09.TerminalSubgroup.Basic
/-!
# The original Lemma 13.9.10 and its terminal source factor

The literal marked affine split, original Sylow placement and central axes
instantiate the checked weak-closure argument. Thus the original terminal
four-group centralizes O²(C_K(t)). The actual S₄ factor simultaneously gives
its residual inside H=O²(C_G(E)), its two-core inside both B and J(T), and
tz inside that core, precisely the next terminal-recognition inputs.

Source: Aschbacher–Smith 13.9.10 and the final proof of 13.9.1,
printed pp.973–974. No factor, module or extension premise remains.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section09.Marking
open Subgroup SymmetricFourWreath FusionAlignment
variable {G:Type*} [Group G] [Finite G] {d:Configuration G} (m:Marking d)

/-- The original terminal four-group centralizes the residual; the source
splitting and every marked factor input are now discharged. -/
theorem terminalFour_centralizes_normalizer_residual
    {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    m.terminalFour≤centralizer (normalizerCentralizerResidual m.B m.t:Set G) := by
  obtain ⟨f,g,X,eX,split,hf,hfJ,hgJ,hft,hgt,hfg,hdisj,hcomm,hXK,hVB,_,_,hfusion,hcoord⟩:=
    m.exists_source_aligned_split hG
  exact m.terminalFour_centralizes_normalizer_residual_of_split hG f g X hf eX hfJ hgJ
    hft hgt hfg hdisj hcomm hXK hVB hfusion split hcoord

/-- The actual S₄ factor retains precisely the two-core inputs of terminal recognition. -/
theorem exists_terminal_symmetric_factor {𝒦:GroupClass} (hG:IsSimpleQTKE 𝒦 G) :
    ∃(X:Subgroup G) (_eX:X≃*S4),
      TerminalSubgroup.residual X≤TerminalSubgroup.terminal m.terminalFour ∧
      X.pCoreIn 2≤m.dihedralBase ∧ X.pCoreIn 2≤m.B ∧ m.t*m.z∈X.pCoreIn 2 := by
  obtain ⟨f,g,X,eX,split,hf,hfJ,hgJ,hft,hgt,hfg,hdisj,hcomm,hXK,hVB,hVJ,htz,hfusion,hcoord⟩:=
    m.exists_source_aligned_split hG
  have hE:=m.terminalFour_le_split_factor hG f g X hf eX hfJ hgJ hft hgt hfg hdisj
    hcomm hXK hVB hfusion
  refine ⟨X,eX,?_,hVJ,hVB,htz⟩
  exact TerminalSubgroup.residual_le_terminal m.terminalFour X
    (le_centralizer_iff.mp (hE.trans hcomm))

end CFSG.Quasithin.Chapter13.Section09.Marking
