module
import all CFSG.Quasithin.Chapter13.Section05.A5Source.RecognitionKnownSimple
public import CFSG.Quasithin.Chapter13.Section05.A5Source.NormalRecognition
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SeedKnownSimple

/-!
# Original normal A₅ recognition over the complete known-simple catalogue

The ordinary and doubled source amalgams already identify the ambient group
as PSU₄(2) or PSL₄(3). Their sole earlier embedding input occurs in the seed
centralizer argument. Replace those seed leaves by the proved common-normal
theorems over the complete known-simple catalogue, retaining the original
relative normality, endpoint inclusions and root maps.

The internal `import all` makes the existing proof-specialization elaborator
available without exporting it. It reconstructs the original normal-branch
proof from its checked bodies; Lean checks every specialized declaration.
The final application excludes normality of the literal residual in a
counterexample to the degree-five conclusion.

Source: Aschbacher–Smith 13.5.17–18, printed p.922, using 13.5.15 and F.4.31.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
  (hn : ((residualCentralizer L V₁).subgroupOf H).Normal)
include d hH hU hn

/-- Original 13.5.17, with the earlier embedding input discharged. -/
theorem source13_5_17_knownSimple :
    ClassicalGroup.IsPSU G 4 2 ∨ ClassicalGroup.IsPSL G 4 3 := by
  exact (seed_specialization% source13_5_17) d hH hU hn

/-- The normal branch supplies the literal degree-five conclusion of 13.5.12. -/
theorem source_normal_modelConclusion_knownSimple : ModelConclusion G 5 :=
  Or.inl ⟨rfl, source13_5_17_knownSimple d hH hU hn⟩

omit hn in
/-- Original 13.5.18 in the A₅ counterexample branch, on the literal residual. -/
theorem source13_5_18_knownSimple (hnot : ¬ ModelConclusion G 5) :
    ¬ ((residualCentralizer L V₁).subgroupOf H).Normal := by
  intro hnormal
  exact hnot (source_normal_modelConclusion_knownSimple d hH hU hnormal)

end CFSG.Quasithin.Chapter13.Section05.A5Source
