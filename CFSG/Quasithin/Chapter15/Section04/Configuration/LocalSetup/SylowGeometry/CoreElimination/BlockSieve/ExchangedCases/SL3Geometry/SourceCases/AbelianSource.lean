module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.Intrinsic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryAbelian.ExceptionalRadical
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.SourceCases.MSContract
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry.Section

/-!
# The abelian binary MS branch in the original source exclusion

The actual quotient orders exclude MS2(b) with a binary SL₃ component, so the
full original MS-pair constructs BinaryMS.Input. Its abelian intrinsic natural
quotient provides a section on the whole block commutator, covering its center
and having exactly the component-fixed kernel. The literal selected-component
consumer applies the existing centralizer obstruction without a classification
callback or a chosen radical alternative.

Source: Aschbacher–Smith C.1.31–34, printed pp.135–137; 15.4.20, p.1164.
-/

public section
open Subgroup CFSG.Quasithin.ChapterC
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry
universe u
namespace SourceCases
variable {D : Type u} [Group D] [Finite D] {κ : GroupClass.{u}} {L R : Subgroup D}

/-- The full binary MS input excludes the exceptional G₂ radical internally. -/
noncomputable def MSPair.binaryInput (h : MSPair κ D L R)
    (e : (L ⧸ pCore 2 L) ≃* Natural.Actor) : BinaryMS.Input κ L R where
  sqtk := h.sqtk
  fitting := h.fitting
  product := h.product
  component := h.component
  characteristic := h.characteristic
  quotientEquiv := e
  radical := by
    rcases h.radical_alternatives with hr | hr
    · exact hr
    · obtain ⟨eG,_,P,_,_,_,_,hR⟩ := hr
      exact (BinaryMS.not_exceptional_radical_of_binary_component h.component.subnormal e
        h.product eG hR).elim

/-- Genuine abelian MS cores produce the actual section used by the source exclusion. -/
theorem MSPair.abelian_coreCenterSection (h : MSPair κ D L R)
    (e : (L ⧸ pCore 2 L) ≃* Natural.Actor)
    (hc : IsMulCommutative (BinaryMS.commutatorCore L)) :
    ∃ a : ℕ, (a = 1 ∨ a = 2) ∧ Nonempty (CoreCenterSection L a) := by
  obtain ⟨a,e',f,ha,_,hk,he,_,_⟩ := (h.binaryInput e).abelian_intrinsic_natural_quotient hc
  refine ⟨a,ha,⟨{
    quotientIso := e'
    layer := blockU L
    normal := inferInstance
    center_le := map_subtype_le _
    map := f
    intertwining := ?_
    kernel_central := ?_ }⟩⟩
  · intro l b
    funext i
    exact he l b i
  · intro b hb
    have hbf : b ∈ f.ker := hb
    rw [hk] at hbf
    exact hbf
end SourceCases

variable {G : Type u} [Group G] [Finite G]
variable {d : Source.Geometry G} {i j : Bool} {H U K K₁ : Subgroup G} {r : G}

/-- The literal selected SL₃ source component cannot have abelian core.
The full MS-pair hypothesis supplies the earlier-source input; no module
section or radical-alternative choice is a premise. -/
theorem not_source_ms_abelian_core (h : Input d i j H U K)
    (s : Selected H U K K₁ r) {κ : GroupClass.{u}} {R : Subgroup H}
    (hMS : SourceCases.MSPair κ H (K₁.subgroupOf H) R)
    (e : ((K₁.subgroupOf H) ⧸ pCore 2 (K₁.subgroupOf H)) ≃* Natural.Actor)
    (hc : IsMulCommutative (BinaryMS.commutatorCore (K₁.subgroupOf H))) : False := by
  obtain ⟨a,_,⟨m⟩⟩ := hMS.abelian_coreCenterSection e hc
  exact not_source_coreCenterSection h s m
end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SL3Geometry
