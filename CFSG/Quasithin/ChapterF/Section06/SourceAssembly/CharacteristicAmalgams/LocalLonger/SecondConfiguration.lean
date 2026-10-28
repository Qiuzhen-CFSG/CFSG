module
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalLonger.FirstConfiguration
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalDistanceOne
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.CharacteristicAmalgams.LocalLonger.LargeCenterBaumann
public import Stellmacher.SectionNine.NineThreeSecondExtractionInputs
public import Stellmacher.SectionFiveToSeven.Result7_8.SelectedBaumannActorConfiguration
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricBaumannTransport

/-!
# The second selected extraction in a cubic Goldschmidt triple

The first configuration supplies a terminal-module vector outside the
initial vertex. The large-center Baumann theorem supplies noncontainment
for the actual selected edge Sylow. Prescribed-actor (7.8) then constructs
the second group, and geometric conjugation retains an exact Sylow on the
new edge whose Baumann commutator contains the actual second residual.

This completes the local cubic construction through Stellmacher (9.3)(3),
Journal of Algebra 190 (1997), p.49. It does not assert the subsequent
common-centralizer contradiction or the universal amalgam bound.
-/

namespace Stellmacher.SectionNine.LocalLonger
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public structure SecondConfigurationData
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (first : FirstConfigurationData ctx) where
  l : ctx.Γ.Vertex
  second : ∃ h : 2 < ctx.criticalPath.length+1, l=ctx.criticalPath.path ⟨2,h⟩
  actor : G
  actor_first_center : actor ∈ ZAt ctx.Γ (ctx.Γ.act first.extraction.x⁻¹ first.l)
  E : Subgroup G
  A0 : Subgroup G
  extraction : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep l
    (VAt ctx.Γ ctx.criticalPath.a') E A0 actor
  new_sylow : Sylow 2 ↥(GAt ctx.Γ ctx.criticalPath.firstStep ⊓
    GAt ctx.Γ (ctx.Γ.act extraction.x⁻¹ l))
  residual_baumann : twoResidualIn E ≤ ⁅twoResidualIn E,baumannIn
    (sylowTwoAmbient (GAt ctx.Γ ctx.criticalPath.firstStep ⊓
      GAt ctx.Γ (ctx.Γ.act extraction.x⁻¹ l)) new_sylow)⁆

end Stellmacher.SectionNine.LocalLonger

namespace CFSG.Quasithin.ChapterF
open Theory.GroupTheory Stellmacher Stellmacher.Later Stellmacher.SectionsFiveToSeven
open Stellmacher.SectionsFiveToSeven.CosetGraphContext
open Stellmacher.SectionsFiveToSeven.SevenSix Stellmacher.SectionNine
universe u
variable {G : Type u} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

/-- Both literal geometric extractions, including the selected Baumann residual relation. -/
public theorem IsGoldschmidtTriple.exists_two_extractions_of_large_center
    (h : IsGoldschmidtTriple G₁ G₂) (hcore : pCore 2 G = ⊥)
    (hgood₁ : generalizedFitting G₁ = pCore 2 G₁)
    (hgood₂ : generalizedFitting G₂ = pCore 2 G₂)
    (Γ : CosetGraphContext.{u,u} G (G₁ ⊓ G₂) G₁ G₂) (cp : CriticalPath Γ)
    (hcomm : ⁅z Γ cp.a,z Γ cp.a'⁆ = ⊥)
    (hlarge : 4 < Nat.card (ZAt Γ cp.a)) :
    let ctx : SectionNineLocalContext G (G₁ ⊓ G₂) G₁ G₂ :=
      ⟨h.sectionSeven_of_characteristic_two hcore hgood₁ hgood₂, Γ, cp, hcomm⟩
    ∃ first : LocalLonger.FirstConfigurationData ctx,
      Nonempty (LocalLonger.SecondConfigurationData ctx first) := by
  classical
  have hb := h.critical_length_gt_one_of_commuting hcore hgood₁ hgood₂ Γ cp hcomm
  let ctx : SectionNineLocalContext G (G₁ ⊓ G₂) G₁ G₂ :=
    ⟨h.sectionSeven_of_characteristic_two hcore hgood₁ hgood₂, Γ, cp, hcomm⟩
  change ∃ first : LocalLonger.FirstConfigurationData ctx,
    Nonempty (LocalLonger.SecondConfigurationData ctx first)
  have he : Nonempty (((stabilizer Γ cp.a) ⧸ pCore 2 (stabilizer Γ cp.a)) ≃*
      Equiv.Perm (Fin 3)) := by
    rcases cp.edge_stabilizers_are_P with he | he
    · rw [show stabilizer Γ cp.a = G₁ from he.1]
      exact h.quotient_left
    · rw [show stabilizer Γ cp.a = G₂ from he.1]
      exact h.quotient_right
  obtain ⟨first⟩ := LocalLonger.exists_first_configuration ctx he.some hb hlarge
  refine ⟨first, ?_⟩
  let l := cp.path ⟨2,by omega⟩
  let V := VAt Γ cp.a'
  let m := Γ.act first.extraction.x⁻¹ first.l
  obtain ⟨hl,hV,hElem,hPhi⟩ := nine_three_second_extraction_inputs ctx hb
  obtain ⟨actor,haZ,haNot⟩ := Set.not_subset.mp first.center_not_le
  have hZV : ZAt Γ m ≤ V := by
    change z Γ m ≤ v Γ cp.a'
    rw [v,Γ.vAt_def]
    exact le_sSup ⟨m,first.extraction.neighbor,rfl⟩
  have haV : actor ∈ V := hZV haZ
  have hQfirst : QAt Γ cp.firstStep ≤ GAt Γ cp.a :=
    (local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2.trans
      (cp.S_le_edge_stabilizers.trans inf_le_left)
  have haQ : actor ∉ QAt Γ cp.firstStep := fun ha => haNot (hQfirst ha)
  have hPhiLe : SectionsFiveToSeven.frattiniAmbient V ≤ QAt Γ cp.firstStep := by
    have hh : SectionsFiveToSeven.frattiniAmbient V = ⊥ := hPhi
    rw [hh]
    exact bot_le
  let U : Sylow 2 ↥(GAt Γ cp.firstStep ⊓ GAt Γ l) := default
  have hBaumann := h.critical_selected_edge_baumann_not_le_core_of_large_center
    hcore hgood₁ hgood₂ Γ cp hcomm hlarge l hl U
  obtain ⟨y,A0,E,hEP,hyP,h0A,hgen,hcard,hyE,hySq,h0core,hedge,hmodel,horbit,hby,hres,ha0⟩ :=
    sevenEight_quotient_configuration_for_edge_sylow_with_actor ctx.sectionSeven Γ
      cp.firstStep l hl V hV first.terminal_module_not_le hPhiLe U hBaumann actor haV haQ
  obtain ⟨data⟩ := nine_three_geometric_extraction ctx.sectionSeven Γ cp.firstStep l hl
    V E A0 hV hPhiLe actor haV ha0 y hyE hEP hgen h0A hcard h0core hedge hmodel hby
  obtain ⟨Unew,hnew⟩ := geometric_extraction_baumann_transport Γ cp.firstStep l
    V E A0 actor data U hres
  exact ⟨{ l := l
           second := ⟨_,rfl⟩
           actor := actor
           actor_first_center := haZ
           E := E
           A0 := A0
           extraction := data
           new_sylow := Unew
           residual_baumann := hnew }⟩

end CFSG.Quasithin.ChapterF
