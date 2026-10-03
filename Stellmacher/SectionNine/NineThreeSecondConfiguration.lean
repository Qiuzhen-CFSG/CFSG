module
public import Stellmacher.SectionNine.NineThreeFirstConfiguration
public import Stellmacher.SectionNine.NineThreeSecondExtractionInputs
public import Stellmacher.SectionNine.NineThreeSelectedEdgeBaumann
public import Stellmacher.SectionFiveToSeven.Result7_8.SelectedBaumannActorConfiguration
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricBaumannTransport

/-!
# Second selected-Baumann extraction in Stellmacher (9.3)

Retain the first geometric configuration and its proved relation (2). The
terminal neighbor-center module supplies a second extraction at the edge
from the first step to the second path vertex. The new configuration keeps
a prescribed actor in the first extracted center and an actual Sylow of its
new edge for which the extracted residual lies in its Baumann commutator.

Relation (2) supplies an actor outside the initial stabilizer and hence
outside the first-step core. Critical minimality and (7.5) supply the second
edge and the elementary actor module. Apply prescribed-actor (7.8) with a
selected edge Sylow; (6.1), transported in the ambient context, gives its
Baumann noncontainment. Geometric extraction replaces the conjugator by an
actual residual element. Conjugating the selected Sylow with that element
preserves the residual bound and places it on the newly extracted edge.

Source: Stellmacher (9.3), Journal of Algebra 190 (1997), p.49, the second
application of (7.8) and assertion (3), `refs/files/stellmacher-n-group.pdf`.
No simultaneous bound for several Sylows or extra critical-distance
assumption is used.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public structure NineThreeSecondConfigurationData
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (first : NineThreeFirstConfigurationData ctx) where
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

public theorem nine_three_second_configuration
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (first : NineThreeFirstConfigurationData ctx) :
    Nonempty (NineThreeSecondConfigurationData ctx first) := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let l := cp.path ⟨2,by dsimp [cp]; omega⟩
  let V := VAt Γ cp.a'
  let m := Γ.act first.extraction.x⁻¹ first.l
  obtain ⟨hl,hV,hElem,hPhi⟩ := nine_three_second_extraction_inputs ctx.toLocalContext hb
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
  have hPhiLe : frattiniAmbient V ≤ QAt Γ cp.firstStep := by
    have hh : frattiniAmbient V = ⊥ := hPhi
    rw [hh]
    exact bot_le
  let U : Sylow 2 ↥(GAt Γ cp.firstStep ⊓ GAt Γ l) := default
  have hBaumann := nine_three_selected_edge_baumann_not_le_core ctx l hl U
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

end Stellmacher.SectionNine
