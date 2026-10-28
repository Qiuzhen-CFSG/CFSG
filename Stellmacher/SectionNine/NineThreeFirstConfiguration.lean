module
public import Stellmacher.SectionNine.NineThreeInitialExtractionInputs
public import Stellmacher.SectionNine.NineThreeFirstSmallFixedSubgroup
public import Stellmacher.SectionNine.NineThreeFirstCenterIntersections
public import Stellmacher.SectionFiveToSeven.Result7_8.PrescribedActorConfiguration

/-!
# First geometric configuration in Stellmacher (9.3)

Under the actual ambient Section Nine hypotheses, critical distance greater
than one and initial center order greater than four give the first geometric
extraction together with the center intersections and index bounds of (2).
The record retains the penultimate vertex, prescribed initial-center actor,
extracted group and its actual residual conjugator for the second extraction.

Critical minimality and (7.5) supply the actor module and its trivial Frattini
subgroup. Prescribed-actor (7.8) and the geometric conversion give (i)–(v).
The quadratic fixed-subgroup argument provides the small subgroup W; the
proved intersection argument, using (9.2), then gives the equal intersections,
index bound and both noncontainments in source relation (2).

Source: Stellmacher, Journal of Algebra 190 (1997), (9.3), p.49, through (2),
`refs/files/stellmacher-n-group.pdf`. No conclusion of (9.3) is assumed.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public structure NineThreeFirstConfigurationData
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B) where
  l : ctx.Γ.Vertex
  penultimate : l = ctx.criticalPath.path ⟨ctx.criticalPath.length-1,
    Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  actor : G
  actor_initial : actor ∈ ZAt ctx.Γ ctx.criticalPath.a
  E : Subgroup G
  A0 : Subgroup G
  extraction : NineThreeGeometricData ctx.Γ ctx.criticalPath.a' l
    (VAt ctx.Γ ctx.criticalPath.firstStep) E A0 actor
  center_intersection :
    ZAt ctx.Γ (ctx.Γ.act extraction.x⁻¹ l) ⊓ QAt ctx.Γ ctx.criticalPath.a =
      ZAt ctx.Γ (ctx.Γ.act extraction.x⁻¹ l) ⊓ ZAt ctx.Γ l
  center_index : Nat.card
      (ZAt ctx.Γ (ctx.Γ.act extraction.x⁻¹ l) ⊓ GAt ctx.Γ ctx.criticalPath.a : Subgroup G) ≤
    2 * Nat.card
      (ZAt ctx.Γ (ctx.Γ.act extraction.x⁻¹ l) ⊓ QAt ctx.Γ ctx.criticalPath.a : Subgroup G)
  center_not_le : ¬ ZAt ctx.Γ (ctx.Γ.act extraction.x⁻¹ l) ≤ GAt ctx.Γ ctx.criticalPath.a
  terminal_module_not_le : ¬ VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep

public theorem nine_three_first_configuration
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a)) :
    Nonempty (NineThreeFirstConfigurationData ctx) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let l := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let V := VAt Γ cp.firstStep
  obtain ⟨hl,hV,hElem,hPhi,hquad1,hquad2,actor,haZ,haV,haNot⟩ :=
    nine_three_initial_extraction_inputs ctx.toLocalContext hb
  have hPhiLe : frattiniAmbient V ≤ QAt Γ cp.a' := by
    have hh : frattiniAmbient V = ⊥ := hPhi
    rw [hh]
    exact bot_le
  have hVnot : ¬ V ≤ QAt Γ cp.a' := fun hle => haNot (hle haV)
  obtain ⟨y,A0,E,hEP,hyP,h0A,hgen,hcard,hyE,hySq,h0core,hedge,hmodel,horbit,hby,hres,ha0⟩ :=
    sevenEight_quotient_configuration_with_actor ctx.sectionSeven Γ cp.a' l hl V hV hVnot
      hPhiLe actor haV haNot
  obtain ⟨data⟩ := nine_three_geometric_extraction ctx.sectionSeven Γ cp.a' l hl
    V E A0 hV hPhiLe actor haV ha0 y hyE hEP hgen h0A hcard h0core hedge hmodel hby
  obtain ⟨W,hWm,hWa,hWl,hWcard,hEC,hCW⟩ :=
    nine_three_first_small_fixed_subgroup ctx hb l E A0 actor haZ data
  obtain ⟨hinter,hindex,hnot,hVend⟩ := nine_three_first_center_intersections ctx hb hlarge
    l rfl E A0 actor haV haZ data W hWm hWa hWl hWcard
  exact ⟨{ l := l
           penultimate := rfl
           actor := actor
           actor_initial := haZ
           E := E
           A0 := A0
           extraction := data
           center_intersection := hinter
           center_index := hindex
           center_not_le := hnot
           terminal_module_not_le := hVend }⟩

end Stellmacher.SectionNine
