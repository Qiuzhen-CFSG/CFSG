module

public import Stellmacher.SectionNine.NineSevenCommutatorCenters
public import Stellmacher.SectionNine.NineSevenCenterLines
public import Stellmacher.SectionNine.NineSevenB7WitnessSelection

/-!
# Commutator geometry in (9.7)

This is the exact long-distance commutator geometry from (9.7), including the
two center witnesses and the exclusion of length seven. The length-seven
contradiction uses the genuine middle-center direct-product decomposition.

Source: Stellmacher, printed p.53 / PDF p.43, (9.7), in
`refs/files/stellmacher-n-group.pdf`.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

private theorem path_even_shift_conjugate
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (start steps : ℕ)
    (hbound : start + 2 * steps ≤ ctx.criticalPath.length) :
    IsConjugateVertex ctx.Γ
      (ctx.criticalPath.path ⟨start, by omega⟩)
      (ctx.criticalPath.path ⟨start + 2 * steps, by omega⟩) := by
  induction steps with
  | zero =>
    exact ⟨1, by simpa using ctx.Γ.act_one (ctx.criticalPath.path ⟨start, by omega⟩)⟩
  | succ steps ih =>
    obtain ⟨first, hfirst⟩ := ih (by omega)
    have hleft := ctx.criticalPath.path_adj ⟨start + 2 * steps, by omega⟩
    have hright := ctx.criticalPath.path_adj ⟨start + 2 * steps + 1, by omega⟩
    obtain ⟨second, hsecond⟩ :=
      (lemma_seven_one ctx.sectionSeven ctx.Γ).local_transitivity
        (ctx.criticalPath.path ⟨start + 2 * steps + 1, by omega⟩)
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr (ctx.Γ.adjacent_symm hleft))
        ((mem_neighborhood_iff_adjacent ctx.Γ).mpr hright)
    refine ⟨first * (second : G), ?_⟩
    rw [ctx.Γ.act_mul, hfirst]
    convert hsecond using 1 <;> congr 1

private theorem initial_orbit_of_even_offset
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (offset : ℕ)
    (hbound : offset ≤ ctx.criticalPath.length) (heven : Even offset) :
    IsConjugateVertex ctx.Γ ctx.criticalPath.a
      (ctx.criticalPath.path ⟨offset, by omega⟩) := by
  obtain ⟨half, hhalf⟩ := heven
  have horbit := path_even_shift_conjugate ctx 0 half (by omega)
  have hnum : 2 * half = offset := by
    omega
  have hpath0 : ctx.criticalPath.path ⟨0, by omega⟩ = ctx.criticalPath.a :=
    ctx.criticalPath.path_start
  rw [hpath0] at horbit
  have horbit' : IsConjugateVertex ctx.Γ ctx.criticalPath.a
      (ctx.criticalPath.path ⟨offset, by omega⟩) := by
    simpa [hnum] using horbit
  exact horbit'

public theorem nine_seven_commutator_geometry
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (third : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 3 third)
    (hindex : QuotientCardEq (VAt ctx.Γ ctx.criticalPath.firstStep)
      (VAt ctx.Γ ctx.criticalPath.firstStep ⊓ VAt ctx.Γ third) 2)
    (hfirstCard : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 2^3)
    (hfirstModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (hendCard : Nat.card (VAt ctx.Γ ctx.criticalPath.a') = 2^3)
    (hendModel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a')
      (QAt ctx.Γ ctx.criticalPath.a') SL2Two)
    (hstartData : ∀ vertex, IsConjugateVertex ctx.Γ ctx.criticalPath.a vertex →
      QuotientIsModel (GAt ctx.Γ vertex) (QAt ctx.Γ vertex) SL2Two ∧
        Nat.card (ZAt ctx.Γ vertex) = 4)
    (hlong : 3 < ctx.criticalPath.length) :
    let Γ := ctx.Γ
    let cp := ctx.criticalPath
    let second := cp.path ⟨2, by dsimp [cp]; omega⟩
    let penultimate := cp.path ⟨cp.length - 1, by dsimp [cp]; omega⟩
    let R := ⁅VAt Γ cp.a', ZAt Γ cp.a⁆
    Nat.card R = 2 ∧
      R ≤ ZAt Γ second ∧ R ≤ ZAt Γ penultimate ∧
      (∃ rho, rho ∈ Neighborhood Γ second ∧ R = ZAt Γ rho) ∧
      (∃ rho', rho' ∈ Neighborhood Γ penultimate ∧ R = ZAt Γ rho') ∧
      cp.length ≠ 7 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let second := cp.path ⟨2, by dsimp [cp]; omega⟩
  let penultimate := cp.path ⟨cp.length - 1, by dsimp [cp]; omega⟩
  let R := ⁅VAt Γ cp.a', ZAt Γ cp.a⁆
  obtain ⟨hRcard, hRsecond, hRpen⟩ := nine_seven_commutator_centers ctx hb third
    hpath hindex hfirstCard hfirstModel hendCard hendModel hstartData hlong
  have hodd := (lemma_seven_five ctx.sectionSeven Γ cp ctx.commutator_eq).odd_distance
  have hlongcp : 3 < cp.length := hlong
  have hlen2 : 2 ≤ cp.length := by omega
  have hlen2' : 2 ≤ ctx.toLocalContext.criticalPath.length := by
    simpa only [show ctx.toLocalContext.criticalPath = cp from rfl] using hlen2
  have hsecondOrbit0 := initial_orbit_of_even_offset ctx.toLocalContext 2 hlen2' ⟨1, by rfl⟩
  have hsecondOrbit : IsConjugateVertex Γ cp.a second := by
    exact hsecondOrbit0
  obtain ⟨halfLength, hhalfLength⟩ := hodd
  have hlenPen : cp.length - 1 ≤ cp.length := by omega
  have hlenPen' : cp.length - 1 ≤ ctx.toLocalContext.criticalPath.length := by
    simpa only [show ctx.toLocalContext.criticalPath = cp from rfl] using hlenPen
  have hpenOrbit0 := initial_orbit_of_even_offset ctx.toLocalContext (cp.length - 1)
    hlenPen' ⟨halfLength, by omega⟩
  have hpenOrbit : IsConjugateVertex Γ cp.a penultimate := by
    exact hpenOrbit0
  have hsecondLines := nine_seven_center_lines ctx hb hfirstModel hstartData second
    hsecondOrbit
  have hpenLines := nine_seven_center_lines ctx hb hfirstModel hstartData penultimate
    hpenOrbit
  obtain ⟨rho, hrho, hReq⟩ := hsecondLines.2.1 R hRcard hRsecond
  obtain ⟨rho', hrho', hReq'⟩ := hpenLines.2.1 R hRcard hRpen
  have hnotseven : cp.length ≠ 7 := by
    intro hseven
    obtain ⟨hleftEq, hrightEq⟩ := nine_seven_b7_commutator_witness_selection
      ctx third hpath hindex hfirstCard hfirstModel hendCard hendModel hstartData hseven
    change R = ZAt Γ (cp.path ⟨3, by omega⟩) at hleftEq
    change R = ZAt Γ (cp.path ⟨5, by omega⟩) at hrightEq
    have hlenEq : ctx.toLocalContext.criticalPath.length = cp.length := by rfl
    have hmiddleBound : 4 ≤ ctx.toLocalContext.criticalPath.length := by
      rw [hlenEq]
      omega
    have hmiddleOrbit := initial_orbit_of_even_offset ctx.toLocalContext 4 hmiddleBound ⟨2, by omega⟩
    have hmiddleLines := nine_seven_center_lines ctx hb hfirstModel hstartData
      (cp.path ⟨4, by omega⟩) hmiddleOrbit
    have hne : cp.path ⟨3, by omega⟩ ≠ cp.path ⟨5, by omega⟩ := by
      intro heq
      have hdist := Γ.distance_le_of_path 5 (fun i : Fin 6 =>
        ![cp.path ⟨0, by omega⟩, cp.path ⟨1, by omega⟩,
          cp.path ⟨2, by omega⟩, cp.path ⟨3, by omega⟩,
          cp.path ⟨6, by omega⟩, cp.path ⟨7, by omega⟩] i) (by
        intro i
        fin_cases i
        · exact cp.path_adj ⟨0, by omega⟩
        · exact cp.path_adj ⟨1, by omega⟩
        · exact cp.path_adj ⟨2, by omega⟩
        · rw [heq]
          exact cp.path_adj ⟨5, by omega⟩
        · exact cp.path_adj ⟨6, by omega⟩)
      change Γ.distance (cp.path ⟨0, by omega⟩) (cp.path ⟨7, by omega⟩) ≤ 5 at hdist
      have hzero : cp.path ⟨0, by omega⟩ = cp.a := cp.path_start
      have hend : cp.path ⟨7, by omega⟩ = cp.a' := by
        simpa only [hseven] using cp.path_end
      rw [hzero, hend, cp.endpoint_distance, hseven] at hdist
      omega
    have hdisj := hmiddleLines.2.2 (cp.path ⟨3, by omega⟩)
      (cp.path ⟨5, by omega⟩)
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm (cp.path_adj ⟨3, by omega⟩)))
      ((mem_neighborhood_iff_adjacent Γ).mpr (cp.path_adj ⟨4, by omega⟩)) hne
    have hbot : ZAt Γ (cp.path ⟨3, by omega⟩) ⊓
        ZAt Γ (cp.path ⟨5, by omega⟩) = ⊥ := disjoint_iff.mp hdisj
    have hRbot : R ⊓ R = ⊥ := by
      rwa [← hleftEq, ← hrightEq] at hbot
    have hRzero : R = ⊥ := by simpa only [inf_idem] using hRbot
    change Nat.card R = 2 at hRcard
    rw [hRzero] at hRcard
    simp at hRcard
  refine ⟨hRcard, hRsecond, hRpen, ⟨rho, hrho, hReq⟩, ⟨rho', hrho', hReq'⟩, hnotseven⟩

end Stellmacher.SectionNine

#print axioms Stellmacher.SectionNine.nine_seven_commutator_geometry
