module
public import Stellmacher.SectionNine.NineThreeCenterSplitting
public import Stellmacher.SectionNine.NineFivePenultimateResidualGeneration

/-!
# A center-plane line centralizes a swap of the other two neighbors

An order-two line in the penultimate center, distinct from the terminal and
preterminal centers, is centralized by an element of the penultimate
stabilizer carrying the terminal vertex to the preterminal vertex.

The three neighbor-center lines exhaust the four-element center plane, so
the supplied line is the center of the third neighbor. That neighbor's core
centralizes its center and is not contained in the penultimate core. Cubic
punctured transitivity therefore supplies the required mover inside that core.

This proves the center-plane case of the centralizing-conjugator assertion
following Stellmacher (9.9)(3), printed p.56/PDF p.46 of
`refs/files/stellmacher-n-group.pdf`. Only the stated line hypotheses and
critical length greater than one are required.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_nine_center_plane_centralizing_conjugator
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (R : Subgroup G) (hRcard : Nat.card R = 2)
    (hRplane : R ≤ ZAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩))
    (hRterminal : R ≠ ZAt ctx.Γ ctx.criticalPath.a')
    (hRpreterminal : R ≠ ZAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) :
    ∃ y : G,
      y ∈ GAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ∧
      y ∈ Subgroup.centralizer (R : Set G) ∧
      ctx.Γ.act y ctx.criticalPath.a' = ctx.criticalPath.path
        ⟨ctx.criticalPath.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hpath : IsCriticalPathOffset Γ cp (cp.length-2) preterminal :=
    ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩
  have hterminalAdj := nine_five_penultimate_adjacent ctx.toLocalContext
  have hpreAdj := Γ.adjacent_symm
    (nine_five_previous_adjacent_penultimate ctx.toLocalContext hb preterminal hpath)
  obtain ⟨alignment,halign,_⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven Γ cp ctx.commutator_eq
  have hpenOrbit : IsConjugateVertex Γ cp.a penultimate := ⟨alignment,halign⟩
  obtain ⟨hmodel,hplaneCard⟩ := lemma_nine_three_ambient ctx hb penultimate hpenOrbit
  obtain ⟨hjoin,hcenters⟩ := nine_seven_center_join ctx penultimate hpenOrbit
  obtain ⟨_,hcover,_⟩ := nine_seven_center_lines_of_center_join
    ctx.sectionSeven Γ penultimate hmodel hplaneCard hjoin hcenters
  obtain ⟨third,hthird,hRthird⟩ := hcover R hRcard hRplane
  have hthirdAdj := (mem_neighborhood_iff_adjacent Γ).mp hthird
  have hterminalNe : cp.a' ≠ third := by
    intro heq
    exact hRterminal (hRthird.trans (congrArg (ZAt Γ) heq.symm))
  have hpreNe : preterminal ≠ third := by
    intro heq
    exact hRpreterminal (hRthird.trans (congrArg (ZAt Γ) heq.symm))
  have hQthirdPen : QAt Γ third ≤ GAt Γ penultimate :=
    ((lemma_seven_three ctx.sectionSeven Γ).sylow_and_core third penultimate
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hthirdAdj)) default).2.2
  have hQthirdSelf : QAt Γ third ≤ GAt Γ third := by
    rw [QAt,q,Γ.twoCoreAt_def]
    exact twoCoreIn_le _
  have hescape := nine_five_penultimate_neighbor_core_not_le ctx.toLocalContext third hthirdAdj
  have htrans := (cubic_local_action_of_sl2Two_quotient Γ ctx.sectionSeven
    penultimate hmodel).punctured_transitivity third hthirdAdj (QAt Γ third)
      (le_inf hQthirdPen hQthirdSelf) hescape
  obtain ⟨mover,hmove⟩ := htrans (d := cp.a') (l := preterminal)
      ⟨(mem_neighborhood_iff_adjacent Γ).mpr hterminalAdj,by simpa using hterminalNe⟩
      ⟨(mem_neighborhood_iff_adjacent Γ).mpr hpreAdj,by simpa using hpreNe⟩
  have hRcentral : R ≤ Subgroup.centralizer (QAt Γ third : Set G) := by
    rw [hRthird]
    intro z hz
    exact Subgroup.mem_centralizer_iff.mpr
      ((mem_omegaOneCenterAmbient_iff (QAt Γ third) z).mp
        ((lemma_seven_three ctx.sectionSeven Γ).center_core third penultimate
          ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm hthirdAdj)) hz)).2.2
  exact ⟨mover,hQthirdPen mover.property,
    (Subgroup.le_centralizer_iff.mp hRcentral) mover.property,hmove⟩

end Stellmacher.SectionNine
