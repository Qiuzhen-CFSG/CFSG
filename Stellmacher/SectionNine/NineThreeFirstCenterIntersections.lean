module
public import Stellmacher.SectionNine.NineThreeGeometricCenterIntersections
public import Stellmacher.SectionNine.NineThreeInitialExtractionInputs

/-!
# The first center-intersection relations in (9.3)

Specialize the generic geometric intersection theorem to the first
extraction at the terminal edge of the actual commuting critical path.
The initial center has order greater than four, and the supplied subgroup
W has the three containments and doubled-cardinality bound produced by
the independent quadratic fixed-subgroup argument.

Critical minimality puts the penultimate center in the initial core.
The center/core theorem supplies centralization, while endpoint alignment
in (7.5) identifies the penultimate and initial center cardinalities.
These are precisely the hypotheses of the generic intersection theorem,
which proves the intersection equality, cardinality bound, and extracted
center noncontainment. Since the terminal neighbor-center module contains
that center and the first-step core lies in the initial stabilizer, the
terminal module also lies outside the first-step core.

The public theorem, hypotheses, and exact extraction data are unchanged.
Source: Stellmacher (9.3), relation (2), Journal of Algebra 190 (1997),
p.49, `refs/files/stellmacher-n-group.pdf`. No distance-three specialization
or additional property of W is assumed.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_three_first_center_intersections
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 1 < ctx.criticalPath.length)
    (hlarge : 4 < Nat.card (ZAt ctx.Γ ctx.criticalPath.a))
    (l : ctx.Γ.Vertex)
    (hl : l = ctx.criticalPath.path ⟨ctx.criticalPath.length-1, by omega⟩)
    (E A0 : Subgroup G) (actor : G)
    (haV : actor ∈ VAt ctx.Γ ctx.criticalPath.firstStep)
    (haZ : actor ∈ ZAt ctx.Γ ctx.criticalPath.a)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.a' l
      (VAt ctx.Γ ctx.criticalPath.firstStep) E A0 actor)
    (W : Subgroup G)
    (hWm : W ≤ ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l))
    (hWa : W ≤ QAt ctx.Γ ctx.criticalPath.a)
    (hWl : W ≤ ZAt ctx.Γ l)
    (hbound : Nat.card ↥(ZAt ctx.Γ (ctx.Γ.act data.x⁻¹ l) ⊓
      GAt ctx.Γ ctx.criticalPath.a) ≤ 2 * Nat.card W) :
    let m := ctx.Γ.act data.x⁻¹ l
    ZAt ctx.Γ m ⊓ QAt ctx.Γ ctx.criticalPath.a = ZAt ctx.Γ m ⊓ ZAt ctx.Γ l ∧
      Nat.card ↥(ZAt ctx.Γ m ⊓ GAt ctx.Γ ctx.criticalPath.a) ≤
        2 * Nat.card ↥(ZAt ctx.Γ m ⊓ QAt ctx.Γ ctx.criticalPath.a) ∧
      ¬ ZAt ctx.Γ m ≤ GAt ctx.Γ ctx.criticalPath.a ∧
      ¬ VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let m := Γ.act data.x⁻¹ l
  have hlNeigh : l ∈ neighborhood Γ cp.a' := by
    rw [hl]
    exact (nine_three_initial_extraction_inputs ctx.toLocalContext hb).1
  have hVQl : VAt Γ cp.firstStep ≤ QAt Γ l := by
    rw [hl]
    exact (nine_three_initial_extraction_inputs ctx.toLocalContext hb).2.1
  have hlQa : ZAt Γ l ≤ QAt Γ cp.a := by
    apply critical_minimality Γ cp
    have hd := path_distance_le Γ cp 0 (cp.length-1) (by omega) (by omega)
    have hd' : Γ.distance cp.a l ≤ cp.length-1 := by
      have hs : cp.path ⟨0,by omega⟩ = cp.a := cp.path_start
      have he : l = cp.path ⟨cp.length-1,by omega⟩ := hl
      simpa only [Nat.sub_zero,hs,← he] using hd
    rw [Γ.distance_symm]
    exact lt_of_le_of_lt hd' (by have := cp.length_pos; omega)
  have hfirst : cp.firstStep ∈ neighborhood Γ cp.a :=
    (mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hZa : ZAt Γ cp.a ≤ Subgroup.centralizer (QAt Γ cp.a : Set G) :=
    ((lemma_seven_three ctx.sectionSeven Γ).center_core cp.a cp.firstStep hfirst).trans
      ((omegaOneCenter_le_centerAmbient _).trans (centerAmbient_le_centralizer _))
  have hlaCard : Nat.card (ZAt Γ l) = Nat.card (ZAt Γ cp.a) := by
    obtain ⟨g,hg,_⟩ := lemma_seven_five_endpoint_alignment ctx.sectionSeven Γ cp ctx.commutator_eq
    have he : Γ.act g cp.a = l := hg.trans hl.symm
    rw [← he]
    change Nat.card (z Γ (Γ.act g cp.a)) = _
    rw [z_act]
    exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  have hlargeL : 4 < Nat.card (ZAt Γ l) := hlaCard.symm ▸ hlarge
  obtain ⟨hF_eq,hcardBound,hmGa⟩ := nine_three_geometric_center_intersections ctx
    cp.a cp.a' l ⟨1,Γ.act_one _⟩ hlNeigh (VAt Γ cp.firstStep) E A0 hVQl
    actor haV haZ hZa hlQa hlargeL data W hWm hWa hWl hbound
  refine ⟨hF_eq,hcardBound,hmGa,?_⟩
  intro hVcore
  apply hmGa
  have hZmV : ZAt Γ m ≤ VAt Γ cp.a' := by
    rw [VAt,v,Γ.vAt_def]
    exact le_sSup ⟨m,data.neighbor,rfl⟩
  exact hZmV.trans (hVcore.trans ((local_cores_le_edge_sylow ctx.sectionSeven Γ cp).2.trans
    (cp.S_le_edge_stabilizers.trans inf_le_left)))
end Stellmacher.SectionNine
