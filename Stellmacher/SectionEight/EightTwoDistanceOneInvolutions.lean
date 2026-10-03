module

public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionEight.CriticalOutsideInvolution

/-!
# Outside involutions at both ends of a critical edge

At critical distance one, both distinguished edge stabilizers contain an
involution outside their two-core. Identify firstStep with the endpoint
of the length-one path. Original criticality supplies an element of the
initial vertex center outside the first-step core; reversed criticality
supplies an element of the first-step center outside the initial core.
The containments of (7.4) place these elements in the opposite stabilizers,
and both centers are elementary abelian by (7.3).

The supplemental theorem uses `SectionEightLocalContext`, with genuine
Section Seven hypotheses and no ambient Sylow parameter. The legacy
theorem is a wrapper through the definitionally graph-preserving adapter.
Neither proof uses the local (6.3) quotient data or center noncentrality.

These are the graph-derived splitting inputs for the final paragraph of
Stellmacher (8.2), Journal of Algebra 190 (1997), p.38, in
`refs/latex/stellmacher-n-group.tex`. They support the whole-stabilizer
classification: weaker local core and quotient data alone permit a
nonsplit extension. No elementary-core or quotient classification is
assumed here.
-/

namespace Stellmacher.SectionEight

open Later SectionsFiveToSeven CosetGraphContext

universe u

private theorem involution_outside_core_of_elementary
    {H : Type u} [Group H] [Finite H]
    (P A : Subgroup H) [IsElementaryAbelian 2 A]
    (hAP : A ≤ P) (hnot : ¬ A ≤ twoCoreIn P) :
    ∃ t : P, t ∉ pCore 2 P ∧ t ^ 2 = 1 := by
  obtain ⟨element, hA, hQ⟩ := SetLike.not_le_iff_exists.mp hnot
  refine ⟨⟨element, hAP hA⟩, ?_, ?_⟩
  · intro hmem
    exact hQ (Subgroup.mem_map_of_mem P.subtype hmem)
  · apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (A := A) element hA

public theorem eight_two_distance_one_edge_involutions_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hlength : ctx.criticalPath.length = 1) :
    ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        ∃ t : GAt ctx.Γ d, t ∉ pCore 2 (GAt ctx.Γ d) ∧ t ^ 2 = 1 := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have h74 := lemma_seven_four ctx.sectionSeven Γ cp
  have hfirst : cp.firstStep = cp.a' := by
    calc
      cp.firstStep = cp.path ⟨1, by have := cp.length_pos; omega⟩ :=
        cp.path_first.symm
      _ = cp.path ⟨cp.length, Nat.lt_succ_self _⟩ := by
        congr 1
        apply Fin.ext
        exact hlength.symm
      _ = cp.a' := cp.path_end
  have hneighbor := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr cp.firstStep_adj
  have hreverse := (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    (Γ.adjacent_symm cp.firstStep_adj)
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hneighbor
  let _ := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven Γ hreverse
  intro d hd
  rcases hd with rfl | rfl
  · apply involution_outside_core_of_elementary (GAt Γ cp.a) (z Γ cp.firstStep)
    · rw [hfirst]
      exact h74.reverse_containment.1
    · have hcore : Γ.twoCoreAt cp.a = twoCoreIn (GAt Γ cp.a) := Γ.twoCoreAt_def _
      rw [← hcore, hfirst]
      exact (h74.commutator_case ctx.commutator_ne).2.2
  · apply involution_outside_core_of_elementary (GAt Γ cp.firstStep) (z Γ cp.a)
    · rw [hfirst]
      exact h74.first_containment.1.trans h74.first_containment.2
    · have hcore : Γ.twoCoreAt cp.firstStep = twoCoreIn (GAt Γ cp.firstStep) :=
        Γ.twoCoreAt_def _
      rw [← hcore, hfirst]
      exact cp.critical.2

public theorem eight_two_distance_one_edge_involutions
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hlength : ctx.criticalPath.length = 1) :
    ∀ d : ctx.Γ.Vertex,
      d = ctx.criticalPath.a ∨ d = ctx.criticalPath.firstStep →
        ∃ t : GAt ctx.Γ d, t ∉ pCore 2 (GAt ctx.Γ d) ∧ t ^ 2 = 1 :=
  eight_two_distance_one_edge_involutions_local ctx.toLocalContext hlength

end Stellmacher.SectionEight
