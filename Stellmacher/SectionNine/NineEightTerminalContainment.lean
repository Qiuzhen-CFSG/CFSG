module

public import Stellmacher.SectionNine.NineThreeCenterSplitting
public import Stellmacher.SectionNine.NineEightWTransfer

/-!
# Terminal containment of the neighborhood join in (9.8)

If the commuting critical length is greater than three and the terminal
center lies in the first-step module, then W at every first-step neighbor
lies in the terminal stabilizer. This supplies the actual containment needed
for the later geometric extraction in (9.8), with no extra center-product
premise.

The penultimate vertex lies in the initial orbit by (7.5). Its preceding and
terminal path neighbors are distinct because the critical path has minimal
length. The post-(9.3) direct product therefore splits its center into those
two neighbor centers. The proved W transfer then uses W abelianness,
preterminal containment, terminal-center commutation, and residual transitivity
with the ambient (7.7)(a) commutator bound.

Source: B. Stellmacher, Journal of Algebra 190 (1997), (9.8), printed p.55,
first paragraph. The local refs/latex/stellmacher-n-group.tex abridges this
paragraph. The theorem does not assert the later extracted-neighbor
alternatives or the bound b ≤ 3.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_eight_neighborhood_le_terminal
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (vertex : ctx.Γ.Vertex)
    (hvertex : vertex ∈ neighborhood ctx.Γ ctx.criticalPath.firstStep) :
    GeneratedNeighborhoodV ctx.Γ vertex ≤ GAt ctx.Γ ctx.criticalPath.a' := by
  let cp := ctx.criticalPath
  have hlong : 3 < cp.length := hb
  let previous := cp.path ⟨cp.length - 2, by omega⟩
  let middle := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hleft : ctx.Γ.adjacent middle previous := by
    apply ctx.Γ.adjacent_symm
    have hedge := cp.path_adj ⟨cp.length - 2, by omega⟩
    have hindex : (⟨cp.length - 2, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hindex] at hedge
    exact hedge
  have hright : ctx.Γ.adjacent middle cp.a' := by
    have hedge := cp.path_adj ⟨cp.length - 1, by omega⟩
    have hlast : (⟨cp.length - 1, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hlast, cp.path_end] at hedge
    exact hedge
  have hdistinct : previous ≠ cp.a' := by
    intro heq
    have hbound := path_distance_le ctx.Γ cp 0 (cp.length - 2) (by omega) (by omega)
    have hzero : (⟨0, by omega⟩ : Fin (cp.length + 1)) = 0 := Fin.ext rfl
    rw [hzero, cp.path_start, Nat.sub_zero] at hbound
    change ctx.Γ.distance cp.a previous ≤ cp.length - 2 at hbound
    rw [heq, cp.endpoint_distance] at hbound
    omega
  obtain ⟨actor, hactor, _⟩ := lemma_seven_five_endpoint_alignment
    ctx.sectionSeven ctx.Γ cp ctx.commutator_eq
  have hmiddle : IsConjugateVertex ctx.Γ cp.a middle := ⟨actor, hactor⟩
  have hproduct := (nine_three_center_split ctx (by omega) hmiddle hleft hright hdistinct).1
  exact nine_eight_neighborhood_le_terminal_of_center_product ctx hb hcontain
    hproduct vertex hvertex

end Stellmacher.SectionNine
