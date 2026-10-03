module
public import Stellmacher.SectionNine.NineEightWTransfer
public import Stellmacher.SectionNine.NineFivePenultimateJoinAction
/-!
# Transfer the commuting predecessor module to the terminal stabilizer

Assume critical length greater than four. If the module at a neighbor of the
initial vertex centralizes the penultimate center, it lies in the terminal
stabilizer. No normalization or extraction witness beyond that adjacency is
needed.

The predecessor module lies in the initial neighborhood join, and the proved
(9.8) distance calculation puts this join in the preterminal stabilizer.
The ambient (7.7)(a) centralizer bound at the penultimate vertex then places
the module/residual commutator in the penultimate core. Residual transitivity
and the existing stabilizer-transfer theorem move containment from the
preterminal to the terminal stabilizer.

This proves the containment invoked in the commuting predecessor case of
Stellmacher (9.10), printed p.57/PDF p.47 of
`refs/files/stellmacher-n-group.pdf`. The actual normalized extracted
predecessor satisfies the only required adjacency hypothesis.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_predecessor_le_terminal_of_centralizing
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length)
    (predecessor : ctx.Γ.Vertex)
    (hpredecessor : ctx.Γ.adjacent ctx.criticalPath.a predecessor)
    (hmodules : ⁅VAt ctx.Γ predecessor,
      ZAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)⁆ = ⊥) :
    VAt ctx.Γ predecessor ≤ GAt ctx.Γ ctx.criticalPath.a' := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let penultimate := cp.path ⟨cp.length-1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let preterminal := cp.path ⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hshort : 1 < cp.length := by change 4 < cp.length at hb; omega
  have hpreW : VAt Γ predecessor ≤ GeneratedNeighborhoodV Γ cp.a :=
    nine_eight_v_le_generated_neighborhood Γ
      ((mem_neighborhood_iff_adjacent Γ).mpr hpredecessor)
  have hWpre : GeneratedNeighborhoodV Γ cp.a ≤ GAt Γ preterminal :=
    nine_eight_neighborhood_le_preterminal ctx.toLocalContext hb cp.a
      ((mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm cp.firstStep_adj))
  have hpath : IsCriticalPathOffset Γ cp (cp.length-2) preterminal :=
    ⟨⟨cp.length-2,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩,rfl,rfl⟩
  have hleft : preterminal ∈ Neighborhood Γ penultimate :=
    (mem_neighborhood_iff_adjacent Γ).mpr (Γ.adjacent_symm
      (nine_five_previous_adjacent_penultimate ctx.toLocalContext hshort preterminal hpath))
  have hright : cp.a' ∈ Neighborhood Γ penultimate :=
    (mem_neighborhood_iff_adjacent Γ).mpr (nine_five_penultimate_adjacent ctx.toLocalContext)
  have hcentral : VAt Γ predecessor ≤ Subgroup.centralizer (ZAt Γ penultimate : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hmodules
  have hcomm : ⁅VAt Γ predecessor,EAt Γ penultimate⁆ ≤ QAt Γ penultimate :=
    (Subgroup.commutator_mono hcentral le_rfl).trans
      (nine_eight_penultimate_centralizer_commutator ctx)
  exact nine_eight_stabilizer_transfer_of_commutator ctx.sectionSeven Γ
    penultimate preterminal cp.a' hleft hright (VAt Γ predecessor)
    (hpreW.trans hWpre) hcomm

end Stellmacher.SectionNine
