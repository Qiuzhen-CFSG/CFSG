module

public import Stellmacher.SectionNine.NineTenReversedCriticalPair
public import Stellmacher.SectionFiveToSeven.ReversedExtendedPath

/-!
# The full reversed supplied path after (9.10)(5)

Retain the actual normalized geometric extraction and the noncommutation
of its predecessor module with the penultimate center. The proved reversed
critical-pair theorem gives commuting critical endpoints. The reversed
internal segment supplies a full path whose first vertex is the original
preterminal vertex and whose backward vertex is the original first step.

The penultimate vertex is adjacent to the preterminal vertex on the actual
critical path. The extracted predecessor is adjacent to the initial vertex
by the same extraction identity. The shared reversed extended path joins
these two edges with the reversed original segment, preserving its length
and the offsets used by the later supplied-path form of (9.5).

This is the reorientation after Stellmacher (9.10)(5), printed pp.57-58.
It assumes only the explicit predecessor noncommutation needed by the
already proved reversed-pair theorem, and adds no support or group-model
hypothesis. Later containment and transvection assertions remain separate.
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_ten_reversed_supplied_path
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 4 < ctx.criticalPath.length)
    (neighbor second : ctx.Γ.Vertex) (actor : G) (E A0 : Subgroup G)
    (data : NineThreeGeometricData ctx.Γ ctx.criticalPath.firstStep second
      (VAt ctx.Γ ctx.criticalPath.a') E A0 actor)
    (hsecond : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 second)
    (hnew : ctx.Γ.act data.x⁻¹ second = ctx.criticalPath.a)
    (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hcenters : ⁅ZAt ctx.Γ ctx.criticalPath.a, ZAt ctx.Γ neighbor⁆ ≠ ⊥)
    (hmodules : ⁅VAt ctx.Γ (ctx.Γ.act data.x⁻¹ (ctx.criticalPath.path ⟨3,by omega⟩)),
      ZAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)⁆ ≠ ⊥) :
    let predecessor := ctx.Γ.act data.x⁻¹ (ctx.criticalPath.path ⟨3,by omega⟩)
    let penultimate := ctx.criticalPath.path
      ⟨ctx.criticalPath.length - 1,Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
    IsCriticalPair ctx.Γ penultimate predecessor ∧
      ⁅ZAt ctx.Γ penultimate, ZAt ctx.Γ predecessor⁆ = ⊥ ∧
      ∃ path : Fin (ctx.criticalPath.length + 1) → ctx.Γ.Vertex,
        path 0 = penultimate ∧
        path ⟨ctx.criticalPath.length, Nat.lt_succ_self _⟩ = predecessor ∧
        path ⟨1, by omega⟩ = ctx.criticalPath.path
          ⟨ctx.criticalPath.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ ∧
        path ⟨ctx.criticalPath.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ =
          ctx.criticalPath.firstStep ∧
        ∀ index : Fin ctx.criticalPath.length,
          ctx.Γ.adjacent (path index.castSucc) (path index.succ) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  have hlength : 4 < cp.length := hb
  let predecessor := Γ.act data.x⁻¹ (cp.path ⟨3, by omega⟩)
  let penultimate := cp.path ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  let preterminal := cp.path ⟨cp.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hcritical := nine_ten_reversed_critical_pair_of_noncommutation ctx hb neighbor second
    actor E A0 data hsecond hnew hneighbor hcenters hmodules
  have hpred := (nine_ten_extracted_predecessor_alternative Γ cp (by omega) second
    actor E A0 data hsecond hnew).1
  have hpen : penultimate ∈ neighborhood Γ preterminal := by
    apply (mem_neighborhood_iff_adjacent Γ).mpr
    have hedge := cp.path_adj ⟨cp.length - 2, by omega⟩
    have hindex : (⟨cp.length - 2, by omega⟩ : Fin cp.length).succ =
        ⟨cp.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      omega
    simpa only [hindex, Fin.castSucc_mk, preterminal, penultimate] using hedge
  exact ⟨hcritical.1, hcritical.2, reversed_extended_path Γ cp (by omega)
    predecessor penultimate ((mem_neighborhood_iff_adjacent Γ).mpr hpred) hpen⟩

end Stellmacher.SectionNine
