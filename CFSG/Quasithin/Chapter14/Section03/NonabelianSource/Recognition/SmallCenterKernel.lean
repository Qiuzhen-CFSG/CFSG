module
public import Theory.GroupAction.TwoElementKernelAutomorphisms
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.NormalCubicKernel

/-!
# The terminal action kernel when the tilded center has order at most two

The actual equivariant projection U-tilde to U-hat has the tilded center as
kernel. Its value-preserving automorphisms form a two-group when that
kernel has order at most two. The original tilded action already has
kernel O2(H), so the dotted kernel is also a two-group. This discharges the
cubic lifting premise used to exclude the degree-two terminal action.

Source: Aschbacher--Smith 14.3.13, printed p.994.
-/

public section
open Subgroup Module Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

/-- The source tilded action controls the dotted kernel through its actual
central quotient map. -/
theorem terminal_kernel_isPGroup_of_tilde_center_card_le_two
    (F : InvariantFlag T V 2) [IsElementaryAbelian 2 V]
    (d : ClosureGeometry F) (hZ : Nat.card (F.tilde F.ZU) ≤ 2) :
    IsPGroup 2 F.terminalHatAction.ker := by
  let q := F.tildeToUhat (by decide : 1 ≤ 2)
  have hk : Nat.card q.ker ≤ 2 := by
    rw [show q.ker = (F.tilde F.ZU).subgroupOf (F.tilde F.U) from F.tildeToUhat_ker (by decide)]
    have hle : F.tilde F.ZU ≤ F.tilde F.U := by
      exact map_mono (comap_mono (map_subtype_le (center F.U)))
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv]
    exact hZ
  have hf := q.isPGroup_fixingAut_of_kernel_card_le_two hk
  let f : F.terminalHatAction.ker →* q.fixingAut :=
    ((F.localTildeAction F.H le_rfl).comp F.terminalHatAction.ker.subtype).codRestrict _ (by
      intro a u
      change q (F.localTildeAction F.H le_rfl (a : F.H) u) = q u
      rw [show q (F.localTildeAction F.H le_rfl (a : F.H) u) =
        F.uhatAction (a : F.H) (q u) from F.tildeToUhat_equivariant (by decide) a u]
      have ha : F.uhatAction (a : F.H) = 1 := a.property
      rw [ha]
      rfl)
  have hfker : f.ker ≤ (pCore 2 F.H).subgroupOf F.terminalHatAction.ker := by
    intro a ha
    change (a : F.H) ∈ pCore 2 F.H
    rw [← d.tilde_kernel]
    exact congrArg Subtype.val ha
  have hp : IsPGroup 2 f.ker :=
    (pCore_isPGroup.comap_subtype : IsPGroup 2 ((pCore 2 F.H).subgroupOf F.terminalHatAction.ker)).to_le hfker
  have ht := (hf.to_subgroup ⊤).comap_of_ker_isPGroup f hp
  rw [comap_top] at ht
  exact ht.of_surjective (⊤ : Subgroup F.terminalHatAction.ker).subtype
    (fun a => ⟨⟨a,mem_top a⟩,rfl⟩)

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
