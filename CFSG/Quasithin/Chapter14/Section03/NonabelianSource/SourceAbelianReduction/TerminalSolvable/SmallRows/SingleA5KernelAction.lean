module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.SmallRows.Preparation
public import Theory.GroupAction.PerfectSmallKernel

/-!
# The supplied component's kernel over a small tilded center

Restrict the original tilded and dotted actions to the supplied perfect
component. If the tilded center has order at most four, perfectness fixes it;
the kernel-and-quotient action theorem makes the restricted dotted kernel a
two-group. For either small image A5 or A6 it is the solvable radical, so
that same component has radical equal to its intrinsic two-core. The whole
terminal kernel need not be a two-group.

Source: Aschbacher--Smith 12.8.4, 12.8.13(3), and 14.3.15,
printed pp.850, 855--856 and 994. Reuses the recovered SingleA5Kernel donor
proof with the literal comap/subgroupOf comparison made explicit.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] [Finite G]

/-- Restrict the actual tilded and terminal actions to the supplied perfect
component. Its terminal kernel is a two-group when the tilded center is small. -/
theorem ComponentLift.restricted_kernel_isPGroup_of_tilde_center_card_le_four {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2}
    [IsElementaryAbelian 2 V] {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (d : Recognition.ClosureGeometry F)
    (hc : Nat.card (F.tilde F.ZU) ≤ 4) :
    IsPGroup 2 (F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype) := by
  let q := F.tildeToUhat (by decide : 1 ≤ 2)
  let f := (F.localTildeAction F.H le_rfl).comp (K.subgroupOf F.H).subtype
  let j := F.terminalHatAction.comp (K.subgroupOf F.H).subtype
  let : Group.IsPerfect (K.subgroupOf F.H) := hK.component.perfect
  have he : ∀ a x, q (f a x) = j a (q x) := by
    intro a x
    exact F.tildeToUhat_equivariant (by decide) a x
  have hq : Nat.card q.ker ≤ 4 := by
    rw [show q.ker = (F.tilde F.ZU).subgroupOf (F.tilde F.U) from F.tildeToUhat_ker (by decide)]
    have hl : F.tilde F.ZU ≤ F.tilde F.U :=
      map_mono (comap_mono (map_subtype_le (center F.U)))
    rw [Nat.card_congr (subgroupOfEquivOfLe hl).toEquiv]
    exact hc
  let : IsElementaryAbelian 2 (F.tilde F.U) := F.tilde_elementary_of_point d.two d.frattini_point
  have hp : IsPGroup 2 q.ker := (IsElementaryAbelian.isPGroup 2 (F.tilde F.U)).to_subgroup _
  have hf : IsPGroup 2 f.ker := by
    change IsPGroup 2 ((F.localTildeAction F.H le_rfl).ker.subgroupOf (K.subgroupOf F.H))
    rw [d.tilde_kernel]
    exact pCore_isPGroup.comap_subtype
  exact Theory.GroupAction.PerfectSmallKernel.quotient_action_kernel_isPGroup q f j he hq hp hf

/-- The canonical radical kernel on the same small-image component is its
two-core. This applies to either A₅ or A₆ without changing the lift. -/
theorem ComponentLift.radical_eq_twoCore_of_tilde_center_card_le_four
    {T : Sylow 2 G} {V : Subgroup G} {F : InvariantFlag T V 2}
    [IsElementaryAbelian 2 V] {g : G} {K : Subgroup G}
    (hK : ComponentLift F g K) (hsmall : SmallImageRow F K)
    (d : Recognition.ClosureGeometry F) (hc : Nat.card (F.tilde F.ZU) ≤ 4) :
    solvableRadical K = pCore 2 K := by
  have hr := hK.terminal_kernel_eq_radical hsmall
  rw [ker_subgroupMap,QuotientGroup.ker_mk'] at hr
  have hp := hK.restricted_kernel_isPGroup_of_tilde_center_card_le_four d hc
  change IsPGroup 2 (F.terminalHatAction.ker.subgroupOf (K.subgroupOf F.H)) at hp
  rw [hr] at hp
  have heq : solvableRadical (K.subgroupOf F.H) = pCore 2 (K.subgroupOf F.H) := by
    apply le_antisymm
    · exact le_sSup ⟨inferInstance,hp⟩
    · let : Group.IsNilpotent (pCore 2 (K.subgroupOf F.H)) := pCore_isPGroup.isNilpotent
      exact le_solvableRadical _ inferInstance inferInstance
  let e := subgroupOfEquivOfLe hK.le_pointNormalizer
  have he := congrArg (Subgroup.map e.toMonoidHom) heq
  rw [map_solvableRadical_equiv,pCore_map_iso] at he
  exact he
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
