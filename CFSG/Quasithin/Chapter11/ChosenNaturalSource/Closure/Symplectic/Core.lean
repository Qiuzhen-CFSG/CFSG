module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.Fundamental
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Identifying the original seed with the symplectic block core

The printed H¹(Sp₄(4),V)=0 argument is unavailable. Instead, the genuine
identity O₂(L)=[O₂(L),L] identifies the core with the short group's block
layer. Its irreducible central quotient forces any nonzero perfect normal
submodule to supplement the fixed part. Taking commutators removes that
fixed part and identifies the whole core with the original chosen V.

The Sp₄(4)-block and core-commutator identity remain explicit intermediate
premises; their construction belongs to the preceding part of 11.5.7.
Source: Aschbacher--Smith C.1.7 and 11.5.7, printed pp.123,783.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter12.Section02
open scoped IsMulCommutative

private theorem core_eq_of_short (A : Type*) [Group A] (hs : IsShort A)
    (hc : pCore 2 A = blockU A) (P : Subgroup A) [P.Normal]
    (hP : P ≤ pCore 2 A) (hne : P ≠ ⊥) (hperfect : ⁅P, ⊤⁆ = P) :
    pCore 2 A = P := by
  let Z := blockU A ⊓ center A
  have hPU : P ≤ blockU A := hP.trans_eq hc
  have hZ : Z ≤ blockU A := inf_le_left
  have hN := hs.irreducible.2 (P ⊔ Z) inferInstance le_sup_right (sup_le hPU hZ)
  rcases hN with hN | hN
  · have hPc : P ≤ center A := (le_sup_left.trans_eq hN).trans inf_le_right
    exact (hne (hperfect.symm.trans (commutator_top_right_eq_bot_iff_le_center.mpr hPc))).elim
  · have hb : ⁅P ⊔ Z, (⊤ : Subgroup A)⁆ ≤ P :=
      commutator_sup_le_of_relative_normal ⊤ P Z ⊤ P le_normalizer_of_normal
        le_top le_top hperfect.le
        ((commutator_mono inf_le_right le_rfl).trans (by rw [commutator_center_left]; exact bot_le))
    rw [hN, ← hc] at hb
    exact le_antisymm (hc.trans_le hb) hP

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V)
include D

/-- Shortness and the genuine core-commutator equality identify the original
chosen perfect submodule with the entire core. No field restriction or
cohomology vanishing is needed. -/
theorem core_eq_chosen_of_short
    (hs : IsShort L) (hc : L.pCoreIn 2 = ⁅L.pCoreIn 2, L⁆) :
    L.pCoreIn 2 = V := by
  have hmap : (blockU L).map L.subtype = ⁅L.pCoreIn 2, L⁆ := by
    rw [blockU, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
    rfl
  have hcore : pCore 2 L = blockU L := by
    apply (map_injective L.subtype_injective)
    exact hc.trans hmap.symm
  let P := V.subgroupOf L
  let : P.Normal := (normal_subgroupOf_iff_le_normalizer D.le_component).mpr D.normalizes
  have hPmap : P.map L.subtype = V := map_subgroupOf_eq_of_le D.le_component
  have hP : P ≤ pCore 2 L := by
    rw [← comap_map_eq_self_of_injective L.subtype_injective (pCore 2 L)]
    exact comap_mono D.le_componentCore
  have hne : P ≠ ⊥ := by
    intro h
    apply D.ne_bot
    rw [← hPmap, h, Subgroup.map_bot]
  have hperfect : ⁅P, ⊤⁆ = P := by
    apply map_injective L.subtype_injective
    rw [map_commutator, hPmap, ← MonoidHom.range_eq_map, range_subtype]
    exact D.eq_commutator.symm
  have he := core_eq_of_short L hs hcore P hP hne hperfect
  exact (congrArg (map L.subtype) he).trans hPmap

/-- The original chosen perfect submodule is the entire core of the block.
This uses no cohomology vanishing or replacement of the chosen module. -/
theorem core_eq_chosen_of_sp4_block
    (hb : IsSp4FourBlock L) (hc : L.pCoreIn 2 = ⁅L.pCoreIn 2, L⁆) :
    L.pCoreIn 2 = V :=
  core_eq_chosen_of_short D hb.1 hc
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
