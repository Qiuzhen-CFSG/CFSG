module
public import CFSG.Quasithin.ChapterB.Section02.Thompson.FixedAction
public import Theory.Representation.ElementaryPerfectSplit
public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Action
public import Theory.Representation.BinaryInternalFixedSpaceCodimension.Rank

/-!
# Near-maximum actors on an internal elementary module

The rank comparison from B.2.4 applies to an elementary subgroup U of S
normalized by C, even when U is not normal in the ambient group. Use the
actual kernel E ∩ C_G(U) in the replacement comparison. Its centralizer
contains U, and the literal actor map identifies the lost rank with the
image rank. The conjugation fixed-space equivalence then gives the bound.

The alternating-component application in 13.4.7 uses this with the original
Sylow group S and an actor E inside C, retaining the full quotient kernel.
Source: Aschbacher--Smith B.2.4(1), p.75, and 13.4.7(1iv), p.901.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterB
variable {G Q : Type*} [Group G] [Finite G] [Group Q]

/-- Near-maximum displacement for an internal elementary module, with
normality required only under its actual actor. -/
theorem near_maximum_internal_action_codimension
    (S U C E : Subgroup G) [IsElementaryAbelian 2 U]
    (hUS : U ≤ S) (hCU : C ≤ normalizer (U : Set G))
    (hEC : E ≤ C) (hE : E ∈ thompsonFamily S 1)
    (f : C →* Q) (hk : f.ker = (centralizer (U : Set G)).subgroupOf C) :
    fixedCodim (Representation.elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hCU))) (E.subgroupOf C) ≤
        rank ((E.subgroupOf C).map f) + 1 := by
  let := hE.2.1
  let N := E ⊓ centralizer (U : Set G)
  have hfix : U ⊓ centralizer (N : Set G) = U :=
    inf_eq_left.mpr (le_centralizer_iff.mpr (show N ≤ centralizer (U : Set G) from inf_le_right))
  have hb := near_maximum_relative_fixed_rank S U E N hUS hE inf_le_left
  rw [hfix] at hb
  have hr : Nat.log 2 (Nat.card E) - Nat.log 2 (Nat.card N) =
      rank ((E.subgroupOf C).map f) := by
    rw [BinaryInternalFixedSpaceCodimension.rank_eq_log_index E (centralizer (U : Set G))]
    rw [rank,←Subgroup.relIndex_ker, hk, relIndex_subgroupOf hEC]
  have hc := BinaryInternalFixedSpaceCodimension.fixedCodim_eq_finrank U C E hCU hEC
  have hrep : Representation.elementaryRepresentation (p := 2)
      (U.normalizerMonoidHom.comp (inclusion hCU)) =
        BinaryInternalFixedSpaceCodimension.representation U C hCU := by
    ext c v
    rfl
  rw [hrep]
  change Module.finrank (ZMod 2) (Additive U ⧸
    invariants ((BinaryInternalFixedSpaceCodimension.representation U C hCU).comp
      (E.subgroupOf C).subtype)) ≤ _
  rw [←hc]
  rwa [hr] at hb
end CFSG.Quasithin.ChapterB
