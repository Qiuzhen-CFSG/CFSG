module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore.Action
public import Theory.Representation.BinaryPermutation.FiveTensorLowRank

/-!
# The orthogonal A₅-module tensor inspection in the literal star action

The group coordinates are actual isomorphisms from H/O₂(H), and the vector
coordinates intertwine its action on U/Z(U). The S₅ alternative yields a pure
transposition and moved rank exactly two; the A₅ alternative has rank greater
than two. No involution classification or low-rank exclusion is assumed.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, 14.4.2(5)
and the first inspection in 14.4.6(a), printed pp.1006,1008. The natural
L₂(4) module and the Sylow-fixed marked line are separate inputs to assembly.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
open BinaryPermutation Subgroup
variable {H V : Type*} [Group H] (U : Subgroup H) [U.Normal]
  [AddCommGroup V] [Module (ZMod 2) V]

/-- Low rank in the S₅ core tensor model identifies the actual quotient actor. -/
theorem SourceAction.tensor_symmetric_lowRank
    (d : SourceAction H U V)
    (e : (H ⧸ pCore 2 H) ≃* Equiv.Perm (Fin 5) × Equiv.Perm (Fin 3))
    (f : V ≃ₗ[ZMod 2] FiveTensorLowRank.Space)
    (hf : ∀ a v, f (d.representation a v) = FiveTensorLowRank.action (e a) (f v))
    (a : H ⧸ pCore 2 H) (ha : a ≠ 1) (hr : d.movedRank a ≤ 2) :
    (∃ i j : Fin 5, i ≠ j ∧ e a = (Equiv.swap i j, 1)) ∧ d.movedRank a = 2 := by
  have he := d.movedRank_eq_of_equivariant a f (FiveTensorLowRank.action (e a)) (hf a)
  have hne : e a ≠ 1 := fun h => ha (e.injective (h.trans (map_one e).symm))
  rw [he] at hr ⊢
  exact FiveTensorLowRank.inspection (e a) hne hr

/-- The A₅ core tensor alternative contains no nonidentity low-rank actor. -/
theorem SourceAction.tensor_alternating_rank_gt_two
    (d : SourceAction H U V)
    (e : (H ⧸ pCore 2 H) ≃* alternatingGroup (Fin 5) × Equiv.Perm (Fin 3))
    (f : V ≃ₗ[ZMod 2] FiveTensorLowRank.Space)
    (hf : ∀ a v, f (d.representation a v) =
      FiveTensorLowRank.action ((e a).1.val, (e a).2) (f v))
    (a : H ⧸ pCore 2 H) (ha : a ≠ 1) : 2 < d.movedRank a := by
  rw [d.movedRank_eq_of_equivariant a f _ (hf a)]
  exact FiveTensorLowRank.alternating_bound (e a)
    (fun h => ha (e.injective (h.trans (map_one e).symm)))
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.RankCore
