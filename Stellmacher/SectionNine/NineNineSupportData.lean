module

public import Stellmacher.SectionNine.NineNineCommutatorBound
public import Stellmacher.SectionNine.NineNineInitialInputs

/-!
# Support data and the final index obstruction for Stellmacher (9.9)

The record states the reversed containment and equations (1)–(2) on printed
p.56 of `refs/files/stellmacher-n-group.pdf`. It is not an existence theorem:
the support, its commutators, the maximal-subgroup identification, and the
lower index bound must all be produced from the original ambient hypotheses.

The theorem below proves the final contradiction from that record and the
three conclusions of the normalizer/conjugation argument on printed pp.56–57.
The principal distance bound still requires both mathematical producers.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven

universe u

public structure NineNineSupportData
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 3 < ctx.criticalPath.length) where
  terminal_core : VAt ctx.Γ ctx.criticalPath.a' ≤ QAt ctx.Γ ctx.criticalPath.firstStep
  support : Subgroup G
  support_le : support ≤ VAt ctx.Γ ctx.criticalPath.a'
  support_commutator : ⁅support, ZAt ctx.Γ ctx.criticalPath.a⁆ =
    ZAt ctx.Γ ctx.criticalPath.firstStep
  centralizer_commutator :
    ⁅support, GAt ctx.Γ ctx.criticalPath.a' ⊓
      Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set G)⁆ ≤
        ZAt ctx.Γ ctx.criticalPath.firstStep ⊔ ZAt ctx.Γ ctx.criticalPath.a'
  previous : ctx.Γ.Vertex
  previous_neighbor : previous ∈ Neighborhood ctx.Γ ctx.criticalPath.a
  previous_ne : previous ≠ ctx.criticalPath.firstStep
  maximal_eq : nineNineCommutatorBound (VAt ctx.Γ previous) support
      (ZAt ctx.Γ ctx.criticalPath.firstStep)
      (nine_nine_previous_normalizes_first_center ctx hb previous previous_neighbor) =
    VAt ctx.Γ previous ⊓ VAt ctx.Γ ctx.criticalPath.firstStep
  large_index : 4 * Nat.card (VAt ctx.Γ previous ⊓
    VAt ctx.Γ ctx.criticalPath.firstStep : Subgroup G) ≤ Nat.card (VAt ctx.Γ previous)

public theorem nine_nine_support_index_contradiction
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 3 < ctx.criticalPath.length)
    (data : NineNineSupportData ctx hb)
    (hindex : QuotientCardEq (VAt ctx.Γ data.previous)
      (VAt ctx.Γ data.previous ⊓ GAt ctx.Γ
        (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
          Nat.lt_succ_of_le (Nat.sub_le _ _)⟩)) 2)
    (hcore : VAt ctx.Γ data.previous ⊓ GAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) ≤ QAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩))
    (hcomm : ⁅VAt ctx.Γ data.previous ⊓ QAt ctx.Γ
      (ctx.criticalPath.path ⟨ctx.criticalPath.length - 1,
        Nat.lt_succ_of_le (Nat.sub_le _ _)⟩), data.support⁆ ≤
        ZAt ctx.Γ ctx.criticalPath.firstStep) : False := by
  apply nine_nine_maximal_commutator_contradiction
    (VAt ctx.Γ data.previous) data.support (ZAt ctx.Γ ctx.criticalPath.firstStep)
    _ _ (nine_nine_previous_normalizes_first_center ctx hb
      data.previous data.previous_neighbor) ?_ hindex hcore hcomm
  rw [data.maximal_eq]
  exact data.large_index

end Stellmacher.SectionNine
