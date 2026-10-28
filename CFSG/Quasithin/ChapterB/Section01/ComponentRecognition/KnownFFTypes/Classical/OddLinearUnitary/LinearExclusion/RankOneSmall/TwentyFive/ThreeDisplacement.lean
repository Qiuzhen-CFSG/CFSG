module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive.Inputs
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSize.ProjectiveDegree
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.AbelianFrobeniusDisplacement
public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive.ThreeDisplacement.Conjugacy

/-!
# Uniform order-three displacement for the PSL₂(25) source component

The proved central-cover comparison identifies the literal component F*(G)
with PSL₂(25). Its Borel 5²:12 supplies a regular twelve-dimensional
complement submodule after scalar extension. An order-three element has
four orbits on that basis, giving displacement at least eight and fixed
dimension at least four. Sylow conjugacy and scalar descent transfer both
bounds to every inner order-three element acting on the original binary
space. In degree twelve, rank-nullity gives fixed dimension exactly four.

There is no degree bound, offender-ratio premise, generation assumption or
module catalogue in the uniform result. This discharges the representation
calculation `ThreeDisplacementBound` used by
`TwentyFive.source_exclusion_of_calculations`; the independent actor geometry
remains with that source-exclusion assembly.

Source: Guralnick--Malle, *Classification of 2F-modules I*, Proposition 4.1,
manuscript p.9; Aschbacher--Smith K.2, printed p.453.
-/

public section

namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups
open Matrix.ProjectiveSpecialLinearGroup
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- In a faithful binary PSL₂(25)-module, every element of order three moves
at least eight dimensions and fixes at least four dimensions. -/
theorem faithful_psl_twentyFive_rank_bounds (rho : Representation (ZMod 2) G V)
    (hrho : Function.Injective rho) (hm : ClassicalGroup.IsPSL G 2 25)
    (x : G) (hx : orderOf x = 3) :
    8 ≤ Module.finrank (ZMod 2) (LinearMap.range (rho x - 1)) ∧
      4 ≤ Module.finrank (ZMod 2) (LinearMap.ker (rho x - 1)) := by
  obtain ⟨F, hF, hfin, hcard, ⟨e⟩⟩ := hm
  let sigma := rho.comp e.symm.toMonoidHom
  have hy : orderOf (e x) = 3 := (e.orderOf_eq x).trans hx
  obtain ⟨c, g, hc, hg⟩ := OddBorel.order_three_conjugate_complement_of_card_twentyFive hcard (e x) hy
  have hb := prime_displacement_bounds_of_fixedPointFree_normalizer sigma
    (OddBorel.kernel F) (OddBorel.complement F) (hrho.comp e.symm.injective)
    (ZMod.natCast_ne_zero_iff_odd.mpr (by rw [OddBorel.card_kernel, hcard]; decide))
    (OddBorel.complement_normalizes F) (OddBorel.fixedPointFree F) c (by decide : Nat.Prime 3) hc
  rw [OddBorel.card_complement, hcard] at hb
  norm_num at hb
  have heval : sigma (e x) = rho x := by
    change rho (e.symm (e x)) = rho x
    rw [e.symm_apply_apply]
  have hconj := fixedCodim_zpowers_conj sigma (c : PSL(2,F)) g
  rw [← hg, fixedCodim_zpowers_eq_displacement_rank,
    fixedCodim_zpowers_eq_displacement_rank, heval] at hconj
  have hd := (rho x - 1).finrank_range_add_finrank_ker
  have hd' := (sigma c - 1).finrank_range_add_finrank_ker
  change Module.finrank (ZMod 2) (LinearMap.range (rho x - 1)) =
    Module.finrank (ZMod 2) (LinearMap.range (sigma c - 1)) at hconj
  omega

variable [Finite G] (rho : Representation (ZMod 2) G V) (h : SourceAction rho)
include h

/-- The Borel calculation applies on the actual component, after the proved
central-cover comparison. There is no degree or offender-ratio assumption. -/
theorem source_three_rank_bounds
    (hm : ClassicalGroup.IsPSL ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25)
    (x : G) (hxL : x ∈ generalizedFitting G) (hx : orderOf x = 3) :
    8 ≤ Module.finrank (ZMod 2) (LinearMap.range (rho x - 1)) ∧
      4 ≤ Module.finrank (ZMod 2) (LinearMap.ker (rho x - 1)) := by
  have hm' := RankOneSize.source_component_isPSL rho h
    (by decide : 3 < 25) (by decide : Odd 25) (by decide : 25 ≠ 9) hm
  exact faithful_psl_twentyFive_rank_bounds (rho.comp (generalizedFitting G).subtype)
    (h.faithful.comp Subtype.val_injective) hm' ⟨x, hxL⟩
    ((orderOf_injective (generalizedFitting G).subtype Subtype.val_injective ⟨x, hxL⟩).symm.trans hx)

/-- The uniform order-three displacement input needed for the source exclusion. -/
theorem source_threeDisplacementBound
    (hm : ClassicalGroup.IsPSL ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25) :
    ThreeDisplacementBound rho := by
  intro x hxL hx
  rw [fixedCodim_zpowers_eq_displacement_rank]
  exact (source_three_rank_bounds rho h hm x hxL hx).1

/-- In degree twelve the same regular-submodule calculation gives the source
fixed-space equality, without assuming an irreducible module catalogue. -/
theorem source_fixedSpace_finrank_eq_four
    (hm : ClassicalGroup.IsPSL ((generalizedFitting G) ⧸ center (generalizedFitting G)) 2 25)
    (hdim : Module.finrank (ZMod 2) V = 12)
    (x : G) (hxL : x ∈ generalizedFitting G) (hx : orderOf x = 3) :
    Module.finrank (ZMod 2) (fixedSpace rho (zpowers x)) = 4 := by
  have hb := source_three_rank_bounds rho h hm x hxL hx
  have hd := (rho x - 1).finrank_range_add_finrank_ker
  rw [hdim] at hd
  change Module.finrank (ZMod 2) (invariants (rho.comp (zpowers x).subtype)) = 4
  rw [← ker_sub_one_eq_cyclic_invariants]
  omega

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Classical.OddLinearUnitary.LinearExclusion.RankOneSmall.TwentyFive
