module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.LocalClass.TwoStepBase
public import CFSG.Quasithin.Chapter10.SourceA5NaturalGeneration.CharacteristicPair

/-!
# Recovering a component block from the common Baumann commutator bound

The source local-class embedding retains Baum(T) and the literal join
K Baum(T). The common base's central involutory commutators force the
join's residual block. Its residual is the original two-perfect K, so
shortness transports back to K in its original local ambient group A.
Original C-component subnormality supplies the ambient block condition.

The explicit common-base commutator bound is the remaining geometric input
from the first recovered block. No block property of the second component
is assumed here, and no equality of its two-core with U is asserted.
Source: Aschbacher--Smith 10.2.3(4), p.747, using C.1.17--18.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open ChapterB ChapterC.GlaubermanNiles ChapterC.RankOne.ChiProduct
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G}

/-- The common Baumann commutator geometry gives the second component's
block status in its actual local ambient group. -/
theorem source_component_block_of_common_baumann_commutator
    {K A : Subgroup G} (hKA : K ≤ A) (hK : (K.subgroupOf A).IsCComponent)
    (hBK : baumann (T : Subgroup G) ≤ normalizer (K : Set G))
    (hlocal : InLocalClass (inclusion
      (show baumann (T : Subgroup G) ≤ K ⊔ baumann (T : Subgroup G) from le_sup_right)))
    (hcomm : commutator (baumann (T : Subgroup G)) ≤
      omegaCenter (baumann (T : Subgroup G))) :
    ChapterC.IsBlock (K.subgroupOf A) := by
  have hb := hlocal.blockAlternative_of_commutator_le_omegaCenter
    (SelectedRankOne.baumann_fixed (T : Subgroup G)) hcomm
  let : Group.IsPerfect K := by
    let := hK.perfect
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKA).toMonoidHom)
      (subgroupOfEquivOfLe hKA).surjective
  have hpK : IsPPerfect 2 K := by
    intro Q hQ hp
    let := hQ
    let : Group.IsNilpotent (K ⧸ Q) := hp.isNilpotent
    apply top_unique
    rw [← solvableResidual_eq_top (G := K)]
    exact solvableResidual_le_of_solvable_quotient Q
  let N := K ⊔ baumann (T : Subgroup G)
  let e := ((pResidual 2 N).equivMapOfInjective N.subtype N.subtype_injective).trans
    (MulEquiv.subgroupCongr
      (SelectedRankOne.selected_component_residual_map T K hpK hBK))
  have hs : ChapterC.IsShort K := ChapterC.RankOne.Solvable.isShort_of_equiv e hb.1.short
  exact ⟨inferInstance,
    ChapterC.RankOne.Solvable.isShort_of_equiv (subgroupOfEquivOfLe hKA).symm hs,
    hK.subnormal⟩

end CFSG.Quasithin.Chapter10
