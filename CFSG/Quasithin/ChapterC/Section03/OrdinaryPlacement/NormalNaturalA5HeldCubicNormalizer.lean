module

public import CFSG.Quasithin.ChapterC.Section03.OrdinaryPlacement.NormalNaturalA5HeldCubic
public import Theory.SpecificGroups.Held.TwoLocalCandidates.ThreeCoreBounds
public import Theory.GroupTheory.PerfectSolvableSectionLift
public import Theory.GroupTheory.PerfectSmallTwoAction
public import CFSG.Quasithin.ChapterA.Section04.Signalizers.SectionCentralizer

/-!
# The native Held cubic in the original actor's section centralizer

A perfect actor centralizes the normal kernel of order at most three in
the native six-point quotient. When the original actor is normalized by
the whole two-core, normalizer reflection through that solvable kernel
places the literal cubic word in the actor's section centralizer. Its
fixed-point-free action on the two-core then excludes any nontrivial
original module fixed by that section centralizer.

This is the same-subgroup local step in the Held row of12.7.5, printed
p.840. The core-normalizer hypothesis is supplied separately by the
original elementary16 inside the solvable core of order64.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.OrdinaryPlacement.HeldCubic
open Held.LocalPairs.PairCoverage
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner
open Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry.CoreKernel

/-- The distinguished cubic belongs to the section centralizer of every
perfect subgroup normalized by the full native two-core. -/
theorem kernelThird_mem_twoSectionCentralizer (i : Bool)
    (B : Subgroup (localOvergroup i)) [Group.IsPerfect B]
    (hn : pCore 2 (localOvergroup i) ≤ normalizer (B : Set (localOvergroup i))) :
    kernelThird i ∈ ChapterA.Section04.twoSectionCentralizer B ⊤ := by
  let q := localQuotientMap i
  have hqker : q.ker = pCore 2 (localOvergroup i) := QuotientGroup.ker_mk' _
  have hp : IsPGroup 2 q.ker := by rw [hqker]; exact pCore_isPGroup
  let : Group.IsNilpotent q.ker := hp.isNilpotent
  let Bq := B.map q
  let : Group.IsPerfect Bq := Group.IsPerfect.map q
  have hsmall : Nat.card (SixPoint.quotientAction i).ker ≤ 4 :=
    (Nat.le_of_dvd (by decide) (Held.TwoLocalCandidates.ThreeCoreBounds.quotientAction_kernel_card_dvd_three i)).trans (by decide)
  have hc := le_centralizer_of_isPerfect_of_card_le_four Bq
    (SixPoint.quotientAction i).ker hsmall
  have hzker : q (kernelThird i) ∈ (SixPoint.quotientAction i).ker :=
    kernelThird_mem_ker i
  have hzcent : q (kernelThird i) ∈ centralizer (Bq : Set (LocalQuotient i)) :=
    (le_centralizer_iff.mp hc) hzker
  have hzN : kernelThird i ∈ normalizer (B : Set (localOvergroup i)) :=
    normalizer_comap_map_le_of_solvable_kernel q B (hqker.symm ▸ hn)
      ((centralizer_le_normalizer _) hzcent)
  refine ⟨mem_top _,hzN,?_⟩
  intro b hb
  apply mem_pCoreIn_of_map_mem q B (by rw [ker_subgroupMap]; exact hp.comap_subtype)
  · exact (le_normalizer_iff_commutator_le_right.mp le_rfl)
      (commutator_mem_commutator hzN hb)
  · rw [map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr (hzcent _ (mem_map_of_mem q hb)).symm]
    exact one_mem _

/-- A nontrivial module inside the native two-core cannot be fixed by the
whole section centralizer of such a perfect actor. -/
theorem not_fixed_by_sectionCentralizer (i : Bool)
    (B E : Subgroup (localOvergroup i)) [Group.IsPerfect B]
    (hn : pCore 2 (localOvergroup i) ≤ normalizer (B : Set (localOvergroup i)))
    (hE : E ≤ pCore 2 (localOvergroup i)) (hne : E ≠ ⊥)
    (hf : ChapterA.Section04.twoSectionCentralizer B ⊤ ≤
      centralizer (E : Set (localOvergroup i))) : False := by
  apply hne
  apply eq_bot_iff.mpr
  intro x hx
  apply mem_bot.mpr
  exact fixed_eq_one i x (hE hx)
    (hf (kernelThird_mem_twoSectionCentralizer i B hn) x hx)

end CFSG.Quasithin.ChapterC.OrdinaryPlacement.HeldCubic
