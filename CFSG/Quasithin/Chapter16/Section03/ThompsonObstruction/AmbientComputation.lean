module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Inputs
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Comparison
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.Contracts
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.RankGeometry
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.DihedralActions
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.AmbientComputation.FrattiniOmega

/-!
# The ambient Thompson calculation

The preceding modules prove the rank geometry, the two dihedral action cases,
the compatible product for the actual Thompson subgroup, and the Frattini
omega calculation. This file is the source-facing assembly: its only inputs
are the prepared data and the local rank-five equality. In particular no
rank-geometry, maximum-family, decomposition, or centrality assertion is left
as a premise here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, printed
pp.1181–1182 / PDF pp.1198–1199.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation

open Subgroup Stellmacher ChapterB

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {z t : G} {L : Subgroup G}

/-!
The existential form is convenient for the source proof: the witness `c`
contains the characteristic rotation, the maximizing involution, both action
alternatives, the dihedral factor and its compatible multiplication map. The
remaining conjuncts expose the rank and centrality conclusions without
requiring callers to reconstruct the internal witnesses.
-/
theorem exists_ambient_calculation (d : Prepared T z t L)
    (hP : twoRank (localSylow d.P) = 5) :
    ∃ c : Decomposition d, ∃ v : G,
      (∀ (a : c.R) (b : componentSylow T L) (e : zpowers c.w),
        (c.product (a, b, e) : G) = (a : G) * (b : G) * (e : G)) ∧
      twoRank (T : Subgroup G) = 5 ∧
      twoRank (commutingSylow T L) = 2 ∧
      twoRank (componentAction d).range = 3 ∧
      (∀ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G),
        A ≤ smallGroup d ∧
          Nat.card ↥(A ⊓ commutingSylow T L) = 4 ∧
          Nat.card (actionImage d A) = 8) ∧
      orderOf v = 2 ∧
      ambientCenter (componentSylow T L) = zpowers v ∧
      thompsonFrattiniOmega (T : Subgroup G) = zpowers z ⊔ zpowers v ∧
      thompsonFrattiniOmega (T : Subgroup G) ≤ ambientCenter (T : Subgroup G) ∧
      (T : Subgroup G) ≤
        centralizer (thompsonFrattiniOmega (T : Subgroup G) : Set G) := by
  let r : RankGeometry d := rankGeometry d hP
  obtain ⟨c⟩ := exists_decomposition d r
  obtain ⟨v, hv, hvC, hOmega⟩ := exists_frattiniOmega_generator d r c
  refine ⟨c, v, c.product_apply, r.rank, r.centralizer_rank, r.action_rank, ?_, hv, hvC,
    hOmega, ?_, ?_⟩
  · intro A hA
    exact ⟨r.maximal_le A hA, r.maximal_intersection A hA,
      r.maximal_image A hA⟩
  · exact thompsonFrattiniOmega_le_ambientCenter d r c
  · exact sylow_le_centralizer_thompsonFrattiniOmega d r c

/-!
Useful projections of the source-facing assembly. They retain the original
`d` and `hP` interface, so downstream arguments do not need to carry the
internal `RankGeometry` or `Decomposition` witnesses as hypotheses.
-/
theorem rankGeometry_of_prepared (d : Prepared T z t L)
    (hP : twoRank (localSylow d.P) = 5) : RankGeometry d :=
  rankGeometry d hP

theorem decomposition_of_prepared (d : Prepared T z t L)
    (hP : twoRank (localSylow d.P) = 5) : Nonempty (Decomposition d) := by
  let r : RankGeometry d := rankGeometry d hP
  exact exists_decomposition d r

theorem frattiniOmega_of_prepared (d : Prepared T z t L)
    (hP : twoRank (localSylow d.P) = 5) :
    ∃ v : G, orderOf v = 2 ∧
      ambientCenter (componentSylow T L) = zpowers v ∧
      thompsonFrattiniOmega (T : Subgroup G) = zpowers z ⊔ zpowers v := by
  let r : RankGeometry d := rankGeometry d hP
  obtain ⟨c⟩ := exists_decomposition d r
  exact exists_frattiniOmega_generator d r c

theorem thompsonFrattiniOmega_central_of_prepared (d : Prepared T z t L)
    (hP : twoRank (localSylow d.P) = 5) :
    thompsonFrattiniOmega (T : Subgroup G) ≤ ambientCenter (T : Subgroup G) := by
  let r : RankGeometry d := rankGeometry d hP
  obtain ⟨c⟩ := exists_decomposition d r
  exact thompsonFrattiniOmega_le_ambientCenter d r c

theorem sylow_centralizes_thompsonFrattiniOmega_of_prepared
    (d : Prepared T z t L) (hP : twoRank (localSylow d.P) = 5) :
    (T : Subgroup G) ≤
      centralizer (thompsonFrattiniOmega (T : Subgroup G) : Set G) := by
  let r : RankGeometry d := rankGeometry d hP
  obtain ⟨c⟩ := exists_decomposition d r
  exact sylow_le_centralizer_thompsonFrattiniOmega d r c

end CFSG.Quasithin.Chapter16.ThompsonObstruction.AmbientComputation
