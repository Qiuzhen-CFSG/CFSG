module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledSymplecticLocal
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubled
public import CFSG.Quasithin.ChapterE.Section06.FrobeniusReduction.SourceCompleteBound

/-!
# Initial global bounds for the original symplectic doubled orbit

The marked doubled setup supplies the literal E.6.1 hypotheses. The full
ambient automizer bounds give m ≥ 3n > 2, so the completed known-simple
E.6.3 proof gives r ≥ m. In particular, every subspace with corank less
than m has its ambient centralizer in N_G(L).

Together with a < 2n, these bounds force w > n by the actual weak-closure
contradiction in DoubledSymplecticBounds.false. Source 7.3.4 must still
supply the opposite inequality w ≤ n from the multiple-overgroup and
non-FF assumptions. This file does not assert the finished row exclusion.
The A₆ row requires a separate marking of the genuine derived binary group.

Source: Aschbacher--Smith E.6.3, H.7 and 7.3.2--7.3.5,
printed pp.245,388--389,698--699 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource ChapterE
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The original symplectic row has the full global centralizer lower bound;
the local bounds refer to the same ambient automizer. -/
theorem sourceOrbit_symplectic_initial_parameters
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2)
        (symplecticNatural (k := F.Carrier) 2)))) :
    (localM D.sourceOrbit : ℕ∞) ≤ globalR D.sourceOrbit ∧
      3 * F.degree ≤ localM D.sourceOrbit ∧
      localA D.sourceOrbit < ((2 * F.degree : ℕ) : ℕ∞) := by
  obtain ⟨hm,ha⟩ := D.sourceOrbit_symplectic_local_parameters h hd F hn hmodel
  have hE := D.sourceOrbit_hypothesisE61_of_markedDoubled h hd
  exact ⟨(Section06.FrobeniusReduction.lower_bound_knownSimple hE (by omega)).1,hm,ha⟩

/-- Every subspace of the actual orbit with corank less than its local
involution parameter has its full ambient centralizer in N_G(L). -/
theorem sourceOrbit_symplectic_small_centralizer
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2)
        (symplecticNatural (k := F.Carrier) 2))))
    {U : Subgroup G} (hU : U ≤ D.sourceOrbit)
    (hc : subgroupCorank D.sourceOrbit U < localM D.sourceOrbit) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  have hr := (D.sourceOrbit_symplectic_initial_parameters h hd F hn hmodel).1
  have hC := centralizer_le_normalizer_of_corank_lt_globalR hU
    ((ENat.natCast_lt_natCast.mpr hc).trans_le hr)
  rwa [D.sourceOrbit_normalizer_eq_of_markedDoubled h hd] at hC

/-- The strict H.7 estimate already forces w > n on the actual orbit.
The remaining upper bound in source 7.3.4 will contradict this statement. -/
theorem sourceOrbit_symplectic_globalW_gt_degree
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hn : 1 < F.degree)
    (hmodel : Nonempty (ActionEquiv (D.seedRepresentation.comp D.componentImage.subtype)
      (Representation.restrictScalars (k := ZMod 2)
        (symplecticNatural (k := F.Carrier) 2)))) :
    (F.degree : ℕ∞) < globalW D.sourceOrbit T := by
  apply lt_of_not_ge
  intro hw
  obtain ⟨hr,hm,ha⟩ := D.sourceOrbit_symplectic_initial_parameters h hd F hn hmodel
  exact DoubledSymplecticBounds.false D.sourceOrbit T
    ⟨hr,hm,ha,hw⟩ D.sourceOrbit_weakClosure_setup

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
