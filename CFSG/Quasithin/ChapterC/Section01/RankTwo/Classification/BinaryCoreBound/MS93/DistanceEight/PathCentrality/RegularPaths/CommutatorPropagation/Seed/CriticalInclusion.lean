module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.CriticalInclusion.EdgeSpan
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.Identification
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inequality

/-!
# Critical commutator inclusion and the terminal edge in MS93 (4.4.4)

The prescribed P-orbit contains the forward edge commutator. Transport by
precisely the source's inverse conjugation puts the selected edge in the
transported span. Since Z_a' does not normalize that selected edge, their
commutator is nonzero. It lies in [Z_a,Z_a'], whose binary order is two,
so it equals that critical commutator. This proves the required inclusion
without a failed-escape or noncontainment assumption.

The final theorem applies terminal_edge_of_critical_le to this inclusion,
the failed-escape bound and the explicit R₀ ≰ Z_a premise. The latter is
produced independently by Seed.OrbitGrowth.failedSpanCommutator_not_le_start_Z;
final TerminalPropagationSeed assembly remains with Seed.lean.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.4), printed p.894, the initial R₀ calculation.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.CriticalInclusion
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The critical commutator lies in the literal failed-span commutator. -/
theorem critical_commutator_le_failedSpan (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {t : Vertex R} (ht : Adjacent R a t)
    (hn : ¬ Z R a' ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a t : Set (FreeAmalgam R)))
    {g : FreeAmalgam R}
    (hge : (edgeCommutator R a (p.walk.getVert 1)).map
      (MulAut.conj g⁻¹).toMonoidHom = edgeCommutator R a t) :
    ⁅Z R a, Z R a'⁆ ≤ failedSpanCommutator p g := by
  let C := ⁅Z R a, Z R a'⁆
  let D := ⁅edgeCommutator R a t, Z R a'⁆
  have hCZ : Nat.card C = 2 := LocalCommutator.CriticalCase.critical_commutator_card common p
  have hEZ : edgeCommutator R a t ≤ Z R a :=
    (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (moduleFacts common) a t p.start_color ht).trans (U_le_Z R a)
  have hDC : D ≤ C := commutator_mono hEZ le_rfl
  let : Finite C := Nat.finite_of_card_ne_zero (by rw [hCZ]; decide)
  let : Finite D := Finite.of_injective (inclusion hDC) (inclusion_injective hDC)
  have hD : D ≠ ⊥ := by
    intro h
    apply hn
    refine le_inf (p.endpoint_Z_le_start_stabilizer (by have := common.large_distance; omega)) ?_
    apply le_normalizer_iff_commutator_le_left.mpr
    change D ≤ edgeCommutator R a t
    rw [h]
    exact bot_le
  have hpos : 1 < Nat.card D := (one_lt_card_iff_ne_bot D).mpr hD
  have hCD : C ≤ D := (eq_of_le_of_card_ge hDC (by omega)).ge
  apply hCD.trans
  change ⁅edgeCommutator R a t, Z R a'⁆ ≤ ⁅_, Z R a'⁆
  apply commutator_mono _ le_rfl
  rw [← hge]
  exact map_mono (first_edge_le_prescribedSpan common p)

/-- The source terminal edge equality, applying the finite identification theorem
to the now-proved critical inclusion. The independent noncontainment stays explicit. -/
theorem terminal_edge (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a')
    {t : Vertex R} (ht : Adjacent R a t)
    (hn : ¬ Z R a' ≤ stabilizer R a ⊓
      normalizer (edgeCommutator R a t : Set (FreeAmalgam R)))
    {g : FreeAmalgam R}
    (hge : (edgeCommutator R a (p.walk.getVert 1)).map
      (MulAut.conj g⁻¹).toMonoidHom = edgeCommutator R a t)
    (hfail : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hnot : ¬ failedSpanCommutator p g ≤ Z R a) :
    failedSpanCommutator p g =
      edgeCommutator R a' (p.walk.getVert (p.walk.length - 1)) :=
  terminal_edge_of_critical_le common p g hfail hnot
    (critical_commutator_le_failedSpan common p ht hn hge)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.CriticalInclusion
