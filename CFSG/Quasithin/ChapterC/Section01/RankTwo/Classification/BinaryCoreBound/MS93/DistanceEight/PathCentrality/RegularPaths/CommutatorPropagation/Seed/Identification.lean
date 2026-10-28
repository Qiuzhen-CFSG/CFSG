module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed.Transport

/-!
# Identifying the terminal edge from critical-commutator inclusion

The failed-span commutator is contained in the terminal edge displacement,
whose order is at most four. If it contains the nonzero critical commutator
and is not contained in Z_a, that inclusion is strict. Lagrange's theorem
then forces its order to be at least four, and hence forces equality with
the terminal edge. No edge-order equality is assumed.

The final theorem applies this argument and the fixed-core transport to the
literal R₀. The initial P-orbit noncontainment and critical-commutator
inclusion remain explicit premises, to be discharged by the seed owner.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.4), printed p.894, the initial R₀ calculation.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- A proper overgroup of the nonzero critical commutator fills the terminal edge. -/
theorem terminal_edge_of_critical_le (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (g : FreeAmalgam R)
    (hfail : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hnot : ¬ failedSpanCommutator p g ≤ Z R a)
    (hcrit : ⁅Z R a, Z R a'⁆ ≤ failedSpanCommutator p g) :
    failedSpanCommutator p g =
      edgeCommutator R a' (p.walk.getVert (p.walk.length - 1)) := by
  have hb := common.large_distance
  have hl := p.length_eq_b
  have ht : Adjacent R a' (p.walk.getVert (p.walk.length - 1)) := by
    have hh := p.walk.adj_getVert_succ (i := p.walk.length - 1) (by omega)
    rw [show p.walk.length - 1 + 1 = p.walk.length by omega,
      SimpleGraph.Walk.getVert_length] at hh
    exact adjacent_symm R ((cosetGraph_adj R _ _).mp hh)
  let E := edgeCommutator R a' (p.walk.getVert (p.walk.length - 1))
  let C := ⁅Z R a, Z R a'⁆
  let K := failedSpanCommutator p g
  change C ≤ K at hcrit
  change ¬ K ≤ Z R a at hnot
  change K = E
  have hKE : K ≤ E := failedSpanCommutator_le_terminal_edge p hb g hfail
  have hE : E ≤ U R a' := Escape.EdgeTransfer.edge_commutator_le_natural hb
    (moduleFacts common) a' _ p.end_color ht
  have hcard : Nat.card E ≤ 4 := Escape.EdgeTransfer.edge_displacement_card_le_four hb
    (moduleFacts common) a' _ p.end_color ht
  let := finite_stabilizer R a'
  let : Finite E := Finite.of_injective
    (inclusion (hE.trans ((U_le_Z R a').trans (Z_le_stabilizer R a'))))
    (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion hKE) (inclusion_injective _)
  let : Finite C := Finite.of_injective (inclusion hcrit) (inclusion_injective _)
  have hCZ : C ≤ Z R a := le_normalizer_iff_commutator_le_left.mp
    ((p.endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized R a))
  have hpos : 1 < Nat.card C := (one_lt_card_iff_ne_bot C).mpr
    (common.critical_noncommutation a p.start_color a' p.critical)
  have hlt : Nat.card C < Nat.card K := by
    by_contra! hh
    have heq : C = K := eq_of_le_of_card_ge hcrit hh
    exact hnot (heq ▸ hCZ)
  obtain ⟨k, hk⟩ := card_dvd_of_le hcrit
  have hk2 : 2 ≤ k := by
    by_contra! h
    interval_cases k
    · simp only [Nat.mul_zero] at hk
      omega
    · simp only [Nat.mul_one] at hk
      omega
  have hfour : 4 ≤ Nat.card K := by nlinarith
  exact eq_of_le_of_card_ge hKE (by omega)

/-- The two remaining P-orbit assertions suffice to construct all four seed fields. -/
theorem seed_of_critical_le (common : CommonFacts R source geometry)
    {a a' : Vertex R} (p : CriticalPath R geometry a a') (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R) (hp : HasTurnConjugators R p)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R a)
    (hfail : (prescribedSpan p).map (MulAut.conj g⁻¹).toMonoidHom ≤
      Q R (p.walk.getVert (p.walk.length - 2)))
    (hnot : ¬ failedSpanCommutator p g ≤ Z R a)
    (hcrit : ⁅Z R a, Z R a'⁆ ≤ failedSpanCommutator p g) :
    TerminalPropagationSeed p (failedSpanCommutator p g) :=
  seed_of_initial_calculation source p hb hlocal hp hg hfail hnot
    (terminal_edge_of_critical_le common p g hfail hnot hcrit)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Seed
