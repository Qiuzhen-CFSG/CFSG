module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Pairings.Edges
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.NeighborAction.Geometry

/-!
# The second-layer edge displacement

The actual neighboring kernels generate the common edge kernel:
Q_beta = Q_a join Q_c. The local turn at c transports the preceding
(4.5.3)(ii) bound from Q_d to Q_a while preserving hat V_c. The Q_c
commutator is H_c, hence lies in Z_c. Both bounds therefore land in
hat V_a. Since Q_beta normalizes hat V_a, the commutator preimage joins
the two actor bounds and gives [hat V_c,Q_beta] <= hat V_a.

The retained source premises are exactly (4.5.1)(v) at a, (4.5.3)(i)
at a and c, and (4.5.3)(ii) at c,d. Their producer is
`qt-c01-ms93-core-factors-early-layers`. In particular the forward choice
d is transported by the actual turn; no unproved choice independence or
erroneous `Early.OrbitFacts` record is used.

The final export supplies the sole remaining displacement premise of
`characterComparisons_of_second_movement`, using the supplied marked dual
sections unchanged. Those sections belong to
`qt-c01-ms93-higher-marked-quotients`; their final discharge and character
assembly remain with `qt-c01-ms93-z-geometry-character-pairings`.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.5.1)(v) and (4.5.3)(i)--(ii), printed pp.896--898; the
neighboring product comparisons are used in (4.5.5), printed p.899.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Pairings.SecondDisplacement
open PathCentrality
variable {M : Type*} [Group M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

private theorem path_color {a : Vertex R} (p : Higher.SourcePath a)
    {i : ℕ} (hi : Even i) (hi14 : i ≤ 14) : color R (p.walk.getVert i) = false :=
  (RegularPaths.walk_vertex_color p.start_color p.walk
    (by rw [p.length_eq]; exact hi14)).mpr hi

private theorem path_adjacent {a : Vertex R} (p : Higher.SourcePath a)
    {i : ℕ} (hi : i < 14) :
    Adjacent R (p.walk.getVert i) (p.walk.getVert (i + 1)) :=
  (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by rw [p.length_eq]; exact hi))

/-- The literal ambient second displacement follows from the preceding source
layers. The turn at c identifies the Q_d action with the Q_a action, and
the two neighboring kernels generate Q_beta. -/
theorem second_movement [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) {a : Vertex R} (p : Higher.SourcePath a)
    (hVa : hatV R a (p.walk.getVert 6) = Vcirc R a ⊔ Z R a)
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hH : Nat.card (H R a) = 4)
    (hforward : ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 8)) :
    ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (p.walk.getVert 5)⁆ ≤ hatV R a (p.walk.getVert 6) := by
  let c := p.walk.getVert 6
  let d := p.walk.getVert 8
  let t := p.walk.getVert 5
  let A := hatV R a c
  let B := hatV R c d
  have ha : color R a = false :=
    p.center_eq ▸ path_color p (i := 4) (by decide) (by decide)
  have hc : color R c = false := path_color p (by decide) (by decide)
  have hat : Adjacent R a t := by
    simpa only [p.center_eq] using path_adjacent p (i := 4) (by decide)
  have hct : Adjacent R c t := adjacent_symm R (path_adjacent p (i := 5) (by decide))
  have hca : (cosetGraph R).dist c a = 2 := p.two_step_distances.1
  have hjoin : Q R a ⊔ Q R c = Q R t :=
    NeighborAction.neighbor_kernel_join common earlier ha hca hat hct hVa hH
  have hZa : Z R a ≤ A := by
    change Z R a ≤ hatV R a c
    rw [hVa]
    exact le_sup_right
  have hZc : Z R c ≤ A := Z_le_localZSpan R c a
  have hQa : ⁅B, Q R a⁆ ≤ A := by
    obtain ⟨g, hg, ht⟩ := p.turns 6 (by decide) (by decide) (by decide)
    have hgd : act R g d = a := by simpa only [p.center_eq] using ht
    let f := (MulAut.conj g⁻¹).toMonoidHom
    have hB : B.map f = B := mem_normalizer_iff_map_conj_eq.mp
      (hatV_normalized R c d ((stabilizer R c).inv_mem hg))
    have hQ : (Q R d).map f = Q R a := by rw [← Q_act, hgd]
    have hZ : (Z R d).map f = Z R a := by rw [← Z_act, hgd]
    have hh := map_mono (f := f) hforward
    change (⁅B, Q R d⁆).map f ≤ (Z R d).map f at hh
    rw [map_commutator, hB, hQ, hZ] at hh
    exact hh.trans hZa
  have hQc : ⁅B, Q R c⁆ ≤ A := by
    rw [NeighborAction.first_kernel_commutator common hc hVc]
    exact (H_le_Z_of_central common hc (earlier.centrality c hc)).trans hZc
  have hQt : Q R t ≤ normalizer A :=
    (show Q R t ≤ stabilizer R a from fun _ hx => hx.2 a (adjacent_symm R hat)).trans
      (hatV_normalized R a c)
  have hpre : Q R t ≤ commutatorPreimage (Q R t) B A := by
    rw [← hjoin]
    exact sup_le
      (le_commutatorPreimage le_sup_left (by rw [commutator_comm]; exact hQa))
      (le_commutatorPreimage le_sup_right (by rw [commutator_comm]; exact hQc))
  rw [commutator_comm]
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hQt)

/-- Apply the proved displacement to the existing character-comparison consumer.
Only the permitted early-source clauses and the two marked sections remain
explicit; no second-edge or Z-case conclusion is an input. -/
theorem characterComparisons [Finite M] (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Higher.SourcePath (alpha R))
    (s : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R)))
    (t : MarkedPairSection source common
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8))
      (hatV R (alpha R) (p.walk.getVert 6)) true)
    (hVa : hatV R (alpha R) (p.walk.getVert 6) = Vcirc R (alpha R) ⊔ Z R (alpha R))
    (hVc : hatV R (p.walk.getVert 6) (p.walk.getVert 8) =
      Vcirc R (p.walk.getVert 6) ⊔ Z R (p.walk.getVert 6))
    (hH : Nat.card (H R (alpha R)) = 4)
    (hforward : ⁅hatV R (p.walk.getVert 6) (p.walk.getVert 8),
      Q R (p.walk.getVert 8)⁆ ≤ Z R (p.walk.getVert 8)) :
    Nonempty (CharacterComparisons p) :=
  characterComparisons_of_second_movement common earlier p s t
    (second_movement common earlier p hVa hVc hH hforward)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Higher.OrbitGeometry.TwoCases.ZGeometry.Pairings.SecondDisplacement
