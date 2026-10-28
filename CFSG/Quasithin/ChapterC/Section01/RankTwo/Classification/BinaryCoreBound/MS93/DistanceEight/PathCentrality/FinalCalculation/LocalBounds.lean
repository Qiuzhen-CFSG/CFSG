module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.SourceCritical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.RegularPaths.CommutatorPropagation.Six

/-!
# The second local calculation in MS93 (4.4.5)

Write d=alpha-2, c=alpha and v=alpha'-2 on the actual extended path.
The regular turn puts Z_d in the forward span at c. Its critical escape
makes the source-critical version of (4.4.1) applicable to
R1=[Z_d,V_v intersect Q_c], placing R1 in the fixed core D_c.

If R1 properly contains the critical commutator, its order bound fills
the incident edge plane. A residual turn fixes R1 pointwise and carries
that plane to the edge at alpha+2. Since b>6, V_v centralizes Z_(alpha'+2).
This contradicts the extended path's nonnormalization clause at alpha+2.
Thus R1 lies in the critical commutator, exactly as on printed p.895.

Only the earlier critical-prefix nonnatural exclusion is used for local
control. Every local span in this application has its own escape witness.
Source: MS93 (4.4.5), final paragraph of p.894 and first lines of p.895.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation
open RegularPaths RegularPaths.CommutatorPropagation
open LocalCommutator.NaturalCase.Opposite.Selection
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

namespace ExtendedPath
variable {a : Vertex R} (e : RegularPaths.ExtendedPath geometry a)

/-- The first source image is nontrivial by the common escape theorem,
applied to the reversed critical window beginning at alpha-2. -/
theorem two_le_source_image (common : CommonFacts R source geometry) :
    2 ≤ (Q R (e.walk.getVert 4)).relIndex
      (V R (e.walk.getVert (2 + geometry.b R))) := by
  let p := (e.window 2 (by decide) (by decide)).reverse common
  have hb := common.large_distance
  have hescape : ¬ V R (e.walk.getVert (2 + geometry.b R)) ≤
      Q R (e.walk.getVert 4) := by
    apply common.escape _ p.start_color _ p.critical
    · rw [SimpleGraph.dist_comm, distance e (by decide) (by omega)]
    · rw [SimpleGraph.dist_comm (u := e.walk.getVert (2 + geometry.b R)),
        distance e (by omega) (by omega),
        SimpleGraph.dist_comm (v := e.walk.getVert 2), distance e (by omega) (by omega)]
      omega
  let := finite_stabilizer R (e.walk.getVert (2 + geometry.b R))
  let : Finite (V R (e.walk.getVert (2 + geometry.b R))) := Finite.of_injective
    (inclusion ((geometry.V_le_Q hb _ p.start_color).trans (fun _ hy => hy.1)))
    (inclusion_injective _)
  have hpos : (Q R (e.walk.getVert 4)).relIndex
      (V R (e.walk.getVert (2 + geometry.b R))) ≠ 0 := index_ne_zero_of_finite
  have hne : (Q R (e.walk.getVert 4)).relIndex
      (V R (e.walk.getVert (2 + geometry.b R))) ≠ 1 := by
    intro he
    exact hescape (Subgroup.relIndex_eq_one.mp he)
  omega

/-- The literal R1 of (4.4.5), with index zero at alpha-4. -/
noncomputable abbrev firstCommutator : Subgroup (FreeAmalgam R) :=
  ⁅Z R (e.walk.getVert 2),
    V R (e.walk.getVert (2 + geometry.b R)) ⊓ Q R (e.walk.getVert 4)⁆

omit [Finite M] in
private theorem adjacent (i : ℕ) (hi : i < geometry.b R + 8) :
    Adjacent R (e.walk.getVert i) (e.walk.getVert (i + 1)) :=
  (cosetGraph_adj R _ _).mp (e.walk.adj_getVert_succ (e.length_eq ▸ hi))

omit [Finite M] in
/-- The source R1 is contained in the terminal radius group. -/
theorem firstCommutator_le_radius (common : CommonFacts R source geometry) :
    firstCommutator e ≤ V R (e.walk.getVert (2 + geometry.b R)) := by
  have hlocal := (e.window 2 (by decide) (by decide)).reverse common
  have hZ := hlocal.endpoint_Z_le_start_stabilizer (by have := common.large_distance; omega)
  exact (commutator_mono le_rfl inf_le_left).trans
    (le_normalizer_iff_commutator_le_right.mp
      (hZ.trans (DistanceEight.V_normalized R _)))

omit [Finite M] in
/-- The critical line lies in R1 because the terminal Z-layer lies in Q_alpha. -/
theorem critical_le_firstCommutator (hb : 2 < geometry.b R) :
    ⁅Z R (e.walk.getVert 2), Z R (e.walk.getVert (2 + geometry.b R))⁆ ≤
      firstCommutator e := by
  apply commutator_mono le_rfl
  refine le_inf (Z_le_VBall R _ 2) ?_
  have hv := (e.window 2 (by decide) (by decide)).end_color
  apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hv)
  rw [geometry.distance_constant _ hv, SimpleGraph.dist_comm,
    distance e (by omega) (by omega)]
  change 2 + geometry.b R - 4 < geometry.b R
  omega

/-- R1 is contained in the edge plane at alpha-2 directed toward alpha. -/
theorem firstCommutator_le_edge :
    firstCommutator e ≤ edgeCommutator R (e.walk.getVert 2) (e.walk.getVert 3) := by
  apply commutator_mono le_rfl
  apply inf_le_right.trans
  apply Q_le_adjacent_h R _ (adjacent_symm R (adjacent e 3 (by omega)))
  have hne := adjacent_color_ne R (adjacent e 2 (by omega))
  have hc := vertex_color e (i := 2) (by decide) (by omega)
  cases ht : color R (e.walk.getVert 3) <;> simp_all

/-- The only (4.4.1) application in the R1 calculation is on an escaping span. -/
theorem firstCommutator_le_fixed (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (exclude : ∀ {d f : Vertex R} (p : CriticalPath R geometry d f),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (p.walk.getVert 2) → False) :
    firstCommutator e ≤ fixedCore R (e.walk.getVert 4) := by
  have hc := vertex_color e (i := 4) (by decide) (by omega)
  have hf := vertex_color e (i := 6) (by decide) (by omega)
  have hfc : (cosetGraph R).dist (e.walk.getVert 6) (e.walk.getVert 4) = 2 := by
    rw [SimpleGraph.dist_comm, distance e (by decide) (by omega)]
  obtain ⟨g, hg, hturn⟩ := e.turns 4 (by decide) (by decide) (by omega)
  have hspan : Z R (e.walk.getVert 2) ≤
      localZSpan R (e.walk.getVert 6) (e.walk.getVert 4) := by
    have hh := le_iSup (fun k : stabilizer R (e.walk.getVert 4) =>
      Z R (act R k (e.walk.getVert 6))) ⟨g, hg⟩
    have hturn' : act R g (e.walk.getVert 6) = e.walk.getVert 2 := by
      simpa only [Nat.reduceAdd, Nat.reduceSub] using hturn
    simpa only [hturn', localZSpan] using hh
  have hv := (e.window 2 (by decide) (by decide)).end_color
  have hV : V R (e.walk.getVert (2 + geometry.b R)) ≤ Q R (e.walk.getVert 6) := by
    apply V_le_Q_of_dist_add_two_lt R hv
    rw [SimpleGraph.dist_comm, distance e (by omega) (by omega)]
    omega
  have hbound : ⁅localZSpan R (e.walk.getVert 6) (e.walk.getVert 4),
      Q R (e.walk.getVert 6) ⊓ Q R (e.walk.getVert 4)⁆ ≤ fixedCore R (e.walk.getVert 4) := by
    by_cases h : ⁅Z R (e.walk.getVert 6), Q R (e.walk.getVert 4)⁆ ≤
        fixedCore R (e.walk.getVert 4)
    · exact (commutator_mono le_rfl inf_le_right).trans
        ((LocalCommutator.span_commutator_le_fixed_iff hc hfc.le common.large_distance).mpr h)
    · apply (LocalCommutator.SourceCritical.localControl_of_spanEscape
        common (by omega) exclude hf hc hfc h ?_).1
      refine ⟨e.walk.getVert (2 + geometry.b R), ?_, ?_⟩
      · rw [distance e (by omega) (by omega)]
        omega
      · intro he
        exact (e.window 2 (by decide) (by decide)).critical.2 (hspan.trans he)
  exact (commutator_mono hspan (inf_le_inf hV le_rfl)).trans hbound

omit [Finite M] in
private theorem midpoint_unique (geometry : Geometry R) {d c t u : Vertex R}
    (hd : (cosetGraph R).dist d c = 2)
    (hdt : Adjacent R d t) (hct : Adjacent R c t)
    (hdu : Adjacent R d u) (hcu : Adjacent R c u) : t = u := by
  let w : (cosetGraph R).Walk d c := .cons ((cosetGraph_adj R _ _).mpr hdt)
    (.cons ((cosetGraph_adj R _ _).mpr (adjacent_symm R hct)) .nil)
  let v : (cosetGraph R).Walk d c := .cons ((cosetGraph_adj R _ _).mpr hdu)
    (.cons ((cosetGraph_adj R _ _).mpr (adjacent_symm R hcu)) .nil)
  have hw : w.length = (cosetGraph R).dist d c := hd.symm
  have hv : v.length = (cosetGraph R).dist d c := hd.symm
  have hh := (geometry.tree.isAcyclic.subsingleton_path d c).elim
    ⟨w, w.isPath_of_length_eq_dist hw⟩ ⟨v, v.isPath_of_length_eq_dist hv⟩
  exact congrArg (fun q : (cosetGraph R).Path d c => q.val.getVert 1) hh

private theorem edge_eq_of_fixed (source : LocalSource L R)
    (hb : 6 < geometry.b R) {K : Subgroup (FreeAmalgam R)}
    (hK : K ≤ fixedCore R (e.walk.getVert 4))
    (hE : K = edgeCommutator R (e.walk.getVert 2) (e.walk.getVert 3)) :
    K = edgeCommutator R (e.walk.getVert 6) (e.walk.getVert 5) := by
  obtain ⟨g, hg, hgturn⟩ := e.turns 4 (by decide) (by decide) (by omega)
  have ht : act R g⁻¹ (e.walk.getVert 2) = e.walk.getVert 6 := by
    have hh := congrArg (act R g⁻¹) hgturn
    simpa only [Nat.reduceAdd, Nat.reduceSub, ← act_mul, mul_inv_cancel, act_one] using hh.symm
  obtain ⟨l, hl, ht⟩ := exists_residual_turn source
    (vertex_color e (i := 4) (by decide) (by omega))
    (show (cosetGraph R).dist (e.walk.getVert 4) (e.walk.getVert 6) = 2 from
      distance e (by decide) (by omega)) ((stabilizer R _).inv_mem hg) ht
  have hlc : act R l (e.walk.getVert 4) = e.walk.getVert 4 := Ltilde_le_stabilizer _ hl
  have hm : act R l (e.walk.getVert 3) = e.walk.getVert 5 := by
    apply midpoint_unique (geometry := geometry)
      (show (cosetGraph R).dist (e.walk.getVert 6) (e.walk.getVert 4) = 2 by
        rw [SimpleGraph.dist_comm, distance e (by decide) (by omega)])
    · simpa only [ht] using (adjacent_act_iff R l _ _).mpr (adjacent e 2 (by omega))
    · simpa only [hlc] using (adjacent_act_iff R l _ _).mpr
        (adjacent_symm R (adjacent e 3 (by omega)))
    · exact adjacent_symm R (adjacent e 5 (by omega))
    · exact adjacent e 4 (by omega)
  have hfix (x : FreeAmalgam R) (hx : x ∈ K) : (MulAut.conj l⁻¹) x = x := by
    have hh := (hK hx).2 l⁻¹ ((Ltilde R _).inv_mem hl)
    change l⁻¹ * x * (l⁻¹)⁻¹ = x
    rw [hh, mul_inv_cancel_right]
  have hmap : K.map (MulAut.conj l⁻¹).toMonoidHom = K := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hfix x hx).symm ▸ hx
    · intro x hx
      exact ⟨x, hx, hfix x hx⟩
  calc
    K = K.map (MulAut.conj l⁻¹).toMonoidHom := hmap.symm
    _ = (edgeCommutator R (e.walk.getVert 2) (e.walk.getVert 3)).map
        (MulAut.conj l⁻¹).toMonoidHom := congrArg _ hE
    _ = edgeCommutator R (e.walk.getVert 6) (e.walk.getVert 5) := by
      rw [← edgeCommutator_act, ht, hm]

/-- If R1 exceeds the critical line, it fills the actual incident edge plane. -/
theorem firstCommutator_eq_edge_of_not_le_critical
    (common : CommonFacts R source geometry)
    (hn : ¬ firstCommutator e ≤
      ⁅Z R (e.walk.getVert 2), Z R (e.walk.getVert (2 + geometry.b R))⁆) :
    firstCommutator e = edgeCommutator R (e.walk.getVert 2) (e.walk.getVert 3) := by
  let K := firstCommutator e
  let E := edgeCommutator R (e.walk.getVert 2) (e.walk.getVert 3)
  let C := ⁅Z R (e.walk.getVert 2), Z R (e.walk.getVert (2 + geometry.b R))⁆
  have hKE : K ≤ E := firstCommutator_le_edge e
  have hc := vertex_color e (i := 2) (by decide) (by omega)
  have hEU : E ≤ U R (e.walk.getVert 2) :=
    Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (RegularPaths.moduleFacts common) _ _ hc (adjacent e 2 (by omega))
  have hEcard : Nat.card E ≤ 4 :=
    Escape.EdgeTransfer.edge_displacement_card_le_four common.large_distance
      (RegularPaths.moduleFacts common) _ _ hc (adjacent e 2 (by omega))
  let := finite_stabilizer R (e.walk.getVert 2)
  let : Finite E := Finite.of_injective
    (inclusion (hEU.trans ((U_le_Z R _).trans (Z_le_stabilizer R _))))
    (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion hKE) (inclusion_injective _)
  have hCK : C ≤ K := critical_le_firstCommutator e common.large_distance
  let : Finite C := Finite.of_injective (inclusion hCK) (inclusion_injective _)
  have hCpos : 1 < Nat.card C := (one_lt_card_iff_ne_bot C).mpr
    (common.critical_noncommutation _ hc _ (e.window 2 (by decide) (by decide)).critical)
  have hlt : Nat.card C < Nat.card K := by
    by_contra! h
    exact hn (eq_of_le_of_card_ge hCK h).ge
  have hKcard : Nat.card K ≤ 4 := (card_le_of_le hKE).trans hEcard
  obtain ⟨k, hk⟩ := card_dvd_of_le hCK
  have hk2 : 2 ≤ k := by
    by_contra! h
    interval_cases k
    · simp only [Nat.mul_zero] at hk
      omega
    · simp only [Nat.mul_one] at hk
      omega
  apply eq_of_le_of_card_ge hKE
  nlinarith

omit [Finite M] in
/-- The radius at alpha'-2 centralizes Z_(alpha'+2), since their radius
plus separation is six, strictly below the critical distance. -/
theorem radius_centralizes_later_Z (hb : 6 < geometry.b R) :
    V R (e.walk.getVert (2 + geometry.b R)) ≤
      centralizer (Z R (e.walk.getVert (6 + geometry.b R)) : Set (FreeAmalgam R)) := by
  have hv := (e.window 2 (by decide) (by decide)).end_color
  have hw := (e.window 6 (by decide) (by decide)).end_color
  apply (V_le_iff R hv _).mpr
  intro d hd hdist
  have hZ : Z R d ≤ Q R (e.walk.getVert (6 + geometry.b R)) := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    change (cosetGraph R).dist d (e.walk.getVert (6 + geometry.b R)) < geometry.b R
    have htri := (cosetGraph_connected R).dist_triangle (u := d)
      (v := e.walk.getVert (2 + geometry.b R)) (w := e.walk.getVert (6 + geometry.b R))
    rw [distance e (by omega) (by omega)] at htri
    omega
  exact hZ.trans (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes _ hw)))

/-- The second local calculation of (4.4.5), with the exact source R1.
No bound on the first image V_(alpha'-2)Q_alpha/Q_alpha is assumed. -/
theorem firstCommutator_le_critical
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (exclude : ∀ {d f : Vertex R} (p : CriticalPath R geometry d f),
      ¬ ⁅Z R d, Q R (p.walk.getVert 2)⁆ ≤ fixedCore R (p.walk.getVert 2) →
      ¬ LocalCommutator.HasNaturalSection R d (p.walk.getVert 2) → False) :
    firstCommutator e ≤
      ⁅Z R (e.walk.getVert 2), Z R (e.walk.getVert (2 + geometry.b R))⁆ := by
  by_contra hn
  have hE := edge_eq_of_fixed e source hb
    (firstCommutator_le_fixed e common hb exclude)
    (firstCommutator_eq_edge_of_not_le_critical e common hn)
  have hc : firstCommutator e ≤
      centralizer (Z R (e.walk.getVert (6 + geometry.b R)) : Set (FreeAmalgam R)) :=
    (firstCommutator_le_radius e common).trans (radius_centralizes_later_Z e hb)
  have hn' := (le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)
  have hlocal := (e.window 6 (by decide) (by decide)).endpoint_Z_le_start_stabilizer (by omega)
  apply e.nonnormalization 6 (by decide) (by decide) (by decide)
  apply le_inf hlocal
  simpa only [hE] using hn'

end ExtendedPath
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation
