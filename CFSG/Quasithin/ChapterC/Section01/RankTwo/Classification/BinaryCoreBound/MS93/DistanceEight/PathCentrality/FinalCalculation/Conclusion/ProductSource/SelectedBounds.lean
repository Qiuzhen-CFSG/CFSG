module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.Choices
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.Geometry

/-!
# Nonzero selected commutators in the final MS93 calculation

The selected local span lies in the literal radius-four ball, so its
commutator lies in the terminal product. The original center is moving
at the selected delta: transport the retained critical window by the
same local conjugator. The full preceding natural section therefore
puts Vcirc_delta in the selected span. If Ri vanished, the actual edge
centralizer would put that span in Q_(alpha'-4). Radius decomposition
would then put all of V_delta there, contrary to escape for the selected
critical pair (delta, alpha'-2).

The proved local fixed-core bound also puts Ri in its selected edge:
intersect that edge with D_delta, and use residual fixation and kernel
normalization to make this intersection invariant under G_delta. This is
the relative-normality argument of the earlier local-span calculation.

The natural section here is the permitted preceding (4.4.5) input. The
geometric choices still need construction; no product order is assumed.
Source: Meierfrankenfeld--Stellmacher (1993), (4.4), printed p.895.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

open NormalizerTransfer

private theorem fixed_span_commutator_le {G : Type*} [Group G]
    (S F Q L D E A : Subgroup G)
    (hgen : L ⊔ Q = F) (hQF : Q ≤ F) (hSQ : S ≤ Q)
    (hFQ : F ≤ normalizer Q) (hFD : F ≤ normalizer D)
    (hDL : D ≤ centralizer (L : Set G)) (hQE : Q ≤ normalizer E)
    (hSE : ⁅S, Q⁆ ≤ E) (hAQ : A ≤ Q)
    (hfixed : ⁅conjugatesIn S F, A⁆ ≤ D) :
    ⁅conjugatesIn S F, A⁆ ≤ E := by
  have hFED : F ≤ normalizer (E ⊓ D : Subgroup G) := by
    rw [← hgen]
    exact sup_le
      ((le_centralizer_iff.mpr (inf_le_right.trans hDL)).trans
        (Subgroup.centralizer_le_normalizer _))
      ((le_inf hQE (hQF.trans hFD)).trans inf_normalizer_le_normalizer_inf)
  have hpre : conjugatesIn S F ≤ commutatorPreimage Q A E := by
    apply iSup_le
    intro g
    have hQ : rightConjugate Q g = Q :=
      mem_normalizer_iff_map_conj_eq.mp (hFQ (F.inv_mem g.property))
    have hD : rightConjugate D g = D :=
      mem_normalizer_iff_map_conj_eq.mp (hFD (F.inv_mem g.property))
    have hED : rightConjugate (E ⊓ D) g = E ⊓ D :=
      mem_normalizer_iff_map_conj_eq.mp (hFED (F.inv_mem g.property))
    have hbound : ⁅rightConjugate S g, A⁆ ≤ rightConjugate E g := by
      apply (commutator_mono le_rfl hAQ).trans
      rw [← hQ, rightConjugate, rightConjugate, ← map_commutator]
      exact map_mono hSE
    have hfix : ⁅rightConjugate S g, A⁆ ≤ D :=
      (commutator_mono (le_iSup (fun h : F => rightConjugate S h) g) le_rfl).trans hfixed
    have hcut : rightConjugate E g ⊓ D = E ⊓ D := by
      calc
        rightConjugate E g ⊓ D = rightConjugate E g ⊓ rightConjugate D g := by rw [hD]
        _ = rightConjugate (E ⊓ D) g :=
          (Subgroup.map_inf _ _ _ (MulAut.conj (g : G)⁻¹).injective).symm
        _ = E ⊓ D := hED
    exact le_commutatorPreimage ((map_mono hSQ).trans hQ.le)
      ((le_inf hbound hfix).trans (hcut.le.trans inf_le_left))
  exact (commutator_mono hpre le_rfl).trans
    (commutator_commutatorPreimage_le Q A E hQE)

private theorem span_commutator_le_edge [Finite M] (source : LocalSource L R)
    (hb : 2 < geometry.b R)
    {a c t : Vertex R} (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c = 2)
    (hat : Adjacent R a t) (hct : Adjacent R c t)
    {A : Subgroup (FreeAmalgam R)} (hA : A ≤ Q R a ⊓ Q R c)
    (hfixed : ⁅localZSpan R a c, A⁆ ≤ fixedCore R c) :
    ⁅localZSpan R a c, A⁆ ≤ edgeCommutator R a t := by
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    rw [ha] at hn
    cases hcol : color R t <;> simp_all
  have hQcQt : Q R c ≤ Q R t := Q_le_adjacent_h R ht hct
  have hQcGa : Q R c ≤ stabilizer R a :=
    Q_le_stabilizer_of_dist_two R c a hc (by rwa [SimpleGraph.dist_comm])
  have hQE : Q R c ≤ normalizer (edgeCommutator R a t) := by
    intro g hg
    apply (mem_normalizer_iff_map_conj_eq).mpr
    change (⁅Z R a, Q R t⁆).map (MulAut.conj g).toMonoidHom = _
    have hZ : (Z R a).map (MulAut.conj g).toMonoidHom = Z R a :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized R a (hQcGa hg))
    have hQ : (Q R t).map (MulAut.conj g).toMonoidHom = Q R t :=
      mem_normalizer_iff_map_conj_eq.mp ((Q R t).le_normalizer (hQcQt hg))
    rw [map_commutator, hZ, hQ]
    rfl
  have hZQ : Z R a ≤ Q R c :=
    (Z_le_localZSpan R a c).trans (localZSpan_le_Q R hc hd.le hb)
  rw [LocalCommutator.span_eq_conjugates] at hfixed ⊢
  exact fixed_span_commutator_le (Z R a) (stabilizer R c) (Q R c) (Ltilde R c)
    (fixedCore R c) (edgeCommutator R a t) A (source.local_generation c hc)
    (fun _ hx => hx.1) hZQ (Q_normalized R c) (fixedCore_normalized R c)
    inf_le_right hQE (commutator_mono le_rfl hQcQt) (hA.trans inf_le_right) hfixed


namespace SelectedVertex
variable {a : Vertex R} {e : RegularPaths.ExtendedPath geometry a} (s : SelectedVertex e)

/-- Every conjugated Z in the selected span is within four steps of alpha. -/
theorem span_le_radius_four : localZSpan R a s.delta ≤ VBall R a 4 :=
  (localZSpan_le_V R s.distance.le).trans
    (Escape.Propagation.RadiusFour.VBall_le_of_dist_add_le a s.delta 2 4 (by
      rw [SimpleGraph.dist_comm, s.distance]))

/-- The selected Ri is a subgroup of the exact terminal product. -/
theorem commutator_le_product : selectedCommutator e s.delta ≤ terminalProduct e := by
  rw [selectedCommutator, terminalProduct, commutator_comm]
  exact commutator_mono le_rfl s.span_le_radius_four

/-- The terminal actor is b-2 steps from the selected critical start. -/
theorem terminal_distance (hb : 6 < geometry.b R) :
    (cosetGraph R).dist s.delta (e.walk.getVert (geometry.b R)) = geometry.b R - 2 := by
  have hd := ExtendedPath.distance e (i := 4) (j := geometry.b R) (by omega) (by omega)
  rw [e.center_eq] at hd
  have hu := (cosetGraph_connected R).dist_triangle (u := s.delta) (v := a)
    (w := e.walk.getVert (geometry.b R))
  rw [SimpleGraph.dist_comm (u := s.delta) (v := a), s.distance, hd] at hu
  have hl := (cosetGraph_connected R).dist_triangle (u := s.delta)
    (v := e.walk.getVert (geometry.b R)) (w := e.walk.getVert (2 + geometry.b R))
  rw [s.critical.shortest.symm.trans s.critical.length_eq_b,
    ExtendedPath.distance e (by omega) (by omega)] at hl
  omega

/-- The same source conjugator preserves actual movement, including B_delta. -/
theorem center_moving [Finite M] (common : CommonFacts R source geometry) :
    a ∈ Escape.movingNeighbors geometry s.delta := by
  have hc := ExtendedPath.vertex_color e (i := 6) (by decide) (by omega)
  have hm := (Escape.PairingControl.FirstPairing.movingNeighbors_act_iff
    common.large_distance s.conjugator (e.walk.getVert 6) (e.walk.getVert 4) hc).mpr
      (marked_moving common e (i := 4) (by decide) (by decide))
  rwa [e.center_eq, s.mem_stabilizer, s.delta_eq] at hm

/-- Ri cannot vanish: its selected local span generates the moving radius,
while the remaining edge radius is already in the terminal kernel. -/
theorem commutator_ne_bot [Finite M] (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c))) :
    selectedCommutator e s.delta ≠ ⊥ := by
  have ha := ExtendedPath.center_color e
  have hd := s.critical.start_color
  have ht := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  have hdist := s.terminal_distance hb
  have hpred : Adjacent R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 1)) := by
    have hh := adjacent_symm R (path_adjacent e (geometry.b R - 1) (by omega))
    simpa only [Nat.sub_add_cancel (show 1 ≤ geometry.b R by omega)] using hh
  have hspanQ : localZSpan R a s.delta ≤ Q R (e.walk.getVert (geometry.b R - 1)) := by
    apply (localZSpan_le_V R s.distance.le).trans
    apply Escape.Initial.Consequences.V_le_Q_of_distance hd
    have ht := ExtendedPath.distance e (i := 4) (j := geometry.b R - 1) (by omega) (by omega)
    rw [e.center_eq] at ht
    have htri := (cosetGraph_connected R).dist_triangle (u := s.delta) (v := a)
      (w := e.walk.getVert (geometry.b R - 1))
    rw [SimpleGraph.dist_comm (u := s.delta) (v := a), s.distance, ht] at htri
    omega
  intro hzero
  have hspan : localZSpan R a s.delta ≤ Q R (e.walk.getVert (geometry.b R)) := by
    rw [← common.centralizer _ _ ht hpred]
    exact le_inf hspanQ (commutator_eq_bot_iff_le_centralizer.mp hzero)
  obtain ⟨n⟩ := sections s.delta hd
  have hm : Vcirc R s.delta ≤ localZSpan R a s.delta := by
    rw [localZSpan_eq_conjugates]
    exact Escape.Initial.Natural.moving_generation_of_naturalSection
      source geometry common.large_distance s.delta hd n a (s.center_moving common)
  have hedge : V R s.beta ≤ Q R (e.walk.getVert (geometry.b R)) := by
    apply (Escape.Initial.Consequences.edge_radius_le_radius ha s.adjacent_center).trans
    apply Escape.Initial.Consequences.V_le_Q_of_distance ha
    have ht := ExtendedPath.distance e (i := 4) (j := geometry.b R) (by omega) (by omega)
    rw [e.center_eq] at ht
    rw [ht]
    omega
  apply common.escape s.delta hd _ s.critical.critical (e.walk.getVert (geometry.b R))
  · rw [ExtendedPath.distance e (by omega) (by omega)]
    omega
  · rw [s.critical.shortest.symm.trans s.critical.length_eq_b, hdist]
    omega
  · rw [Escape.Initial.Consequences.radius_eq_moving_sup_edge source hd
      (adjacent_symm R s.adjacent_delta)]
    exact sup_le (hm.trans hspan) hedge

/-- Residual fixation places the selected Ri inside its actual incident
edge. Normality throughout is relative to G_delta and its kernel. -/
theorem commutator_le_chosen_edge [Finite M]
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R) :
    selectedCommutator e s.delta ≤ edgeCommutator R a s.beta := by
  have ht := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  apply span_commutator_le_edge source common.large_distance
    (ExtendedPath.center_color e) s.critical.start_color s.distance
    s.adjacent_center (adjacent_symm R s.adjacent_delta)
    (hfixed := (s.local_bounds common hb hlocal).trans inf_le_right)
  apply le_inf
  · apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ ht)
    rw [geometry.distance_constant _ ht, SimpleGraph.dist_comm]
    have hd := ExtendedPath.distance e (i := 4) (j := geometry.b R) (by omega) (by omega)
    rw [e.center_eq] at hd
    change (cosetGraph R).dist a (e.walk.getVert (geometry.b R)) < geometry.b R
    rw [hd]
    omega
  · apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ ht)
    rw [geometry.distance_constant _ ht, SimpleGraph.dist_comm]
    change (cosetGraph R).dist s.delta (e.walk.getVert (geometry.b R)) < geometry.b R
    rw [s.terminal_distance hb]
    omega

/-- The printed edge/kernel bound for Ri. Kernel containment comes from
its inclusion in the terminal product, supported on Z_(alpha'-4). -/
theorem commutator_le_edge_inf_kernel [Finite M]
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hlocal : LocalCommutatorControl R) :
    selectedCommutator e s.delta ≤ edgeCommutator R a s.beta ⊓
      Q R (e.walk.getVert (4 + geometry.b R)) := by
  have ht := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  have hpred : Adjacent R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 1)) := by
    have hh := adjacent_symm R (path_adjacent e (geometry.b R - 1) (by omega))
    simpa only [Nat.sub_add_cancel (show 1 ≤ geometry.b R by omega)] using hh
  apply le_inf (s.commutator_le_chosen_edge common hb hlocal)
  apply (s.commutator_le_product.trans (terminalProduct_le_backward_edge hb e)).trans
  apply ((Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
    (LocalCommutator.moduleFacts common) _ _ ht hpred).trans (U_le_Z R _)).trans
  apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ ht)
  rw [geometry.distance_constant _ ht, ExtendedPath.distance e (by omega) (by omega)]
  change 4 + geometry.b R - geometry.b R < geometry.b R
  omega

end SelectedVertex
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource
