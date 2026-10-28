module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.SelectedCriticalPrefix
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.FinalCalculation.Conclusion.ProductSource.SelectedBounds

/-!
# The selected terminal product from critical-prefix control

Each selected commutator receives its fixed-core bound from the actual
critical-prefix theorem. Relative normality then puts it in its selected
edge and the terminal kernel. The two separated nonzero commutators fill
the terminal product of order at most four, retaining its natural-kernel
containment for the concluding first-edge comparison.

Source: Meierfrankenfeld--Stellmacher (1993), conclusion of (4.4), p.895.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.Product
open NormalizerTransfer
open FinalCalculation FinalCalculation.Conclusion FinalCalculation.Conclusion.ProductSource
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

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


private theorem selected_le_edge [Finite M]
    {a : Vertex R} {e : RegularPaths.ExtendedPath geometry a} (s : SelectedVertex e)
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hprefix : LocalCommutator.CriticalPrefixControl R geometry) :
    selectedCommutator e s.delta ≤ edgeCommutator R a s.beta := by
  have ht := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  apply span_commutator_le_edge source common.large_distance
    (ExtendedPath.center_color e) s.critical.start_color s.distance
    s.adjacent_center (adjacent_symm R s.adjacent_delta)
    (hfixed := (selectedCommutator_bounds_of_criticalPrefix hb hprefix e s.distance s.critical).trans inf_le_right)
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
private theorem selected_le_edge_inf_kernel [Finite M]
    {a : Vertex R} {e : RegularPaths.ExtendedPath geometry a} (s : SelectedVertex e)
    (common : CommonFacts R source geometry) (hb : 6 < geometry.b R)
    (hprefix : LocalCommutator.CriticalPrefixControl R geometry) :
    selectedCommutator e s.delta ≤ edgeCommutator R a s.beta ⊓
      Q R (e.walk.getVert (4 + geometry.b R)) := by
  have ht := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  have hpred : Adjacent R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 1)) := by
    have hh := adjacent_symm R (path_adjacent e (geometry.b R - 1) (by omega))
    simpa only [Nat.sub_add_cancel (show 1 ≤ geometry.b R by omega)] using hh
  apply le_inf (selected_le_edge s common hb hprefix)
  apply (s.commutator_le_product.trans (terminalProduct_le_backward_edge hb e)).trans
  apply ((Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
    (LocalCommutator.moduleFacts common) _ _ ht hpred).trans (U_le_Z R _)).trans
  apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ ht)
  rw [geometry.distance_constant _ ht, ExtendedPath.distance e (by omega) (by omega)]
  change 4 + geometry.b R - geometry.b R < geometry.b R
  omega

private theorem fill_four_group {G : Type*} [Group G] (A B K : Subgroup G)
    [Finite K] (hAK : A ≤ K) (hBK : B ≤ K) (hA : A ≠ ⊥) (hB : B ≠ ⊥)
    (hdis : A ⊓ B = ⊥) (hK : Nat.card K ≤ 4) :
    Nat.card K = 4 ∧ K = A ⊔ B := by
  let J := A ⊔ B
  have hJK : J ≤ K := sup_le hAK hBK
  let : Finite J := Finite.of_injective (inclusion hJK) (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion hAK) (inclusion_injective _)
  have hAJ : A ≤ J := le_sup_left
  have hBJ : B ≤ J := le_sup_right
  have hpos : 1 < Nat.card A := (one_lt_card_iff_ne_bot _).mpr hA
  have hlt : Nat.card A < Nat.card J := by
    by_contra! h
    have heq : A = J := eq_of_le_of_card_ge hAJ h
    apply hB
    apply le_bot_iff.mp
    rw [← hdis]
    exact le_inf (heq ▸ hBJ) le_rfl
  obtain ⟨k, hk⟩ := card_dvd_of_le hAJ
  have hk2 : 2 ≤ k := by
    by_contra! h
    interval_cases k
    · simp only [Nat.mul_zero] at hk
      omega
    · simp only [Nat.mul_one] at hk
      omega
  have hfour : 4 ≤ Nat.card J := by nlinarith
  have heq : J = K := eq_of_le_of_card_ge hJK (hK.trans hfour)
  refine ⟨?_, heq.symm⟩
  rw [heq] at hfour
  omega

variable [Finite M] {a : Vertex R} {e : RegularPaths.ExtendedPath geometry a}
  (p : SelectedPair e)
include p

private theorem selected_disjoint (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hprefix : LocalCommutator.CriticalPrefixControl R geometry) :
    selectedCommutator e p.left.delta ⊓ selectedCommutator e p.right.delta = ⊥ := by
  have hl := selected_le_edge_inf_kernel p.left common hb hprefix
  have hr := selected_le_edge_inf_kernel p.right common hb hprefix
  apply le_bot_iff.mp
  rw [← p.separated]
  exact le_inf
    (le_inf (inf_le_left.trans (hl.trans inf_le_left))
      (inf_le_right.trans (hr.trans inf_le_left)))
    (inf_le_left.trans (hl.trans inf_le_right))

/-- Two disjoint nonzero selected commutators fill the order-at-most-four
terminal product. This proves both saturation and its order. -/
theorem selected_card_and_product (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c))) :
    Nat.card (terminalProduct e) = 4 ∧
      terminalProduct e = selectedCommutator e p.left.delta ⊔
        selectedCommutator e p.right.delta := by
  have hc := ExtendedPath.vertex_color e (i := geometry.b R)
    (geometry.even (alpha R) rfl) (by omega)
  have hadj : Adjacent R (e.walk.getVert (geometry.b R))
      (e.walk.getVert (geometry.b R - 1)) := by
    have h := adjacent_symm R (path_adjacent e (geometry.b R - 1) (by omega))
    simpa only [Nat.sub_add_cancel (show 1 ≤ geometry.b R by omega)] using h
  have hU := (terminalProduct_le_backward_edge hb e).trans
    (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
      (LocalCommutator.moduleFacts common) _ _ hc hadj)
  let : Finite (U R (e.walk.getVert (geometry.b R))) :=
    Nat.finite_of_card_ne_zero (by rw [common.natural.card_at _ hc]; decide)
  let : Finite (terminalProduct e) :=
    Finite.of_injective (inclusion hU) (inclusion_injective _)
  exact fill_four_group _ _ _ p.left.commutator_le_product p.right.commutator_le_product
    (p.left.commutator_ne_bot common hb sections) (p.right.commutator_ne_bot common hb sections)
    (selected_disjoint p common hb hprefix) (terminalProduct_card_le_four common hb e)

/-- The order estimate, with only the actual source choices still explicit. -/
theorem selected_card (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c))) :
    Nat.card (terminalProduct e) = 4 :=
  (selected_card_and_product p common hb hprefix sections).1

/-- The two incident-edge bounds place the entire saturated product in
the source natural intersection, without assuming that intersection identity. -/
theorem selected_le_natural_kernel (common : CommonFacts R source geometry)
    (hb : 6 < geometry.b R) (hprefix : LocalCommutator.CriticalPrefixControl R geometry)
    (sections : ∀ c, color R c = false →
      Nonempty (Escape.NaturalSectionAt c (V R c) (Z R c))) :
    terminalProduct e ≤ U R a ⊓ Q R (e.walk.getVert (4 + geometry.b R)) := by
  rw [(selected_card_and_product p common hb hprefix sections).2]
  have hbound (s : SelectedVertex e) : selectedCommutator e s.delta ≤
      U R a ⊓ Q R (e.walk.getVert (4 + geometry.b R)) :=
    (selected_le_edge_inf_kernel s common hb hprefix).trans (inf_le_inf_right _
      (Escape.EdgeTransfer.edge_commutator_le_natural common.large_distance
        (LocalCommutator.moduleFacts common) _ _ (ExtendedPath.center_color e)
        s.adjacent_center))
  exact sup_le (hbound p.left) (hbound p.right)


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44.SourceEarlier.Product
