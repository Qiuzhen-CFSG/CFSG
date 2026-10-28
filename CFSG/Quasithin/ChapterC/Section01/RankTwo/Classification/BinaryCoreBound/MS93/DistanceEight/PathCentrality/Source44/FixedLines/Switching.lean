module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.FixedLines.CommutatorPlane


/-!
# Backward switching with the selected terminal conjugator

The odd edge kernel normalizes the nonzero displacement [Z_d,Q_c]. Its
fixed subgroup in the natural layer is the source line of order two, so
that line lies in the displacement. Moving the line therefore gives the
nonzero triple commutator required by a backward witness.

Replace the final two edges of the old critical path by a shortest path
to the selected terminal vertex. The replacement keeps every earlier
vertex, including the original predecessor. The consumer uses the same
conjugator chosen simultaneously for the line and the Z-product. It
retains the selected index-two image; excluding that case is a separate
source obligation.

Source: Meierfrankenfeld--Stellmacher (1993), (4.4.1), printed p.892,
the penultimate paragraph and its repeated backward configuration.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator LocalCommutator.CriticalCase
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem fixed_line_le_nonzero_invariant
    {G : Type*} [Group G] (U T E : Subgroup G) [Finite U]
    (hU : IsPGroup 2 U) (hT : IsPGroup 2 T)
    (hEU : E ≤ U) (hTE : T ≤ normalizer E) (hne : E ≠ ⊥)
    (hfixed : Nat.card (U ⊓ centralizer (T : Set G) : Subgroup G) = 2) :
    U ⊓ centralizer (T : Set G) ≤ E := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Finite E := Finite.of_injective (inclusion hEU) (inclusion_injective _)
  let : Subgroup.Normalizes T E := ⟨hTE⟩
  have hE : IsPGroup 2 E := hU.of_injective (inclusion hEU) (inclusion_injective _)
  have hdiv : 2 ∣ Nat.card E := hE.card_eq_or_dvd.resolve_left (by
    intro he
    have hh := (one_lt_card_iff_ne_bot E).mpr hne
    omega)
  obtain ⟨x,hx,hxn⟩ := hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point E hdiv
    (show (1 : E) ∈ MulAction.fixedPoints T E by simp)
  have hne' : E ⊓ centralizer (T : Set G) ≠ ⊥ := by
    intro he
    have hm : (x : G) ∈ E ⊓ centralizer (T : Set G) := by
      refine ⟨x.property,?_⟩
      intro t ht
      have hh := congrArg Subtype.val (hx (⟨t,ht⟩ : T))
      change t * (x : G) * t⁻¹ = x at hh
      exact mul_inv_eq_iff_eq_mul.mp hh
    rw [he,mem_bot] at hm
    exact hxn (Subtype.ext hm.symm)
  have hle : E ⊓ centralizer (T : Set G) ≤ U ⊓ centralizer (T : Set G) :=
    inf_le_inf_right _ hEU
  let : Finite (U ⊓ centralizer (T : Set G) : Subgroup G) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  let : Finite (E ⊓ centralizer (T : Set G) : Subgroup G) :=
    Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have he := eq_of_le_of_card_ge hle (by
    rw [hfixed]
    exact (one_lt_card_iff_ne_bot _).mpr hne')
  rw [← he]
  exact inf_le_left

theorem fixed_line_le_displacement (common : CommonFacts R source geometry)
    {d c t : Vertex R} (hd : color R d = false)
    (hdc : (cosetGraph R).dist d c = 2) (hdt : Adjacent R d t) (hct : Adjacent R c t)
    (hcard : Nat.card (edgeFixedNatural (R := R) d t) = 2)
    (hne : ⁅Z R d,Q R c⁆ ≠ ⊥) :
    edgeFixedNatural (R := R) d t ≤ ⁅Z R d,Q R c⁆ := by
  let E := ⁅Z R d,Q R c⁆
  let : Finite (U R d) := Nat.finite_of_card_ne_zero
    (by rw [(naturalStructure common).natural.card_at d hd]; decide)
  let := geometry.U_elementary (by have := common.large_distance; omega) d hd
  have hTgd : Q R t ≤ stabilizer R d := fun _ hx => hx.2 d (adjacent_symm R hdt)
  have hTgc : Q R t ≤ stabilizer R c := fun _ hx => hx.2 c (adjacent_symm R hct)
  have hn : Q R t ≤ normalizer E := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change ⁅Z R d,Q R c⁆.map (MulAut.conj g : FreeAmalgam R →* FreeAmalgam R) = E
    rw [map_commutator,
      mem_normalizer_iff_map_conj_eq.mp ((hTgd.trans (Z_normalized R d)) hg),
      mem_normalizer_iff_map_conj_eq.mp ((hTgc.trans (Q_normalized R c)) hg)]
  exact fixed_line_le_nonzero_invariant (U R d) (Q R t) E
    (IsElementaryAbelian.isPGroup 2 (U R d))
    (Escape.EdgeTransfer.edge_kernel_two source d t hd hdt)
    (displacement_le_U common hd hdc) hn hne hcard

theorem selected_displacement_triple_ne (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {t : Vertex R}
    (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R c)
    (hmove : ¬ Z R n.vertex ≤ normalizer
      (edgeFixedNatural (R := R) (act R g w.backward) (act R g t))) :
    ⁅⁅Z R (act R g w.backward),Q R c⁆,Z R n.vertex⁆ ≠ ⊥ := by
  have hgc : act R g c = c := hg
  have hcol : color R (act R g w.backward) = false :=
    (action_preserves_color R g w.backward).trans (w.backward_color ha)
  have hdist : (cosetGraph R).dist (act R g w.backward) c = 2 := by
    simpa only [hgc] using (dist_act R g w.backward c).trans (w.backward_distance hd)
  have hgt := (adjacent_act_iff R g w.backward t).mpr hdt
  have hcgt : Adjacent R c (act R g t) := by
    simpa only [hgc] using (adjacent_act_iff R g c t).mpr hct
  have hne : ⁅Z R (act R g w.backward),Q R c⁆ ≠ ⊥ := by
    intro he
    have hm : ⁅Z R w.backward,Q R c⁆.map (MulAut.conj g⁻¹).toMonoidHom = ⊥ := by
      rwa [map_commutator,← Z_act,← Q_act,hgc]
    have hz := (map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).mp hm
    exact w.triple_ne (by rw [hz,commutator_bot_left])
  have hF := fixed_line_le_displacement common hcol hdist hgt hcgt
    (fixed_line_card common hb ha hd w n hcol hgt) hne
  intro hz
  apply hmove
  exact le_normalizer_iff_commutator_le_left.mpr
    (((commutator_mono hF le_rfl).trans hz.le).trans bot_le)

theorem terminal_path_retaining_segment (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) :
    ∃ p : CriticalPath R geometry c n.vertex,
      ∀ i ≤ w.path.walk.length - 2, p.walk.getVert i = w.path.walk.getVert i := by
  obtain ⟨v,hv⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist w.predecessor n.vertex
  dsimp only [BackwardWitness.predecessor] at v hv
  have hv2 : v.length = 2 := hv.trans n.distance
  let q := (w.path.walk.take (w.path.walk.length - 2)).append v
  have hlen : q.length = geometry.b R := by
    dsimp only [q]
    rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.take_length,
      inf_eq_left.mpr (Nat.sub_le _ _),hv2,w.path.length_eq_b]
    omega
  have hcrit := n.critical_from_center common hb ha hd
  let p : CriticalPath R geometry c n.vertex := {
    start_color := w.path.start_color
    walk := q
    shortest := hlen.trans (hcrit.1.trans (geometry.distance_constant c w.path.start_color)).symm
    critical := hcrit }
  refine ⟨p,?_⟩
  intro i hi
  change q.getVert i = _
  dsimp only [q]
  rw [SimpleGraph.Walk.getVert_append',SimpleGraph.Walk.take_length,
    inf_eq_left.mpr (Nat.sub_le _ _),if_pos hi,SimpleGraph.Walk.take_getVert,
    inf_eq_right.mpr hi]

theorem switched_backward_witness (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {t : Vertex R}
    (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    {g : FreeAmalgam R} (hg : g ∈ stabilizer R c)
    (hmove : ¬ Z R n.vertex ≤ normalizer
      (edgeFixedNatural (R := R) (act R g w.backward) (act R g t)))
    (hprod : ¬ Z R n.vertex ≤ normalizer
      (Z R (act R g w.backward) ⊔ Z R c : Subgroup (FreeAmalgam R))) :
    ∃ v : BackwardWitness R geometry a c,
      v.endpoint = n.vertex ∧ v.backward = act R g w.backward ∧
      v.conjugator = w.conjugator * g ∧ v.predecessor = w.predecessor ∧
      ∀ i ≤ w.path.walk.length - 2, v.path.walk.getVert i = w.path.walk.getVert i := by
  obtain ⟨p,hp⟩ := terminal_path_retaining_segment common hb ha hd w n
  have hpred : p.walk.getVert (p.walk.length - 2) = w.predecessor := by
    rw [p.length_eq_b,← w.path.length_eq_b]
    exact hp _ le_rfl
  have hgc : act R g c = c := hg
  have hdist : (cosetGraph R).dist (act R g w.backward) c = 2 := by
    simpa only [hgc] using (dist_act R g w.backward c).trans (w.backward_distance hd)
  obtain ⟨q⟩ := terminal_new_critical_pair common hb ha hd w n hdist hprod
  let back := (actWalk R g w.backwardWalk).copy rfl hgc
  let v : BackwardWitness R geometry a c := {
    endpoint := n.vertex
    path := p
    backward := act R g w.backward
    conjugator := w.conjugator * g
    local_conjugator := (stabilizer R c).mul_mem w.local_conjugator hg
    conjugator_image := by rw [act_mul,w.conjugator_image]
    backwardWalk := back
    backward_length := (SimpleGraph.Walk.length_copy _ _ _).trans
      ((actWalk_length R g _).trans w.backward_length)
    noncontainment := by rw [hpred]; exact q.critical.2
    triple_ne := selected_displacement_triple_ne common hb ha hd w n hdt hct hg hmove }
  exact ⟨v,rfl,rfl,rfl,hpred,hp⟩

theorem first_selection_switching (common : CommonFacts R source geometry)
    (hb : 4 < geometry.b R) {a c : Vertex R} (ha : color R a = false)
    (hd : (cosetGraph R).dist a c = 2) (w : BackwardWitness R geometry a c)
    (n : TerminalNeighbor w) {t : Vertex R}
    (hdt : Adjacent R w.backward t) (hct : Adjacent R c t)
    (hnot : ¬ edgeFixedNatural (R := R) w.backward t ≤ fixedCore R c) :
    ∃ g ∈ stabilizer R c, ∃ v : BackwardWitness R geometry a c,
      v.endpoint = n.vertex ∧ v.backward = act R g w.backward ∧
      v.conjugator = w.conjugator * g ∧ v.predecessor = w.predecessor ∧
      (¬ Z R n.vertex ≤ normalizer
        (edgeFixedNatural (R := R) v.backward (act R g t))) ∧
      (¬ Z R n.vertex ≤ normalizer (Z R v.backward ⊔ Z R c : Subgroup (FreeAmalgam R))) ∧
      (Q R w.predecessor).relIndex (Z R v.backward) = 2 ∧
      (∀ i ≤ w.path.walk.length - 2, v.path.walk.getVert i = w.path.walk.getVert i) := by
  obtain ⟨g,hg,hF,hJ,hi⟩ := first_selection_index_two common hb ha hd w n hdt hct hnot
  obtain ⟨v,hv,hb',hg',hp,hs⟩ := switched_backward_witness common hb ha hd w n hdt hct hg hF hJ
  exact ⟨g,hg,v,hv,hb',hg',hp,by rwa [hb'],by rwa [hb'],by rwa [hb'],hs⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
