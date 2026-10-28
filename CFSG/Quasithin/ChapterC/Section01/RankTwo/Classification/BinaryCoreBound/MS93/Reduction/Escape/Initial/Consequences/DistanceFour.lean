module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Consequences.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.RadiusGrowth
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Excluding critical distance four in the initial contrary configuration

At distance four, the earlier nonnormality theorem makes the start a moving
neighbor of the midpoint c. The natural section at c makes [Q_c,Z_a]Z_c
normal in G_c. Thus its conjugates bound [V_a,Z_a^g] by Z_a Z_c, which
centralizes V_a. Moving generation, the incident-edge supplement and the
class-two assertion extend this to [V_a,V_c]. In particular the critical
endpoint acts centrally on V_a. Its normal closure contains the local
residual, so Vcirc_a is central in V_a. The edge supplement is abelian,
forcing V_a to be abelian. Transporting that fact to the midpoint contradicts
the original critical pair's noncommutation.

Source: Meierfrankenfeld--Stellmacher (1993), (3.9), (4.3.1)(v), p.883.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Consequences
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

omit [Finite M] in
private theorem triple_le (a : Vertex R)
    (s : NaturalSectionAt a (V R a) (Z R a)) :
    ⁅⁅V R a, Q R a⁆, Ltilde R a⁆ ≤ Z R a := by
  have h := map_mono (f := (stabilizer R a).subtype) s.module_section.triple_le
  rw [map_commutator, map_commutator,
    map_subgroupOf_eq_of_le s.local_group,
    map_subgroupOf_eq_of_le (show Q R a ≤ stabilizer R a from fun _ hx => hx.1),
    map_subgroupOf_eq_of_le (Z_le_stabilizer R a)] at h
  exact h

private theorem fixed_neighbor_normal (source : LocalSource L R)
    (hb : 2 < geometry.b R) (a d : Vertex R) (ha : color R a = false)
    (had : (cosetGraph R).dist a d = 2)
    (hfixed : Z R d ≤ B R a (geometry.Z_normal a)) :
    ((Z R d ⊔ Z R a).subgroupOf (stabilizer R a)).Normal := by
  have hV : V R a ≤ stabilizer R a := (geometry.V_le_Q hb a ha).trans (fun _ hx => hx.1)
  have hc : ⁅Z R d, Ltilde R a⁆ ≤ Z R a := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl z hz
    exact ((mem_B_iff R a _ hV z).mp (hfixed hz)).2 l hl
  have hL : Ltilde R a ≤ normalizer (Z R a ⊔ Z R d : Subgroup (FreeAmalgam R)) :=
    normalizes_sup_of_commutator_le _ _ _
      ((Ltilde_le_stabilizer a).trans (Z_normalized R a)) hc
  have hQ : Q R a ≤ normalizer (Z R a ⊔ Z R d : Subgroup (FreeAmalgam R)) :=
    (le_inf ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Z_normalized R a))
      ((Q_le_stabilizer_of_dist_two R a d ha had).trans (Z_normalized R d))).trans
        (normalizer_inf_normalizer_le_normalizer_sup _ _)
  apply normal_subgroupOf_of_le_normalizer
  rw [sup_comm, ← source.local_generation a ha]
  exact sup_le hL hQ

/-- Earlier critical-path nonnormality supplies precisely the moving condition
needed in the distance-four argument. -/
theorem start_moving_at_midpoint (source : LocalSource L R)
    (hb : geometry.b R = 4) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry) : p.a ∈ movingNeighbors geometry p.c := by
  have hac : (cosetGraph R).dist p.a p.c = 2 := by
    have h := p.before.2
    rw [p.distance_eq_b, hb] at h
    omega
  refine ⟨by rw [SimpleGraph.dist_comm]; exact hac, ?_⟩
  intro hfixed
  have hn := critical_nonnormal_forward R geometry (source.edgeCentralizerCondition geometry)
    p.a p.color_a (by
      rw [geometry.distance_constant p.a p.color_a]
      change 0 < geometry.b R
      omega)
    p.a' p.critical p.c hac (by rw [p.before.1, p.distance_eq_b, hb])
  rw [modules.X_eq_Z p.c p.before_color] at hn
  exact hn.2 (fixed_neighbor_normal source (by omega) p.c p.a p.before_color
    (by rwa [SimpleGraph.dist_comm]) hfixed)

omit [Finite M] in
/-- The radius at an H-vertex is abelian already for b > 2. -/
theorem edge_radius_commutative (hb : 2 < geometry.b R)
    (a t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t) :
    IsMulCommutative (V R t) := by
  apply le_centralizer_iff_isMulCommutative.mp
  apply V_le_of_h_neighbors ha hat
  intro d hdt
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases h : color R t <;> simp_all
  have hd : color R d = false := by
    have hn := adjacent_color_ne R hdt
    cases h : color R d <;> simp_all
  apply le_centralizer_iff.mpr
  apply V_le_of_h_neighbors ha hat
  intro e het
  have he : color R e = false := by
    have hn := adjacent_color_ne R het
    cases h : color R e <;> simp_all
  have hZe : Z R e ≤ Q R d := by
    apply Z_le_Q_of_dist_lt R e (geometry.exists_critical e he)
    rw [geometry.distance_constant e he]
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr het)
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hdt))
    have htri := (cosetGraph_connected R).dist_triangle (u := e) (v := t) (w := d)
    exact lt_of_le_of_lt (by omega) hb
  exact hZe.trans (le_centralizer_iff.mp
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes d hd)))

/-- The class-two edge term and moving generation together make the entire
midpoint radius act centrally on the starting radius. -/
theorem midpoint_commutator_central (source : LocalSource L R)
    (hb : geometry.b R = 4) (modules : ModuleFacts source geometry)
    (p : Counterexample geometry)
    (hsections : ∀ q : Counterexample geometry, Nonempty (SectionFacts q)) :
    ⁅V R p.a, V R p.c⁆ ≤ centralizer (V R p.a : Set (FreeAmalgam R)) := by
  have hlarge : 2 < geometry.b R := by omega
  have hac : (cosetGraph R).dist p.a p.c = 2 := by
    have h := p.before.2
    rw [p.distance_eq_b, hb] at h
    omega
  have hZa : Z R p.a ≤ V R p.c := le_iSup_of_le p.a (le_iSup_of_le hac.le le_rfl)
  obtain ⟨s⟩ := natural_section_at p hsections p.c p.before_color
  let D := ⁅Q R p.c, Z R p.a⁆
  let K := Z R p.c ⊔ D
  let C := centralizer (V R p.a : Set (FreeAmalgam R))
  have hDL : ⁅D, Ltilde R p.c⁆ ≤ Z R p.c := by
    have hD : D ≤ ⁅V R p.c, Q R p.c⁆ := by
      change ⁅Q R p.c, Z R p.a⁆ ≤ _
      rw [commutator_comm]
      exact commutator_mono hZa le_rfl
    exact (commutator_mono hD le_rfl).trans (triple_le p.c s)
  have hnormK : stabilizer R p.c ≤ normalizer (K : Set (FreeAmalgam R)) := by
    rw [← source.local_generation p.c p.before_color]
    apply sup_le
    · exact normalizes_sup_of_commutator_le _ _ _
        ((Ltilde_le_stabilizer p.c).trans (Z_normalized R p.c)) hDL
    · exact (le_inf
        ((show Q R p.c ≤ stabilizer R p.c from fun _ hx => hx.1).trans (Z_normalized R p.c))
        (normalizer_commutator_ge_left (Q R p.c) (Z R p.a))).trans
          (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hDZa : D ≤ Z R p.a := le_normalizer_iff_commutator_le_right.mp
    ((Q_le_stabilizer_of_dist_two R p.c p.a p.before_color (by rwa [SimpleGraph.dist_comm])).trans
      (Z_normalized R p.a))
  have hKC : K ≤ C := sup_le
    ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes p.c p.before_color)).trans
      (centralizer_le p.trapped))
    (hDZa.trans ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes p.a p.color_a)).trans
      (centralizer_le (geometry.V_le_Q hlarge p.a p.color_a))))
  have hVcG : V R p.c ≤ stabilizer R p.a := V_le_stabilizer_of_distance p.before_color (by
    rw [SimpleGraph.dist_comm, hac, hb])
  have hGC : stabilizer R p.a ≤ normalizer (C : Set (FreeAmalgam R)) :=
    (V_normalized p.a).trans (normalizer_le_normalizer_centralizer (V R p.a))
  let P := commutatorPreimage (stabilizer R p.a) (V R p.a) C
  have hconj : NormalizerTransfer.conjugatesIn (Z R p.a) (stabilizer R p.c) ≤ P := by
    apply iSup_le
    intro g
    have hfix : act R (g : FreeAmalgam R) p.c = p.c := g.property
    have hZg : Z R (act R (g : FreeAmalgam R) p.a) ≤ V R p.c := by
      have h := map_mono (f := (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom) hZa
      rwa [← Z_act, ← V_act, hfix] at h
    change (Z R p.a).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom ≤ P
    rw [← Z_act]
    apply le_commutatorPreimage (hZg.trans hVcG)
    rw [commutator_comm]
    have hm : ⁅Q R p.c, Z R (act R (g : FreeAmalgam R) p.a)⁆ ≤ K := by
      have h := map_mono (f := (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom)
        (show D ≤ K from le_sup_right)
      dsimp only [D] at h
      rw [map_commutator, ← Q_act, ← Z_act, hfix] at h
      exact h.trans (mem_normalizer_iff_map_conj_eq.mp
        (hnormK ((stabilizer R p.c).inv_mem g.property))).le
    exact (commutator_mono p.trapped le_rfl).trans (hm.trans hKC)
  have hmov : Vcirc R p.c ≤ P := (moving_generation_at p hsections p.c p.before_color
    p.a (start_moving_at_midpoint source hb modules p)).trans hconj
  obtain ⟨t, hat, hct⟩ := exists_common_neighbor_of_dist_two R p.a p.c hac
  have hVt : V R t ≤ V R p.a := edge_radius_le_radius p.color_a hat
  have htP : V R t ≤ P := by
    apply le_commutatorPreimage (hVt.trans
      ((geometry.V_le_Q hlarge p.a p.color_a).trans (fun _ hx => hx.1)))
    exact (commutator_mono hVt le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mp (modules.b_four_class_two hb p.a p.color_a))
  have hVcP : V R p.c ≤ P := by
    rw [radius_eq_moving_sup_edge source p.before_color hct]
    exact sup_le hmov htP
  rw [commutator_comm]
  exact (commutator_mono hVcP le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hGC)

private theorem local_residual_le_closure (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false)
    (A : Subgroup (FreeAmalgam R)) (hA : A ≤ stabilizer R a) (hout : ¬ A ≤ Q R a) :
    Ltilde R a ≤ NormalizerTransfer.conjugatesIn A (stabilizer R a) := by
  let S := stabilizer R a
  let N := NormalizerTransfer.conjugatesIn A S
  let N₀ := N.subgroupOf S
  let Q₀ := (Q R a).subgroupOf S
  have hNS : N ≤ S := NormalizerTransfer.conjugatesIn_le _ _ hA
  have hQS : Q R a ≤ S := fun _ hx => hx.1
  let : N₀.Normal := normal_subgroupOf_of_le_normalizer
    (NormalizerTransfer.conjugatesIn_normalized A S)
  have hgen : N₀ ⊔ Q₀ = ⊤ := by
    apply map_injective S.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hNS, map_subgroupOf_eq_of_le hQS,
      ← MonoidHom.range_eq_map, range_subtype]
    exact local_conjugate_generation source a ha A hA hout
  let : Finite S := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective (inclusion hQS) (inclusion_injective _)
  have hQ : IsPGroup 2 (Q R a) := by
    rw [IsPGroup.iff_card, source.Q_card a ha]
    exact pCore_isPGroup.exists_card_eq
  have hres : pResidual 2 S ≤ N₀ :=
    sInf_le ⟨inferInstance, isPGroup_quotient_of_sup_eq_top N₀ Q₀ hQ.comap_subtype hgen⟩
  have h := map_mono (f := S.subtype) hres
  rwa [map_subgroupOf_eq_of_le hNS] at h

private theorem moving_central_of_critical_central (source : LocalSource L R)
    (p : Counterexample geometry)
    (hc : radiusCommutator p.a p.a' ≤ centralizer (V R p.a : Set (FreeAmalgam R))) :
    Vcirc R p.a ≤ centralizer (V R p.a : Set (FreeAmalgam R)) := by
  let S := stabilizer R p.a
  let C := centralizer (V R p.a : Set (FreeAmalgam R))
  have hSC : S ≤ normalizer (C : Set (FreeAmalgam R)) :=
    (V_normalized p.a).trans (normalizer_le_normalizer_centralizer (V R p.a))
  have hgen := local_residual_le_closure source p.a p.color_a (Z R p.a')
    p.end_Z_le_start_stabilizer
    (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
  have hN : NormalizerTransfer.conjugatesIn (Z R p.a') S ≤
      commutatorPreimage S (V R p.a) C := by
    apply iSup_le
    intro g
    have hV := mem_normalizer_iff_map_conj_eq.mp (V_normalized p.a (S.inv_mem g.property))
    have hC := mem_normalizer_iff_map_conj_eq.mp (hSC (S.inv_mem g.property))
    change (V R p.a).map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom = V R p.a at hV
    change C.map (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom = C at hC
    apply le_commutatorPreimage
    · exact (map_mono p.end_Z_le_start_stabilizer).trans
        (mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer (S.inv_mem g.property))).le
    · have h := map_mono (f := (MulAut.conj (g : FreeAmalgam R)⁻¹).toMonoidHom) hc
      rw [radiusCommutator, map_commutator, hV, hC, commutator_comm] at h
      exact h
  change ⁅V R p.a, Ltilde R p.a⁆ ≤ C
  rw [commutator_comm]
  exact (commutator_mono (hgen.trans hN) le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _ hSC)

private theorem radius_commutative_of_moving_central (source : LocalSource L R)
    (hb : 2 < geometry.b R) (a t : Vertex R)
    (ha : color R a = false) (hat : Adjacent R a t)
    (hc : Vcirc R a ≤ centralizer (V R a : Set (FreeAmalgam R))) :
    IsMulCommutative (V R a) := by
  have hVt := edge_radius_le_radius ha hat
  have ht := le_centralizer_iff_isMulCommutative.mpr (edge_radius_commutative hb a t ha hat)
  apply le_centralizer_iff_isMulCommutative.mp
  rw [radius_eq_moving_sup_edge source ha hat]
  apply sup_le
  · rw [← radius_eq_moving_sup_edge source ha hat]
    exact hc
  · apply le_centralizer_iff.mpr
    apply sup_le (hc.trans (centralizer_le hVt)) ht

/-- Unlike the later distance-four escape lemma, this contradiction uses only
critical noncommutation at the actual midpoint, with explicit transport. -/
theorem radius_not_commutative_at_four (source : LocalSource L R)
    (hb : geometry.b R = 4) (p : Counterexample geometry) :
    ¬ IsMulCommutative (V R p.a) := by
  intro hcomm
  obtain ⟨g, hg⟩ := exists_mVertex_of_color R p.color_a
  obtain ⟨h, hh⟩ := exists_mVertex_of_color R p.before_color
  have hmove : act R (g⁻¹ * h) p.a = p.c := by
    rw [hg, act_mVertex, mul_inv_cancel_left, ← hh]
  have hVc : IsMulCommutative (V R p.c) := by
    rw [← hmove, V_act]
    let := hcomm
    infer_instance
  have hZa : Z R p.a ≤ V R p.c := by
    apply le_iSup_of_le p.a
    apply le_iSup_of_le (show (cosetGraph R).dist p.a p.c ≤ 2 from ?_)
    · exact le_rfl
    · have h := p.before.2
      rw [p.distance_eq_b, hb] at h
      omega
  have hZa' : Z R p.a' ≤ V R p.c := le_iSup_of_le p.a' (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm, p.before.1]) le_rfl)
  exact source.critical_noncommutation geometry p.a p.color_a p.critical
    (commutator_eq_bot_iff_le_centralizer.mpr (hZa.trans
      ((le_centralizer_iff_isMulCommutative.mpr hVc).trans (centralizer_le hZa'))))

/-- Source (4.3.1)(v): the contrary configuration cannot have distance four. -/
theorem distance_ne_four (source : LocalSource L R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry)
    (hsections : ∀ q : Counterexample geometry, Nonempty (SectionFacts q)) :
    geometry.b R ≠ 4 := by
  intro hb
  have hZ : Z R p.a' ≤ V R p.c := le_iSup_of_le p.a' (le_iSup_of_le
    (by rw [SimpleGraph.dist_comm, p.before.1]) le_rfl)
  have hc : radiusCommutator p.a p.a' ≤ centralizer (V R p.a : Set (FreeAmalgam R)) :=
    (commutator_mono le_rfl hZ).trans (midpoint_commutator_central source hb modules p hsections)
  obtain ⟨u, hau, _⟩ := exists_common_neighbor_of_dist_two R p.a p.c (by
    have h := p.before.2
    rw [p.distance_eq_b, hb] at h
    omega)
  exact radius_not_commutative_at_four source hb p
    (radius_commutative_of_moving_central source (by omega) p.a u p.color_a hau
      (moving_central_of_critical_central source p hc))

/-- Even critical distance, b > 2, and the distance-four exclusion give (v). -/
theorem six_le (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (p : Counterexample geometry)
    (hsections : ∀ q : Counterexample geometry, Nonempty (SectionFacts q)) :
    6 ≤ geometry.b R := by
  have hne := distance_ne_four source modules p hsections
  have heven := geometry.even p.a p.color_a
  rw [geometry.distance_constant p.a p.color_a] at heven
  change Even (geometry.b R) at heven
  rw [Nat.even_iff] at heven
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Initial.Consequences
