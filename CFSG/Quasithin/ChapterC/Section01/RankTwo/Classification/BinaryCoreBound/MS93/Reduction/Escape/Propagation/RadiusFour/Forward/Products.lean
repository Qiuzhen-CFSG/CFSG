module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Forward.Stages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Moving.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Endpoint
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.RadiusFour.Ball
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Residual
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FaithfulSection

/-!
# The moving products and the radius-four join in MS93 (4.3.8)

The critical endpoint moves at its second predecessor: otherwise its normal
Z-product can be conjugated toward the starting vertex and put in its kernel.
Part (4.3.7)(i) then normalizes the moving product, so the actual first local
conjugator preserves that product. The same normal-product geometry puts the
endpoint radius group in the kernel two steps from the starting vertex.

To prove the printed noncontainment, suppose the endpoint moving group lies
in Vcirc_c Q_alpha. Since Q_alpha centralizes Z_alpha and H_c = R_0 lies in
Z_alpha', its commutator with Z_alpha lies in Z_alpha'. Faithfulness of the
natural section at alpha' would put Z_alpha in Q_alpha', contradicting
criticality. The product equality transfers this to the first conjugate mu.

Both moving groups lie in the radius-four ball at d = alpha'-4. The first
has nontrivial image modulo Q_alpha, and the second is outside that image.
The literal edge index is four, so these two strict inclusions generate all
of Q_beta/Q_alpha. Distance estimates supply the other inclusion of the join.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), printed p.889, the second and third paragraphs. Only the preceding
stages are used. The separate commutation and normalization-transfer premises
are unnecessary for these product deductions.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Forward.Products
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- A nonmoving endpoint would give a normal Z-product at its second
predecessor, forcing the critical endpoint Z-layer into the starting kernel. -/
theorem endpoint_moving (source : LocalSource L R) (hb : 2 < geometry.b R)
    (p : Counterexample geometry) : p.a' ∈ movingNeighbors geometry p.c := by
  by_contra hn
  have hnormal := Backward.Moving.nonmoving_Z_join_normalized source hb
    p.before_color p.before.1 hn
  obtain ⟨s, hs⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  obtain ⟨t, ht⟩ := p.exists_before (show 3 ≤ geometry.b R by omega)
  have hcs := p.before.adjacent (geometry := geometry) hs
  have hct := adjacent_symm R (ht.adjacent (geometry := geometry) p.before)
  obtain ⟨g, hg, hgs⟩ := stabilizer_transitive_neighbors R p.c hcs hct
  have hgc : act R g p.c = p.c := hg
  have heq := mem_normalizer_iff_map_conj_eq.mp
    (hnormal ((stabilizer R p.c).inv_mem hg))
  change (Z R p.c ⊔ Z R p.a').map (MulAut.conj g⁻¹).toMonoidHom = _ at heq
  rw [Subgroup.map_sup, ← Z_act, ← Z_act, hgc] at heq
  have hgt : Adjacent R (act R g p.a') t := by
    rw [← hgs]
    exact (adjacent_act_iff R g _ _).mpr hs.endpoint_adjacent
  have hcolor : color R (act R g p.a') = false := by
    rw [action_preserves_color, p.end_color]
  have hbound : Z R (act R g p.a') ≤ Q R p.a := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ hcolor)
    rw [geometry.distance_constant _ hcolor]
    change (cosetGraph R).dist (act R g p.a') p.a < geometry.b R
    have hd := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hgt)
    have hp := ht.2
    rw [p.distance_eq_b, SimpleGraph.dist_comm (u := p.a) (v := t)] at hp
    have htri := (cosetGraph_connected R).dist_triangle
      (u := act R g p.a') (v := t) (w := p.a)
    omega
  have hcQ : Z R p.c ≤ Q R p.a := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ p.before_color)
    rw [geometry.distance_constant _ p.before_color]
    change (cosetGraph R).dist p.c p.a < geometry.b R
    have hp := p.before.2
    rw [p.distance_eq_b, SimpleGraph.dist_comm (u := p.a) (v := p.c)] at hp
    omega
  exact (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
    (le_sup_right.trans (heq ▸ sup_le hcQ hbound))

/-- The printed moving-product equality uses the specified first
conjugator in G_c, with normality relative to that actual stabilizer. -/
theorem moving_product_eq (source : LocalSource L R) (hb : 2 < geometry.b R)
    (backward : BackwardFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ : Vertex R} (w : CentralOrbitWitnesses p d t₃ t₅) :
    Vcirc R w.mu ⊔ Vcirc R p.c = Vcirc R p.a' ⊔ Vcirc R p.c := by
  obtain ⟨q, hq⟩ := counterexample_at_vertex p (by omega) p.c p.before_color
  have hm := (backward.moving_symmetric q p.a').mp
    (show p.a' ∈ movingNeighbors geometry q.a by
      simpa only [hq] using endpoint_moving source hb p)
  have hp := backward.product_normal q p.a' (by simpa only [hq] using p.before.1) hm
  rw [hq] at hp
  obtain ⟨t, ht⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  have hn := PairingControl.Geometry.LocalProducts.moving_product_normal_of_residual source
    p.before_color (p.before.adjacent (geometry := geometry) ht) ht.endpoint_adjacent hp.2.2
  have hlocal : Vcirc R p.c ⊔ Vcirc R p.a' ≤ stabilizer R p.c :=
    (sup_le_sup (PairingControl.Geometry.Vcirc_le_V _) (PairingControl.Geometry.Vcirc_le_V _)).trans
      ((sup_comm _ _).trans_le hp.1)
  have hnorm := (normal_subgroupOf_iff_le_normalizer hlocal).mp hn
  have heq := mem_normalizer_iff_map_conj_eq.mp
    (hnorm ((stabilizer R p.c).inv_mem w.first_local))
  change (Vcirc R p.c ⊔ Vcirc R p.a').map
    (MulAut.conj w.first_conjugator⁻¹).toMonoidHom = _ at heq
  have hfix : act R w.first_conjugator p.c = p.c := w.first_local
  rw [Subgroup.map_sup, ← Vcirc_act, ← Vcirc_act, hfix, w.first_image] at heq
  simpa only [sup_comm] using heq

/-- Every generator of the radius-four ball is strictly closer than b
to the first path edge, and hence lies in that edge kernel. -/
theorem radius_join_le (hb : 4 < geometry.b R) (p : Counterexample geometry) {d t : Vertex R}
    (hd : Before p.a p.a' d 4) (ht : Before p.a' p.a t 1) :
    VBall R d 4 ⊔ Q R p.a ≤ Q R t := by
  have hcol : color R d = false := (hd.color (by decide)).trans p.end_color
  have ht' : Before p.a p.a' t (geometry.b R - 1) := by
    have hh := PairingControl.Geometry.before_reverse ht
    rwa [SimpleGraph.dist_comm (u := p.a') (v := p.a), p.distance_eq_b] at hh
  have hdt := Backward.before_dist (geometry := geometry) ht' hd (by omega : 4 ≤ geometry.b R - 1)
  have htcol : color R t = true := by
    have hh := adjacent_color_ne R ht.endpoint_adjacent
    cases hc : color R t <;> simp_all [p.color_a]
  apply sup_le _ (Q_le_adjacent_h R htcol ht.endpoint_adjacent)
  apply (VBall_le_iff hcol _).mpr
  intro x hx hxd
  apply Z_le_Q_of_dist_lt R x (geometry.exists_critical x hx)
  rw [geometry.distance_constant x hx]
  change (cosetGraph R).dist x t < geometry.b R
  have htri := (cosetGraph_connected R).dist_triangle (u := x) (v := d) (w := t)
  rw [SimpleGraph.dist_comm (u := t) (v := d)] at hdt
  omega

/-- The full endpoint radius group lies in the kernel two steps from the
starting vertex, by the normal product at the other end of the path. -/
theorem endpoint_radius_le_forward_kernel (source : LocalSource L R)
    (hb : 4 < geometry.b R) (backward : BackwardFacts geometry)
    (p : Counterexample geometry) {s : Vertex R} (hs : Before p.a' p.a s 2) :
    V R p.a' ≤ Q R s := by
  obtain ⟨q, hq⟩ := counterexample_at_vertex p (by omega) p.c p.before_color
  have hm := (backward.moving_symmetric q p.a').mp
    (show p.a' ∈ movingNeighbors geometry q.a by
      simpa only [hq] using endpoint_moving source (by omega) p)
  have hp := backward.product_normal q p.a' (by simpa only [hq] using p.before.1) hm
  rw [hq] at hp
  have hs' : Before p.a p.a' s (geometry.b R - 2) := by
    have hh := PairingControl.Geometry.before_reverse hs
    rwa [SimpleGraph.dist_comm (u := p.a') (v := p.a), p.distance_eq_b] at hh
  have hdist := Backward.before_dist (geometry := geometry) hs' p.before (by omega)
  apply le_sup_left.trans (normal_product_le_Q p.before_color hb p.before.1 hp.1 hp.2.1 ?_)
  rw [SimpleGraph.dist_comm (u := p.c) (v := s), hdist]
  omega

omit [Finite M] in
/-- Both the earlier moving subgroup and the first conjugate moving
subgroup occur in the radius-four ball, with their actual vertices. -/
theorem moving_groups_le_ball (p : Counterexample geometry)
    {d t₃ t₅ : Vertex R} (hd : Before p.a p.a' d 4)
    (h₃ : Before p.a p.a' t₃ 3) (w : CentralOrbitWitnesses p d t₃ t₅) :
    Vcirc R p.c ≤ VBall R d 4 ∧ Vcirc R w.mu ≤ VBall R d 4 := by
  have hdc := Backward.before_dist (geometry := geometry) hd p.before (by decide)
  have hmu₃ := SimpleGraph.dist_eq_one_iff_adj.mpr
    ((cosetGraph_adj R _ _).mpr w.first_adjacent)
  have hd₃ := SimpleGraph.dist_eq_one_iff_adj.mpr
    ((cosetGraph_adj R _ _).mpr (hd.adjacent (geometry := geometry) h₃))
  have htri := (cosetGraph_connected R).dist_triangle (u := w.mu) (v := t₃) (w := d)
  rw [SimpleGraph.dist_comm (u := t₃) (v := d), hd₃, hmu₃] at htri
  constructor
  · exact (PairingControl.Geometry.Vcirc_le_V _).trans
      (VBall_le_of_dist_add_le d p.c 2 4 (by
        rw [SimpleGraph.dist_comm (u := p.c) (v := d), hdc]))
  · exact (PairingControl.Geometry.Vcirc_le_V _).trans
      (VBall_le_of_dist_add_le d w.mu 2 4 (by omega))

/-- The radius-four join is already strictly larger than Q_alpha, using
critical reversal at the original endpoint. -/
theorem radius_join_ne_kernel (source : LocalSource L R)
    (p : Counterexample geometry) {d : Vertex R} (hd : Before p.a p.a' d 4) :
    VBall R d 4 ⊔ Q R p.a ≠ Q R p.a := by
  intro heq
  apply (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
  have hZ : Z R p.a' ≤ VBall R d 4 := le_iSup_of_le p.a'
    (le_iSup_of_le (show (cosetGraph R).dist p.a' d ≤ 4 by
      rw [SimpleGraph.dist_comm, hd.1]) le_rfl)
  exact hZ.trans (heq ▸ le_sup_left)

/-- An index-four interval has no three strict inclusions. This uses
literal relative indices, with no quotient identification implicit. -/
private theorem eq_of_index_four_chain {G : Type*} [Group G]
    (N J K T : Subgroup G) (hNJ : N < J) (hJK : J < K) (hKT : K ≤ T)
    (hindex : N.relIndex T = 4) : K = T := by
  have h₁ := relIndex_mul_relIndex N J T hNJ.le (hJK.le.trans hKT)
  have h₂ := relIndex_mul_relIndex J K T hJK.le hKT
  rw [hindex, ← h₂] at h₁
  have hNJne : N.relIndex J ≠ 1 := fun h => hNJ.not_ge (relIndex_eq_one.mp h)
  have hJKne : J.relIndex K ≠ 1 := fun h => hJK.not_ge (relIndex_eq_one.mp h)
  have hNJpos : 0 < N.relIndex J := by nlinarith
  have hJKpos : 0 < J.relIndex K := by
    by_contra hn
    have hz : J.relIndex K = 0 := by omega
    rw [hz, zero_mul, mul_zero] at h₁
    contradiction
  have hKTpos : 0 < K.relIndex T := by
    by_contra hn
    have hz : K.relIndex T = 0 := by omega
    rw [hz, mul_zero, mul_zero] at h₁
    contradiction
  have hNJtwo : 2 ≤ N.relIndex J := by omega
  have hJKtwo : 2 ≤ J.relIndex K := by omega
  have hprod : 4 ≤ N.relIndex J * J.relIndex K := by nlinarith
  have hKTone : K.relIndex T = 1 := by
    rw [← mul_assoc] at h₁
    nlinarith
  exact le_antisymm hKT (relIndex_eq_one.mp hKTone)

/-- The moving group at the critical endpoint escapes the product of the
predecessor moving group with the starting kernel. Faithfulness of its actual
natural section detects the critical action of Z_alpha. -/
theorem endpoint_moving_not_le_product (source : LocalSource L R)
    (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (p : Counterexample geometry) :
    ¬ Vcirc R p.a' ≤ Vcirc R p.c ⊔ Q R p.a := by
  obtain ⟨hi⟩ := initial p
  obtain ⟨t, ht⟩ := p.exists_before (show 1 ≤ geometry.b R by omega)
  have hm := endpoint_moving source hb p
  have hH : H R p.c = radiusCommutator p.a p.a' :=
    (moving_edge_eq_at p (by omega) control p.c t p.a' p.before_color
      (p.before.adjacent (geometry := geometry) ht) ht.endpoint_adjacent hm).2.trans
      (hi.radius_eq_edge t ht).symm
  have hBlocal : Vcirc R p.c ≤ stabilizer R p.a := by
    apply (PairingControl.Geometry.Vcirc_le_V _).trans
    apply PairingControl.Geometry.V_le_stabilizer_of_distance p.before_color
    rw [SimpleGraph.dist_comm]
    have hp := p.before.2
    rw [p.distance_eq_b] at hp
    exact hp.le
  have hcomm : ⁅Z R p.a, Vcirc R p.c ⊔ Q R p.a⁆ = ⁅Z R p.a, Vcirc R p.c⁆ :=
    (commutator_eq_of_centralizing_sup (sup_comm _ _)
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes p.a p.color_a)))
      (hBlocal.trans (Z_normalized R p.a))).symm
  intro hle
  have hbound : ⁅Vcirc R p.a', Z R p.a⁆ ≤ Z R p.a' := by
    rw [commutator_comm]
    apply (commutator_mono le_rfl hle).trans
    rw [hcomm, commutator_comm]
    apply (commutator_mono le_rfl ((Z_le_VBall R p.a 2).trans p.trapped)).trans
    change H R p.c ≤ Z R p.a'
    rw [hH]
    exact p.radius_le_end
  obtain ⟨q, hq⟩ := counterexample_at_vertex p (by omega) p.a' p.end_color
  obtain ⟨hqi⟩ := initial q
  have hsection : NaturalSectionAt p.a' (V R p.a') (Z R p.a') := by
    simpa only [hq] using hqi.natural_section
  exact p.critical.2 (PairingControl.actor_le_Q source p.end_color hsection (Z R p.a)
    (source.critical_Z_le_stabilizer geometry p.a p.color_a p.a' p.critical).1 hbound)

/-- The literal printed noncontainment, transported through the actual
first conjugator by the moving-product equality. -/
theorem first_moving_not_le_product (source : LocalSource L R)
    (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (backward : BackwardFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ : Vertex R} (w : CentralOrbitWitnesses p d t₃ t₅) :
    ¬ Vcirc R w.mu ≤ Vcirc R p.c ⊔ Q R p.a := by
  intro hle
  apply endpoint_moving_not_le_product source hb initial control p
  have hprod : Vcirc R w.mu ⊔ Vcirc R p.c ≤ Vcirc R p.c ⊔ Q R p.a :=
    sup_le hle le_sup_left
  rw [moving_product_eq source hb backward p w] at hprod
  exact le_sup_left.trans hprod

/-- The first output of ProductFacts follows from the stronger printed
moving-subgroup noncontainment. -/
theorem first_not_le (source : LocalSource L R) (hb : 2 < geometry.b R)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (backward : BackwardFacts geometry) (p : Counterexample geometry)
    {d t₃ t₅ : Vertex R} (w : CentralOrbitWitnesses p d t₃ t₅) :
    ¬ V R w.mu ≤ Q R p.a := by
  intro hle
  exact first_moving_not_le_product source hb initial control backward p w
    ((PairingControl.Geometry.Vcirc_le_V _).trans (hle.trans le_sup_right))

/-- Both inclusions of the literal radius-four join. Its image has order
four because it properly contains the nontrivial image of Vcirc_c. -/
theorem radius_join (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (edge : EdgeTransfer geometry) (rigidity : RigidityFacts geometry)
    (backward : BackwardFacts geometry) (p : Counterexample geometry)
    {d t : Vertex R} (hd : Before p.a p.a' d 4) (ht : Before p.a' p.a t 1) :
    VBall R d 4 ⊔ Q R p.a = Q R t := by
  have hlarge := rigidity.six_lt p
  obtain ⟨t₃, h₃⟩ := p.exists_before (show 3 ≤ geometry.b R by omega)
  obtain ⟨t₅, h₅⟩ := p.exists_before (show 5 ≤ geometry.b R by omega)
  obtain ⟨w⟩ := central_orbit_witnesses source hb modules initial control edge backward p d t₃ t₅ hd h₃ h₅
  have hgroups := moving_groups_le_ball p hd h₃ w
  apply eq_of_index_four_chain (Q R p.a) (Vcirc R p.c ⊔ Q R p.a)
    (VBall R d 4 ⊔ Q R p.a) (Q R t)
  · exact lt_of_le_not_ge le_sup_right (fun h =>
      PairingControl.Geometry.LocalProducts.endpoint_moving_not_le source p hlarge
        (le_sup_left.trans h))
  · exact lt_of_le_not_ge (sup_le_sup hgroups.1 le_rfl) (fun h =>
      first_moving_not_le_product source hb initial control backward p w
        (hgroups.2.trans (le_sup_left.trans h)))
  · exact radius_join_le (by omega) p hd ht
  · exact (edge_indices hb modules p initial control edge p.a t p.color_a ht.endpoint_adjacent).2

/-- The source product deductions, independent of the separate radius-four
commutation argument. -/
theorem productFacts (source : LocalSource L R) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (edge : EdgeTransfer geometry) (rigidity : RigidityFacts geometry)
    (backward : BackwardFacts geometry) : Forward.ProductFacts geometry where
  first_not_le p _ _ _ _ _ _ w := first_not_le source hb initial control backward p w
  radius_join p _ hd _ ht := radius_join source hb modules initial control edge rigidity backward p hd ht

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.RadiusFour.Forward.Products
