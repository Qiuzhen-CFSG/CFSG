module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Control
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Stages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.LocalProducts.Endpoint
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.FaithfulSection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Initial.Edges
public import Theory.GroupTheory.Commutator.NormalizedIndexTwo

/-!
# The critical-commutator contradiction in MS93 (4.3.6)

Noncentrality at the vertex d four before the endpoint identifies R₀ with an
edge displacement in its natural eight-group. The reverse-moving span W(t)
centralizes this plane, so its action on the quotient of order two is trivial:
[Z_d,W(t)] ≤ R₀. This avoids an additional edge identification in the printed
proof, while proving its exact required commutator containment.

If W(t) is not contained in Q_d, critical minimality selects a reverse-moving
generator V_e and a new critical pair (f,d). The edge supplement for V_e puts
[Z_f,Z_d] in H_e, which is the displacement at the chosen starting edge.
Faithfulness of the supplied natural section gives R₀ ∩ Z_a = R. The nontrivial
new critical commutator is therefore R itself. Local generation would then
normalize the starting edge displacement in G_a, contradicting its index two
in the natural group. This proves the W(t) clause without assuming movement
of d at c, product normality, moving symmetry or subsequent escape results.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.3.6), printed pp.886--887.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : Geometry R}

private theorem four_index_in_eight {G : Type*} [Group G]
    (A U : Subgroup G) (hAU : A ≤ U) (hA : Nat.card A = 4) (hU : Nat.card U = 8) :
    A.relIndex U = 2 := by
  have hh := (A.subgroupOf U).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hAU).toEquiv, hA, hU] at hh
  change 4 * A.relIndex U = 8 at hh
  omega

/-- A centralized plane contains every displacement of the natural eight. -/
theorem natural_plane_commutator_le (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry) (a : Vertex R) (ha : color R a = false)
    (A W : Subgroup (FreeAmalgam R)) (hAU : A ≤ U R a) (hA : Nat.card A = 4)
    (hW : W ≤ stabilizer R a) (hWA : W ≤ centralizer (A : Set (FreeAmalgam R))) :
    ⁅Z R a, W⁆ ≤ A := by
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  have hAW := commutator_le_of_normalized_index_two _ _ _ hAU
    (four_index_in_eight _ _ hAU hA (modules.natural.card_at a ha))
    (hW.trans (U_normalized a)) (hWA.trans (Subgroup.centralizer_le_normalizer _))
  have hZA : Z R a ≤ centralizer (A : Set (FreeAmalgam R)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha)).trans
      (centralizer_le (hAU.trans ((U_le_Z a).trans
        ((Z_le_VBall R a 2).trans (geometry.V_le_Q hb a ha)))))
  have hp : Z R a ≤ commutatorPreimage (Z R a) W A := by
    conv_lhs => rw [s.decomposition_at a ha]
    apply sup_le (le_commutatorPreimage (U_le_Z a) hAW)
    exact le_commutatorPreimage inf_le_left
      ((commutator_eq_bot_iff_le_centralizer.mpr
        (inf_le_right.trans (centralizer_le hW))).le.trans bot_le)
  exact (commutator_mono hp le_rfl).trans
    (commutator_commutatorPreimage_le _ _ _
      (hZA.trans (Subgroup.centralizer_le_normalizer _)))

/-- Noncentrality identifies a plane at d, and this plane controls W(t). -/
theorem noncentral_backward_commutator_le (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry) (initial : InitialFacts p)
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (d t : Vertex R)
    (hd : Before p.a p.a' d 4)
    (hn : ¬ radiusCommutator p.a p.a' ≤ localCenter d) :
    ⁅Z R d, backwardSpan geometry p.a t⁆ ≤ radiusCommutator p.a p.a' := by
  obtain ⟨s, hs⟩ := p.exists_before (show 3 ≤ geometry.b R by omega)
  obtain ⟨g, hg, hgs, hZ, hR, hRd⟩ :=
    noncentral_backward_edge source p hb modules initial control edge rigidity d s hd hs hn
  have hdcol : color R d = false := (hd.color (by decide)).trans p.end_color
  have hRU : radiusCommutator p.a p.a' ≤ U R d := by
    rw [hRd]
    exact Initial.edge_le_natural source d s hdcol (hd.adjacent (geometry := geometry) hs)
  have hW : backwardSpan geometry p.a t ≤ stabilizer R d := by
    apply iSup_le
    intro e
    apply iSup_le
    intro _
    apply iSup_le
    intro he
    have hecol : color R e = false :=
      (color_eq_of_dist_even R e p.a (he.1.symm ▸ (by decide : Even 2))).trans p.color_a
    apply PairingControl.Geometry.V_le_stabilizer_of_distance hecol
    have hh := (cosetGraph_connected R).dist_triangle (u := e) (v := p.a) (w := d)
    have hh' := hd.2
    rw [p.distance_eq_b] at hh'
    rw [he.1] at hh
    omega
  apply natural_plane_commutator_le source hb modules d hdcol _ _ hRU initial.radius_card hW
  rw [← commutator_eq_bot_iff_le_centralizer, commutator_comm]
  exact radius_commutes_backwardSpan p (rigidity.six_lt p) t

/-- Faithfulness of the actual natural section excludes R₀ ≤ Z_a. -/
theorem radius_not_le_start_Z (source : LocalSource L R)
    (p : Counterexample geometry) (initial : InitialFacts p) :
    ¬ radiusCommutator p.a p.a' ≤ Z R p.a := by
  intro h
  apply (source.critical_reverse geometry p.a p.color_a p.a' p.end_color p.critical).2
  exact PairingControl.actor_le_Q source p.color_a initial.natural_section _
    p.end_Z_le_start_stabilizer
    ((commutator_mono (PairingControl.Geometry.Vcirc_le_V p.a) le_rfl).trans h)

/-- The intersection in the printed critical-commutator contradiction. -/
theorem radius_inf_start_Z (source : LocalSource L R)
    (p : Counterexample geometry) (initial : InitialFacts p) :
    radiusCommutator p.a p.a' ⊓ Z R p.a = criticalCommutator p.a p.a' := by
  let := p.radius_finite
  let D := radiusCommutator p.a p.a' ⊓ Z R p.a
  let : Finite D := Finite.of_injective
    (inclusion (show D ≤ radiusCommutator p.a p.a' from inf_le_left)) (inclusion_injective _)
  have hsmall : Nat.card D < 4 := by
    by_contra! h
    have he := eq_of_le_of_card_ge (show D ≤ radiusCommutator p.a p.a' from inf_le_left)
      (initial.radius_card ▸ h)
    exact radius_not_le_start_Z source p initial (he ▸ (show D ≤ Z R p.a from inf_le_right))
  have hdiv : Nat.card D ∣ 4 := initial.radius_card ▸ card_dvd_of_le
    (show D ≤ radiusCommutator p.a p.a' from inf_le_left)
  have hh := Nat.mem_divisors.mpr ⟨hdiv, (by decide : 4 ≠ 0)⟩
  rw [show Nat.divisors 4 = ({1, 2, 4} : Finset ℕ) by decide] at hh
  simp only [Finset.mem_insert, Finset.mem_singleton] at hh
  exact (eq_of_le_of_card_ge p.critical_le_radius_inf_start
    (by rw [initial.critical_card]; change Nat.card D ≤ 2; omega)).symm

/-- The edge displacement cannot contain R when the edge and endpoint generate G_a. -/
theorem critical_not_le_generating_edge (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (t : Vertex R) (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a) :
    ¬ criticalCommutator p.a p.a' ≤ edgeDisplacement p.a t := by
  intro hR
  let A := edgeDisplacement p.a t
  have hAZ : A ≤ Z R p.a := (Initial.edge_le_natural source p.a t p.color_a hat).trans (U_le_Z p.a)
  have hAN : stabilizer R p.a ⊓ stabilizer R t ≤ normalizer (A : Set (FreeAmalgam R)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅Z R p.a, Q R t⁆).map (MulAut.conj g).toMonoidHom = _
    have hZ := mem_normalizer_iff_map_conj_eq.mp (Z_normalized R p.a hg.1)
    have hQ := mem_normalizer_iff_map_conj_eq.mp (Q_normalized R t hg.2)
    change (Z R p.a).map (MulAut.conj g).toMonoidHom = Z R p.a at hZ
    change (Q R t).map (MulAut.conj g).toMonoidHom = Q R t at hQ
    rw [map_commutator, hZ, hQ]
    rfl
  have hEnd : Z R p.a' ≤ normalizer (A : Set (FreeAmalgam R)) :=
    le_normalizer_iff_commutator_le_left.mpr ((commutator_mono hAZ le_rfl).trans hR)
  have hlocal : stabilizer R p.a ≤ normalizer (A : Set (FreeAmalgam R)) :=
    hgen ▸ sup_le hAN hEnd
  have hAU : A ≤ U R p.a := Initial.edge_le_natural source p.a t p.color_a hat
  have hcard : Nat.card A = 4 := edge_card p (by omega) initial p.a t p.color_a hat
  have hsmall : ⁅U R p.a, stabilizer R p.a⁆ ≤ A :=
    commutator_le_of_normalized_index_two _ _ _ hAU
      (four_index_in_eight _ _ hAU hcard (modules.natural.card_at p.a p.color_a))
      (U_normalized p.a) hlocal
  let s : BinaryNaturalStructure source :=
    ⟨modules.X_eq_Z, modules.natural, modules.decomposition, modules.disjoint⟩
  have hfull : ⁅U R p.a, stabilizer R p.a⁆ = U R p.a := by
    rw [commutator_comm, commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans (s.decomposition_at p.a p.color_a).symm)
      inf_le_right ((U_le_Z p.a).trans ((Z_le_stabilizer R p.a).trans (stabilizer R p.a).le_normalizer)),
      commutator_comm]
    exact Initial.Z_commutator_stabilizer source p.a p.color_a
  rw [hfull] at hsmall
  have hh := congrArg (fun K : Subgroup (FreeAmalgam R) => Nat.card K) (le_antisymm hAU hsmall)
  rw [hcard, modules.natural.card_at p.a p.color_a] at hh
  omega

/-- The reverse-moving generator forces the new critical commutator into
exactly the displacement at the selected starting edge. -/
theorem backward_critical_commutator_le_edge (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (control : ∀ q : Counterexample geometry, LocalControl q)
    (d t e f : Vertex R) (hd : Before p.a p.a' d 4)
    (hat : Adjacent R p.a t) (het : Adjacent R e t)
    (hea : p.a ∈ movingNeighbors geometry e) (hfe : (cosetGraph R).dist f e = 2) :
    ⁅Z R f, Z R d⁆ ≤ edgeDisplacement p.a t := by
  have hecol : color R e = false :=
    (color_eq_of_dist_even R e p.a (hea.1.symm ▸ (by decide : Even 2))).trans p.color_a
  have hdcol : color R d = false := (hd.color (by decide)).trans p.end_color
  have hde : (cosetGraph R).dist d e + 2 ≤ geometry.b R := by
    have hh := (cosetGraph_connected R).dist_triangle (u := d) (v := p.a) (w := e)
    have hh' := hd.2
    rw [p.distance_eq_b, SimpleGraph.dist_comm (u := p.a) (v := d)] at hh'
    rw [SimpleGraph.dist_comm (u := p.a) (v := e), hea.1] at hh
    omega
  have hQ : Z R d ≤ Q R e := by
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hdcol)
    rw [geometry.distance_constant d hdcol]
    change _ < geometry.b R
    omega
  have hlocal : V R e ≤ stabilizer R d :=
    PairingControl.Geometry.V_le_stabilizer_of_distance hecol (by
      rw [SimpleGraph.dist_comm]; exact hde)
  have hcentral : V R t ≤ centralizer (Z R d : Set (FreeAmalgam R)) := by
    apply PairingControl.Geometry.V_le_of_h_neighbors p.color_a hat
    intro u hut
    have hdu : Z R d ≤ Q R u := by
      apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hdcol)
      rw [geometry.distance_constant d hdcol]
      change _ < geometry.b R
      have h₁ := (cosetGraph_connected R).dist_triangle (u := d) (v := p.a) (w := t)
      have h₂ := (cosetGraph_connected R).dist_triangle (u := d) (v := t) (w := u)
      have hh := hd.2
      rw [p.distance_eq_b, SimpleGraph.dist_comm (u := p.a) (v := d)] at hh
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hat)] at h₁
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr
        ((cosetGraph_adj R _ _).mpr (adjacent_symm R hut))] at h₂
      omega
    have huc : color R u = false := by
      have h₁ := adjacent_color_ne R hat
      have h₂ := adjacent_color_ne R hut
      rw [p.color_a] at h₁
      cases ht : color R t <;> cases hu : color R u <;> simp_all
    exact (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes u huc)).trans
      (centralizer_le hdu)
  have heq : ⁅Z R d, Vcirc R e⁆ = ⁅Z R d, V R e⁆ :=
    commutator_eq_of_centralizing_sup
      ((sup_comm _ _).trans (PairingControl.Geometry.LocalProducts.radius_eq_moving_sup_edge
        source hecol het).symm) hcentral
      ((PairingControl.Geometry.Vcirc_le_V e).trans (hlocal.trans (Z_normalized R d)))
  have hZf : Z R f ≤ V R e := le_iSup_of_le f (le_iSup_of_le hfe.le le_rfl)
  have hbound : ⁅Z R f, Z R d⁆ ≤ H R e := by
    apply (commutator_mono hZf le_rfl).trans
    rw [commutator_comm, ← heq, commutator_comm]
    exact commutator_mono le_rfl hQ
  exact hbound.trans (moving_edge_eq_at p (by omega) control e t p.a hecol het hat hea).2.le

/-- The commutator contradiction proves the full W(t) containment, while
retaining the reverse moving condition in the definition of W(t). -/
theorem noncentral_backward_bound (source : LocalSource L R)
    (p : Counterexample geometry) (hb : 2 < geometry.b R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (control : ∀ q : Counterexample geometry, LocalControl q) (edge : EdgeTransfer geometry)
    (rigidity : RigidityFacts geometry) (d t : Vertex R)
    (hd : Before p.a p.a' d 4) (hn : ¬ radiusCommutator p.a p.a' ≤ localCenter d)
    (hat : Adjacent R p.a t)
    (hgen : (stabilizer R p.a ⊓ stabilizer R t) ⊔ Z R p.a' = stabilizer R p.a) :
    backwardSpan geometry p.a t ≤ Q R d := by
  classical
  obtain ⟨hi⟩ := initial p
  by_contra hW
  obtain ⟨e, het, hea, f, hf, hfe, hcrit⟩ := exists_backward_critical p d t hd hW
  have hsmall := backward_critical_commutator_le_edge source p hb control d t e f hd hat het hea hfe
  have hZf : Z R f ≤ backwardSpan geometry p.a t :=
    (show Z R f ≤ V R e from le_iSup_of_le f (le_iSup_of_le hfe.le le_rfl)).trans
      (V_le_backwardSpan het hea)
  have hR : ⁅Z R f, Z R d⁆ ≤ radiusCommutator p.a p.a' := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl hZf).trans
      (noncentral_backward_commutator_le source p hb modules hi control edge rigidity d t hd hn)
  have hline : ⁅Z R f, Z R d⁆ ≤ criticalCommutator p.a p.a' := by
    rw [← radius_inf_start_Z source p hi]
    exact le_inf hR (hsmall.trans ((Initial.edge_le_natural source p.a t p.color_a hat).trans (U_le_Z p.a)))
  let := finite_stabilizer R p.a
  let : Finite (criticalCommutator p.a p.a') := Finite.of_injective
    (inclusion (p.critical_le_radius_inf_start.trans (inf_le_right.trans (Z_le_stabilizer R p.a))))
    (inclusion_injective _)
  let : Finite (⁅Z R f, Z R d⁆ : Subgroup (FreeAmalgam R)) :=
    Finite.of_injective (inclusion hline) (inclusion_injective _)
  have hnontrivial : 1 < Nat.card (⁅Z R f, Z R d⁆ : Subgroup (FreeAmalgam R)) :=
    (one_lt_card_iff_ne_bot _).mpr (source.critical_noncommutation geometry f hf hcrit)
  have heq : ⁅Z R f, Z R d⁆ = criticalCommutator p.a p.a' :=
    eq_of_le_of_card_ge hline (by rw [hi.critical_card]; omega)
  exact critical_not_le_generating_edge source p hb modules initial t hat hgen (heq ▸ hsmall)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.Propagation.Backward
