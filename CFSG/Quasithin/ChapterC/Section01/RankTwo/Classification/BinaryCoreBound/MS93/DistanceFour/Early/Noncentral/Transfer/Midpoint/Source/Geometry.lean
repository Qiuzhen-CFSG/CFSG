module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Transfer.Midpoint.Escape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.Propagation.Backward.Products.RelativeNormalizer

/-!
# The source relative-normalizer comparison at a critical midpoint

The normalizer of the edge kernel need not fix its holomorph vertex. Its
conjugation on that kernel is nevertheless realized inside the holomorph
stabilizer, preserving the literal conjugated Z, Q and V subgroups and the
edge Z-layer's intersection with the conjugated local center. This supplies
the genuine geometric transport needed in the source comparison.

A retained central line survives this action. For a distinct conjugate plane,
the radius escapes the conjugate kernel; its nontrivial displacement is central
in the original local group and complements the retained line. The final
critical-pair application constructs that line from the original source
hypotheses. The later orbit and fixed-index argument consumes these results.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), relative normalizers on p.881 and the second (4.6.6), pp.903--904.
The older edge-stabilizer contracts remain unchanged.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint.Source
open Initial
open Escape.Propagation.Backward.Products
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
/-- A normalizer actor preserves the literal omega-center of the edge kernel. -/
theorem edge_normalizer_normalizes_Z (b : Vertex R) (hb : color R b = true) :
    normalizer (Q R b : Set (FreeAmalgam R)) ≤ normalizer (Z R b) := by
  have hZ : Z R b = omegaCenter (Q R b) := by simp only [Z, hb, Bool.true_eq_false, if_false]; rfl
  intro h hh
  rw [mem_normalizer_iff_map_conj_eq, hZ, ← omegaCenter_map _ _ (MulAut.conj h).injective]
  rw [mem_normalizer_iff_map_conj_eq.mp hh]

/-- The source actor has the same action on every subgroup of the actual
edge kernel as an actor in the holomorph stabilizer. -/
theorem exists_edge_actor (d b : Vertex R) (hd : color R d = false)
    (hdb : Adjacent R d b) (h : FreeAmalgam R)
    (hh : h ∈ normalizer (Q R b : Set (FreeAmalgam R))) :
    ∃ k ∈ stabilizer R b, ∀ A : Subgroup (FreeAmalgam R), A ≤ Q R b →
      A.map (MulAut.conj k⁻¹).toMonoidHom = A.map (MulAut.conj h⁻¹).toMonoidHom := by
  obtain ⟨k, hk, he⟩ := holomorph_realizes b d hd hdb h⁻¹ ((normalizer _).inv_mem hh)
  refine ⟨k⁻¹, (stabilizer R b).inv_mem hk, ?_⟩
  intro A hA
  simpa only [inv_inv] using map_conj_eq_of_agree hA he

/-- Retain the three actual conjugated local subgroups, without asserting
that the original normalizer actor fixes the edge vertex. -/
theorem exists_edge_actor_local_groups (common : CommonFacts R source geometry)
    (d b : Vertex R) (hd : color R d = false) (hdb : Adjacent R d b)
    (h : FreeAmalgam R) (hh : h ∈ normalizer (Q R b : Set (FreeAmalgam R))) :
    ∃ k ∈ stabilizer R b,
      Z R (act R k d) = Z R (act R h d) ∧
      Q R (act R k d) = Q R (act R h d) ∧
      V R (act R k d) = V R (act R h d) := by
  have hb : color R b = true := by
    have hn := adjacent_color_ne R hdb
    cases hx : color R b <;> simp_all
  have hQQ : Q R d ≤ Q R b := Q_le_adjacent_h R hb hdb
  have hVQ : V R d ≤ Q R b := (radius_le_Q common d hd).trans hQQ
  have hZQ : Z R d ≤ Q R b := (Z_le_VBall R d 2).trans hVQ
  obtain ⟨k, hk, he⟩ := exists_edge_actor d b hd hdb h hh
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · simpa only [Z_act] using he (Z R d) hZQ
  · simpa only [Q_act] using he (Q R d) hQQ
  · simpa only [V_act] using he (V R d) hVQ

omit [Finite M] in
/-- Conjugation by the genuine relative-normalizer actor preserves the edge
kernel appearing in the displacement plane. -/
theorem edge_plane_act (d b : Vertex R) (h : FreeAmalgam R)
    (hh : h ∈ normalizer (Q R b : Set (FreeAmalgam R))) :
    ⁅Z R (act R h d), Q R b⁆ =
      (⁅Z R d, Q R b⁆).map (MulAut.conj h⁻¹).toMonoidHom := by
  have hq : (Q R b).map (MulAut.conj h⁻¹).toMonoidHom = Q R b :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hh)
  rw [Z_act, map_commutator, hq]

omit [Finite M] in
/-- Every retained central line survives the actual relative-normalizer action. -/
theorem retained_line_le_conjugate_plane
    (d c b : Vertex R) (C : Subgroup (FreeAmalgam R))
    (hC : C ≤ ⁅Z R d, Q R b⁆ ⊓
      (center (stabilizer R c)).map (stabilizer R c).subtype)
    (h : FreeAmalgam R) (hhc : h ∈ stabilizer R c)
    (hhb : h ∈ normalizer (Q R b : Set (FreeAmalgam R))) :
    C ≤ ⁅Z R (act R h d), Q R b⁆ := by
  rw [edge_plane_act d b h hhb]
  intro x hx
  refine ⟨x, (hC hx).1, ?_⟩
  obtain ⟨z, hz, hzx⟩ := (hC hx).2
  have hc := congrArg Subtype.val ((mem_center_iff.mp hz) ⟨h, hhc⟩)
  change h * (z : FreeAmalgam R) = (z : FreeAmalgam R) * h at hc
  change (z : FreeAmalgam R) = x at hzx
  rw [hzx] at hc
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rw [mul_assoc, ← hc, inv_mul_cancel_left]

/-- The conjugate Z-layer lies in the original radius by realization on Q_b. -/
theorem conjugate_Z_le_radius (common : CommonFacts R source geometry)
    (d b : Vertex R) (hd : color R d = false) (hdb : Adjacent R d b)
    (h : FreeAmalgam R) (hhb : h ∈ normalizer (Q R b : Set (FreeAmalgam R))) :
    Z R (act R h d) ≤ V R d := by
  obtain ⟨k, hk, hZ, _, _⟩ := exists_edge_actor_local_groups common d b hd hdb h hhb
  rw [← hZ]
  have hkb : act R k b = b := hk
  have hdb' : Adjacent R (act R k d) b := by
    simpa only [hkb] using (adjacent_act_iff R k d b).mpr hdb
  have hdist : (cosetGraph R).dist (act R k d) d ≤ 2 := by
    have ht := (cosetGraph_connected R).dist_triangle (u := act R k d) (v := b) (w := d)
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdb')
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hdb))
    omega
  exact le_iSup_of_le (act R k d) (le_iSup_of_le hdist le_rfl)

/-- Central radius displacement through the corrected source actor. -/
theorem conjugate_radius_displacement_le (common : CommonFacts R source geometry)
    (d b : Vertex R) (hd : color R d = false) (hdb : Adjacent R d b)
    (hcentral : ⁅V R d, V R d⁆ ≤
      (center (stabilizer R d)).map (stabilizer R d).subtype)
    (h : FreeAmalgam R) (hhb : h ∈ normalizer (Q R b : Set (FreeAmalgam R))) :
    ⁅V R d, Z R (act R h d)⁆ ≤ ⁅Z R (act R h d), Q R b⁆ ⊓
      (center (stabilizer R d)).map (stabilizer R d).subtype := by
  obtain ⟨k, hk, hZ, _, _⟩ := exists_edge_actor_local_groups common d b hd hdb h hhb
  rw [← hZ]
  exact Midpoint.conjugate_radius_displacement_le common d b hd hdb hcentral k hk

/-- Escape makes the literal radius displacement nontrivial. -/
theorem conjugate_radius_displacement_ne_bot (common : CommonFacts R source geometry)
    (d b : Vertex R) (hd : color R d = false) (hdb : Adjacent R d b)
    (h : FreeAmalgam R) (hhb : h ∈ normalizer (Q R b : Set (FreeAmalgam R)))
    (hescape : ¬ V R d ≤ Q R (act R h d)) :
    ⁅V R d, Z R (act R h d)⁆ ≠ ⊥ := by
  obtain ⟨k, hk, hZ, hQ, _⟩ := exists_edge_actor_local_groups common d b hd hdb h hhb
  rw [← hZ]
  exact Midpoint.conjugate_radius_displacement_ne_bot common d b hd hdb k hk
    (by rwa [hQ])

/-- The first source comparison uses only the retained line and the actual
normalizer action. A critical pair will supply that line in the application. -/
theorem conjugate_escape_of_retained_line
    (common : CommonFacts R source geometry) (initial : InitialFacts R geometry)
    (edge : EdgeFacts R) (d c b : Vertex R) (hd : color R d = false)
    (hdb : Adjacent R d b)
    (_hcentral : ⁅V R d, V R d⁆ ≤
      (center (stabilizer R d)).map (stabilizer R d).subtype)
    (C : Subgroup (FreeAmalgam R)) (hcard : Nat.card C = 2)
    (hC : C ≤ ⁅Z R d, Q R b⁆ ⊓
      (center (stabilizer R c)).map (stabilizer R c).subtype)
    (h : FreeAmalgam R) (hhc : h ∈ stabilizer R c)
    (hhb : h ∈ normalizer (Q R b : Set (FreeAmalgam R)))
    (hne : ⁅Z R (act R h d), Q R b⁆ ≠ ⁅Z R d, Q R b⁆) :
    ¬ V R d ≤ Q R (act R h d) := by
  intro hcontained
  have hd' : color R (act R h d) = false := (action_preserves_color R h d).trans hd
  have hZV := conjugate_Z_le_radius common d b hd hdb h hhb
  have hZcenter : Z R (act R h d) ≤ (center (V R d)).map (V R d).subtype := by
    intro x hx
    refine ⟨⟨x, hZV hx⟩, ?_, rfl⟩
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext ((commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes (act R h d) hd')) hx y (hcontained y.property))
  have hB := hZcenter.trans (initial.center_le_B d hd)
  have hn : ¬ ⁅Z R (act R h d), Q R b⁆ ≤
      (center (stabilizer R d)).map (stabilizer R d).subtype := by
    intro hfix
    have hline := retained_line_le_conjugate_plane d c b C hC h hhc hhb
    have hzero : C = ⊥ := le_bot_iff.mp
      ((le_inf (hC.trans inf_le_left) (hline.trans hfix)).trans
        (edge_plane_inf_center common d b hd hdb).le)
    have hc1 := card_eq_one.mpr hzero
    omega
  obtain ⟨k, hk, hZ, _, _⟩ := exists_edge_actor_local_groups common d b hd hdb h hhb
  have hkb : act R k b = b := hk
  have hdb' : Adjacent R (act R k d) b := by
    simpa only [hkb] using (adjacent_act_iff R k d b).mpr hdb
  have heq := nonmoving_plane_eq common edge d b (act R k d) hd hdb hdb'
    (by rwa [hZ]) (by rwa [hZ])
  exact hne (by rwa [hZ] at heq)

/-- Every distinct source conjugate plane splits as the retained line and
the nontrivial radius displacement central in the original local group. -/
theorem conjugate_plane_split_of_retained_line
    (common : CommonFacts R source geometry) (initial : InitialFacts R geometry)
    (edge : EdgeFacts R) (d c b : Vertex R) (hd : color R d = false)
    (hdb : Adjacent R d b)
    (hcentral : ⁅V R d, V R d⁆ ≤
      (center (stabilizer R d)).map (stabilizer R d).subtype)
    (C : Subgroup (FreeAmalgam R)) (hcard : Nat.card C = 2)
    (hC : C ≤ ⁅Z R d, Q R b⁆ ⊓
      (center (stabilizer R c)).map (stabilizer R c).subtype)
    (h : FreeAmalgam R) (hhc : h ∈ stabilizer R c)
    (hhb : h ∈ normalizer (Q R b : Set (FreeAmalgam R)))
    (hne : ⁅Z R (act R h d), Q R b⁆ ≠ ⁅Z R d, Q R b⁆) :
    C ⊓ ⁅V R d, Z R (act R h d)⁆ = ⊥ ∧
      C ⊔ ⁅V R d, Z R (act R h d)⁆ = ⁅Z R (act R h d), Q R b⁆ := by
  let D := ⁅V R d, Z R (act R h d)⁆
  let P := ⁅Z R (act R h d), Q R b⁆
  have hCP : C ≤ P := retained_line_le_conjugate_plane d c b C hC h hhc hhb
  have hD := conjugate_radius_displacement_le common d b hd hdb hcentral h hhb
  have hCD : C ⊓ D = ⊥ := by
    apply le_bot_iff.mp
    exact (inf_le_inf (hC.trans inf_le_left) (hD.trans inf_le_right)).trans
      (edge_plane_inf_center common d b hd hdb).le
  have hDC : D ≤ centralizer (C : Set (FreeAmalgam R)) := by
    rintro x hx y hy
    obtain ⟨z, hz, hzx⟩ := (hD hx).2
    have hyG : y ∈ stabilizer R d :=
      ((hC.trans inf_le_left).trans ((edge_commutator_le_natural common d b hd hdb).trans
        ((U_le_Z d).trans (Z_le_stabilizer R d)))) hy
    have hc := congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hyG⟩)
    change y * (z : FreeAmalgam R) = (z : FreeAmalgam R) * y at hc
    change (z : FreeAmalgam R) = x at hzx
    rwa [hzx] at hc
  have hCn : D ≤ normalizer C := hDC.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨k, hk, hZ, _, _⟩ := exists_edge_actor_local_groups common d b hd hdb h hhb
  have hkb : act R k b = b := hk
  have hdb' : Adjacent R (act R k d) b := by
    simpa only [hkb] using (adjacent_act_iff R k d b).mpr hdb
  have hd' : color R (act R k d) = false := (action_preserves_color R k d).trans hd
  have hPcard : Nat.card P = 4 := by
    change Nat.card (⁅Z R (act R h d), Q R b⁆ : Subgroup (FreeAmalgam R)) = 4
    rw [← hZ]
    exact edge.edge_commutator_card (act R k d) b hd' hdb'
  let : Finite P := Nat.finite_of_card_ne_zero (by rw [hPcard]; decide)
  let : Finite D := Finite.of_injective (inclusion (hD.trans inf_le_left))
    (inclusion_injective _)
  have hDcard : 2 ≤ Nat.card D := (one_lt_card_iff_ne_bot D).mpr
    (conjugate_radius_displacement_ne_bot common d b hd hdb h hhb
      (conjugate_escape_of_retained_line common initial edge d c b hd hdb hcentral
        C hcard hC h hhc hhb hne))
  have hproduct := card_sup_eq_mul_of_normalizes_of_disjoint C D hCn (disjoint_iff.mpr hCD)
  refine ⟨hCD, eq_of_le_of_card_ge (sup_le hCP (hD.trans inf_le_left)) ?_⟩
  rw [hproduct, hcard, hPcard]
  omega

/-- The actual critical pair supplies the retained line needed by the source
normalizer comparison. No edge-stabilizer substitution is made. -/
theorem critical_conjugate_plane_split
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (initial : InitialFacts R geometry) (edge : EdgeFacts R)
    (d e c b : Vertex R) (hd : color R d = false)
    (hcrit : CriticalPair R d e (geometry.exists_critical d hd))
    (hdc : (cosetGraph R).dist d c = 2) (hce : (cosetGraph R).dist c e = 2)
    (hdb : Adjacent R d b) (hcb : Adjacent R c b)
    (hcentral : ⁅V R d, V R d⁆ ≤
      (center (stabilizer R d)).map (stabilizer R d).subtype)
    (h : FreeAmalgam R) (hhc : h ∈ stabilizer R c)
    (hhb : h ∈ normalizer (Q R b : Set (FreeAmalgam R)))
    (hne : ⁅Z R (act R h d), Q R b⁆ ≠ ⁅Z R d, Q R b⁆) :
    ⁅Z R d, Z R e⁆ ⊓ ⁅V R d, Z R (act R h d)⁆ = ⊥ ∧
      ⁅Z R d, Z R e⁆ ⊔ ⁅V R d, Z R (act R h d)⁆ = ⁅Z R (act R h d), Q R b⁆ := by
  exact conjugate_plane_split_of_retained_line common initial edge d c b hd hdb hcentral
    ⁅Z R d, Z R e⁆ (critical_line_card common d e hd hcrit)
    (critical_line_le_edge_and_midpoint_center common hb d e c b hd hcrit hdc hce hcb hcentral)
    h hhc hhb hne

omit [Finite M] in
/-- The local center's intersection with the edge Z-layer transforms under
the original normalizer actor by the same literal conjugation. -/
theorem edge_center_intersection_act (d b : Vertex R) (hb : color R b = true)
    (h : FreeAmalgam R) (hh : h ∈ normalizer (Q R b : Set (FreeAmalgam R))) :
    Z R b ⊓ (center (stabilizer R (act R h d))).map
        (stabilizer R (act R h d)).subtype =
      (Z R b ⊓ (center (stabilizer R d)).map (stabilizer R d).subtype).map
        (MulAut.conj h⁻¹).toMonoidHom := by
  have hE : (Z R b).map (MulAut.conj h⁻¹).toMonoidHom = Z R b :=
    mem_normalizer_iff_map_conj_eq.mp
      (edge_normalizer_normalizes_Z b hb ((normalizer _).inv_mem hh))
  rw [stabilizer_act, ← map_embeddedCenter _ _ (MulAut.conj h⁻¹).injective,
    Subgroup.map_inf _ _ _ (MulAut.conj h⁻¹).injective,
    hE]

/-- Realize the source conjugate by a genuine adjacent vertex, preserving
Z, Q, V and the exact center intersection used by the symmetry argument. -/
theorem exists_edge_actor_source_data (common : CommonFacts R source geometry)
    (d b : Vertex R) (hd : color R d = false) (hdb : Adjacent R d b)
    (h : FreeAmalgam R) (hh : h ∈ normalizer (Q R b : Set (FreeAmalgam R))) :
    ∃ k ∈ stabilizer R b,
      Z R (act R k d) = Z R (act R h d) ∧
      Q R (act R k d) = Q R (act R h d) ∧
      V R (act R k d) = V R (act R h d) ∧
      Z R b ⊓ (center (stabilizer R (act R k d))).map
          (stabilizer R (act R k d)).subtype =
        Z R b ⊓ (center (stabilizer R (act R h d))).map
          (stabilizer R (act R h d)).subtype := by
  have hb : color R b = true := by
    have hn := adjacent_color_ne R hdb
    cases hx : color R b <;> simp_all
  have hQQ : Q R d ≤ Q R b := Q_le_adjacent_h R hb hdb
  have hVQ : V R d ≤ Q R b := (radius_le_Q common d hd).trans hQQ
  have hZQ : Z R d ≤ Q R b := (Z_le_VBall R d 2).trans hVQ
  have hEQ : Z R b ≤ Q R b := by
    simpa only [Z, hb, Bool.true_eq_false, if_false, edgeOmega] using
      (omegaCenter_le (Q R b))
  obtain ⟨k, hk, he⟩ := exists_edge_actor d b hd hdb h hh
  refine ⟨k, hk, ?_, ?_, ?_, ?_⟩
  · simpa only [Z_act] using he (Z R d) hZQ
  · simpa only [Q_act] using he (Q R d) hQQ
  · simpa only [V_act] using he (V R d) hVQ
  · rw [edge_center_intersection_act d b hb k (Q_normalized R b hk),
      edge_center_intersection_act d b hb h hh]
    exact he _ (inf_le_left.trans hEQ)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint.Source
