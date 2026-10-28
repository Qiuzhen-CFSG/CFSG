module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Transfer.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.Basic
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The critical line and the midpoint conjugate planes

The critical commutator is a line inside the first edge plane. Under the
contrary central-derived hypothesis it is central at the midpoint, so every
conjugation through the midpoint edge retains this same line. Escape of the
radius group from a conjugate kernel makes its displacement nontrivial.
The displacement is central at the first endpoint and disjoint from the
retained line; their join is therefore the whole order-four conjugate plane.

The marked natural decomposition also gives index four for the edge layer
modulo its intersection with the original local center. Consequently a
product decomposition by the original and a conjugated local center forces
index four on the latter. The fixed points of the conjugating element in
that center lie in the original center, so an element of fixed index at most
two contradicts that product decomposition.

This file proves these reductions, including their actual subgroup and
conjugation formulas. It does not construct the missing conjugate escape or
the central-product witness. Those are the two remaining source inputs in
Midpoint/Contracts.lean. No finiteness of the free amalgam is assumed.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), second assertion numbered (4.6.6), printed pp.903--904.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint
open Initial
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem center_le_centralizer {G : Type*} [Group G] (A : Subgroup G) :
    (center A).map A.subtype ≤ centralizer (A : Set G) := by
  rintro x ⟨z, hz, rfl⟩ y hy
  exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨y, hy⟩)

/-- The natural edge plane has no nonidentity point central in its own vertex group. -/
theorem edge_plane_inf_center (common : CommonFacts R source geometry)
    (d b : Vertex R) (hd : color R d = false) (hdb : Adjacent R d b) :
    ⁅Z R d, Q R b⁆ ⊓ (center (stabilizer R d)).map (stabilizer R d).subtype = ⊥ := by
  apply le_bot_iff.mp
  exact (inf_le_inf (edge_commutator_le_natural common d b hd hdb)
    ((center_le_centralizer _).trans (centralizer_le (map_subtype_le _)))).trans
      (Flags.U_fixed_eq_bot common d hd).le

/-- The critical commutator is a line, without any extra image-index premise. -/
theorem critical_line_card (common : CommonFacts R source geometry)
    (d e : Vertex R) (hd : color R d = false)
    (hcrit : CriticalPair R d e (geometry.exists_critical d hd)) :
    Nat.card (⁅Z R d, Z R e⁆ : Subgroup (FreeAmalgam R)) = 2 := by
  have he := critical_endpoint_color R d hd _ hcrit
  rw [(naturalStructure common).critical_commutator_eq geometry d hd e hcrit]
  let : Finite (U R d) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at d hd]; decide)
  let : Finite (U R e) := Nat.finite_of_card_ne_zero (by rw [common.natural.card_at e he]; decide)
  let := geometry.U_elementary (by have := common.large_distance; omega) d hd
  let := geometry.U_elementary (by have := common.large_distance; omega) e he
  obtain ⟨hn, hn'⟩ := source.critical_U_mutually_normalize geometry d hd e hcrit
  exact card_commutator_eq_two_of_elementary_eight _ _
    (common.natural.card_at d hd) (common.natural.card_at e he) hn hn'
    ((naturalStructure common).critical_U_noncommutation geometry d hd e hcrit)

/-- The critical line lies in the actual first edge plane and is central
at the midpoint under the transported contrary hypothesis of (4.6.6). -/
theorem critical_line_le_edge_and_midpoint_center
    (_common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (d e c b : Vertex R) (hd : color R d = false)
    (hcrit : CriticalPair R d e (geometry.exists_critical d hd))
    (hdc : (cosetGraph R).dist d c = 2) (hce : (cosetGraph R).dist c e = 2)
    (hcb : Adjacent R c b)
    (hcentral : ⁅V R d, V R d⁆ ≤
      (center (stabilizer R d)).map (stabilizer R d).subtype) :
    ⁅Z R d, Z R e⁆ ≤ ⁅Z R d, Q R b⁆ ⊓
      (center (stabilizer R c)).map (stabilizer R c).subtype := by
  have hc : color R c = false :=
    (color_eq_of_dist_even R d c (by rw [hdc]; decide)).symm.trans hd
  have he := critical_endpoint_color R d hd _ hcrit
  have heb : (cosetGraph R).dist e b < geometry.b R := by
    have ht := (cosetGraph_connected R).dist_triangle (u := e) (v := c) (w := b)
    have hec : (cosetGraph R).dist e c = 2 := by rw [SimpleGraph.dist_comm, hce]
    have hbc := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hcb)
    omega
  have hZeb : Z R e ≤ Q R b := by
    apply Z_le_Q_of_dist_lt R e (geometry.exists_critical e he)
    rwa [geometry.distance_constant e he]
  have hdV : Z R d ≤ V R c := le_iSup_of_le d (le_iSup_of_le hdc.le le_rfl)
  have heV : Z R e ≤ V R c := le_iSup_of_le e
    (le_iSup_of_le (by rw [SimpleGraph.dist_comm, hce]) le_rfl)
  exact le_inf (commutator_mono le_rfl hZeb)
    ((commutator_mono hdV heV).trans (derived_central_at_all d hd hcentral c hc))

omit [Finite M] in
/-- Right conjugation agrees with the vertex action, retaining the literal edge kernel. -/
theorem edge_plane_act (d b : Vertex R) (h : FreeAmalgam R)
    (hb : h ∈ stabilizer R b) :
    ⁅Z R (act R h d), Q R b⁆ =
      (⁅Z R d, Q R b⁆).map (MulAut.conj h⁻¹).toMonoidHom := by
  conv_lhs => rw [← show act R h b = b from hb]
  rw [Z_act, Q_act, map_commutator]

/-- The retained critical line is contained in every midpoint-edge conjugate. -/
theorem critical_line_le_conjugate_plane
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (d e c b : Vertex R) (hd : color R d = false)
    (hcrit : CriticalPair R d e (geometry.exists_critical d hd))
    (hdc : (cosetGraph R).dist d c = 2) (hce : (cosetGraph R).dist c e = 2)
    (hcb : Adjacent R c b)
    (hcentral : ⁅V R d, V R d⁆ ≤
      (center (stabilizer R d)).map (stabilizer R d).subtype)
    (h : FreeAmalgam R) (hhc : h ∈ stabilizer R c) (hhb : h ∈ stabilizer R b) :
    ⁅Z R d, Z R e⁆ ≤ ⁅Z R (act R h d), Q R b⁆ := by
  have hline := critical_line_le_edge_and_midpoint_center common hb d e c b hd
    hcrit hdc hce hcb hcentral
  rw [edge_plane_act d b h hhb]
  intro x hx
  refine ⟨x, (hline hx).1, ?_⟩
  have hc := center_le_centralizer _ (hline hx).2 h hhc
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  rw [mul_assoc, ← hc, inv_mul_cancel_left]


/-- Conjugating the first endpoint through the edge preserves the literal
radius and edge-kernel containments needed by the comparison. -/
theorem conjugate_radius_displacement_le
    (common : CommonFacts R source geometry)
    (d b : Vertex R) (hd : color R d = false) (hdb : Adjacent R d b)
    (hcentral : ⁅V R d, V R d⁆ ≤
      (center (stabilizer R d)).map (stabilizer R d).subtype)
    (h : FreeAmalgam R) (hhb : h ∈ stabilizer R b) :
    ⁅V R d, Z R (act R h d)⁆ ≤ ⁅Z R (act R h d), Q R b⁆ ⊓
      (center (stabilizer R d)).map (stabilizer R d).subtype := by
  have hhb' : act R h b = b := hhb
  have hdb' : Adjacent R (act R h d) b := by
    simpa only [hhb'] using (adjacent_act_iff R h d b).mpr hdb
  have hbcol : color R b = true := by
    have hh := adjacent_color_ne R hdb
    cases hb : color R b <;> simp_all
  have hdist : (cosetGraph R).dist (act R h d) d ≤ 2 := by
    have ht := (cosetGraph_connected R).dist_triangle (u := act R h d) (v := b) (w := d)
    have h₁ := SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hdb')
    have h₂ := SimpleGraph.dist_eq_one_iff_adj.mpr
      ((cosetGraph_adj R _ _).mpr (adjacent_symm R hdb))
    omega
  have hZV : Z R (act R h d) ≤ V R d :=
    le_iSup_of_le (act R h d) (le_iSup_of_le hdist le_rfl)
  have hVQ : V R d ≤ Q R b :=
    (radius_le_Q common d hd).trans (Q_le_adjacent_h R hbcol hdb)
  apply le_inf
  · rw [commutator_comm]
    exact commutator_mono le_rfl hVQ
  · exact (commutator_mono le_rfl hZV).trans hcentral

/-- Escape from the conjugate kernel makes the radius displacement nontrivial. -/
theorem conjugate_radius_displacement_ne_bot
    (common : CommonFacts R source geometry)
    (d b : Vertex R) (hd : color R d = false) (hdb : Adjacent R d b)
    (h : FreeAmalgam R) (hhb : h ∈ stabilizer R b)
    (hescape : ¬ V R d ≤ Q R (act R h d)) :
    ⁅V R d, Z R (act R h d)⁆ ≠ ⊥ := by
  intro hzero
  apply hescape
  have hhb' : act R h b = b := hhb
  have hdb' : Adjacent R (act R h d) b := by
    simpa only [hhb'] using (adjacent_act_iff R h d b).mpr hdb
  have hd' : color R (act R h d) = false := (action_preserves_color R h d).trans hd
  have hbcol : color R b = true := by
    have hh := adjacent_color_ne R hdb
    cases hb : color R b <;> simp_all
  rw [← common.centralizer (act R h d) b hd' hdb']
  exact le_inf ((radius_le_Q common d hd).trans (Q_le_adjacent_h R hbcol hdb))
    (commutator_eq_bot_iff_le_centralizer.mp hzero)

/-- Once the source escape is supplied, the conjugate plane splits as the
retained critical line and the nontrivial displacement central at d. -/
theorem conjugate_plane_split_of_radius_escape
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (edge : EdgeFacts R)
    (d e c b : Vertex R) (hd : color R d = false)
    (hcrit : CriticalPair R d e (geometry.exists_critical d hd))
    (hdc : (cosetGraph R).dist d c = 2) (hce : (cosetGraph R).dist c e = 2)
    (hdb : Adjacent R d b) (hcb : Adjacent R c b)
    (hcentral : ⁅V R d, V R d⁆ ≤
      (center (stabilizer R d)).map (stabilizer R d).subtype)
    (h : FreeAmalgam R) (hhc : h ∈ stabilizer R c) (hhb : h ∈ stabilizer R b)
    (hescape : ¬ V R d ≤ Q R (act R h d)) :
    ⁅Z R d, Z R e⁆ ⊓ ⁅V R d, Z R (act R h d)⁆ = ⊥ ∧
      ⁅Z R d, Z R e⁆ ⊔ ⁅V R d, Z R (act R h d)⁆ = ⁅Z R (act R h d), Q R b⁆ := by
  let C := ⁅Z R d, Z R e⁆
  let D := ⁅V R d, Z R (act R h d)⁆
  let P := ⁅Z R (act R h d), Q R b⁆
  have hC := critical_line_le_edge_and_midpoint_center common hb d e c b hd
    hcrit hdc hce hcb hcentral
  have hCP : C ≤ P := critical_line_le_conjugate_plane common hb d e c b hd
    hcrit hdc hce hcb hcentral h hhc hhb
  have hD := conjugate_radius_displacement_le common d b hd hdb hcentral h hhb
  have hCD : C ⊓ D = ⊥ := by
    apply le_bot_iff.mp
    exact (inf_le_inf (hC.trans inf_le_left) (hD.trans inf_le_right)).trans
      (edge_plane_inf_center common d b hd hdb).le
  have hCn : D ≤ normalizer C := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    exact (hD.trans inf_le_right).trans ((center_le_centralizer _).trans
      (centralizer_le ((hC.trans inf_le_left).trans
        ((edge_commutator_le_natural common d b hd hdb).trans
          ((U_le_Z d).trans (Z_le_stabilizer R d))))))
  have hhb' : act R h b = b := hhb
  have hdb' : Adjacent R (act R h d) b := by
    simpa only [hhb'] using (adjacent_act_iff R h d b).mpr hdb
  have hd' : color R (act R h d) = false := (action_preserves_color R h d).trans hd
  have hPcard : Nat.card P = 4 := edge.edge_commutator_card (act R h d) b hd' hdb'
  let : Finite P := Nat.finite_of_card_ne_zero (by rw [hPcard]; decide)
  let : Finite D := Finite.of_injective (inclusion (hD.trans inf_le_left))
    (inclusion_injective _)
  have hDcard : 2 ≤ Nat.card D := (one_lt_card_iff_ne_bot D).mpr
    (conjugate_radius_displacement_ne_bot common d b hd hdb h hhb hescape)
  have hproduct := card_sup_eq_mul_of_normalizes_of_disjoint C D hCn (disjoint_iff.mpr hCD)
  have hCcard : Nat.card C = 2 := critical_line_card common d e hd hcrit
  refine ⟨hCD, eq_of_le_of_card_ge (sup_le hCP (hD.trans inf_le_left)) ?_⟩
  rw [hproduct, hCcard, hPcard]
  omega

omit [Finite M] in
/-- A point of a conjugated center fixed by the conjugating element was
already in the original center. This fixes the orientation of the last
centralizer inclusion on MS93 p.904. -/
theorem fixed_conjugate_center_le (d : Vertex R) (h : FreeAmalgam R) :
    (center (stabilizer R (act R h d))).map (stabilizer R (act R h d)).subtype ⊓
      centralizer ({h} : Set (FreeAmalgam R)) ≤
        (center (stabilizer R d)).map (stabilizer R d).subtype := by
  rintro x ⟨hx, hxfix⟩
  rw [stabilizer_act, ← map_embeddedCenter _ _ (MulAut.conj h⁻¹).injective] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have hcomm := hxfix h (by simp)
  have heq := congrArg (fun t : FreeAmalgam R => h * t * h⁻¹) hxy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at heq
  have hyx : y = x := by
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, hcomm,
      mul_inv_cancel_right, mul_inv_cancel, mul_one] using heq
  exact hyx ▸ hy

/-- Restricting a conjugating element to a conjugated local center cannot
have larger fixed index than its action on the whole edge layer. -/
theorem conjugate_center_index_le_fixed_index
    (d b : Vertex R) (h : FreeAmalgam R) :
    ((center (stabilizer R d)).map (stabilizer R d).subtype).relIndex
      (Z R b ⊓ (center (stabilizer R (act R h d))).map
        (stabilizer R (act R h d)).subtype) ≤
      (centralizer ({h} : Set (FreeAmalgam R))).relIndex (Z R b) := by
  let E := Z R b
  let A := (center (stabilizer R d)).map (stabilizer R d).subtype
  let A' := (center (stabilizer R (act R h d))).map (stabilizer R (act R h d)).subtype
  let H := centralizer ({h} : Set (FreeAmalgam R))
  let K := E ⊓ A'
  let := finite_stabilizer R b
  let : Finite E := Finite.of_injective (inclusion (Z_le_stabilizer R b))
    (inclusion_injective _)
  let : Finite K := Finite.of_injective (inclusion (show K ≤ E from inf_le_left))
    (inclusion_injective _)
  have hle : K ⊓ H ≤ A := (inf_le_inf inf_le_right le_rfl).trans
    (fixed_conjugate_center_le d h)
  have h₁ := relIndex_le_of_le_left hle
    (show (K ⊓ H).relIndex K ≠ 0 from ((K ⊓ H).subgroupOf K).index_ne_zero_of_finite)
  rw [inf_relIndex_left] at h₁
  have h₂ := relIndex_le_of_le_right (show K ≤ E from inf_le_left)
    (show H.relIndex E ≠ 0 from (H.subgroupOf E).index_ne_zero_of_finite)
  exact h₁.trans h₂


/-- The edge layer has index four over its fixed part in the first local
group. This uses the marked natural summand, not an unmarked module tag. -/
theorem edge_center_index (common : CommonFacts R source geometry) (edge : EdgeFacts R)
    (d b : Vertex R) (hd : color R d = false) (hdb : Adjacent R d b) :
    ((center (stabilizer R d)).map (stabilizer R d).subtype).relIndex (Z R b) = 4 := by
  let C := Z R d ⊓ centralizer (stabilizer R d : Set (FreeAmalgam R))
  have hCQ : C ≤ centralizer (Q R b : Set (FreeAmalgam R)) :=
    inf_le_right.trans (centralizer_le (fun _ hx => hx.2 d (adjacent_symm R hdb)))
  have hCb : C ≤ Z R b := by
    rw [edge_Z_eq_fixed common d b hd hdb]
    exact le_inf inf_le_left hCQ
  have hCU : U R d ⊓ C = ⊥ := by
    apply le_bot_iff.mp
    exact (inf_le_inf le_rfl (inf_le_right.trans
      (centralizer_le (map_subtype_le _)))).trans (Flags.U_fixed_eq_bot common d hd).le
  have hCn : Z R d ≤ normalizer C :=
    (le_centralizer_iff.mp (show C ≤ centralizer (Z R d : Set (FreeAmalgam R)) from
      inf_le_right.trans (centralizer_le (Z_le_stabilizer R d)))).trans
        (Subgroup.centralizer_le_normalizer _)
  let : (C.subgroupOf (Z R d)).Normal := normal_subgroupOf_of_le_normalizer hCn
  have hsup : (U R d).subgroupOf (Z R d) ⊔ C.subgroupOf (Z R d) = ⊤ := by
    rw [← subgroupOf_sup (U_le_Z d) (show C ≤ Z R d from inf_le_left),
      ← (naturalStructure common).decomposition_at d hd, subgroupOf_self]
  have hindex := relIndex_sup_right ((U R d).subgroupOf (Z R d)) (C.subgroupOf (Z R d))
  rw [hsup, relIndex_top_right, relIndex_subgroupOf (U_le_Z d)] at hindex
  change C.relIndex (Z R d) = C.relIndex (U R d) at hindex
  have hindex8 : C.relIndex (Z R d) = 8 := by
    rw [hindex, ← inf_relIndex_left (U R d) C, hCU, relIndex_bot_left,
      common.natural.card_at d hd]
  have hmul := relIndex_mul_relIndex C (Z R b) (Z R d) hCb (edge_Z_le d b hd hdb)
  rw [hindex8, edge.edge_Z_index d b hd hdb] at hmul
  have hC4 : C.relIndex (Z R b) = 4 := by omega
  have heq : C.subgroupOf (Z R b) =
      ((center (stabilizer R d)).map (stabilizer R d).subtype).subgroupOf (Z R b) := by
    ext x
    change (x : FreeAmalgam R) ∈ C ↔
      (x : FreeAmalgam R) ∈ (center (stabilizer R d)).map (stabilizer R d).subtype
    constructor
    · intro hx
      refine ⟨⟨x, Z_le_stabilizer R d hx.1⟩, ?_, rfl⟩
      apply mem_center_iff.mpr
      intro y
      exact Subtype.ext (hx.2 y y.property)
    · intro hx
      exact ⟨edge_Z_le d b hd hdb x.property, center_le_centralizer _ hx⟩
  change (C.subgroupOf (Z R b)).index = 4 at hC4
  change (((center (stabilizer R d)).map (stabilizer R d).subtype).subgroupOf (Z R b)).index = 4
  rwa [heq] at hC4


/-- The central-product conclusion of the conjugate-plane comparison forces
index four on the conjugated center. The center in the denominator is the
original local center. -/
theorem edge_center_span_index (common : CommonFacts R source geometry) (edge : EdgeFacts R)
    (d b : Vertex R) (hd : color R d = false) (hdb : Adjacent R d b)
    (h : FreeAmalgam R)
    (hspan : Z R b =
      (Z R b ⊓ (center (stabilizer R d)).map (stabilizer R d).subtype) ⊔
      (Z R b ⊓ (center (stabilizer R (act R h d))).map
        (stabilizer R (act R h d)).subtype)) :
    ((center (stabilizer R d)).map (stabilizer R d).subtype).relIndex
      (Z R b ⊓ (center (stabilizer R (act R h d))).map
        (stabilizer R (act R h d)).subtype) = 4 := by
  let E := Z R b
  let A := (center (stabilizer R d)).map (stabilizer R d).subtype
  let A' := (center (stabilizer R (act R h d))).map (stabilizer R (act R h d)).subtype
  let C := E ⊓ A
  let D := E ⊓ A'
  have hEn : E ≤ normalizer C := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    apply le_centralizer_iff.mp
    exact inf_le_right.trans ((center_le_centralizer _).trans
      (centralizer_le ((edge_Z_le d b hd hdb).trans (Z_le_stabilizer R d))))
  let : (C.subgroupOf E).Normal := normal_subgroupOf_of_le_normalizer hEn
  have hcover : C.subgroupOf E ⊔ D.subgroupOf E = ⊤ := by
    rw [← subgroupOf_sup (show C ≤ E from inf_le_left) (show D ≤ E from inf_le_left)]
    rw [show C ⊔ D = E from hspan.symm, subgroupOf_self]
  have hi := relIndex_sup_left (D.subgroupOf E) (C.subgroupOf E)
  rw [hcover, relIndex_top_right, relIndex_subgroupOf (show D ≤ E from inf_le_left)] at hi
  change C.relIndex E = C.relIndex D at hi
  have hsub : C.subgroupOf D = A.subgroupOf D := by
    ext x
    change ((x : FreeAmalgam R) ∈ E ∧ (x : FreeAmalgam R) ∈ A) ↔
      (x : FreeAmalgam R) ∈ A
    exact and_iff_right x.property.1
  have hCD : C.relIndex D = A.relIndex D := congrArg Subgroup.index hsub
  have hCE : C.relIndex E = 4 := by
    change (Z R b ⊓ A).relIndex (Z R b) = 4
    rw [inf_relIndex_left]
    exact edge_center_index common edge d b hd hdb
  exact hCD ▸ hi ▸ hCE

/-- The final fixed-index contradiction on p.904, for the literal local
centers and the literal conjugating element. -/
theorem not_edge_center_span_of_small_fixed_index
    (common : CommonFacts R source geometry) (edge : EdgeFacts R)
    (d b : Vertex R) (hd : color R d = false) (hdb : Adjacent R d b)
    (h : FreeAmalgam R)
    (hsmall : (centralizer ({h} : Set (FreeAmalgam R))).relIndex (Z R b) ≤ 2) :
    Z R b ≠
      (Z R b ⊓ (center (stabilizer R d)).map (stabilizer R d).subtype) ⊔
      (Z R b ⊓ (center (stabilizer R (act R h d))).map
        (stabilizer R (act R h d)).subtype) := by
  intro hspan
  have hindex := edge_center_span_index common edge d b hd hdb h hspan
  have hbound := conjugate_center_index_le_fixed_index (R := R) d b h
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Midpoint
