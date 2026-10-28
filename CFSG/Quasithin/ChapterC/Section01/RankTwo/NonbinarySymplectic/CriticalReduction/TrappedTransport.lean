module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TrappedTwist
public import Theory.GroupTheory.Commutator.TwoSubgroupNormalizer

/-!
# The full terminal intersection and its residual twist

Under the uniform neighboring U-index bound, the terminal B-intersection lies in the starting
kernel: its join with the terminal Z-layer is residual invariant, and an actual
edge transporter moves it strictly inside the critical distance. The global
B-index bound and the natural lower bound then identify the literal subgroups
U_z intersect Q_a and U_z intersect B_(z-2), both of index q.

The whole natural cover has order at most q^5. Its terminal intersection has
order at most q^4, and its commutator with the terminal two-core is strictly
smaller. Relative normality and the symplectic small-section bound make that
commutator residual fixed. Consequently every terminal residual twist preserves
the same source commutator whenever its selected seed is trapped, including the
full covering kernel. Full-radius trapping is not required by these local results;
the original full-radius interfaces remain available as specializations.

The final application keeps the original path, its actual terminal transporter,
and the same escaping selected neighbor. It proves that the transported pair
is critical and has full moving-layer fixed index q. Both original fixed indices,
the literal conjugation maps and the order-q commutator are retained. The
whole-layer commutator equality and the concluding trapped-radius contradiction
are still required; this module does not assert a distance-two replacement.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two,
MS93 (5.8), printed p.920, using the natural-cover action of (1.5)(ii).
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

private theorem terminal_color
    {M : Type*} [Group M] {R : Subgroup M} {geometry : Geometry R}
    {a z : Vertex R} (path : CriticalPath R geometry a z) (hb : 4 ≤ geometry.b R) :
    color R (path.walk.getVert (path.walk.length-2))=false := by
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; exact hb
  apply (path.vertex_color (Nat.sub_le _ _)).mpr
  have he : Even path.walk.length := by
    rw [path.shortest,path.critical.1]
    exact geometry.even a path.start_color
  rw [Nat.even_iff] at he ⊢
  omega

private theorem terminal_B_intersection_le_kernel
    {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geometry : Geometry R}
    {a z : Vertex R} (path : CriticalPath R geometry a z) (hb : 4 ≤ geometry.b R)
    (x : FreeAmalgam R) (hx : x ∈ Ltilde R (path.walk.getVert (path.walk.length-2)))
    (htwist : act R x (path.walk.getVert (path.walk.length-1)) =
      path.walk.getVert (path.walk.length-3)) :
    U R z ⊓ B R (path.walk.getVert (path.walk.length-2)) (geometry.Z_normal _) ≤ Q R a := by
  let p := path.walk.getVert (path.walk.length-2)
  let A := U R z ⊓ B R p (geometry.Z_normal p)
  have hp : color R p=false := terminal_color path hb
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; exact hb
  have hVS : V R p ≤ stabilizer R p :=
    (geometry.V_le_Q (by omega) p hp).trans (fun _ hy => hy.1)
  have hcomm : ⁅A,Ltilde R p⁆ ≤ Z R p := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl u hu
    exact ((mem_B_iff R p (geometry.Z_normal p) hVS u).mp hu.2).2 l hl
  have hnorm : Ltilde R p ≤ normalizer ((A ⊔ Z R p : Subgroup (FreeAmalgam R)) : Set _) :=
    normalizes_sup_of_displacement _ _ _ ((Ltilde_le_stabilizer p).trans (Z_normalized R p)) hcomm
  have hmap := mem_normalizer_iff_map_conj_eq.mp (hnorm ((Ltilde R p).inv_mem hx))
  change (A ⊔ Z R p).map (MulAut.conj x⁻¹).toMonoidHom = A ⊔ Z R p at hmap
  have hfix : act R x p=p := Ltilde_le_stabilizer p hx
  have hbound : A ⊔ Z R p ≤ U R (act R x z) ⊔ Z R p := by
    rw [←hmap,Subgroup.map_sup,←Z_act,hfix, U_act]
    exact sup_le_sup (map_mono inf_le_left) le_rfl
  have hlast : Adjacent R z (path.walk.getVert (path.walk.length-1)) := by
    apply adjacent_symm R
    have hh := path.walk.adj_getVert_succ (by omega : path.walk.length-1 < path.walk.length)
    rw [show path.walk.length-1+1=path.walk.length by omega,SimpleGraph.Walk.getVert_length] at hh
    exact (cosetGraph_adj R _ _).mp hh
  have hnew : Adjacent R (act R x z) (path.walk.getVert (path.walk.length-3)) := by
    rw [←htwist]
    exact (adjacent_act_iff R x _ _).mpr hlast
  have hdist : (cosetGraph R).dist (act R x z) a < geometry.b R := by
    have hh := (cosetGraph_connected R).dist_triangle (u := act R x z)
      (v := path.walk.getVert (path.walk.length-3)) (w := a)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hnew),
      SimpleGraph.dist_comm (u := path.walk.getVert (path.walk.length-3)) (v := a),
      path.dist_start (Nat.sub_le _ _)] at hh
    have he := path.length_eq_b
    omega
  have hnewQ : U R (act R x z) ≤ Q R a := (U_le_Z _).trans
    (Z_le_Q_of_dist_lt R _ (geometry.exists_critical _
      (by rw [action_preserves_color]; exact path.end_color))
      (by rwa [geometry.distance_constant _ (by rw [action_preserves_color]; exact path.end_color)]))
  have hpQ : Z R p ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R p (geometry.exists_critical p hp)
    rw [geometry.distance_constant p hp,SimpleGraph.dist_comm]
    dsimp only [p]
    rw [path.dist_start (Nat.sub_le _ _)]
    change path.walk.length-2 < geometry.b R
    have he := path.length_eq_b
    omega
  exact le_sup_left.trans (hbound.trans (sup_le hnewQ hpQ))

private theorem inf_eq_of_relIndex_bounds
    {G : Type*} [Group G] (U B Q : Subgroup G) [Finite U]
    (hsub : U ⊓ B ≤ Q) (q : ℕ)
    (hQ : Q.relIndex U=q) (hB : B.relIndex U≤q) : U ⊓ Q=U ⊓ B := by
  let : Finite (U ⊓ Q : Subgroup G) := Finite.of_injective
    (inclusion (show U ⊓ Q ≤ U from inf_le_left)) (inclusion_injective _)
  have hle : U ⊓ B ≤ U ⊓ Q := le_inf inf_le_left hsub
  have hh := relIndex_mul_relIndex (U ⊓ B) (U ⊓ Q) U hle inf_le_left
  rw [inf_relIndex_left,inf_relIndex_left,hQ] at hh
  have hq : 0 < q := hQ ▸ Nat.pos_of_ne_zero (index_ne_zero_of_finite (H := Q.subgroupOf U))
  have hone : (U ⊓ B).relIndex (U ⊓ Q)=1 := by
    have hpos : 0 < (U ⊓ B).relIndex (U ⊓ Q) := Nat.pos_of_ne_zero index_ne_zero_of_finite
    nlinarith
  exact le_antisymm (relIndex_eq_one.mp hone) hle

private theorem commutator_normalized_of_triple
    {G : Type*} [Group G] (B A Q L : Subgroup G) [Q.Normal]
    (hBA : B ≤ A) (htriple : ⁅⁅A,L⁆,Q⁆ = ⊥) :
    L ≤ normalizer ((⁅B,Q⁆ : Subgroup G) : Set G) := by
  apply le_normalizer_closure_iff.mpr
  rintro l hl _ ⟨a, ha, y, hy, rfl⟩
  have hy' : l * y * l⁻¹ ∈ Q := (inferInstance : Q.Normal).conj_mem y hy l
  have hc : ⁅l,a⁆ ∈ ⁅A,L⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator hl (hBA ha)
  have hcy : Commute ⁅l,a⁆ (l * y * l⁻¹) :=
    (commutator_eq_bot_iff_le_centralizer.mp htriple hc _ hy').symm
  have hck : Commute ⁅l,a⁆ ⁅a,l * y * l⁻¹⁆ :=
    (commutator_eq_bot_iff_le_centralizer.mp htriple hc _
      (commutator_le_right B Q (commutator_mem_commutator ha hy'))).symm
  rw [conjugate_commutatorElement, show l * a * l⁻¹ = ⁅l,a⁆ * a by
    simp [commutatorElement_def, mul_assoc]]
  rw [commutatorElement_mul_left_eq_conj_mul, hcy.commutator_eq,
    hck.eq, mul_inv_cancel_right, mul_one]
  exact commutator_mem_commutator ha hy'

private theorem proper_commutator_in_two_group
    {G : Type*} [Group G] (A Q : Subgroup G) [Finite Q]
    (hQ : IsPGroup 2 Q) (hAQ : A ≤ Q) (hn : Q ≤ normalizer (A : Set G))
    (hne : A ≠ ⊥) : ⁅A,Q⁆ < A := by
  refine lt_of_le_of_ne (le_normalizer_iff_commutator_le_left.mp hn) ?_
  intro heq
  let T := A.subgroupOf Q
  have he : ⁅T, (⊤ : Subgroup Q)⁆ = T := by
    apply map_injective Q.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hAQ,
      ←MonoidHom.range_eq_map,range_subtype,heq]
  have hquot : IsPGroup 2 (Q ⧸ (⊥ : Subgroup Q)) := hQ.to_quotient ⊥
  have hz := le_normal_of_quotient_isPGroup_of_eq_commutator
    T (⊤ : Subgroup Q) ⊥ hquot he
  apply hne
  have hm := map_mono (f := Q.subtype) hz
  rw [map_subgroupOf_eq_of_le hAQ,Subgroup.map_bot] at hm
  exact le_bot_iff.mp hm

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full moving cover has at most five field dimensions, including its entire fixed kernel. -/
theorem Input.replacement_U_card_le_fifth_power
    {a : Vertex d.radical} (ha : color d.radical a=false) :
    Nat.card (U d.radical a) ≤ Nat.card F^5 := by
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d ha
  obtain ⟨f,hf,hpf⟩ := Representation.SymplecticFourOrthogonalCover.exists_cover_quotient _ he
  have hcard := Nat.card_le_card_of_surjective f hf
  have hspace : Nat.card (Representation.SymplecticFourOrthogonalCover.Space (K := E.Carrier)) =
      Nat.card F^5 := by
    rw [Module.natCard_eq_pow_finrank (K := E.Carrier),
      Representation.SymplecticFourOrthogonalCover.space_finrank,E.card_eq,hE,h.field_card]
  rw [hspace] at hcard
  rw [←hjr,MonoidHom.range_eq_map,card_map_of_injective hj,Subgroup.card_top]
  exact hcard

/-- A whole U-intersection of index q has order at most q to the fourth power. -/
theorem Input.replacement_U_intersection_card_le_fourth_power
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (T : Subgroup (FreeAmalgam d.radical))
    (hindex : T.relIndex (U d.radical a)=Nat.card F) :
    Nat.card (U d.radical a ⊓ T : Subgroup (FreeAmalgam d.radical)) ≤ Nat.card F^4 := by
  have hh := (T.subgroupOf (U d.radical a)).card_mul_index
  rw [←relIndex,hindex] at hh
  have hmap : (T.subgroupOf (U d.radical a)).map (U d.radical a).subtype = U d.radical a ⊓ T := by
    rw [subgroupOf_map_subtype,inf_comm]
  have hc := card_map_of_injective (K := T.subgroupOf (U d.radical a)) (U d.radical a).subtype_injective
  rw [hmap] at hc
  rw [←hc] at hh
  have hb := h.replacement_U_card_le_fifth_power d ha
  have hq : 0 < Nat.card F := Nat.card_pos
  have hp : Nat.card F^5=Nat.card F^4*Nat.card F := by ring
  rw [←hh,hp] at hb
  exact (Nat.mul_le_mul_right_iff hq).mp hb

/-- The terminal residual fixes the core commutator of the full intersection.
Its order is strictly below q to the fourth power, so the symplectic small-section
bound applies without selecting a complement to the cover kernel. -/
theorem Input.replacement_small_B_intersection_core_fixed
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {p z : Vertex d.radical} (hp : color d.radical p=false) (hz : color d.radical z=false)
    (hQz : Q d.radical p ≤ stabilizer d.radical z)
    (hi : (B d.radical p (geometry.Z_normal p)).relIndex (U d.radical z)=Nat.card F) :
    ⁅U d.radical z ⊓ B d.radical p (geometry.Z_normal p),Q d.radical p⁆ ≤
      centralizer (Ltilde d.radical p : Set (FreeAmalgam d.radical)) := by
  let S := stabilizer d.radical p
  let Bp := B d.radical p (geometry.Z_normal p)
  let A := U d.radical z ⊓ Bp
  let W := ⁅A,Q d.radical p⁆
  have hBQ : Bp ≤ Q d.radical p :=
    (Escape.EdgeTransfer.B_le_radius (by omega) p hp).trans (geometry.V_le_Q (by omega) p hp)
  have hAS : A ≤ S := (inf_le_right.trans hBQ).trans (fun _ hx => hx.1)
  have hQS : Q d.radical p ≤ S := fun _ hx => hx.1
  have hBS : Bp ≤ S := hBQ.trans hQS
  have hVS : V d.radical p ≤ S := (geometry.V_le_Q (by omega) p hp).trans hQS
  have hBZ : ⁅Bp,Ltilde d.radical p⁆ ≤ Z d.radical p := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl u hu
    exact ((mem_B_iff d.radical p (geometry.Z_normal p) hVS u).mp hu).2 l hl
  have hnorm : Q d.radical p ≤ normalizer (A : Set (FreeAmalgam d.radical)) :=
    (le_inf (hQz.trans (U_normalized z))
      (hQS.trans (Escape.Propagation.Rigidity.B_normalized (by omega) p hp))).trans
      inf_normalizer_le_normalizer_inf
  have hWA : W ≤ A := le_normalizer_iff_commutator_le_left.mp hnorm
  have hWQ : W ≤ Q d.radical p := hWA.trans (inf_le_right.trans hBQ)
  let := finite_stabilizer d.radical p
  let : Finite (Q d.radical p) := Finite.of_injective (inclusion hQS) (inclusion_injective _)
  let : Finite A := Finite.of_injective (inclusion hAS) (inclusion_injective _)
  let : Finite W := Finite.of_injective (inclusion hWA) (inclusion_injective _)
  have hQ := Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d) p hp
  have hWL : Ltilde d.radical p ≤ normalizer (W : Set (FreeAmalgam d.radical)) := by
    let : ((Q d.radical p).subgroupOf S).Normal := Q_normal d.radical p
    have htriple : ⁅⁅Bp.subgroupOf S,pResidual 2 S⁆,(Q d.radical p).subgroupOf S⁆=⊥ := by
      apply map_injective S.subtype_injective
      rw [map_commutator,map_commutator,map_subgroupOf_eq_of_le hBS,
        map_subgroupOf_eq_of_le hQS,Subgroup.map_bot]
      exact le_bot_iff.mp ((commutator_mono hBZ le_rfl).trans (geometry.centralizes p hp).le)
    have hn := commutator_normalized_of_triple (A.subgroupOf S) (Bp.subgroupOf S)
      ((Q d.radical p).subgroupOf S) (pResidual 2 S) (comap_mono inf_le_right) htriple
    have hm := (map_mono (f := S.subtype) hn).trans (le_normalizer_map S.subtype)
    rw [map_commutator,map_subgroupOf_eq_of_le hAS,map_subgroupOf_eq_of_le hQS] at hm
    exact hm
  by_cases hA : A=⊥
  · change ⁅A,Q d.radical p⁆ ≤ _
    rw [hA,commutator_bot_left]
    exact bot_le
  have hlt := proper_commutator_in_two_group A (Q d.radical p) hQ
    (inf_le_right.trans hBQ) hnorm hA
  have hcard : Nat.card W < Nat.card F^4 :=
    (lt_of_le_of_ne (card_le_of_le hlt.le) (fun he => hlt.ne (eq_of_le_of_card_ge hlt.le he.ge))).trans_le (h.replacement_U_intersection_card_le_fourth_power d hz Bp hi)
  let := h.quotient_simple
  let : IsSimpleGroup (Matrix.symplecticGroup (Fin 2) F) := h.quotientEquiv.symm.isSimpleGroup
  let : Finite (Ltilde d.radical p) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer p)) (inclusion_injective _)
  obtain ⟨q,hq,hker⟩ := h.replacement_residual_projection d hp
  have hc := commutator_component_le_of_symplectic_section_lt_fourth_power
    (by have := h.nonbinary; omega) h.field_card rfl
    (Ltilde d.radical p) W ⊥ (isPPerfect_embedded_pResidual_of_finite 2 _) q hq hker
    (hQ.to_le hWQ) (by rwa [relIndex_bot_left]) hWL le_normalizer_of_normal
  exact commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hc)

/-- A uniform neighboring bound determines both full critical U-indices. -/
theorem Input.replacement_critical_moving_index_of_uniform_bound
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hbound : ∀ v w c : Vertex d.radical, color d.radical v=false →
      Adjacent d.radical v w → Adjacent d.radical c w →
      (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F) :
    (Q d.radical a).relIndex (U d.radical z)=Nat.card F ∧
      (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical z)=Nat.card F := by
  obtain ⟨x,hx,he,_⟩ := h.replacement_terminal_edge_residual_twist d path hb
  have hle := terminal_B_intersection_le_kernel path hb x hx he
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; exact hb
  have ht : Adjacent d.radical (path.walk.getVert (path.walk.length-2))
      (path.walk.getVert (path.walk.length-1)) := by
    have hh := path.walk.adj_getVert_succ (by omega : path.walk.length-2 < path.walk.length)
    rw [show path.walk.length-2+1=path.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hz : Adjacent d.radical z (path.walk.getVert (path.walk.length-1)) := by
    apply adjacent_symm d.radical
    have hh := path.walk.adj_getVert_succ (by omega : path.walk.length-1 < path.walk.length)
    rw [show path.walk.length-1+1=path.walk.length by omega,SimpleGraph.Walk.getVert_length] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hidx := hbound _ _ _ (terminal_color path hb) ht hz
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective (inclusion (U_le_Z z)) (inclusion_injective _)
  have hupper := relIndex_le_of_le_left hle (L := U d.radical z) index_ne_zero_of_finite
  rw [inf_relIndex_left] at hupper
  have hAS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hlo := h.replacement_natural_fixed_index_lower d geometry hb path.end_color
    (Z d.radical a) hAS path.critical.2
  have hUS : U d.radical z ≤ stabilizer d.radical a :=
    (U_le_Z z).trans (path.endpoint_Z_le_start_stabilizer (by omega))
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hfix : U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ Q d.radical a := by
    rw [←hCa]
    ext r
    exact ⟨fun hr => ⟨hr.1,hUS hr.1,hr.2⟩,fun hr => ⟨hr.1,hr.2.2⟩⟩
  have hidxeq : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z)=(Q d.radical a).relIndex (U d.radical z) := by
    rw [←inf_relIndex_left,hfix,inf_relIndex_left]
  rw [hidxeq] at hlo
  have heq := le_antisymm (hupper.trans hidx) hlo
  exact ⟨heq,hidxeq.trans heq⟩

/-- The terminal B-intersection is the literal endpoint intersection, with its full index q. -/
theorem Input.replacement_terminal_intersection_of_uniform_bound
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hbound : ∀ v w c : Vertex d.radical, color d.radical v=false →
      Adjacent d.radical v w → Adjacent d.radical c w →
      (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F) :
    U d.radical z ⊓ Q d.radical a =
      U d.radical z ⊓ B d.radical (path.walk.getVert (path.walk.length-2)) (geometry.Z_normal _) ∧
      (Q d.radical a).relIndex (U d.radical z) = Nat.card F ∧
      (B d.radical (path.walk.getVert (path.walk.length-2)) (geometry.Z_normal _)).relIndex
        (U d.radical z) = Nat.card F := by
  obtain ⟨x,hx,he,_⟩ := h.replacement_terminal_edge_residual_twist d path hb
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; exact hb
  have ht : Adjacent d.radical (path.walk.getVert (path.walk.length-2))
      (path.walk.getVert (path.walk.length-1)) := by
    have hh := path.walk.adj_getVert_succ (by omega : path.walk.length-2 < path.walk.length)
    rw [show path.walk.length-2+1=path.walk.length-1 by omega] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hz : Adjacent d.radical z (path.walk.getVert (path.walk.length-1)) := by
    apply adjacent_symm d.radical
    have hh := path.walk.adj_getVert_succ (by omega : path.walk.length-1 < path.walk.length)
    rw [show path.walk.length-1+1=path.walk.length by omega,SimpleGraph.Walk.getVert_length] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hidx := hbound _ _ _ (terminal_color path hb) ht hz
  obtain ⟨hqi,_⟩ := h.replacement_critical_moving_index_of_uniform_bound d path hb hbound
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective (inclusion (U_le_Z z)) (inclusion_injective _)
  have hEq := inf_eq_of_relIndex_bounds (U d.radical z)
    (B d.radical (path.walk.getVert (path.walk.length-2)) (geometry.Z_normal _))
    (Q d.radical a) (terminal_B_intersection_le_kernel path hb x hx he) (Nat.card F) hqi hidx
  refine ⟨hEq,hqi,?_⟩
  rw [←inf_relIndex_left,←hEq,inf_relIndex_left,hqi]

/-- The original trapped-radius application, with its public interface retained. -/
theorem Input.replacement_trapped_terminal_intersection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1 = t)
    (htrap : V d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    U d.radical z ⊓ Q d.radical a =
      U d.radical z ⊓ B d.radical (path.walk.getVert (path.walk.length-2)) (geometry.Z_normal _) ∧
      (Q d.radical a).relIndex (U d.radical z) = Nat.card F ∧
      (B d.radical (path.walk.getVert (path.walk.length-2)) (geometry.Z_normal _)).relIndex
        (U d.radical z) = Nat.card F := by
  exact h.replacement_terminal_intersection_of_uniform_bound d path hb
    (h.replacement_trapped_radius_uniform_indices d path hb hat hfirst htrap)


omit h d in
private theorem commutator_sup_of_central
    {G : Type*} [Group G] (Y A Z : Subgroup G)
    (hZA : Z ≤ centralizer (A : Set G)) (hZY : Z ≤ centralizer (Y : Set G)) :
    ⁅Y,A ⊔ Z⁆=⁅Y,A⁆ := by
  rw [commutator_comm Y (A ⊔ Z),commutator_comm Y A]
  apply le_antisymm ?_ (commutator_mono le_sup_left le_rfl)
  have hZC : Z ≤ centralizer ((A ⊔ Y : Subgroup G) : Set G) :=
    le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hZA) (le_centralizer_iff.mp hZY))
  have hn : A ⊔ Z ≤ normalizer ((⁅A,Y⁆ : Subgroup G) : Set G) :=
    sup_le (normalizer_commutator_ge_left A Y)
      ((hZC.trans (centralizer_le (Subgroup.commutator_le_sup _ _))).trans
        (Subgroup.centralizer_le_normalizer _))
  apply commutator_sup_le_of_relative_normal (A ⊔ Z) A Z Y ⁅A,Y⁆ hn le_sup_left le_sup_right le_rfl
  rw [commutator_eq_bot_iff_le_centralizer.mpr hZY]
  exact bot_le

/-- Every terminal residual twist preserves the same source commutator, and
transports its full endpoint intersection through the literal conjugation map. -/
theorem Input.replacement_seed_twist_transport_of_uniform_bound
    {geometry : Geometry d.radical} {a z v : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hYQ : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)))
    (hbound : ∀ v w c : Vertex d.radical, color d.radical v=false →
      Adjacent d.radical v w → Adjacent d.radical c w →
      (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F)
    (x : FreeAmalgam d.radical)
    (hx : x ∈ Ltilde d.radical (path.walk.getVert (path.walk.length-2))) :
    let p := path.walk.getVert (path.walk.length-2)
    let A := U d.radical z ⊓ Q d.radical a
    let A' := U d.radical (act d.radical x z) ⊓ B d.radical p (geometry.Z_normal p)
    let D := ⁅Z d.radical v,A⁆
    A.map (MulAut.conj x⁻¹).toMonoidHom=A' ∧
      A ⊔ Z d.radical p=A' ⊔ Z d.radical p ∧
      D ≤ centralizer (Ltilde d.radical p : Set (FreeAmalgam d.radical)) ∧
      D.map (MulAut.conj x⁻¹).toMonoidHom=D ∧
      D=⁅Z d.radical v,A'⁆ ∧
      D=⁅Z d.radical (act d.radical x⁻¹ v),A⁆ := by
  dsimp only
  let p := path.walk.getVert (path.walk.length-2)
  let A := U d.radical z ⊓ Q d.radical a
  let A' := U d.radical (act d.radical x z) ⊓ B d.radical p (geometry.Z_normal p)
  let D := ⁅Z d.radical v,A⁆
  have hp : color d.radical p=false := terminal_color path hb
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; exact hb
  obtain ⟨hA,_,hi⟩ := h.replacement_terminal_intersection_of_uniform_bound d path hb hbound
  have hxS : x ∈ stabilizer d.radical p := Ltilde_le_stabilizer p hx
  have hfix : act d.radical x p=p := hxS
  have hmapB := mem_normalizer_iff_map_conj_eq.mp
    (Escape.Propagation.Rigidity.B_normalized (by omega) p hp ((stabilizer d.radical p).inv_mem hxS))
  change (B d.radical p (geometry.Z_normal p)).map (MulAut.conj x⁻¹).toMonoidHom = _ at hmapB
  change A = U d.radical z ⊓ B d.radical p (geometry.Z_normal p) at hA
  have hmapA : A.map (MulAut.conj x⁻¹).toMonoidHom=A' := by
    dsimp only [A']
    rw [hA,map_inf _ _ _ (MulAut.conj x⁻¹).injective,←U_act,hmapB]
  have hQz : Q d.radical p ≤ stabilizer d.radical z :=
    Q_le_stabilizer_of_dist_two d.radical p z hp (by dsimp [p]; rw [path.dist_end]; omega)
  have hDF : D ≤ centralizer (Ltilde d.radical p : Set (FreeAmalgam d.radical)) := by
    change ⁅Z d.radical v,A⁆ ≤ _
    rw [commutator_comm,hA]
    exact (commutator_mono le_rfl hYQ).trans
      (h.replacement_small_B_intersection_core_fixed d geometry hb hp path.end_color hQz hi)
  have hmapD (y : FreeAmalgam d.radical) (hy : y ∈ Ltilde d.radical p) :
      D.map (MulAut.conj y).toMonoidHom=D :=
    mem_normalizer_iff_map_conj_eq.mp ((Subgroup.centralizer_le_normalizer _)
      ((le_centralizer_iff.mp hDF) hy))
  have hAZ : ⁅A,Ltilde d.radical p⁆ ≤ Z d.radical p := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro l hl r hr
    have hrB := (hA ▸ hr).2
    exact ((mem_B_iff d.radical p (geometry.Z_normal p)
      ((geometry.V_le_Q (by omega) p hp).trans (fun _ hr => hr.1)) r).mp hrB).2 l hl
  have hnorm : Ltilde d.radical p ≤ normalizer ((A ⊔ Z d.radical p : Subgroup (FreeAmalgam d.radical)) : Set _) :=
    normalizes_sup_of_displacement _ _ _ ((Ltilde_le_stabilizer p).trans (Z_normalized d.radical p)) hAZ
  have hsup := mem_normalizer_iff_map_conj_eq.mp (hnorm ((Ltilde d.radical p).inv_mem hx))
  change (A ⊔ Z d.radical p).map (MulAut.conj x⁻¹).toMonoidHom=A ⊔ Z d.radical p at hsup
  rw [Subgroup.map_sup,hmapA,←Z_act,hfix] at hsup
  have hpQ : Z d.radical p ≤ Q d.radical z := by
    apply Z_le_Q_of_dist_lt d.radical p (geometry.exists_critical p hp)
    rw [geometry.distance_constant p hp]
    dsimp only [p]
    rw [path.dist_end]
    change path.walk.length-(path.walk.length-2)<geometry.b d.radical
    omega
  have hZA : Z d.radical p ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    hpQ.trans ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes z path.end_color))).trans (centralizer_le (inf_le_left.trans (U_le_Z z))))
  have hZY : Z d.radical p ≤ centralizer (Z d.radical v : Set (FreeAmalgam d.radical)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes p hp)).trans (centralizer_le hYQ)
  have hZA' : Z d.radical p ≤ centralizer (A' : Set (FreeAmalgam d.radical)) := by
    have hh := (map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hZA).trans
      (map_centralizer_le_centralizer_image _ _)
    change (Z d.radical p).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer ((A.map (MulAut.conj x⁻¹).toMonoidHom : Subgroup _) : Set _) at hh
    rw [←Z_act,hfix,hmapA] at hh
    exact hh
  have hcomm : D=⁅Z d.radical v,A'⁆ := by
    rw [show D=⁅Z d.radical v,A⁆ from rfl,
      ←commutator_sup_of_central (Z d.radical v) A (Z d.radical p) hZA hZY,
      ←hsup,commutator_sup_of_central (Z d.radical v) A' (Z d.radical p) hZA' hZY]
  refine ⟨hmapA,hsup.symm,hDF,hmapD x⁻¹ ((Ltilde d.radical p).inv_mem hx),hcomm,?_⟩
  have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hcomm
  rw [hmapD x hx,map_commutator,←hmapA,map_map] at hh
  have hZmap : (Z d.radical v).map (MulAut.conj x).toMonoidHom =
      Z d.radical (act d.radical x⁻¹ v) := by rw [Z_act,inv_inv]
  rw [hZmap] at hh
  have hid : (MulAut.conj x).toMonoidHom.comp (MulAut.conj x⁻¹).toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro g
    simp [MulAut.conj_apply,mul_assoc]
  rw [hid,Subgroup.map_id] at hh
  exact hh

/-- The full-radius specialization preserves the original transport API. -/
theorem Input.replacement_trapped_root_twist_transport
    {geometry : Geometry d.radical} {a z t v w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (haw : Adjacent d.radical a w) (hvw : Adjacent d.radical v w)
    (htrap : V d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2)))
    (x : FreeAmalgam d.radical)
    (hx : x ∈ Ltilde d.radical (path.walk.getVert (path.walk.length-2))) :
    let p := path.walk.getVert (path.walk.length-2)
    let A := U d.radical z ⊓ Q d.radical a
    let A' := U d.radical (act d.radical x z) ⊓ B d.radical p (geometry.Z_normal p)
    let D := ⁅Z d.radical v,A⁆
    A.map (MulAut.conj x⁻¹).toMonoidHom=A' ∧
      A ⊔ Z d.radical p=A' ⊔ Z d.radical p ∧
      D ≤ centralizer (Ltilde d.radical p : Set (FreeAmalgam d.radical)) ∧
      D.map (MulAut.conj x⁻¹).toMonoidHom=D ∧
      D=⁅Z d.radical v,A'⁆ ∧
      D=⁅Z d.radical (act d.radical x⁻¹ v),A⁆ := by
  exact h.replacement_seed_twist_transport_of_uniform_bound d path hb
    ((le_sup_left.trans (neighbor_seed_join_le_radius haw hvw)).trans htrap)
    (h.replacement_trapped_radius_uniform_indices d path hb hat hfirst htrap) x hx

/-- The same twisting element produces an actual new critical pair, with the
original order-q commutator unchanged and nonfixed at the original endpoint. -/
theorem Input.replacement_seed_twisted_critical_pair_of_uniform_bound
    {geometry : Geometry d.radical} {a z v w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (haw : Adjacent d.radical a w) (hvw : Adjacent d.radical v w)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hYQ : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)))
    (hbound : ∀ v w c : Vertex d.radical, color d.radical v=false →
      Adjacent d.radical v w → Adjacent d.radical c w →
      (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F)
    (x : FreeAmalgam d.radical)
    (hx : x ∈ Ltilde d.radical (path.walk.getVert (path.walk.length-2)))
    (htwist : act d.radical x (path.walk.getVert (path.walk.length-1))=
      path.walk.getVert (path.walk.length-3)) :
    ∃ hv : color d.radical v=false,
      CriticalPair d.radical v (act d.radical x z) (geometry.exists_critical v hv) ∧
      Nat.card (⁅Z d.radical v,U d.radical (act d.radical x z) ⊓
        B d.radical (path.walk.getVert (path.walk.length-2)) (geometry.Z_normal _)⁆ :
          Subgroup (FreeAmalgam d.radical)) = Nat.card F ∧
      ¬ ⁅Z d.radical (act d.radical x⁻¹ v),U d.radical z ⊓ Q d.radical a⁆ ≤
        centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
  have hv := Escape.Propagation.Rigidity.neighbor_color path.start_color haw hvw
  have hlen : 4 ≤ path.walk.length := by rw [path.length_eq_b]; exact hb
  obtain ⟨hmap,hjoin,hfixed,hinv,hcomm,hback⟩ :=
    h.replacement_seed_twist_transport_of_uniform_bound d path hb hYQ hbound x hx
  obtain ⟨_,hcard,_,_,hsource,_⟩ :=
    h.replacement_trapped_root_exact_indices d path hb haw hvw hn hYQ
  rw [hsource] at hcard
  have hnon := h.replacement_trapped_root_commutator_not_fixed d path hb haw hvw hn hYQ
  have hlast : Adjacent d.radical z (path.walk.getVert (path.walk.length-1)) := by
    apply adjacent_symm d.radical
    have hh := path.walk.adj_getVert_succ (by omega : path.walk.length-1 < path.walk.length)
    rw [show path.walk.length-1+1=path.walk.length by omega,SimpleGraph.Walk.getVert_length] at hh
    exact (cosetGraph_adj d.radical _ _).mp hh
  have hnew : Adjacent d.radical (act d.radical x z) (path.walk.getVert (path.walk.length-3)) := by
    rw [←htwist]
    exact (adjacent_act_iff d.radical x _ _).mpr hlast
  have hnear : (cosetGraph d.radical).dist (act d.radical x z) a ≤ path.walk.length-2 := by
    have hh := (cosetGraph_connected d.radical).dist_triangle (u := act d.radical x z)
      (v := path.walk.getVert (path.walk.length-3)) (w := a)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj d.radical _ _).mpr hnew),
      SimpleGraph.dist_comm (u := path.walk.getVert (path.walk.length-3)) (v := a),
      path.dist_start (Nat.sub_le _ _)] at hh
    omega
  have hdist : (cosetGraph d.radical).dist v (act d.radical x z) ≤ geometry.b d.radical := by
    have hh := (cosetGraph_connected d.radical).dist_triangle (u := v) (v := a) (w := act d.radical x z)
    have hva := neighbor_distance_le_two haw hvw
    rw [SimpleGraph.dist_comm (u := a) (v := act d.radical x z)] at hh
    have he := path.length_eq_b
    omega
  have hnot : ¬ Z d.radical v ≤ Q d.radical (act d.radical x z) := by
    intro hle
    have hc := (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes _ (by rw [action_preserves_color]; exact path.end_color))).trans
      (centralizer_le hle)
    have hzero : ⁅Z d.radical v,U d.radical (act d.radical x z) ⊓
        B d.radical (path.walk.getVert (path.walk.length-2)) (geometry.Z_normal _)⁆=⊥ :=
      commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp
        ((inf_le_left.trans (U_le_Z _)).trans hc))
    exact hnon (hcomm ▸ hzero ▸ bot_le)
  refine ⟨hv,⟨?_,hnot⟩,hcomm ▸ hcard,hback ▸ hnon⟩
  apply le_antisymm ?_ (criticalDistance_le d.radical v _ hnot)
  rwa [geometry.distance_constant v hv]



/-- The full-radius specialization preserves the original critical-pair API. -/
theorem Input.replacement_trapped_twisted_critical_pair
    {geometry : Geometry d.radical} {a z t v w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (haw : Adjacent d.radical a w) (hvw : Adjacent d.radical v w)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : V d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2)))
    (x : FreeAmalgam d.radical)
    (hx : x ∈ Ltilde d.radical (path.walk.getVert (path.walk.length-2)))
    (htwist : act d.radical x (path.walk.getVert (path.walk.length-1))=
      path.walk.getVert (path.walk.length-3)) :
    ∃ hv : color d.radical v=false,
      CriticalPair d.radical v (act d.radical x z) (geometry.exists_critical v hv) ∧
      Nat.card (⁅Z d.radical v,U d.radical (act d.radical x z) ⊓
        B d.radical (path.walk.getVert (path.walk.length-2)) (geometry.Z_normal _)⁆ :
          Subgroup (FreeAmalgam d.radical)) = Nat.card F ∧
      ¬ ⁅Z d.radical (act d.radical x⁻¹ v),U d.radical z ⊓ Q d.radical a⁆ ≤
        centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) := by
  exact h.replacement_seed_twisted_critical_pair_of_uniform_bound d path hb haw hvw hn
    ((le_sup_left.trans (neighbor_seed_join_le_radius haw hvw)).trans htrap)
    (h.replacement_trapped_radius_uniform_indices d path hb hat hfirst htrap) x hx htwist

/-- In the original trapped configuration, the actual terminal twist and the
same selected neighbor preserve the literal order-q commutator and give a new
critical pair. The full terminal intersection and both source fixed indices
are retained, with the inverse dictated by the amalgam action. -/
theorem Input.replacement_trapped_radius_transported_configuration
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (htrap : V d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    let p := path.walk.getVert (path.walk.length-2)
    let A := U d.radical z ⊓ Q d.radical a
    A = U d.radical z ⊓ B d.radical p (geometry.Z_normal p) ∧
    (Q d.radical a).relIndex (U d.radical z)=Nat.card F ∧
    (∀ v w c : Vertex d.radical, color d.radical v=false →
      Adjacent d.radical v w → Adjacent d.radical c w →
      (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F) ∧
    ∃ x u y, x ∈ Ltilde d.radical p ∧
      act d.radical x (path.walk.getVert (path.walk.length-1))=
        path.walk.getVert (path.walk.length-3) ∧
      (B d.radical p (geometry.Z_normal p)).relIndex (U d.radical (act d.radical x z))=
        Nat.card F ∧
      Adjacent d.radical u t ∧ y ∈ stabilizer d.radical a ∧
      let v := act d.radical y u
      let w := act d.radical y t
      let A' := U d.radical (act d.radical x z) ⊓ B d.radical p (geometry.Z_normal p)
      let D := ⁅Z d.radical v,A⁆
      Adjacent d.radical a w ∧ Adjacent d.radical v w ∧
      Z d.radical v ≤ Q d.radical p ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      (Q d.radical z).relIndex (Z d.radical a)=Nat.card F ∧
      (Q d.radical a).relIndex (Z d.radical z)=Nat.card F ∧
      (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical v)=Nat.card F ∧
      (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (Z d.radical v)=Nat.card F ∧
      A.map (MulAut.conj x⁻¹).toMonoidHom=A' ∧
      A ⊔ Z d.radical p=A' ⊔ Z d.radical p ∧
      D ≤ centralizer (Ltilde d.radical p : Set (FreeAmalgam d.radical)) ∧
      D.map (MulAut.conj x⁻¹).toMonoidHom=D ∧
      D=⁅Z d.radical v,A'⁆ ∧
      D=⁅Z d.radical (act d.radical x⁻¹ v),A⁆ ∧
      Nat.card D=Nat.card F ∧
      ¬ D ≤ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)) ∧
      ∃ hv : color d.radical v=false,
        CriticalPair d.radical v (act d.radical x z) (geometry.exists_critical v hv) ∧
        (Q d.radical v).relIndex (U d.radical (act d.radical x z))=Nat.card F ∧
        (centralizer (Z d.radical v : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical (act d.radical x z))=Nat.card F := by
  obtain ⟨hA,hAQ,hAB⟩ := h.replacement_trapped_terminal_intersection d path hb hat hfirst htrap
  obtain ⟨hbound,⟨x,hx,htwist,_,hidx⟩,u,y,hut,hy,haw,hvw,htrapv,hn,hi,hi',hcard,hU,hZ,hnot⟩ :=
    h.replacement_trapped_radius_twist_configuration d path hb hat hfirst htrap
  obtain ⟨hmap,hjoin,hfixed,hinv,hcomm,hback⟩ :=
    h.replacement_trapped_root_twist_transport d path hb hat hfirst haw hvw htrap x hx
  obtain ⟨hv,hcritical,_,_⟩ :=
    h.replacement_trapped_twisted_critical_pair d path hb hat hfirst haw hvw hn htrap x hx htwist
  obtain ⟨hnewQ,hnewC⟩ := h.replacement_critical_moving_index_of_uniform_bound d
    (CriticalPath.ofPair hv hcritical) hb hbound
  exact ⟨hA,hAQ,hbound,x,u,y,hx,htwist,hidx.trans hAB,hut,hy,haw,hvw,htrapv,hn,
    hi,hi',hU,hZ,hmap,hjoin,hfixed,hinv,hcomm,hback,hcard,hnot,hv,hcritical,hnewQ,hnewC⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
