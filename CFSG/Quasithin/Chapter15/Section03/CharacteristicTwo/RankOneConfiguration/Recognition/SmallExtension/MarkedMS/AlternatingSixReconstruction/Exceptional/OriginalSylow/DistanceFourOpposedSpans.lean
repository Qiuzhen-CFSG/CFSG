module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourEvenCore

/-!
# Opposed selected spans on the original Borel graph

For a critical path starting at a with midpoint c, take the full spans
P₁ = ⟨Z_c^{G_a}⟩ and P₂ = ⟨Z_a^{G_c}⟩. The actual backward selection
provides a critical path starting at c with midpoint a. The midpoint
core index and the selected critical seed give both opposite-core indices
exactly four. Conjugation transports the derived-radius identities to
that same backward path. Consequently [P₁,Q_a] ≤ Z_c and [P₂,Q_c] ≤ Z_a,
which give both cross-kernel commutator bounds.

The entire P₂ has the same conjugate even three-pair image as V_c under
the original cubic projection. Its action on P₁/Z(P₁) fixes the image of
P₁ ∩ Q_c, hence has fixed codimension at most two. An even involution in
that image and the faithful-component kernel bound give the reverse
inequality. This is a statement about the literal central quotient; no
identification with the Baumann quotient is assumed.

OriginalSylowExceptional applies these results to c.L,d.S, including a
constructed path with its whole opposite actor. Both full moving covers,
central attachments and E/Q remain. Whole-radius/core fixedness and the
terminal module contradiction are still required for CoreExhaustion.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.12)(2), printed p.926; Aschbacher--Smith C.1.31--32,
printed pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk


include h e hz hk in
/-- The full selected span has index four modulo the opposite two-core. -/
theorem borel_four_span_core_index
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    (Q Rg (p.walk.getVert 2)).relIndex
      (localZSpan Rg (p.walk.getVert 2) (alpha Rg)) = 4 := by
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨_,hindex,_,t,hat,hgen,g,hg,hgt,q,hqt,hqa,hover,hstrict⟩ :=
    large_remaining_four_span_configuration h e hz hk hb u (Or.inr hR) p
      (borel_four_critical_images_large h e hz hk u hR p)
  let r : CriticalPath Rg (sourceGeometry h) (p.walk.getVert 2)
      (act Rg g (p.walk.getVert 2)) :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        _ q.start_color (by
          rw [(sourceGeometry h).distance_constant _ q.start_color]
          exact sourceDistance_pos h) _ q.end_color q.critical⟩
  have hr2 : r.walk.getVert 2 = alpha Rg := by
    change q.walk.reverse.getVert 2 = alpha Rg
    rw [SimpleGraph.Walk.getVert_reverse,
      show q.walk.length-2=2 from by have hh := q.length_eq_b.trans hb; omega,hqa]
  have hcore := (borel_four_midpoint_core_at h e hz hk u hR r).1
  rw [hr2] at hcore
  have hPQ : localZSpan Rg (p.walk.getVert 2) (alpha Rg) ≤ Q Rg (alpha Rg) :=
    (localZSpan_le_V Rg (by rw [SimpleGraph.dist_comm,p.dist_start (by omega)])).trans
      ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) _ rfl)
  have hup := relIndex_le_of_le_right hPQ
    (show (Q Rg (p.walk.getVert 2)).relIndex (Q Rg (alpha Rg)) ≠ 0 from by rw [hcore]; decide)
  have hdP : Z Rg (act Rg g (p.walk.getVert 2)) ≤
      localZSpan Rg (p.walk.getVert 2) (alpha Rg) := by
    rw [Z_act]
    exact (map_mono (Z_le_localZSpan Rg _ _)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (localZSpan_normalized Rg _ _
        ((stabilizer Rg (alpha Rg)).inv_mem hg)))
  have hlo := relIndex_le_of_le_right hdP
    (show (Q Rg (p.walk.getVert 2)).relIndex
      (localZSpan Rg (p.walk.getVert 2) (alpha Rg)) ≠ 0 from by omega)
  have hcrit := (borel_four_critical_indices h e hz hk u hR q).1
  rw [hcrit] at hlo
  omega

include h e hz hk in
/-- Both the exact core index and derived-group identities hold on every
original critical path, with its literal midpoint. -/
theorem borel_four_span_at
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) a z) :
    let P := localZSpan Rg (p.walk.getVert 2) a
    (Q Rg (p.walk.getVert 2)).relIndex P = 4 ∧
      ⁅V Rg a,V Rg a⁆ = ⁅P,P⁆ ∧ ⁅P,P⁆ = ⁅P,Q Rg a⁆ ∧
      ⁅P,Q Rg a⁆ ≤ Z Rg (p.walk.getVert 2) := by
  obtain ⟨x,hx⟩ := exists_mVertex_of_color Rg p.start_color
  have he : act Rg x⁻¹ a = alpha Rg := by
    rw [hx,act_mVertex,mul_inv_cancel]
    rfl
  obtain ⟨q,hq⟩ : ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x⁻¹ z),
      ∀ i, q.walk.getVert i = act Rg x⁻¹ (p.walk.getVert i) := by
    have hh : ∃ q : CriticalPath Rg (sourceGeometry h) (act Rg x⁻¹ a) (act Rg x⁻¹ z),
        ∀ i, q.walk.getVert i = act Rg x⁻¹ (p.walk.getVert i) :=
      ⟨p.act x⁻¹,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
    rwa [he] at hh
  have hi := borel_four_span_core_index h e hz hk u hR q
  obtain ⟨hv,hp,hz⟩ := borel_four_radius_span_derived h e hz hk u hR q
  have hm := (hv.trans hp).symm.le.trans hz
  rw [hq 2,←he,Q_act,LocalCommutator.CriticalCase.localZSpan_act,
    relIndex_map_map_of_injective _ _ (MulAut.conj _).injective] at hi
  rw [hq 2,←he,V_act,LocalCommutator.CriticalCase.localZSpan_act,
    ←map_commutator,←map_commutator] at hv
  rw [hq 2,←he,Q_act,LocalCommutator.CriticalCase.localZSpan_act,
    ←map_commutator,←map_commutator] at hp
  rw [hq 2,←he,Q_act,Z_act,LocalCommutator.CriticalCase.localZSpan_act,
    ←map_commutator] at hm
  exact ⟨hi,(map_injective (MulAut.conj _).injective) hv,
    (map_injective (MulAut.conj _).injective) hp,
    (map_le_map_iff_of_injective (MulAut.conj _).injective).mp hm⟩

include h e hz hk in
/-- The two opposed full selected spans on an actual original critical path
have exact opposite-core index four and control both cross-kernel actions. -/
theorem borel_four_opposed_spans
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    let a := alpha Rg
    let c := p.walk.getVert 2
    let P₁ := localZSpan Rg c a
    let P₂ := localZSpan Rg a c
    (Q Rg c).relIndex P₁ = 4 ∧ (Q Rg a).relIndex P₂ = 4 ∧
      ⁅P₁,Q Rg a⁆ ≤ Z Rg c ∧ ⁅P₂,Q Rg c⁆ ≤ Z Rg a ∧
      ⁅P₁ ⊓ Q Rg c,P₂⁆ ≤ Z Rg a ∧
      ⁅P₂ ⊓ Q Rg a,P₁⁆ ≤ Z Rg c := by
  let a := alpha Rg
  let c := p.walk.getVert 2
  let P₁ := localZSpan Rg c a
  let P₂ := localZSpan Rg a c
  have hb := borel_distance_eq_four h e hz hk u hR
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  obtain ⟨_,_,_,t,hat,hgen,g,hg,hgt,q,hqt,hqa,hover,hstrict⟩ :=
    large_remaining_four_span_configuration h e hz hk hb u (Or.inr hR) p
      (borel_four_critical_images_large h e hz hk u hR p)
  let r : CriticalPath Rg (sourceGeometry h) c (act Rg g c) :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse Rg (sourceGeometry h) (sourceEdgeCentralizer h e)
        _ q.start_color (by
          rw [(sourceGeometry h).distance_constant _ q.start_color]
          exact sourceDistance_pos h) _ q.end_color q.critical⟩
  have hr2 : r.walk.getVert 2 = a := by
    change q.walk.reverse.getVert 2 = a
    rw [SimpleGraph.Walk.getVert_reverse,
      show q.walk.length-2=2 from by have hh := q.length_eq_b.trans hb; omega,hqa]
  have h₁ := borel_four_span_at h e hz hk u hR p
  have h₂ := borel_four_span_at h e hz hk u hR r
  dsimp only at h₁ h₂
  rw [hr2] at h₂
  refine ⟨h₁.1,h₂.1,h₁.2.2.2,h₂.2.2.2,?_,?_⟩
  · rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans h₂.2.2.2
  · rw [commutator_comm]
    exact (commutator_mono le_rfl inf_le_right).trans h₁.2.2.2

private theorem linearized_fixed_codim_le_two
    {Y : Type*} [Group Y] [Finite Y] [IsElementaryAbelian 2 Y]
    {D : Type*} [Group D] (ρ : D →* MulAut Y) (A : Subgroup D)
    (F : Subgroup Y) (hF : ∀ y ∈ F, ∀ a ∈ A, ρ a y = y)
    (hi : F.index ≤ 4) : fixedCodim (Offenders.linearize ρ) A ≤ 2 := by
  let σ := Offenders.linearize ρ
  let j : F → fixedSpace σ A := fun y =>
    ⟨Additive.ofMul y.val,fun a => congrArg Additive.ofMul (hF y.val y.property a.val a.property)⟩
  have hj : Function.Injective j := by
    intro x y hxy
    exact Subtype.ext (congrArg (fun z : fixedSpace σ A => z.val.toMul) hxy)
  have hf : Nat.card F ≤ Nat.card (fixedSpace σ A) := Nat.card_le_card_of_injective j hj
  have hcard : Nat.card Y ≤ Nat.card (fixedSpace σ A) * 4 := by
    rw [←F.card_mul_index]
    exact Nat.mul_le_mul hf hi
  change Nat.card (Additive Y) ≤ _ at hcard
  have hV := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive Y)
  have hW := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace σ A)
  rw [Nat.card_zmod] at hV hW
  rw [hV,hW,show 4 = 2^2 from rfl,←pow_add] at hcard
  have hd := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hcard
  have he := fixedCodim_add_finrank σ A
  change fixedCodim σ A ≤ 2
  omega

include h e hz hk in
/-- The whole opposite selected span fixes a subgroup of index at most four
in the literal central quotient of the forward span. This is the full-actor
fixed-codimension bound in MS93 (5.12)(2), rather than a single involution bound. -/
theorem borel_four_opposed_span_fixed_codim
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    let c := p.walk.getVert 2
    letI := selected_span_central_quotient_elementary h e hz hk
      (distance_gt_two h e hz hk) c (by
        rw [SimpleGraph.dist_comm,p.dist_start (by
          have hl := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
          omega)])
    fixedCodim (Offenders.linearize (forwardSpanCentralAction Rg c))
      ((localZSpan Rg (alpha Rg) c).comap (embedM Rg)) ≤ 2 := by
  let c := p.walk.getVert 2
  let P := localZSpan Rg c (alpha Rg)
  let A := (localZSpan Rg (alpha Rg) c).comap (embedM Rg)
  let C := Q Rg c
  let q : P →* P ⧸ center P := QuotientGroup.mk' (center P)
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
  have hd : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)]
  have hPQ : P ≤ Q Rg (alpha Rg) :=
    (localZSpan_le_V Rg hd).trans ((sourceGeometry h).V_le_Q hb _ rfl)
  have hPG : P ≤ stabilizer Rg (alpha Rg) := hPQ.trans (fun _ hx => hx.1)
  let := finite_stabilizer Rg (alpha Rg)
  let : Finite P := Finite.of_injective (inclusion hPG) (inclusion_injective _)
  let := selected_span_central_quotient_elementary h e hz hk hb c hd
  change fixedCodim (Offenders.linearize (forwardSpanCentralAction Rg c)) A ≤ 2
  have hZaC : Z Rg (alpha Rg) ≤ centralizer (P : Set (FreeAmalgam Rg)) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q Rg _ rfl)).trans
      (centralizer_le hPQ)
  have hcross := (borel_four_opposed_spans h e hz hk u hR p).2.2.2.2.1
  have hfixed : ∀ y ∈ (C.subgroupOf P).map q, ∀ m ∈ A,
      forwardSpanCentralAction Rg c m y = y := by
    rintro _ ⟨x,hx,rfl⟩ m hm
    rw [forwardSpanCentralAction_apply]
    apply QuotientGroup.eq_iff_div_mem.mpr
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hz : ⁅embedM Rg m,(x : FreeAmalgam Rg)⁆ ∈ Z Rg (alpha Rg) := by
      apply hcross
      rw [commutator_comm]
      exact commutator_mem_commutator hm ⟨x.property,hx⟩
    change (y : FreeAmalgam Rg) *
        (embedM Rg m * (x : FreeAmalgam Rg) * (embedM Rg m)⁻¹ / (x : FreeAmalgam Rg)) =
      (embedM Rg m * (x : FreeAmalgam Rg) * (embedM Rg m)⁻¹ / (x : FreeAmalgam Rg)) *
        (y : FreeAmalgam Rg)
    simpa only [div_eq_mul_inv,commutatorElement_def] using hZaC hz y y.property
  apply linearized_fixed_codim_le_two (forwardSpanCentralAction Rg c) A
    ((C.subgroupOf P).map q) hfixed
  have hi : ((C.subgroupOf P).map q).index ≤ C.relIndex P := Nat.le_of_dvd
    (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    ((C.subgroupOf P).index_map_dvd (QuotientGroup.mk'_surjective (center P)))
  exact hi.trans_eq (borel_four_span_core_index h e hz hk u hR p)

include h e hz hk in
/-- The whole opposite selected span has the same even three-pair image as
the midpoint radius, under the original cubic map. Its image has order four. -/
theorem borel_four_opposed_span_image
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    ∃ v : S, CubicAction.graphImage h e hz hk
      (localZSpan Rg (alpha Rg) (p.walk.getVert 2)) = D0.map (MulAut.conj v).toMonoidHom := by
  let c := p.walk.getVert 2
  let P := localZSpan Rg (alpha Rg) c
  let A := P.comap (embedM Rg)
  have hl : p.walk.length = 4 := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hca : (cosetGraph Rg).dist c (alpha Rg) = 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)]
  have hPV : P ≤ V Rg c := localZSpan_le_V Rg (by rw [SimpleGraph.dist_comm]; exact hca.le)
  have hPQ := hPV.trans ((sourceGeometry h).V_le_Q (distance_gt_two h e hz hk) c hc)
  have hPG : P ≤ stabilizer Rg (alpha Rg) :=
    hPQ.trans (Q_le_stabilizer_of_dist_two Rg c (alpha Rg) hc hca)
  have hm : A.map (embedM Rg) = P :=
    map_comap_eq_self (hPG.trans_eq (stabilizer_m_base Rg))
  have htwo : IsPGroup 2 P :=
    (Q_isPGroup Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le c hc).to_le hPQ
  have hcard : Nat.card (CubicAction.graphImage h e hz hk P) = 4 := by
    change Nat.card (A.map π) = 4
    rw [CubicAction.permutation_image_card_of_two h e hz hk A
      (htwo.comap_of_injective _ (embedM_injective Rg)),
      ←relIndex_map_map_of_injective _ _ (embedM_injective Rg),hm,
      ←Q_alpha Rg h.relative_radical.isPGroup h.relative_radical.twoCore_le]
    exact (borel_four_opposed_spans h e hz hk u hR p).2.1
  obtain ⟨v,hv,_,_,_⟩ := borel_four_midpoint_radius_image h e hz hk u hR p
  refine ⟨v,eq_of_le_of_card_ge ((map_mono (comap_mono hPV)).trans_eq hv) ?_⟩
  rw [card_map_of_injective (MulAut.conj v).injective,D0_card,hcard]

include h e hz hk in
/-- The full opposite-span actor has fixed codimension exactly two in the
forward span's actual central quotient. The original cubic projection is
retained; no identification of its odd kernel with the two-core is used. -/
theorem borel_four_opposed_span_fixed_codim_eq_two
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z) :
    let c := p.walk.getVert 2
    letI := selected_span_central_quotient_elementary h e hz hk
      (distance_gt_two h e hz hk) c (by
        rw [SimpleGraph.dist_comm,p.dist_start (by
          have hl := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
          omega)])
    fixedCodim (Offenders.linearize (forwardSpanCentralAction Rg c))
      ((localZSpan Rg (alpha Rg) c).comap (embedM Rg)) = 2 := by
  let c := p.walk.getVert 2
  let A := (localZSpan Rg (alpha Rg) c).comap (embedM Rg)
  have hb := distance_gt_two h e hz hk
  have hl : p.walk.length = 4 := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
  have hd : (cosetGraph Rg).dist c (alpha Rg) ≤ 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)]
  let := finite_stabilizer Rg (alpha Rg)
  have hPG : localZSpan Rg c (alpha Rg) ≤ stabilizer Rg (alpha Rg) :=
    (localZSpan_le_V Rg hd).trans ((sourceGeometry h).V_local _ rfl hb)
  let : Finite (localZSpan Rg c (alpha Rg)) :=
    Finite.of_injective (inclusion hPG) (inclusion_injective _)
  let := selected_span_central_quotient_elementary h e hz hk hb c hd
  let σ := Offenders.linearize (forwardSpanCentralAction Rg c)
  change fixedCodim σ A = 2
  have hnon := (large_remaining_four_span_configuration h e hz hk
    (borel_distance_eq_four h e hz hk u hR) u (Or.inr hR) p
    (borel_four_critical_images_large h e hz hk u hR p)).1
  have hker : σ.ker ≤ (π).ker := by
    rw [CubicAction.projection_kernel]
    apply le_trans ?_ (selected_span_central_action_kernel_le_extension h e hz hk hb p hnon)
    intro m hm
    apply MonoidHom.mem_ker.mpr
    apply MulEquiv.ext
    intro v
    exact congrArg Additive.toMul (LinearMap.congr_fun hm (Additive.ofMul v))
  obtain ⟨v,hv⟩ := borel_four_opposed_span_image h e hz hk u hR p
  change A.map π = D0.map (MulAut.conj v).toMonoidHom at hv
  have hcard : Nat.card (A.map π) = 4 := by
    rw [hv,card_map_of_injective (MulAut.conj v).injective,D0_card]
  have hAlt : A.map π ≤ alternatingGroup (Fin 6) := by
    rw [hv]
    exact (map_mono (show D0 ≤ alternatingGroup (Fin 6) from inf_le_right)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top v))
  obtain ⟨a,ha2⟩ := exists_prime_orderOf_dvd_card' (G := A.map π) 2 (by rw [hcard]; decide)
  have ha : orderOf (a : S) = 2 := (orderOf_injective _ (A.map π).subtype_injective a).trans ha2
  obtain ⟨m,hm,heq⟩ := a.property
  have hlo := EvenLift.fixedCodim_lower π (CubicEven.projection_surjective h e hz hk)
    σ hker m (heq.symm ▸ hAlt a.property) (heq.symm ▸ ha)
  have hF := Submodule.finrank_mono (fixedSpace_antitone σ (zpowers_le.mpr hm))
  have hmF := fixedCodim_add_finrank σ (zpowers m)
  have hAF := fixedCodim_add_finrank σ A
  have hup := borel_four_opposed_span_fixed_codim h e hz hk u hR p
  change fixedCodim σ A ≤ 2 at hup
  omega

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
