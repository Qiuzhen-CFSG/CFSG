module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.ReciprocalActors
public import Theory.Representation.BinaryConjugationSection.Ambient
public import Theory.Representation.BinaryConjugationSection.FixedIndex

/-!
# Failure of factorization on the reciprocal moved quotient

The original large critical path and its large backward path supply the
two reciprocal span covers. The intersection commutator identities bound
each literal fixed index by the opposite actor order. Comparing those
two orders produces an offender at one reciprocal vertex. Its elementary
nontrivial actor is the actual span image, and its module is exactly
(Vcirc B)/B with the original quotient coordinates.

Both radius-core fixedness premises remain explicit for their independent
source producers. The final consumer retains an actual large critical
path starting at the FF vertex for the later natural/Thompson argument.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (5.12)(2), printed p.926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

variable (s : FullSymmetricAction h e hz hn d)

include s in
theorem reciprocal_large_moving_radius_le_span_at
    (hc : DistanceTwo.CentralLayer d) (hb : replacementDistance h d = 4)
    {a z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical a)) :
    Vcirc d.radical a ≤ localZSpan d.radical (p.walk.getVert 2) a ⊔ Z d.radical a := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hbase : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have base := large_moving_radius_le_selected_span s hc hb
    (z := act d.radical g⁻¹ z)
  rw [←hbase] at base
  have hlarge₀ : 4 ≤ (Q d.radical (act d.radical g⁻¹ z)).relIndex
      (Z d.radical (act d.radical g⁻¹ a)) := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj _).injective]
    exact hlarge
  have hm := base (p.act g⁻¹) hlarge₀
  simp only [CriticalPath.act,actWalk_getVert] at hm
  rw [Vcirc_act,LocalCommutator.CriticalCase.localZSpan_act,Z_act,←Subgroup.map_sup] at hm
  exact (map_le_map_iff_of_injective (MulAut.conj _).injective).mp hm

include e hz hn in
theorem large_reciprocal_moving_radius_span_cover_knownSimple
    (hb : replacementDistance h d = 4) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    Vcirc d.radical (alpha d.radical) ≤
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical) ⊔ Z d.radical (alpha d.radical) ∧
    Vcirc d.radical (p.walk.getVert 2) ≤
      localZSpan d.radical (alpha d.radical) (p.walk.getVert 2) ⊔ Z d.radical (p.walk.getVert 2) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  refine ⟨large_moving_radius_le_selected_span s hc hb p hlarge,?_⟩
  obtain ⟨W,hFE,hWZ,hi,hcomm,hWne,hexact,t,c,hat,hct,hgen,hgenQ,
    q,hq1,hq2,hq3,hidx,hstrict,htransport,hmove,hDexact,hWN,hfix,hback⟩ :=
    full_seed_backward_large_knownSimple (e := e) (hz := hz) (hn := hn) hb p hlarge
  let qr : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) c :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc q⟩
  have hrlarge := reverse_critical_image_four_le s hc (replacementDistance_pos h d) q hback
  have hh := reciprocal_large_moving_radius_le_span_at s hc hb qr hrlarge
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hmiddle : qr.walk.getVert 2 = alpha d.radical := by
    change q.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,hql]
    exact hq2
  rwa [hmiddle] at hh

private theorem reciprocal_modulo_index_le_of_cover
    {F : Type*} [Group F] [Finite F] (M P A B K : Subgroup F) [B.Normal]
    (hMP : M ≤ P ⊔ B) (hcomm : ⁅P ⊓ K,A⁆ ≤ B) :
    (centralizerModulo M A B).relIndex M ≤ K.relIndex P := by
  let π := QuotientGroup.mk' B
  have hB : B.map π = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by
    rw [QuotientGroup.ker_mk'])
  have hm : M.map π ≤ P.map π := by
    have hh := map_mono (f := π) hMP
    rwa [Subgroup.map_sup,hB,sup_bot_eq] at hh
  rw [NoncentralChiefRefinement.SymmetricSixBudget.centralizerModulo_relIndex_eq]
  exact (relIndex_le_of_le_right hm
    ((centralizer (A.map π : Set (F ⧸ B))).subgroupOf (P.map π)).index_ne_zero_of_finite).trans
      (by rw [←NoncentralChiefRefinement.SymmetricSixBudget.centralizerModulo_relIndex_eq]
          exact NoncentralChiefRefinement.SymmetricSixBudget.centralizerModulo_relIndex_le_of_commutator
            P A B K hcomm)

/-- The fixed index on the source moved quotient under the reciprocal span,
computed inside the original finite vertex stabilizer modulo B. -/
def reciprocalMovedFixedIndex
    (hb : 2 < replacementDistance h d) (a c : Vertex d.radical)
    (ha : color d.radical a = false) : ℕ :=
  let S := stabilizer d.radical a
  let B₀ := (B d.radical a ((replacementGeometry h d).Z_normal a)).subgroupOf S
  let M₀ := (reciprocalMovedNumerator h d a).subgroupOf S
  let A₀ := (localZSpan d.radical a c).subgroupOf S
  letI : B₀.Normal := normal_subgroupOf_of_le_normalizer
    (Escape.Propagation.Rigidity.B_normalized hb a ha)
  (centralizerModulo M₀ A₀ B₀).relIndex M₀

theorem reciprocal_moved_fixed_index_le_span_index
    (hb : 2 < replacementDistance h d) {a c : Vertex d.radical}
    (ha : color d.radical a = false) (hc : color d.radical c = false)
    (hd : (cosetGraph d.radical).dist a c = 2)
    (hfixedC : ⁅V d.radical c,Q d.radical c⁆ ≤ fixedCore d.radical c)
    (hspan : Vcirc d.radical a ≤ localZSpan d.radical c a ⊔ Z d.radical a) :
    reciprocalMovedFixedIndex (h := h) hb a c ha ≤
      (Q d.radical c).relIndex (localZSpan d.radical c a) := by
  let S := stabilizer d.radical a
  let B₀ := B d.radical a ((replacementGeometry h d).Z_normal a)
  let M₀ := reciprocalMovedNumerator h d a
  let P₁ := localZSpan d.radical c a
  let P₂ := localZSpan d.radical a c
  have hVS : V d.radical a ≤ S := (V_le_Q d.radical ha hb).trans (fun _ hx => hx.1)
  have hZB : Z d.radical a ≤ B₀ := Escape.EdgeTransfer.Z_le_B hb a ha
  have hBS : B₀ ≤ S := (Escape.EdgeTransfer.B_le_radius hb a ha).trans hVS
  have hPS : P₁ ≤ S := (localZSpan_le_V d.radical (by rw [SimpleGraph.dist_comm,hd])).trans hVS
  have hMS : M₀ ≤ S := (reciprocal_moved_numerator_le_radius (h := h) hb ha).trans hVS
  have hcover : M₀ ≤ P₁ ⊔ B₀ :=
    sup_le (hspan.trans (sup_le_sup_left hZB P₁)) le_sup_right
  let : Finite S := finite_stabilizer d.radical a
  let : (B₀.subgroupOf S).Normal := normal_subgroupOf_of_le_normalizer
    (Escape.Propagation.Rigidity.B_normalized hb a ha)
  have hcover₀ : M₀.subgroupOf S ≤ P₁.subgroupOf S ⊔ B₀.subgroupOf S := by
    rw [←subgroupOf_sup hPS hBS]
    exact comap_mono hcover
  have hcross : ⁅P₁ ⊓ Q d.radical c,P₂⁆ ≤ B₀ := by
    rw [commutator_comm]
    exact ((commutator_mono le_rfl inf_le_right).trans
      (reciprocal_span_core_eq_seed_of_radius_fixed (h := h) hb hc ha
        (by rwa [SimpleGraph.dist_comm]) hfixedC).2).trans hZB
  have hcross₀ : ⁅P₁.subgroupOf S ⊓ (Q d.radical c).subgroupOf S,P₂.subgroupOf S⁆ ≤
      B₀.subgroupOf S := by
    apply commutator_le.mpr
    intro x hx y hy
    exact hcross (commutator_mem_commutator ⟨hx.1,hx.2⟩ hy)
  have hi := reciprocal_modulo_index_le_of_cover (M₀.subgroupOf S) (P₁.subgroupOf S)
    (P₂.subgroupOf S) (B₀.subgroupOf S) ((Q d.radical c).subgroupOf S) hcover₀ hcross₀
  rw [relIndex_subgroupOf hPS] at hi
  exact hi

include e hz hn in
/-- The original large path supplies the span cover in both directions;
one of its actual reciprocal actor indices satisfies the offender inequality. -/
theorem large_reciprocal_fixed_index_alternative_knownSimple
    (hb : replacementDistance h d = 4) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical)))
    (hfixedA : ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical))
    (hfixedC : ⁅V d.radical (p.walk.getVert 2),Q d.radical (p.walk.getVert 2)⁆ ≤
      fixedCore d.radical (p.walk.getVert 2)) :
    let hb2 : 2 < replacementDistance h d := by omega
    let hc : color d.radical (p.walk.getVert 2) = false :=
      (p.vertex_color (by
        have hl : p.walk.length = 4 := p.length_eq_b.trans hb
        omega)).mpr (by decide)
    reciprocalMovedFixedIndex (h := h) hb2 (alpha d.radical) (p.walk.getVert 2) rfl ≤
      (Q d.radical (alpha d.radical)).relIndex (localZSpan d.radical (alpha d.radical) (p.walk.getVert 2)) ∨
    reciprocalMovedFixedIndex (h := h) hb2 (p.walk.getVert 2) (alpha d.radical) hc ≤
      (Q d.radical (p.walk.getVert 2)).relIndex (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)) := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hc : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph d.radical).dist (alpha d.radical) (p.walk.getVert 2) = 2 := p.dist_start (by omega)
  obtain ⟨hspanA,hspanC⟩ := large_reciprocal_moving_radius_span_cover_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge
  have hiA := reciprocal_moved_fixed_index_le_span_index (h := h) hb2 rfl hc hd hfixedC hspanA
  have hiC := reciprocal_moved_fixed_index_le_span_index (h := h) hb2 hc rfl
    (by rwa [SimpleGraph.dist_comm]) hfixedA hspanC
  rcases le_total
      ((Q d.radical (p.walk.getVert 2)).relIndex (localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)))
      ((Q d.radical (alpha d.radical)).relIndex (localZSpan d.radical (alpha d.radical) (p.walk.getVert 2))) with h | h
  · exact Or.inl (hiA.trans h)
  · exact Or.inr (hiC.trans h)

open Representation.BinaryOffender

private theorem reciprocal_section_offender_of_index
    {F D W : Type*} [Group F] [Group D] [Finite D]
    [AddCommGroup W] [Module (ZMod 2) W]
    (H M B A : Subgroup F) [Finite H] [(B.subgroupOf H).Normal]
    (ρ : Representation (ZMod 2) D W) (π : H →* D)
    (c : Representation.BinaryConjugationSection H M B (ρ.comp π))
    (hAH : A ≤ H) (hEA : IsElementaryTwo ((A.subgroupOf H).map π))
    (hindex : (centralizerModulo (M.subgroupOf H) (A.subgroupOf H)
      (B.subgroupOf H)).relIndex (M.subgroupOf H) ≤ Nat.card ((A.subgroupOf H).map π)) :
    IsOffender ρ ((A.subgroupOf H).map π) := by
  let c₀ := c.subgroupOf H le_rfl
  let e := (subgroupOfEquivOfLe (le_rfl : H ≤ H)).toMonoidHom
  let π₀ := π.comp e
  have hAA : A.subgroupOf H ≤ H.subgroupOf H := fun _ hx => hAH hx
  have himage : ((A.subgroupOf H).subgroupOf (H.subgroupOf H)).map π₀ =
      (A.subgroupOf H).map π := by
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨e x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨⟨x,x.property⟩,hx,rfl⟩
  have hfix := Representation.BinaryConjugationSection.fixed_index_image ρ π₀ c₀
    (A.subgroupOf H) hAA
  rw [commutatorPreimage_eq_inf_comap_centralizer,himage] at hfix
  change (centralizerModulo (M.subgroupOf H) (A.subgroupOf H)
    (B.subgroupOf H)).relIndex (M.subgroupOf H) = _ at hfix
  have hp := hfix.symm.le.trans hindex
  rw [hEA.card_eq_two_pow_rank] at hp
  exact ⟨hEA,(Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp⟩

/-- The literal moved quotient carries a binary FF representation of the local quotient,
with its original quotient coordinates. -/
@[expose] def ReciprocalMovedFF
    (hb : 2 < replacementDistance h d) (a : Vertex d.radical)
    (ha : color d.radical a = false)
    (hfixedA : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) : Prop :=
    letI := Q_normal d.radical a
    letI := reciprocal_B_normal_moved (h := h) hb ha
    letI := reciprocal_moved_quotient_elementary_of_fixed (h := h) hb ha hfixedA
    ∃ (ρ : Representation (ZMod 2)
        ((stabilizer d.radical a) ⧸ (Q d.radical a).subgroupOf (stabilizer d.radical a))
        (Additive ((reciprocalMovedNumerator h d a) ⧸
          (B d.radical a ((replacementGeometry h d).Z_normal a)).subgroupOf
            (reciprocalMovedNumerator h d a))))
      (sec : Representation.BinaryConjugationSection (stabilizer d.radical a)
        (reciprocalMovedNumerator h d a)
        (B d.radical a ((replacementGeometry h d).Z_normal a))
        (ρ.comp (QuotientGroup.mk' ((Q d.radical a).subgroupOf (stabilizer d.radical a))))),
      IsFFModule ρ ∧ ∀ v : reciprocalMovedNumerator h d a, (sec.coordinates v).toAdd =
        Additive.ofMul (QuotientGroup.mk'
          ((B d.radical a ((replacementGeometry h d).Z_normal a)).subgroupOf
            (reciprocalMovedNumerator h d a)) v)

/-- A genuine FF witness on the literal source moved quotient. The actor is
the image of the reciprocal span in the original local quotient. -/
theorem reciprocal_moved_quotient_ff_of_bound
    (hb : 2 < replacementDistance h d) {a c : Vertex d.radical}
    (ha : color d.radical a = false) (hc : color d.radical c = false)
    (hd : (cosetGraph d.radical).dist a c = 2)
    (hfixedA : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hfixedC : ⁅V d.radical c,Q d.radical c⁆ ≤ fixedCore d.radical c)
    (hne : ¬ localZSpan d.radical a c ≤ Q d.radical a)
    (hindex : reciprocalMovedFixedIndex (h := h) hb a c ha ≤
      (Q d.radical a).relIndex (localZSpan d.radical a c)) :
    ReciprocalMovedFF (h := h) hb a ha hfixedA := by
  let := Q_normal d.radical a
  let := reciprocal_B_normal_moved (h := h) hb ha
  let := reciprocal_moved_quotient_elementary_of_fixed (h := h) hb ha hfixedA
  let H := stabilizer d.radical a
  let := finite_stabilizer d.radical a
  let : ((B d.radical a ((replacementGeometry h d).Z_normal a)).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (Escape.Propagation.Rigidity.B_normalized hb a ha)
  obtain ⟨ρ,sec,hcoordinates⟩ := reciprocal_moved_quotient_action_of_fixed (h := h) hb ha hfixedA
  obtain ⟨hel,hcard,hbot⟩ := reciprocal_actor_image_data_of_radius_fixed (h := h) hb ha hc hd hfixedC
  have hEA : IsElementaryTwo
      (((localZSpan d.radical a c).subgroupOf H).map (QuotientGroup.mk' ((Q d.radical a).subgroupOf H))) :=
    ⟨fun hh => hne (hbot.mp hh),hel⟩
  have hPH : localZSpan d.radical a c ≤ H := (localZSpan_le_Q d.radical hc hd.le hb).trans
    (Q_le_stabilizer_of_dist_le_two c a hc ha (by rw [SimpleGraph.dist_comm,hd]))
  refine ⟨ρ,sec,?_,hcoordinates⟩
  refine ⟨((localZSpan d.radical a c).subgroupOf H).map
    (QuotientGroup.mk' ((Q d.radical a).subgroupOf H)),?_⟩
  apply reciprocal_section_offender_of_index H (reciprocalMovedNumerator h d a)
    (B d.radical a ((replacementGeometry h d).Z_normal a)) (localZSpan d.radical a c)
    ρ (QuotientGroup.mk' ((Q d.radical a).subgroupOf H)) sec hPH hEA
  rw [hcard]
  exact hindex

include e hz hn in
/-- The two reciprocal spans attached to a large critical path are nonabelian.
The second is selected by reversing the large backward path. -/
theorem large_reciprocal_spans_nonabelian_knownSimple
    (hb : replacementDistance h d = 4) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical))) :
    ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥ ∧
    ⁅localZSpan d.radical (alpha d.radical) (p.walk.getVert 2),
      localZSpan d.radical (alpha d.radical) (p.walk.getVert 2)⁆ ≠ ⊥ := by
  let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  refine ⟨large_image_selected_span_nonabelian s hc hb p hlarge,?_⟩
  obtain ⟨W,hFE,hWZ,hi,hcomm,hWne,hexact,t,c,hat,hct,hgen,hgenQ,
    q,hq1,hq2,hq3,hidx,hstrict,htransport,hmove,hDexact,hWN,hfix,hback⟩ :=
    full_seed_backward_large_knownSimple (e := e) (hz := hz) (hn := hn) hb p hlarge
  let qr : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) c :=
    ⟨q.end_color,q.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc q⟩
  have hrlarge := reverse_critical_image_four_le s hc (replacementDistance_pos h d) q hback
  have hh := large_image_selected_span_nonabelian s hc hb qr hrlarge
  have hql : q.walk.length = 4 := q.length_eq_b.trans hb
  have hmiddle : qr.walk.getVert 2 = alpha d.radical := by
    change q.walk.reverse.getVert 2 = _
    rw [SimpleGraph.Walk.getVert_reverse,hql]
    exact hq2
  rwa [hmiddle] at hh


include e hz hn in
/-- A large critical path supplies a genuine FF witness at one of its two
reciprocal vertices, with no actor or offender premise left to the caller. -/
theorem large_reciprocal_moved_ff_alternative_knownSimple
    (hb : replacementDistance h d = 4) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical)))
    (hfixedA : ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical))
    (hfixedC : ⁅V d.radical (p.walk.getVert 2),Q d.radical (p.walk.getVert 2)⁆ ≤
      fixedCore d.radical (p.walk.getVert 2)) :
    let hb2 : 2 < replacementDistance h d := by omega
    let hc : color d.radical (p.walk.getVert 2) = false :=
      (p.vertex_color (by
        have hl : p.walk.length = 4 := p.length_eq_b.trans hb
        omega)).mpr (by decide)
    ReciprocalMovedFF (h := h) hb2 (alpha d.radical) rfl hfixedA ∨
      ReciprocalMovedFF (h := h) hb2 (p.walk.getVert 2) hc hfixedC := by
  have hb2 : 2 < replacementDistance h d := by omega
  have hl : p.walk.length = 4 := p.length_eq_b.trans hb
  have hc : color d.radical (p.walk.getVert 2) = false :=
    (p.vertex_color (by omega)).mpr (by decide)
  have hd : (cosetGraph d.radical).dist (alpha d.radical) (p.walk.getVert 2) = 2 :=
    p.dist_start (by omega)
  obtain ⟨hnonA,hnonC⟩ := large_reciprocal_spans_nonabelian_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge
  have hneA := reciprocal_nonabelian_span_not_le_seed_core hc hnonA
  have hneC := reciprocal_nonabelian_span_not_le_seed_core rfl hnonC
  rcases large_reciprocal_fixed_index_alternative_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge hfixedA hfixedC with hi | hi
  · exact Or.inl (reciprocal_moved_quotient_ff_of_bound hb2 rfl hc hd hfixedA hfixedC hneC hi)
  · exact Or.inr (reciprocal_moved_quotient_ff_of_bound hb2 hc rfl
      (by rwa [SimpleGraph.dist_comm]) hfixedC hfixedA hneA hi)

include e hz hn in
/-- The FF alternative is realized at the start of an actual large critical
path. This retains the source path for the subsequent natural and Thompson
arguments, whichever reciprocal vertex supplied the offender inequality. -/
theorem large_reciprocal_moved_ff_at_large_path_knownSimple
    (hb : replacementDistance h d = 4) {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical)))
    (hfixedA : ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical))
    (hfixedC : ⁅V d.radical (p.walk.getVert 2),Q d.radical (p.walk.getVert 2)⁆ ≤
      fixedCore d.radical (p.walk.getVert 2)) :
    ∃ (a z' : Vertex d.radical)
      (q : CriticalPath d.radical (replacementGeometry h d) a z'),
      4 ≤ (Q d.radical z').relIndex (Z d.radical a) ∧
      ∃ hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a,
        ReciprocalMovedFF (h := h) (by omega) a q.start_color hfixed := by
  rcases large_reciprocal_moved_ff_alternative_knownSimple
    (e := e) (hz := hz) (hn := hn) hb p hlarge hfixedA hfixedC with hff | hff
  · exact ⟨alpha d.radical,z,p,hlarge,hfixedA,hff⟩
  · let s := fullSymmetricAction_knownSimple h e hz hn d (by omega)
    have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
    obtain ⟨W,hFE,hWZ,hi,hcomm,hWne,hexact,t,c,hat,hct,hgen,hgenQ,
      q,hq1,hq2,hq3,hidx,hstrict,htransport,hmove,hDexact,hWN,hfix,hback⟩ :=
      full_seed_backward_large_knownSimple (e := e) (hz := hz) (hn := hn) hb p hlarge
    let qr : CriticalPath d.radical (replacementGeometry h d) (p.walk.getVert 2) c :=
      ⟨q.end_color,q.walk.reverse,
        by rw [SimpleGraph.Walk.length_reverse,q.shortest,SimpleGraph.dist_comm],
        critical_reverse_pair s hc q⟩
    have hrlarge := reverse_critical_image_four_le s hc (replacementDistance_pos h d) q hback
    exact ⟨p.walk.getVert 2,c,qr,hrlarge,hfixedC,hff⟩

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
