module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.RadiusGrowth
public import Theory.GroupTheory.CentralizerInjectiveImage
public import Theory.GroupTheory.PResidual.PrimeSection

/-!
# The exact-four radius kernel and its fixed quotient classes

When a critical radius has opposite-kernel index at most four, the doubled
seed-index bound is saturated. Its full kernel is therefore exactly the
centralizer of the opposite full seed. On the actual radius quotient by
the initial seed the fixed index is two.

Multiplicativity of relative indices identifies the preimage of this
quotient fixed subgroup with the seed times the full radius kernel. Thus
every fixed quotient class has a fixed representative, and the preimage's
commutator with the opposite seed is exactly the original critical line,
of order two. All maps are the original replacement embeddings. No splitting
or deletion of the central line is used for the cover of order thirty-two.

These are equality-case calculations for the small-radius branch of MS93
(5.11)(1), printed pp.923--924. They do not exclude that branch: the
source-selected shifts, intermediate R₄/R₆ noncentrality, and both terminal
arguments remain with qt-e-ms-small-a6-exhaustion-large-distance. The original
replacement applications below discharge the full symmetric marking and
central-layer premises; unconditional whole-core reconstruction remains
with qt-e-ms-small-a6-reconstruction.
-/

public noncomputable section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)


include s in
private theorem seed_fixed_eq_kernel (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    Z d.radical a ⊓ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ Q d.radical a' := by
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1,?_⟩
    rw [← C_eq_Q s hc a' p.end_color]
    exact ⟨Z_le_stabilizer_of_dist_le a _ p.critical.1.le hx.1,hx.2⟩
  · exact inf_le_inf_left _ (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a' p.end_color)))

include s in
private theorem base_small_radius_indices (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (V d.radical (alpha d.radical)) ≤ 4) :
    let A := (Z d.radical a').comap (embedM d.radical)
    let K := (Q d.radical a').comap (embedM d.radical)
    (centralizer (A : Set d.overgroup)).relIndex (radiusSeed d) = 2 ∧
      (centralizer (A : Set d.overgroup)).relIndex (radiusPreimage d) = 4 ∧
      radiusPreimage d ⊓ K = radiusPreimage d ⊓ centralizer (A : Set d.overgroup) := by
  let f := embedM d.radical
  let A := (Z d.radical a').comap f
  let K := (Q d.radical a').comap f
  have hAG : Z d.radical a' ≤ f.range :=
    (critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical)
      rfl (replacementDistance_pos h d) p.critical).trans_eq (stabilizer_m_base d.radical)
  have hmA : A.map f = Z d.radical a' := map_comap_eq_self hAG
  have hmZ : (radiusSeed d).map f = Z d.radical (alpha d.radical) :=
    map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))
  have hA : ¬ A ≤ pCore 2 d.overgroup := by
    intro hh
    apply (critical_reverse_pair s hc p).2
    rw [←hmA,Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)]
    exact map_mono hh
  have hidx : (centralizer (A : Set d.overgroup)).relIndex (radiusSeed d) =
      (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) := by
    calc
      _ = ((radiusSeed d).map f ⊓ centralizer (A.map f : Set (FreeAmalgam d.radical))).relIndex
          ((radiusSeed d).map f) := by
        rw [map_inf_centralizer_of_injective f (embedM_injective d.radical),
          relIndex_map_map_of_injective _ _ (embedM_injective d.radical),inf_relIndex_left]
      _ = _ := by rw [hmA,hmZ,seed_fixed_eq_kernel s hc p,inf_relIndex_left]
  have hKA : K ≤ centralizer (A : Set d.overgroup) := by
    intro x hx y hy
    apply embedM_injective d.radical
    simp only [map_mul]
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color))) hx _ hy
  have hKidx : K.relIndex (radiusPreimage d) ≤ 4 := by
    rw [relIndex_comap,radius_comap_map (h := h) hb]
    exact hsmall
  have hne : (centralizer (A : Set d.overgroup)).relIndex (radiusSeed d) ≠ 1 := by
    rw [hidx]
    exact fun hi => p.critical.2 (relIndex_eq_one.mp hi)
  have hpos : 0 < (centralizer (A : Set d.overgroup)).relIndex (radiusSeed d) :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hmon : (centralizer (A : Set d.overgroup)).relIndex (radiusPreimage d) ≤
      K.relIndex (radiusPreimage d) := relIndex_le_of_le_left hKA index_ne_zero_of_finite
  have hupper := hmon.trans hKidx
  have hlower := radius_actor_index_two_mul_seed_le s hc hb A hA
  have hseed : (centralizer (A : Set d.overgroup)).relIndex (radiusSeed d) = 2 := by omega
  have hradius : (centralizer (A : Set d.overgroup)).relIndex (radiusPreimage d) = 4 := by omega
  have hkernel : K.relIndex (radiusPreimage d) = 4 := by
    omega
  refine ⟨hseed,hradius,?_⟩
  apply le_antisymm (inf_le_inf_left _ hKA)
  have hi := relIndex_mul_relIndex (radiusPreimage d ⊓ K)
    (radiusPreimage d ⊓ centralizer (A : Set d.overgroup)) (radiusPreimage d)
    (inf_le_inf_left _ hKA) inf_le_left
  rw [inf_relIndex_left,inf_relIndex_left,hradius,hkernel] at hi
  exact relIndex_eq_one.mp (by omega :
    (radiusPreimage d ⊓ K).relIndex (radiusPreimage d ⊓ centralizer (A : Set d.overgroup)) = 1)

include s in
/-- Saturation of the radius bound identifies the full kernel with the actual
fixed subgroup, without requiring the radius to lie in the opposite stabilizer. -/
theorem small_radius_fixed_kernel (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (V d.radical a) ≤ 4) :
    V d.radical a ⊓ Q d.radical a' =
      V d.radical a ⊓ centralizer (Z d.radical a' : Set (FreeAmalgam d.radical)) := by
  have hbase {b : Vertex d.radical}
      (q : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) b)
      (hs : (Q d.radical b).relIndex (V d.radical (alpha d.radical)) ≤ 4) :
      V d.radical (alpha d.radical) ⊓ Q d.radical b =
        V d.radical (alpha d.radical) ⊓ centralizer (Z d.radical b : Set (FreeAmalgam d.radical)) := by
    have he := (base_small_radius_indices s hc hb q hs).2.2
    have hm := congrArg (Subgroup.map (embedM d.radical)) he
    rw [map_inf _ _ _ (embedM_injective d.radical),
      ←map_inf_centralizer_of_injective _ (embedM_injective d.radical),
      radius_comap_map (h := h) hb] at hm
    have hZG : Z d.radical b ≤ (embedM d.radical).range :=
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical)
        rfl (replacementDistance_pos h d) q.critical).trans_eq (stabilizer_m_base d.radical)
    rw [map_comap_eq_self hZG,map_comap_eq] at hm
    have hVG : V d.radical (alpha d.radical) ≤ (embedM d.radical).range :=
      ((replacementGeometry h d).V_local _ rfl hb).trans_eq (stabilizer_m_base d.radical)
    rwa [←inf_assoc,inf_eq_left.mpr hVG] at hm
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical p.start_color
  have hstart : act d.radical g⁻¹ a = alpha d.radical := by
    rw [hg,act_mVertex,mul_inv_cancel]
    rfl
  have q := p.act g⁻¹
  rw [hstart] at q
  have hs : (Q d.radical (act d.radical g⁻¹ a')).relIndex
      (V d.radical (alpha d.radical)) ≤ 4 := by
    rw [←hstart,Q_act,V_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
    exact hsmall
  have he := hbase q hs
  rw [←hstart,V_act,Q_act,Z_act,
    map_inf_centralizer_of_injective _ (MulAut.conj (g⁻¹)⁻¹).injective] at he
  rw [←map_inf _ _ _ (MulAut.conj (g⁻¹)⁻¹).injective] at he
  exact le_antisymm
    ((map_le_map_iff_of_injective (MulAut.conj (g⁻¹)⁻¹).injective).mp he.le)
    ((map_le_map_iff_of_injective (MulAut.conj (g⁻¹)⁻¹).injective).mp he.ge)

include s in
/-- In the exact-four case the endpoint seed has fixed index exactly two
on the literal radius quotient by its full initial seed. -/
theorem small_radius_section_index (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (V d.radical (alpha d.radical)) ≤ 4) :
    SymmetricSixBudget.sectionIndex ((Z d.radical a').comap (embedM d.radical))
      ⟨radiusSeed d,(inferInstance : (radiusSeed d).Normal)⟩ ⟨radiusPreimage d,(inferInstance : (radiusPreimage d).Normal)⟩ = 2 := by
  let B : NormalNode d.overgroup := ⟨radiusSeed d,(inferInstance : (radiusSeed d).Normal)⟩
  let C : NormalNode d.overgroup := ⟨radiusPreimage d,(inferInstance : (radiusPreimage d).Normal)⟩
  let A := (Z d.radical a').comap (embedM d.radical)
  have hA : ¬ A ≤ pCore 2 d.overgroup := by
    intro hh
    apply (critical_reverse_pair s hc p).2
    have hZG : Z d.radical a' ≤ (embedM d.radical).range :=
      (critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical)
        rfl (replacementDistance_pos h d) p.critical).trans_eq (stabilizer_m_base d.radical)
    rw [←map_comap_eq_self hZG,Q_alpha d.radical (replacement_radical_isPGroup h d)
      (replacement_core_le_radical h d)]
    exact map_mono hh
  have hlo := section_index_two_le s B C (radius_moving_not_le_seed s hc hb) A hA
  have hhi := SymmetricSixBudget.sectionIndex_mul_lower_le A B C radiusSeed_le_radiusPreimage
  obtain ⟨hi,hj,_⟩ := base_small_radius_indices s hc hb p hsmall
  change (centralizer (A : Set d.overgroup)).relIndex B.val = 2 at hi
  change (centralizer (A : Set d.overgroup)).relIndex C.val = 4 at hj
  rw [hi,hj] at hhi
  change SymmetricSixBudget.sectionIndex A B C = 2
  omega


private theorem section_index_eq_modulo {H : Type*} [Group H] [Finite H]
    (A : Subgroup H) (B C : NormalNode H) :
    SymmetricSixBudget.sectionIndex A B C =
      (centralizerModulo C.val A B.val).relIndex C.val := by
  let ρ := sectionAction B C
  let : MulDistribMulAction H (Section B C) := MulDistribMulAction.compHom _ ρ
  let N := B.val.subgroupOf C.val
  let F := FixedPoints.subgroup A (Section B C)
  have he : F.comap (QuotientGroup.mk' N) =
      (centralizerModulo C.val A B.val).subgroupOf C.val := by
    ext c
    constructor
    · intro hc
      apply mem_centralizerModulo_iff.mpr
      refine ⟨c.property,fun a ha => ?_⟩
      have hh := hc ⟨a,ha⟩
      change QuotientGroup.mk' N (MulAut.conjNormal a c) = QuotientGroup.mk' N c at hh
      have hm := QuotientGroup.eq_iff_div_mem.mp hh
      change a*c.val*a⁻¹/c.val ∈ B.val at hm
      simpa only [commutatorElement_def,div_eq_mul_inv,Subgroup.subtype_apply] using hm
    · intro hc a
      have hh := (mem_centralizerModulo_iff.mp hc).2 a a.property
      change QuotientGroup.mk' N (MulAut.conjNormal a.val c) = QuotientGroup.mk' N c
      apply QuotientGroup.eq_iff_div_mem.mpr
      change a.val*c.val*a.val⁻¹/c.val ∈ B.val
      simpa only [commutatorElement_def,div_eq_mul_inv,Subgroup.subtype_apply] using hh
  change F.index = _
  rw [←index_comap_of_surjective (H := F) (QuotientGroup.mk'_surjective N),he]
  rfl

private theorem modulo_eq_sup_of_indices {H : Type*} [Group H] [Finite H]
    (V A Z : Subgroup H) [Z.Normal] (hZV : Z ≤ V)
    (hseed : (centralizer (A : Set H)).relIndex Z = 2)
    (hfull : (centralizer (A : Set H)).relIndex V = 4)
    (hquot : (centralizerModulo V A Z).relIndex V = 2) :
    centralizerModulo V A Z = Z ⊔ (V ⊓ centralizer (A : Set H)) := by
  let F := V ⊓ centralizer (A : Set H)
  let J := Z ⊔ F
  let T := centralizerModulo V A Z
  have hFV : F ≤ V := inf_le_left
  have hJV : J ≤ V := sup_le hZV hFV
  have hFZ : F.relIndex Z = 2 := by
    have he : F.subgroupOf Z = (centralizer (A : Set H)).subgroupOf Z := by
      ext z
      exact and_iff_right (hZV z.property)
    change (F.subgroupOf Z).index = 2
    rw [he]
    exact hseed
  have hFVidx : F.relIndex V = 4 := by
    simpa only [F,inf_relIndex_left] using hfull
  have hZF : Z.relIndex J = Z.relIndex F := by
    exact relIndex_sup_left F Z
  have h1 := relIndex_inf_mul_relIndex Z F V
  rw [inf_eq_left.mpr hFV,hFVidx] at h1
  have h2 := relIndex_inf_mul_relIndex F Z V
  rw [inf_eq_left.mpr hZV,hFZ,inf_comm F Z] at h2
  have h3 := relIndex_mul_relIndex Z J V le_sup_left hJV
  rw [hZF] at h3
  have hprod : Z.relIndex F * 4 = Z.relIndex F * (2 * J.relIndex V) := by
    calc
      _ = (Z ⊓ F).relIndex V := h1
      _ = 2 * Z.relIndex V := h2.symm
      _ = 2 * (Z.relIndex F * J.relIndex V) := by rw [h3]
      _ = _ := by ring
  have hJidx : J.relIndex V = 2 := by
    have hh := Nat.eq_of_mul_eq_mul_left
      (Nat.pos_of_ne_zero (show Z.relIndex F ≠ 0 from index_ne_zero_of_finite)) hprod
    omega
  have hJT : J ≤ T := by
    apply sup_le
    · simpa only [inf_eq_right.mpr hZV] using inf_le_centralizerModulo V A Z
    · intro c hc
      apply mem_centralizerModulo_iff.mpr
      refine ⟨hc.1,fun a ha => ?_⟩
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hc.2 a ha)]
      exact one_mem _
  have htower := relIndex_mul_relIndex J T V hJT (centralizerModulo_le V A Z)
  change J.relIndex T * (centralizerModulo V A Z).relIndex V = J.relIndex V at htower
  rw [hquot,hJidx] at htower
  exact le_antisymm (relIndex_eq_one.mp (by omega : J.relIndex T = 1)) hJT

include s in
/-- Every fixed class of the actual radius quotient lifts to an element
centralizing the opposite full seed in the exact-four branch. -/
theorem small_radius_fixed_modulo_lift (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (V d.radical (alpha d.radical)) ≤ 4)
    (v : d.overgroup) (hv : v ∈ radiusPreimage d)
    (hfix : ∀ a ∈ (Z d.radical a').comap (embedM d.radical), ⁅a,v⁆ ∈ radiusSeed d) :
    ∃ z ∈ radiusSeed d, ∃ c ∈ radiusPreimage d ⊓
      centralizer ((Z d.radical a').comap (embedM d.radical) : Set d.overgroup), v = z*c := by
  let A := (Z d.radical a').comap (embedM d.radical)
  let B : NormalNode d.overgroup := ⟨radiusSeed d,(inferInstance : (radiusSeed d).Normal)⟩
  let C : NormalNode d.overgroup := ⟨radiusPreimage d,(inferInstance : (radiusPreimage d).Normal)⟩
  have hsection := small_radius_section_index s hc hb p hsmall
  rw [section_index_eq_modulo] at hsection
  obtain ⟨hseed,hfull,_⟩ := base_small_radius_indices s hc hb p hsmall
  have he := modulo_eq_sup_of_indices (radiusPreimage d) A (radiusSeed d)
    radiusSeed_le_radiusPreimage hseed hfull hsection
  have hvT : v ∈ centralizerModulo (radiusPreimage d) A (radiusSeed d) :=
    mem_centralizerModulo_iff.mpr ⟨hv,hfix⟩
  rw [he] at hvT
  obtain ⟨z,hz,c,hc,heq⟩ := mem_sup_of_normal_left.mp hvT
  exact ⟨z,hz,c,hc,heq.symm⟩

include s in
/-- The full preimage of the fixed subgroup of the radius quotient is the
seed times the actual opposite kernel, and has exactly the critical line
as its commutator with the opposite seed. -/
theorem small_radius_modulo_kernel (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (V d.radical (alpha d.radical)) ≤ 4) :
    let A := (Z d.radical a').comap (embedM d.radical)
    let K := (Q d.radical a').comap (embedM d.radical)
    let T := centralizerModulo (radiusPreimage d) A (radiusSeed d)
    T = radiusSeed d ⊔ (radiusPreimage d ⊓ K) ∧
      ⁅T,A⁆ = ⁅radiusSeed d,A⁆ ∧ Nat.card (⁅T,A⁆ : Subgroup d.overgroup) = 2 := by
  let A := (Z d.radical a').comap (embedM d.radical)
  let K := (Q d.radical a').comap (embedM d.radical)
  let T := centralizerModulo (radiusPreimage d) A (radiusSeed d)
  have hZ : radiusSeed d ≤ T := by
    simpa only [inf_eq_right.mpr radiusSeed_le_radiusPreimage] using
      (inf_le_centralizerModulo (radiusPreimage d) A (radiusSeed d))
  have hkernel := (base_small_radius_indices s hc hb p hsmall).2.2
  have heq : T = radiusSeed d ⊔ (radiusPreimage d ⊓ K) := by
    apply le_antisymm
    · intro v hv
      obtain ⟨hv,hfix⟩ := mem_centralizerModulo_iff.mp hv
      obtain ⟨z,hz,c,hc,he⟩ := small_radius_fixed_modulo_lift s hc hb p hsmall v hv hfix
      rw [he]
      exact mul_mem (mem_sup_left hz) (mem_sup_right (hkernel.symm ▸ hc))
    · apply sup_le hZ
      rw [hkernel]
      intro c hc
      apply mem_centralizerModulo_iff.mpr
      refine ⟨hc.1,fun a ha => ?_⟩
      rw [commutatorElement_eq_one_iff_mul_comm.mpr (hc.2 a ha)]
      exact one_mem _
  have hcomm : ⁅T,A⁆ = ⁅radiusSeed d,A⁆ := by
    apply le_antisymm _ (commutator_mono hZ le_rfl)
    rw [commutator_comm T A,commutator_comm (radiusSeed d) A]
    apply commutator_le.mpr
    intro a ha v hv
    obtain ⟨hv,hfix⟩ := mem_centralizerModulo_iff.mp hv
    obtain ⟨z,hz,c,hc,he⟩ := small_radius_fixed_modulo_lift s hc hb p hsmall v hv hfix
    rw [he,commutatorElement_mul_right_eq_mul_conj,
      commutatorElement_eq_one_iff_mul_comm.mpr (hc.2 a ha),mul_one,mul_inv_cancel_right]
    exact commutator_mem_commutator ha hz
  have hidx := critical_radius_index_two_mul_seed_le s hc hb p
  have hs : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4 := by omega
  have hZG : Z d.radical a' ≤ (embedM d.radical).range :=
    (critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical)
      rfl (replacementDistance_pos h d) p.critical).trans_eq (stabilizer_m_base d.radical)
  have hmap : (⁅radiusSeed d,A⁆ : Subgroup d.overgroup).map (embedM d.radical) =
      ⁅Z d.radical (alpha d.radical),Z d.radical a'⁆ := by
    rw [map_commutator,map_comap_eq_self hZG]
    rw [show (radiusSeed d).map (embedM d.radical) = Z d.radical (alpha d.radical) from
      map_comap_eq_self ((Z_le_stabilizer d.radical _).trans_eq (stabilizer_m_base d.radical))]
  have hcard := small_critical_commutator_card s hc p hs
  rw [←hmap,card_map_of_injective (embedM_injective d.radical)] at hcard
  exact ⟨heq,hcomm,hcomm.symm ▸ hcard⟩

/-- The actual replacement supplies the exact opposite-radius kernel. All
source marking and central-layer inputs are discharged, for both cover orders. -/
theorem small_opposite_radius_fixed_kernel_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a).relIndex (V d.radical a') ≤ 4) :
    V d.radical a' ⊓ Q d.radical a =
      V d.radical a' ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  let q : CriticalPath d.radical (replacementGeometry h d) a' a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      critical_reverse_pair s hc p⟩
  exact small_radius_fixed_kernel s hc hb q hsmall

/-- On the original replacement, the complete quotient-fixed preimage has
the exact critical commutator of order two. No natural-subgroup or splitting
hypothesis replaces the original quotient or either full seed. -/
theorem small_radius_modulo_kernel_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (V d.radical (alpha d.radical)) ≤ 4) :
    let A := (Z d.radical a').comap (embedM d.radical)
    let K := (Q d.radical a').comap (embedM d.radical)
    let T := centralizerModulo (radiusPreimage d) A (radiusSeed d)
    T = radiusSeed d ⊔ (radiusPreimage d ⊓ K) ∧
      ⁅T,A⁆ = ⁅radiusSeed d,A⁆ ∧ Nat.card (⁅T,A⁆ : Subgroup d.overgroup) = 2 :=
  small_radius_modulo_kernel (fullSymmetricAction_knownSimple h e hz hn d hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hb p hsmall

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
