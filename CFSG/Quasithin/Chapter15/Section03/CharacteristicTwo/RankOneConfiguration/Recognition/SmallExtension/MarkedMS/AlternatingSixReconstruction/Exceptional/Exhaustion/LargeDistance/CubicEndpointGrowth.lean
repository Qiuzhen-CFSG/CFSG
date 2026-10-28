module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicChiefComplete
public import Theory.GroupTheory.MutualBinaryActions
public import Theory.GroupTheory.CentralizerInjectiveImage

/-!
# Critical endpoint growth with the cubic kernel retained

An escaping two-subgroup detects component movement on every normal section.
Applied above the full Z-seed, this makes the actual radius index at least
twice the seed index. An even marked involution has fixed index greater
than eight on the full radius: the chief-factor budget cannot accommodate
both movement inside the seed and movement above it.

Critical reversal and the edge centralizer equality carry these bounds to
both endpoints through the original embeddings. A radius index at most four
therefore equals four, both seed indices equal two, and the actual critical
commutator is a noncentral line of order two. The whole moving cover already
generates that line, which misses the stabilizer-fixed attachment. The proof
retains both cover orders and E/Q of order three; E is never identified with Q.

The final alternatives apply this geometry to the whole intrinsic core and
the literal C.1.32 rank-two consumer. The selected shifted-path contradiction
in MS93 (5.11), the distance-four exclusion (5.12), and final assembly of the
natural and exceptional reconstructions remain with
qt-e-ms-small-a6-reconstruction. This is not either terminal exclusion.

Source: MS93 (3.3)(ii), pp.866--867, and (5.11)(1), pp.923--924.
The proof adapts Natural.Exhaustion.LargeDistance.SectionFive's
OppositeRadiusIndex, SmallCriticalLine and RadiusGrowth, replacing their
faithful-kernel normal-generation argument by escaping-two-subgroup detection.
-/

public noncomputable section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open scoped IsMulCommutative
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "T" => edge L R

include h e in
private theorem reverse_pair {a c : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a c) :
    CriticalPair T c a ((sourceGeometry h).exists_critical c p.end_color) :=
  critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
    c p.end_color p.critical

include h e in
/-- The critical seed centralizer is measured modulo Q, even though the full
initial-action kernel retains E/Q of order three. -/
theorem critical_seed_centralizer_intersection {a c : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a c) :
    Z T a ⊓ centralizer (Z T c : Set (FreeAmalgam T)) = Z T a ⊓ Q T c := by
  obtain ⟨t,hct,_,hZt⟩ := critical_predecessor T a p.start_color _
    (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
    p.critical
  apply le_antisymm
  · rintro x ⟨hx,hxc⟩
    exact ⟨hx,(sourceEdgeCentralizer h e c t p.end_color hct) ▸ ⟨hZt hx,hxc⟩⟩
  · exact inf_le_inf_left _ (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q T c p.end_color)))

include h e hz hk in
private theorem radiusSeed_movement_ne_bot :
    ⁅radiusSeed L R,L.subgroupOf (L ⊔ R)⁆ ≠ ⊥ := by
  intro hz0
  have hmap := congrArg (Subgroup.map (embedM T)) hz0
  rw [map_commutator,Subgroup.map_bot] at hmap
  have hZ : (radiusSeed L R).map (embedM T) = Z T (alpha T) :=
    map_comap_eq_self ((Z_le_stabilizer T _).trans_eq
      (stabilizer_m_base T))
  have hL : (L.subgroupOf (L ⊔ R)).map (embedM T) =
      Ltilde T (alpha T) := by
    rw [Ltilde_alpha]
    exact congrArg (Subgroup.map (embedM T)) (h.relative_residual).symm
  rw [hZ,hL] at hmap
  change U T (alpha T) = ⊥ at hmap
  have hcard := graph_U_card h e hz hk (alpha T) rfl
  rw [hmap,card_bot] at hcard
  omega

include h e hz hk in
/-- The full radius has two distinct sources of noncentral residual movement,
so an even involution in the actor image forces fixed index greater than eight. -/
theorem radius_even_actor_fixed_index_gt_eight
    (hb : 2 < sourceDistance h)
    (A : Subgroup M) (a : Equiv.Perm (Fin 6))
    (ha : orderOf a = 2) (heven : a ∈ alternatingGroup (Fin 6))
    (haA : a ∈ A.map (CubicAction.projection h e hz hk)) :
    8 < (centralizer (A : Set M)).relIndex (radiusPreimage L R) := by
  by_contra! hsmall
  have hV : radiusPreimage L R ≤ pCore 2 M := by
    have hh := comap_mono (f := embedM T) (V_le_Q T
      (geometry := sourceGeometry h) (a := alpha T) rfl hb)
    rwa [Q_alpha_comap T h.relative_radical.isPGroup h.relative_radical.twoCore_le] at hh
  have hfixed : (centralizerModulo (radiusPreimage L R) A ⊥).relIndex
      (radiusPreimage L R) ≤ 8 := by
    apply (NoncentralChiefRefinement.SymmetricSixBudget.centralizerModulo_relIndex_le_of_commutator
      (radiusPreimage L R) A ⊥ (centralizer (A : Set M)) ?_).trans hsmall
    exact (commutator_mono inf_le_right le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.mpr le_rfl).le
  have hh := residual_dichotomy_modulo h e hz hk
    (radiusPreimage L R) ⊥ bot_le (pCore_isPGroup.to_le hV) A a ha heven haA
    hfixed (radiusSeed L R) (radiusSeed_le_radiusPreimage (L := L) (R := R))
  rw [h.relative_residual,sup_bot_eq,le_bot_iff] at hh
  rcases hh with hf | hm
  · exact radiusSeed_movement_ne_bot h e hz hk hf
  · exact radius_moving_not_le_seed h e hz hk hb hm

include h e hz hk in
private theorem critical_radius_index_gt_eight_base
    (hb : 2 < sourceDistance h)
    {a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) (alpha T) a')
    (hforward : 4 ≤ (Q T a').relIndex (Z T (alpha T))) :
    8 < (Q T a').relIndex (V T (alpha T)) := by
  obtain ⟨a,haA,ha,heven⟩ := exists_even_involution_reverse_critical_image h e hz hk
    (sourceDistance_pos h) p hforward
  let A := (Z T a').comap (embedM T)
  let K := (Q T a').comap (embedM T)
  have hKA : K ≤ centralizer (A : Set M) := by
    intro x hx y hy
    apply embedM_injective T
    simp only [map_mul]
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q T a' p.end_color))) hx _ hy
  have hi := (radius_even_actor_fixed_index_gt_eight h e hz hk hb A a ha heven haA).trans_le
    (relIndex_le_of_le_left hKA index_ne_zero_of_finite)
  rw [relIndex_comap,radius_comap_map (h := h) hb] at hi
  exact hi


include h e hz hk in
/-- A large critical seed image forces a strict radius index at the other
endpoint, with the original starting radius retained. -/
theorem critical_radius_index_gt_eight
    (hb : 2 < sourceDistance h)
    {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (hforward : 4 ≤ (Q T a').relIndex (Z T a)) :
    8 < (Q T a').relIndex (V T a) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color T p.start_color
  have hbase : act T g⁻¹ a = alpha T := by
    rw [hg,act_mVertex]
    simp only [mul_inv_cancel]
    rfl
  have pc := p.act g⁻¹
  rw [hbase] at pc
  have hf : 4 ≤ (Q T (act T g⁻¹ a')).relIndex
      (Z T (alpha T)) := by
    rw [←hbase,Q_act,Z_act,relIndex_map_map_of_injective _ _
      (MulAut.conj (g⁻¹)⁻¹).injective]
    exact hforward
  have hi := critical_radius_index_gt_eight_base h e hz hk hb pc hf
  rw [←hbase,Q_act,V_act,relIndex_map_map_of_injective _ _
    (MulAut.conj (g⁻¹)⁻¹).injective] at hi
  exact hi

include h e hz hk in
/-- Reversal gives the strict bound for the opposite radius itself. -/
theorem opposite_radius_index_gt_eight
    (hb : 2 < sourceDistance h)
    {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (hforward : 4 ≤ (Q T a').relIndex (Z T a)) :
    8 < (Q T a).relIndex (V T a') := by
  let q := CriticalPath.ofPair (geometry := sourceGeometry h) p.end_color (reverse_pair h e p)
  exact critical_radius_index_gt_eight h e hz hk hb q
    (reverse_critical_image_four_le h e hz hk (sourceDistance_pos h) p hforward)

include h e hz hk in
/-- The large-image cases are excluded by a small opposite-radius index;
criticality and the two-group order constraint leave exactly index two. -/
theorem critical_index_two_of_small_opposite_radius
    (hb : 2 < sourceDistance h)
    {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (hsmall : (Q T a).relIndex (V T a') ≤ 8) :
    (Q T a').relIndex (Z T a) = 2 := by
  have hl : (Q T a').relIndex (Z T a) < 4 := by
    by_contra! hlarge
    exact (not_lt_of_ge hsmall) (opposite_radius_index_gt_eight h e hz hk hb p hlarge)
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  let := finite_stabilizer T a
  let : Finite (Z T a) := Finite.of_injective
    (inclusion (Z_le_stabilizer T a)) (inclusion_injective _)
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 (Z T a)).index
    ((Q T a').subgroupOf (Z T a))
  change (Q T a').relIndex (Z T a) = 2^n at hn
  have hne : (Q T a').relIndex (Z T a) ≠ 1 := by
    intro hi
    exact p.critical.2 (relIndex_eq_one.mp hi)
  have hn2 : n < 2 := by
    by_contra! hn2
    have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hn2
    rw [←hn] at hpow
    omega
  have hn1 : n = 1 := by
    by_contra hh
    have hz : n = 0 := by omega
    rw [hz] at hn
    exact hne hn
  simpa only [hn1,pow_one] using hn

private theorem binary_index_two {G : Type*} [Group G]
    (A K : Subgroup G) [Finite A] [IsElementaryAbelian 2 A]
    (hsmall : K.relIndex A < 4) (hne : ¬ A ≤ K) : K.relIndex A = 2 := by
  obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup 2 A).index (K.subgroupOf A)
  change K.relIndex A = 2^n at hn
  have hlt : n < 2 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (hn ▸ hsmall)
  have hn0 : n ≠ 0 := by
    intro he
    rw [he,pow_zero] at hn
    exact hne (relIndex_eq_one.mp hn)
  have he : n = 1 := by omega
  simpa only [he,pow_one] using hn

include h e hz hk in
/-- Both literal critical images have order two in the small-image branch. -/
theorem small_critical_indices {a c : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a c)
    (hsmall : (Q T c).relIndex (Z T a) < 4) :
    (Q T c).relIndex (Z T a) = 2 ∧ (Q T a).relIndex (Z T c) = 2 := by
  have hb : 0 < criticalDistance T a ((sourceGeometry h).exists_critical a p.start_color) := by
    rw [(sourceGeometry h).distance_constant a p.start_color]
    exact (sourceDistance_pos h)
  have hr := critical_reverse T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a p.start_color hb c p.end_color p.critical
  let p' : CriticalPath T (sourceGeometry h) c a := CriticalPath.ofPair p.end_color hr
  have hrs : (Q T a).relIndex (Z T c) < 4 := by
    by_contra hn
    exact (Nat.not_le_of_gt hsmall)
      (reverse_critical_image_four_le h e hz hk (sourceDistance_pos h) p' (by omega))
  let := finite_Z T a
  let := finite_Z T c
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c p.end_color
  exact ⟨binary_index_two _ _ hsmall p.critical.2,binary_index_two _ _ hrs hr.2⟩

include h e hz in
/-- An actor escaping the original two-core cannot fix a normal section
on which the original component acts nontrivially. -/
theorem section_index_two_le (B C : NormalNode M)
    (hmove : ¬ ⁅C.val,L.subgroupOf (L ⊔ R)⁆ ≤ B.val)
    (A : Subgroup M) (hAtwo : IsPGroup 2 A) (hA : ¬ A ≤ pCore 2 M) :
    2 ≤ SymmetricSixBudget.sectionIndex A B C := by
  let ρ := sectionAction B C
  let : MulDistribMulAction M (Section B C) :=
    MulDistribMulAction.compHom _ ρ
  have hpos : 0 < (FixedPoints.subgroup A (Section B C)).index :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  by_contra! hsmall
  change (FixedPoints.subgroup A (Section B C)).index < 2 at hsmall
  have he : (FixedPoints.subgroup A (Section B C)).index = 1 := by omega
  have htop : FixedPoints.subgroup A (Section B C) = ⊤ := index_eq_one.mp he
  have hAK : A ≤ ρ.ker := by
    intro a ha
    apply MulEquiv.ext
    intro x
    have hx : x ∈ FixedPoints.subgroup A (Section B C) := htop ▸ mem_top x
    exact hx ⟨a,ha⟩
  have hL : L.subgroupOf (L ⊔ R) ≤ ρ.ker :=
    CubicAction.component_le_normal_of_escaping_two h e hz ρ.ker A hAtwo hA hAK
  apply hmove
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha c hc
  have heq := congrArg (fun f : MulAut (Section B C) =>
    f (QuotientGroup.mk' (B.val.subgroupOf C.val) ⟨c,hc⟩)) (hL ha)
  change QuotientGroup.mk' (B.val.subgroupOf C.val) (MulAut.conjNormal a ⟨c,hc⟩) =
    QuotientGroup.mk' (B.val.subgroupOf C.val) ⟨c,hc⟩ at heq
  have hm := QuotientGroup.eq_iff_div_mem.mp heq
  change a*c*a⁻¹/c ∈ B.val at hm
  simpa only [commutatorElement_def,div_eq_mul_inv] using hm

include h e hz hk in
/-- Every nontrivial marked actor has movement beyond the initial seed. -/
theorem radius_actor_index_two_mul_seed_le
    (hb : 2 < sourceDistance h)
    (A : Subgroup M) (hAtwo : IsPGroup 2 A) (hA : ¬ A ≤ pCore 2 M) :
    2 * (centralizer (A : Set M)).relIndex (radiusSeed L R) ≤
      (centralizer (A : Set M)).relIndex (radiusPreimage L R) := by
  let B : NormalNode M := ⟨radiusSeed L R,(inferInstance : (radiusSeed L R).Normal)⟩
  let C : NormalNode M := ⟨radiusPreimage L R,(inferInstance : (radiusPreimage L R).Normal)⟩
  have hidx := section_index_two_le h e hz B C (radius_moving_not_le_seed h e hz hk hb) A hAtwo hA
  exact (Nat.mul_le_mul_right _ hidx).trans
    (SymmetricSixBudget.sectionIndex_mul_lower_le A B C (radiusSeed_le_radiusPreimage (L := L) (R := R)))

include h e hz hk in
private theorem critical_radius_index_two_mul_seed_le_base
    (hb : 2 < sourceDistance h)
    {a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) (alpha T) a') :
    2 * (Q T a').relIndex (Z T (alpha T)) ≤
      (Q T a').relIndex (V T (alpha T)) := by
  let f := embedM T
  let A := (Z T a').comap f
  let K := (Q T a').comap f
  have hAG : Z T a' ≤ f.range :=
    (critical_Z_le_stabilizer T (sourceGeometry h) (alpha T)
      rfl (sourceDistance_pos h) p.critical).trans_eq (stabilizer_m_base T)
  have hmA : A.map f = Z T a' := map_comap_eq_self hAG
  have hmZ : (radiusSeed L R).map f = Z T (alpha T) :=
    map_comap_eq_self ((Z_le_stabilizer T _).trans_eq (stabilizer_m_base T))
  have hA : ¬ A ≤ pCore 2 M := by
    intro hh
    apply (reverse_pair h e p).2
    rw [←hmA,Q_alpha T (h.relative_radical.isPGroup)
      (h.relative_radical.twoCore_le)]
    exact map_mono hh
  have hfixed := critical_seed_centralizer_intersection h e p
  have hidx : (centralizer (A : Set M)).relIndex (radiusSeed L R) =
      (Q T a').relIndex (Z T (alpha T)) := by
    calc
      _ = ((radiusSeed L R).map f ⊓ centralizer (A.map f : Set (FreeAmalgam T))).relIndex
          ((radiusSeed L R).map f) := by
        rw [map_inf_centralizer_of_injective f (embedM_injective T),
          relIndex_map_map_of_injective _ _ (embedM_injective T),inf_relIndex_left]
      _ = _ := by rw [hmA,hmZ,hfixed,inf_relIndex_left]
  have hKA : K ≤ centralizer (A : Set M) := by
    intro x hx y hy
    apply embedM_injective T
    simp only [map_mul]
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q T a' p.end_color))) hx _ hy
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a' p.end_color
  have hAtwo : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 (Z T a')).comap_of_injective
    f (embedM_injective T)
  have hi := (radius_actor_index_two_mul_seed_le h e hz hk hb A hAtwo hA).trans
    (relIndex_le_of_le_left hKA index_ne_zero_of_finite)
  rw [hidx,relIndex_comap,radius_comap_map (h := h) hb] at hi
  exact hi

include h e hz hk in
/-- The radius index at a critical endpoint is at least twice the seed index,
including the transposition branch and the central attachment. -/
theorem critical_radius_index_two_mul_seed_le
    (hb : 2 < sourceDistance h)
    {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a') :
    2 * (Q T a').relIndex (Z T a) ≤
      (Q T a').relIndex (V T a) := by
  obtain ⟨g,hg⟩ := exists_mVertex_of_color T p.start_color
  have hbase : act T g⁻¹ a = alpha T := by
    rw [hg,act_mVertex]
    simp only [mul_inv_cancel]
    rfl
  have pc := p.act g⁻¹
  rw [hbase] at pc
  have hi := critical_radius_index_two_mul_seed_le_base h e hz hk hb pc
  rw [←hbase,Q_act,Z_act,V_act,relIndex_map_map_of_injective _ _
    (MulAut.conj (g⁻¹)⁻¹).injective,relIndex_map_map_of_injective _ _
    (MulAut.conj (g⁻¹)⁻¹).injective] at hi
  exact hi

include h e hz hk in
/-- Strict index growth at both endpoints of the same critical walk. -/
theorem critical_radius_indices_gt_seed
    (hb : 2 < sourceDistance h)
    {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a') :
    (Q T a').relIndex (Z T a) < (Q T a').relIndex (V T a) ∧
      (Q T a).relIndex (Z T a') < (Q T a).relIndex (V T a') := by
  have hf := critical_radius_index_two_mul_seed_le h e hz hk hb p
  let q : CriticalPath T (sourceGeometry h) a' a :=
    ⟨p.end_color,p.walk.reverse,
      by rw [SimpleGraph.Walk.length_reverse,p.shortest,SimpleGraph.dist_comm],
      reverse_pair h e p⟩
  have hr := critical_radius_index_two_mul_seed_le h e hz hk hb q
  let := finite_Z T a
  let := finite_Z T a'
  have hp : 0 < (Q T a').relIndex (Z T a) :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hp' : 0 < (Q T a).relIndex (Z T a') :=
    Nat.pos_of_ne_zero index_ne_zero_of_finite
  constructor <;> omega



include h in
private theorem critical_seed_commutator_le {a c : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a c) :
    ⁅Z T a,Z T c⁆ ≤ Z T a ⊓ Z T c := by
  have hac : Z T a ≤ stabilizer T c :=
    Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hca : Z T c ≤ stabilizer T a :=
    critical_Z_le_stabilizer T (sourceGeometry h) a p.start_color
      (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
      p.critical
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp (hca.trans (Z_normalized T a)))
    (le_normalizer_iff_commutator_le_right.mp (hac.trans (Z_normalized T c)))

private theorem centralizer_index_map {G H : Type*} [Group G] [Group H]
    (f : G →* H) (hf : Function.Injective f) (A B : Subgroup G) :
    (centralizer (A.map f : Set H)).relIndex (B.map f) =
      (centralizer (A : Set G)).relIndex B := by
  have hc : (centralizer (A.map f : Set H)).comap f = centralizer (A : Set G) := by
    ext x
    constructor
    · intro hx a ha
      apply hf
      simpa only [map_mul] using hx (f a) (mem_map_of_mem f ha)
    · intro hx a ha
      obtain ⟨b,hb,rfl⟩ := ha
      simpa only [map_mul] using congrArg f (hx b hb)
  rw [←relIndex_comap,hc]

include h e hz hk in
/-- The genuine critical commutator has order two. -/
theorem small_critical_commutator_card {a c : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a c)
    (hsmall : (Q T c).relIndex (Z T a) < 4) :
    Nat.card (⁅Z T a,Z T c⁆ : Subgroup (FreeAmalgam T)) = 2 := by
  obtain ⟨ha2,he2⟩ := small_critical_indices h e hz hk p hsmall
  have hb : 0 < criticalDistance T a ((sourceGeometry h).exists_critical a p.start_color) := by
    rw [(sourceGeometry h).distance_constant a p.start_color]
    exact (sourceDistance_pos h)
  let J := stabilizer T a
  let A := (Z T a).subgroupOf J
  let E := (Z T c).subgroupOf J
  let := finite_stabilizer T a
  let := finite_Z T a
  let := finite_Z T c
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a p.start_color
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) c p.end_color
  have hAJ : Z T a ≤ J := Z_le_stabilizer T a
  have hEJ : Z T c ≤ J :=
    critical_Z_le_stabilizer T (sourceGeometry h) a p.start_color hb p.critical
  have hAe : Z T a ≤ stabilizer T c :=
    Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hEA : Z T c ≤ normalizer (Z T a : Set (FreeAmalgam T)) :=
    hEJ.trans (Z_normalized T a)
  have hAE : Z T a ≤ normalizer (Z T c : Set (FreeAmalgam T)) :=
    hAe.trans (Z_normalized T c)
  have hmA : A.map J.subtype = Z T a := map_subgroupOf_eq_of_le hAJ
  have hmE : E.map J.subtype = Z T c := map_subgroupOf_eq_of_le hEJ
  have hidxA : (centralizer (Z T c : Set (FreeAmalgam T))).relIndex (Z T a) ≤ 2 := by
    have hle : Q T c ≤ centralizer (Z T c : Set (FreeAmalgam T)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q T c p.end_color))
    exact (relIndex_le_of_le_left hle index_ne_zero_of_finite).trans_eq ha2
  have hidxE : (centralizer (Z T a : Set (FreeAmalgam T))).relIndex (Z T c) ≤ 2 := by
    have hle : Q T a ≤ centralizer (Z T a : Set (FreeAmalgam T)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q T a p.start_color))
    exact (relIndex_le_of_le_left hle index_ne_zero_of_finite).trans_eq he2
  have hcard : Nat.card (⁅A,E⁆ : Subgroup J) ≤ 2 := by
    apply commutator_card_le_two_of_mutual_centralizer_indices A E
    · rw [←subgroupOf_normalizer_eq hAJ]
      exact fun _ he => hEA he
    · rw [←subgroupOf_normalizer_eq hEJ]
      exact fun _ ha => hAE ha
    · rw [←centralizer_index_map J.subtype J.subtype_injective,hmA,hmE]
      exact hidxE
    · rw [←centralizer_index_map J.subtype J.subtype_injective,hmE,hmA]
      exact hidxA
  have hm : (⁅A,E⁆ : Subgroup J).map J.subtype = ⁅Z T a,Z T c⁆ := by
    rw [map_commutator,hmA,hmE]
  have hcard' : Nat.card (⁅Z T a,Z T c⁆ : Subgroup (FreeAmalgam T)) ≤ 2 := by
    rw [←hm,card_map_of_injective J.subtype_injective]
    exact hcard
  have hn := critical_noncommutation T (sourceGeometry h) (sourceEdgeCentralizer h e)
    a p.start_color hb p.critical
  let : Finite (⁅Z T a,Z T c⁆ : Subgroup (FreeAmalgam T)) := by
    exact Finite.of_injective (inclusion
      ((critical_seed_commutator_le h p).trans inf_le_left)) (inclusion_injective _)
  have hone : 1 < Nat.card (⁅Z T a,Z T c⁆ : Subgroup (FreeAmalgam T)) :=
    (one_lt_card_iff_ne_bot _).mpr hn
  omega

include h e hz hk in
/-- A central commutator on the whole cover forces the actor into the
actual two-core: the faithful natural quotient still detects the actor. -/
theorem cover_central_commutator_forces_core (A : Subgroup M) (hAtwo : IsPGroup 2 A)
    (hcentral : ⁅initialMoved L R,A⁆ ≤ center M) :
    A ≤ pCore 2 M := by
  let := h.relative_normal
  apply two_subgroup_le_core_of_le_extensionKernel h hz A hAtwo
  intro a ha
  have hact : BinaryPermutation.naturalRepresentation (Fin 6) ((CubicAction.projection h e hz hk) a) = 1 := by
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw⟩ := coverProjection_surjective h e hz hk (Multiplicative.ofAdd v)
    let z : initialMoved L R := MulAut.conjNormal a w * w⁻¹
    have hzA : (z : M) ∈ ⁅initialMoved L R,A⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator ha w.property
    have hz0 : coverProjection h e hz hk z = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [coverProjection_kernel_center h e hz hk]
      exact hcentral hzA
    have hcz : (coverProjection h e hz hk z).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) ((CubicAction.projection h e hz hk) a) v - v := by
      change (coverProjection h e hz hk (MulAut.conjNormal a w * w⁻¹)).toAdd = _
      rw [map_mul,map_inv]
      simp only [toAdd_mul,toAdd_inv,sub_eq_add_neg]
      rw [coverProjection_conjugate h e hz hk a w (MulAut.conjNormal a w) rfl,hw]
      rfl
    rw [hz0] at hcz
    exact sub_eq_zero.mp hcz.symm
  have hproj : (CubicAction.projection h e hz hk) a = 1 :=
    BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
      (hact.trans (map_one _).symm)
  rw [←CubicAction.projection_kernel h e hz hk]
  exact hproj

include h e hz hk in
/-- Critical movement is noncentral at its starting vertex even when the
whole moved cover has a central line of order two. -/
theorem critical_moving_commutator_not_central
    {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a') :
    ¬ ⁅U T a,Z T a'⁆ ≤
      centralizer (stabilizer T a : Set (FreeAmalgam T)) := by
  intro hcentral
  obtain ⟨i,hi,hir,hiQ,_,hiU,_⟩ := graph_cover h e hz hk a p.start_color
  have hA : Z T a' ≤ i.range := by
    rw [hir]
    exact critical_Z_le_stabilizer T (sourceGeometry h) a
      p.start_color (by rw [(sourceGeometry h).distance_constant a p.start_color]; exact sourceDistance_pos h)
      p.critical
  let A := (Z T a').comap i
  have hmA : A.map i = Z T a' := map_comap_eq_self hA
  have hcA : ⁅initialMoved L R,A⁆ ≤ center M := by
    intro x hx
    apply mem_center_iff.mpr
    intro m
    apply hi
    simp only [map_mul]
    apply hcentral
    · have hh := mem_map_of_mem i hx
      rw [map_commutator,hmA,hiU] at hh
      exact hh
    · rw [←hir]
      exact ⟨m,rfl⟩
  let := (sourceGeometry h).Z_elementary (sourceDistance_pos h) a' p.end_color
  have hAtwo : IsPGroup 2 A := (IsElementaryAbelian.isPGroup 2 (Z T a')).comap_of_injective i hi
  have hle := map_mono (f := i) (cover_central_commutator_forces_core h e hz hk A hAtwo hcA)
  rw [hmA,hiQ] at hle
  exact (reverse_pair h e p).2 hle

include h e hz hk in
/-- The full seed commutator is noncentral at its starting vertex. -/
theorem critical_commutator_not_central
    {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a') :
    ¬ ⁅Z T a,Z T a'⁆ ≤
      centralizer (stabilizer T a : Set (FreeAmalgam T)) := by
  intro hcentral
  exact critical_moving_commutator_not_central h e hz hk p
    ((commutator_mono (DistanceEight.U_le_Z T a) le_rfl).trans hcentral)

include h e hz hk in
/-- The small critical line is already generated by the actual moving cover. -/
theorem small_critical_moving_commutator_eq
    {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (hsmall : (Q T a').relIndex (Z T a) < 4) :
    ⁅U T a,Z T a'⁆ = ⁅Z T a,Z T a'⁆ := by
  have hle := commutator_mono (DistanceEight.U_le_Z T a)
    (show Z T a' ≤ Z T a' from le_rfl)
  let := finite_Z T a
  let : Finite (⁅Z T a,Z T a'⁆ : Subgroup (FreeAmalgam T)) :=
    Finite.of_injective (inclusion
      ((critical_seed_commutator_le h p).trans inf_le_left)) (inclusion_injective _)
  let : Finite (⁅U T a,Z T a'⁆ : Subgroup (FreeAmalgam T)) :=
    Finite.of_injective (inclusion hle) (inclusion_injective _)
  have hne : ⁅U T a,Z T a'⁆ ≠ ⊥ := by
    intro hzero
    exact critical_moving_commutator_not_central h e hz hk p (by rw [hzero]; exact bot_le)
  have hl := (one_lt_card_iff_ne_bot _).mpr hne
  have hc := small_critical_commutator_card h e hz hk p hsmall
  exact eq_of_le_of_card_ge hle (by omega)

include h e hz hk in
/-- In the index-two branch the critical line misses the stabilizer center.
This is a statement about that line, retaining the full central cover. -/
theorem small_critical_commutator_inf_centralizer
    {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (hsmall : (Q T a').relIndex (Z T a) < 4) :
    ⁅Z T a,Z T a'⁆ ⊓
      centralizer (stabilizer T a : Set (FreeAmalgam T)) = ⊥ := by
  let D := ⁅Z T a,Z T a'⁆
  let C := centralizer (stabilizer T a : Set (FreeAmalgam T))
  let := finite_Z T a
  let : Finite D := Finite.of_injective
    (inclusion ((critical_seed_commutator_le h p).trans inf_le_left)) (inclusion_injective _)
  let : Finite (D ⊓ C : Subgroup (FreeAmalgam T)) := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hcard : Nat.card D = 2 := small_critical_commutator_card h e hz hk p hsmall
  by_contra hne
  have hl : 1 < Nat.card (D ⊓ C : Subgroup (FreeAmalgam T)) := (one_lt_card_iff_ne_bot _).mpr hne
  have hD : D ⊓ C = D := eq_of_le_of_card_ge inf_le_left (by omega)
  apply critical_commutator_not_central h e hz hk p
  change D ≤ C
  rw [←hD]
  exact inf_le_right

include h e hz hk in
/-- A small opposite-radius index supplies the noncentral critical line
needed for the shifted-path argument, on the same critical pair. -/
theorem small_opposite_radius_critical_line
    (hb : 2 < sourceDistance h) {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (hsmall : (Q T a).relIndex (V T a') ≤ 8) :
    (Q T a').relIndex (Z T a) = 2 ∧
    (Q T a).relIndex (Z T a') = 2 ∧
    Nat.card (⁅Z T a,Z T a'⁆ : Subgroup (FreeAmalgam T)) = 2 ∧
    ⁅Z T a,Z T a'⁆ ⊓
      centralizer (stabilizer T a : Set (FreeAmalgam T)) = ⊥ := by
  have hi := critical_index_two_of_small_opposite_radius h e hz hk hb p hsmall
  have hlt : (Q T a').relIndex (Z T a) < 4 := by omega
  exact ⟨hi,(small_critical_indices h e hz hk p hlt).2,
    small_critical_commutator_card h e hz hk p hlt,
    small_critical_commutator_inf_centralizer h e hz hk p hlt⟩


include h e hz hk in
/-- On the original cubic-kernel graph, the remaining small opposite-radius branch
has index four or eight, and both endpoint seed indices are exactly two. -/
theorem small_opposite_radius_four_or_eight
    (hb : 2 < sourceDistance h)
    {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (hsmall : (Q T a).relIndex (V T a') ≤ 8) :
    (Q T a').relIndex (Z T a) = 2 ∧
      (Q T a).relIndex (Z T a') = 2 ∧
      ((Q T a).relIndex (V T a') = 4 ∨
        (Q T a).relIndex (V T a') = 8) := by
  have hi := critical_index_two_of_small_opposite_radius h e hz hk hb p hsmall
  have hi' := (small_critical_indices h e hz hk p (by omega)).2
  have hl := (critical_radius_indices_gt_seed h e hz hk hb p).2
  have hVQ := V_le_Q T p.end_color hb
  let := finite_stabilizer T a'
  let : Finite (V T a') := Finite.of_injective
    (inclusion (hVQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
  obtain ⟨n,hn⟩ := ((Q_isPGroup T (h.relative_radical.isPGroup)
    (h.relative_radical.twoCore_le) a' p.end_color).to_le hVQ).index
      ((Q T a).subgroupOf (V T a'))
  change (Q T a).relIndex (V T a') = 2^n at hn
  have hnlo : 2 ≤ n := by
    by_contra! hh
    interval_cases n <;> simp_all
  have hnhi : n ≤ 3 := by
    by_contra! hh
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) hh
    omega
  refine ⟨hi,hi',?_⟩
  have hn23 : n = 2 ∨ n = 3 := by omega
  rcases hn23 with rfl | rfl <;> simp_all

include h e hz hk in
/-- In the negation of source (5.11)(1), the actual opposite radius has
index exactly four and both critical seeds have index two. -/
theorem small_opposite_radius_eq_four
    (hb : 2 < sourceDistance h)
    {a a' : Vertex T}
    (p : CriticalPath T (sourceGeometry h) a a')
    (hsmall : (Q T a).relIndex (V T a') ≤ 4) :
    (Q T a').relIndex (Z T a) = 2 ∧
      (Q T a).relIndex (Z T a') = 2 ∧
      (Q T a).relIndex (V T a') = 4 := by
  obtain ⟨hi,hi',hr⟩ := small_opposite_radius_four_or_eight
    h e hz hk hb p (by omega)
  exact ⟨hi,hi',by omega⟩


include h e hz hk in
/-- The only obstruction to a strict radius bound of four has exact radius
index four and a genuine noncentral critical line on the same path. -/
theorem small_opposite_radius_exact_line
    {a c : Vertex T} (p : CriticalPath T (sourceGeometry h) a c)
    (hsmall : (Q T a).relIndex (V T c) ≤ 4) :
    (Q T a).relIndex (V T c) = 4 ∧
      (Q T c).relIndex (Z T a) = 2 ∧
      (Q T a).relIndex (Z T c) = 2 ∧
      Nat.card (⁅Z T a,Z T c⁆ : Subgroup (FreeAmalgam T)) = 2 ∧
      ⁅Z T a,Z T c⁆ ⊓ centralizer (stabilizer T a : Set (FreeAmalgam T)) = ⊥ := by
  have hb := distance_gt_two h e hz hk
  obtain ⟨hi,hi',hr⟩ := small_opposite_radius_eq_four h e hz hk hb p hsmall
  obtain ⟨_,_,hcard,hfixed⟩ := small_opposite_radius_critical_line h e hz hk hb p (by omega)
  exact ⟨hr,hi,hi',hcard,hfixed⟩

omit hk in
include h e hz in
/-- Whole-core assembly retains only the cubic full-symmetric branch, now
with strict large-image endpoint bounds and exact small-radius geometry.
The selected shifted-path exclusion remains with this assembly owner. -/
theorem coreExhaustion_or_cubic_endpoint_bounds :
    CoreExhaustion L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      ∀ a c : Vertex T, ∀ _p : CriticalPath T (sourceGeometry h) a c,
        (2 * (Q T c).relIndex (Z T a) ≤ (Q T c).relIndex (V T a)) ∧
        (4 ≤ (Q T c).relIndex (Z T a) → 8 < (Q T a).relIndex (V T c)) ∧
        ((Q T a).relIndex (V T c) ≤ 4 →
          (Q T a).relIndex (V T c) = 4 ∧
          (Q T c).relIndex (Z T a) = 2 ∧
          (Q T a).relIndex (Z T c) = 2 ∧
          Nat.card (⁅Z T a,Z T c⁆ : Subgroup (FreeAmalgam T)) = 2 ∧
          ⁅Z T a,Z T c⁆ ⊓ centralizer (stabilizer T a : Set (FreeAmalgam T)) = ⊥) := by
  rcases CubicEven.coreExhaustion_or_cubic_fullSymmetric h e hz with hx | ⟨hk,hs,hb⟩
  · exact Or.inl hx
  · exact Or.inr ⟨hk,hs,hb,fun a c p =>
      ⟨critical_radius_index_two_mul_seed_le h e hz hk hb p,
        opposite_radius_index_gt_eight h e hz hk hb p,
        small_opposite_radius_exact_line h e hz hk p⟩⟩

omit hk in
include h e hz in
/-- Literal C.1.32 application, preserving the entire intrinsic core and
both reconstruction outcomes while refining its remaining cubic branch. -/
theorem rankTwo_or_cubic_endpoint_bounds :
    RankTwoAlternatives L R ∨ ∃ hk : layerKernel L R = extensionKernel h,
      Function.Surjective (CubicAction.projection h e hz hk) ∧
      2 < sourceDistance h ∧
      ∀ a c : Vertex T, ∀ _p : CriticalPath T (sourceGeometry h) a c,
        (2 * (Q T c).relIndex (Z T a) ≤ (Q T c).relIndex (V T a)) ∧
        (4 ≤ (Q T c).relIndex (Z T a) → 8 < (Q T a).relIndex (V T c)) ∧
        ((Q T a).relIndex (V T c) ≤ 4 →
          (Q T a).relIndex (V T c) = 4 ∧
          (Q T c).relIndex (Z T a) = 2 ∧
          (Q T a).relIndex (Z T c) = 2 ∧
          Nat.card (⁅Z T a,Z T c⁆ : Subgroup (FreeAmalgam T)) = 2 ∧
          ⁅Z T a,Z T c⁆ ⊓ centralizer (stabilizer T a : Set (FreeAmalgam T)) = ⊥) :=
  (coreExhaustion_or_cubic_endpoint_bounds h e hz).imp (rankTwo_of_exhaustion h e hz) id

end AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicFull
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
