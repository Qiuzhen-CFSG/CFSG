module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.OppositeRadiusIndex
public import Theory.GroupTheory.MutualBinaryActions
public import Theory.Representation.BinaryOffender.QuadraticQuotient

/-!
# The full small critical image and its noncentral commutator line

A critical image of order below four forces both endpoint images to have
order two. Mutual abelian actions then give an actual commutator of order
two. The moving cover already generates this line: a central commutator
would be killed by the natural quotient, forcing its actor into the genuine
two-core. Thus the line misses the stabilizer center even when the cover
has order thirty-two and retains its own central line.

The fixed-index bound descends through the surjective cover map. The binary
six-letter catalogue identifies the full reverse seed image with a cyclic
transposition subgroup in the original marking. The applications consume
OppositeRadiusIndex's small-radius branch on the literal characteristic
replacement, with the earlier symmetric-action and central-layer producers
discharged.

These are the small critical-image calculations of MS93 (3.3)(ii), printed
pp.866--867, used in (5.7)--(5.12), pp.919--927. The mutual-action and finite
catalogue proofs adapt the project's SymplecticSetup.SmallBackwardInputs and
CriticalGeneration arguments, replacing their natural subgroup by the whole
central cover and its surjection. The coordinated shifted-path estimates,
noncentral R4/R6 at intermediate vertices, and selected terminal natural
section remain with qt-e-ms-small-a6-exhaustion-large-distance. These results
do not assert either terminal distance exclusion.
-/

public noncomputable section
open Subgroup BinaryPermutation Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
  {h : SmallMSPair κ L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R} (s : FullSymmetricAction h e hz hn d)

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

include s in
/-- Both literal critical images have order two in the small-image branch. -/
theorem small_critical_indices (hc : DistanceTwo.CentralLayer d) {a e : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a e)
    (hsmall : (Q d.radical e).relIndex (Z d.radical a) < 4) :
    (Q d.radical e).relIndex (Z d.radical a) = 2 ∧ (Q d.radical a).relIndex (Z d.radical e) = 2 := by
  have hb : 0 < criticalDistance d.radical a ((replacementGeometry h d).exists_critical a p.start_color) := by
    rw [(replacementGeometry h d).distance_constant a p.start_color]
    exact (replacementDistance_pos h d)
  have hr := critical_reverse d.radical (replacementGeometry h d) (edgeCentralizerCondition s hc)
    a p.start_color hb e p.end_color p.critical
  let p' : CriticalPath d.radical (replacementGeometry h d) e a := CriticalPath.ofPair p.end_color hr
  have hrs : (Q d.radical a).relIndex (Z d.radical e) < 4 := by
    by_contra hn
    exact (Nat.not_le_of_gt hsmall)
      (reverse_critical_image_four_le s hc (replacementDistance_pos h d) p' (by omega))
  let := finite_Z d.radical a
  let := finite_Z d.radical e
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) e p.end_color
  exact ⟨binary_index_two _ _ hsmall p.critical.2,binary_index_two _ _ hrs hr.2⟩

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

include s in
/-- The genuine critical commutator has order two. -/
theorem small_critical_commutator_card (hc : DistanceTwo.CentralLayer d) {a e : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a e)
    (hsmall : (Q d.radical e).relIndex (Z d.radical a) < 4) :
    Nat.card (⁅Z d.radical a,Z d.radical e⁆ : Subgroup (FreeAmalgam d.radical)) = 2 := by
  obtain ⟨ha2,he2⟩ := small_critical_indices s hc p hsmall
  have hb : 0 < criticalDistance d.radical a ((replacementGeometry h d).exists_critical a p.start_color) := by
    rw [(replacementGeometry h d).distance_constant a p.start_color]
    exact (replacementDistance_pos h d)
  let J := stabilizer d.radical a
  let A := (Z d.radical a).subgroupOf J
  let E := (Z d.radical e).subgroupOf J
  let := finite_stabilizer d.radical a
  let := finite_Z d.radical a
  let := finite_Z d.radical e
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a p.start_color
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) e p.end_color
  have hAJ : Z d.radical a ≤ J := Z_le_stabilizer d.radical a
  have hEJ : Z d.radical e ≤ J :=
    critical_Z_le_stabilizer d.radical (replacementGeometry h d) a p.start_color hb p.critical
  have hAe : Z d.radical a ≤ stabilizer d.radical e :=
    Z_le_stabilizer_of_dist_le a _ p.critical.1.le
  have hEA : Z d.radical e ≤ normalizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    hEJ.trans (Z_normalized d.radical a)
  have hAE : Z d.radical a ≤ normalizer (Z d.radical e : Set (FreeAmalgam d.radical)) :=
    hAe.trans (Z_normalized d.radical e)
  have hmA : A.map J.subtype = Z d.radical a := map_subgroupOf_eq_of_le hAJ
  have hmE : E.map J.subtype = Z d.radical e := map_subgroupOf_eq_of_le hEJ
  have hidxA : (centralizer (Z d.radical e : Set (FreeAmalgam d.radical))).relIndex (Z d.radical a) ≤ 2 := by
    have hle : Q d.radical e ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical e p.end_color))
    exact (relIndex_le_of_le_left hle index_ne_zero_of_finite).trans_eq ha2
  have hidxE : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex (Z d.radical e) ≤ 2 := by
    have hle : Q d.radical a ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
      le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a p.start_color))
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
  have hm : (⁅A,E⁆ : Subgroup J).map J.subtype = ⁅Z d.radical a,Z d.radical e⁆ := by
    rw [map_commutator,hmA,hmE]
  have hcard' : Nat.card (⁅Z d.radical a,Z d.radical e⁆ : Subgroup (FreeAmalgam d.radical)) ≤ 2 := by
    rw [←hm,card_map_of_injective J.subtype_injective]
    exact hcard
  have hn := critical_noncommutation d.radical (replacementGeometry h d) (edgeCentralizerCondition s hc)
    a p.start_color hb p.critical
  let : Finite (⁅Z d.radical a,Z d.radical e⁆ : Subgroup (FreeAmalgam d.radical)) := by
    exact Finite.of_injective (inclusion
      ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left |>.trans
        (DistanceEight.U_le_Z d.radical a))) (inclusion_injective _)
  have hone : 1 < Nat.card (⁅Z d.radical a,Z d.radical e⁆ : Subgroup (FreeAmalgam d.radical)) :=
    (one_lt_card_iff_ne_bot _).mpr hn
  omega

include s in
/-- A central commutator on the whole cover forces the actor into the
actual two-core: the faithful natural quotient still detects the actor. -/
theorem cover_central_commutator_forces_core (A : Subgroup d.overgroup)
    (hcentral : ⁅replacementMoved d,A⁆ ≤ center d.overgroup) :
    A ≤ pCore 2 d.overgroup := by
  let := replacementMoved_normal h d
  intro a ha
  have hact : BinaryPermutation.naturalRepresentation (Fin 6) (s.projection a) = 1 := by
    apply LinearMap.ext
    intro v
    obtain ⟨w,hw⟩ := coverProjection_surjective h e hz hn d (Multiplicative.ofAdd v)
    let z : replacementMoved d := MulAut.conjNormal a w * w⁻¹
    have hzA : (z : d.overgroup) ∈ ⁅replacementMoved d,A⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator ha w.property
    have hz0 : coverProjection h e hz hn d z = 1 := by
      apply MonoidHom.mem_ker.mp
      rw [coverProjection_kernel_center s]
      exact hcentral hzA
    have hcz : (coverProjection h e hz hn d z).toAdd =
        BinaryPermutation.naturalRepresentation (Fin 6) (s.projection a) v - v := by
      change (coverProjection h e hz hn d (MulAut.conjNormal a w * w⁻¹)).toAdd = _
      rw [map_mul,map_inv]
      simp only [toAdd_mul,toAdd_inv,sub_eq_add_neg]
      rw [s.cover_conjugate a w (MulAut.conjNormal a w) rfl,hw]
      rfl
    rw [hz0] at hcz
    exact sub_eq_zero.mp hcz.symm
  have hproj : s.projection a = 1 :=
    BinaryPermutation.naturalRepresentation_injective (Fin 6) (by decide)
      (hact.trans (map_one _).symm)
  rw [←s.projection_kernel]
  exact hproj

include s in
/-- Critical movement is noncentral at its starting vertex even when the
whole moved cover has a central line of order two. -/
theorem critical_moving_commutator_not_central (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ¬ ⁅U d.radical a,Z d.radical a'⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  intro hcentral
  obtain ⟨i,hi,hir,hiQ,hiU⟩ := vertex_coordinates (h := h) hc a p.start_color
  have hA : Z d.radical a' ≤ i.range := by
    rw [hir]
    exact critical_Z_le_stabilizer d.radical (replacementGeometry h d) a
      p.start_color (by rw [(replacementGeometry h d).distance_constant a p.start_color]; exact replacementDistance_pos h d)
      p.critical
  let A := (Z d.radical a').comap i
  have hmA : A.map i = Z d.radical a' := map_comap_eq_self hA
  have hcA : ⁅replacementMoved d,A⁆ ≤ center d.overgroup := by
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
  have hle := map_mono (f := i) (cover_central_commutator_forces_core s A hcA)
  rw [hmA,hiQ] at hle
  exact (critical_reverse_pair s hc p).2 hle

include s in
/-- The full seed commutator is noncentral at its starting vertex. -/
theorem critical_commutator_not_central (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a') :
    ¬ ⁅Z d.radical a,Z d.radical a'⁆ ≤
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
  intro hz
  exact critical_moving_commutator_not_central s hc p
    ((commutator_mono (DistanceEight.U_le_Z d.radical a) le_rfl).trans hz)

include s in
/-- The small critical line is already generated by the actual moving cover. -/
theorem small_critical_moving_commutator_eq (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    ⁅U d.radical a,Z d.radical a'⁆ = ⁅Z d.radical a,Z d.radical a'⁆ := by
  have hle := commutator_mono (DistanceEight.U_le_Z d.radical a)
    (show Z d.radical a' ≤ Z d.radical a' from le_rfl)
  let := finite_Z d.radical a
  let : Finite (⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion
      ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left |>.trans
        (DistanceEight.U_le_Z d.radical a))) (inclusion_injective _)
  let : Finite (⁅U d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hle) (inclusion_injective _)
  have hne : ⁅U d.radical a,Z d.radical a'⁆ ≠ ⊥ := by
    intro hz
    exact critical_moving_commutator_not_central s hc p (by rw [hz]; exact bot_le)
  have hl := (one_lt_card_iff_ne_bot _).mpr hne
  have hc := small_critical_commutator_card s hc p hsmall
  exact eq_of_le_of_card_ge hle (by omega)

include s in
/-- In the index-two branch the critical line misses the stabilizer center.
This is a statement about that line, retaining the full central cover. -/
theorem small_critical_commutator_inf_centralizer (hc : DistanceTwo.CentralLayer d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical a) < 4) :
    ⁅Z d.radical a,Z d.radical a'⁆ ⊓
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) = ⊥ := by
  let D := ⁅Z d.radical a,Z d.radical a'⁆
  let C := centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))
  let := finite_Z d.radical a
  let : Finite D := Finite.of_injective
    (inclusion ((critical_Z_commutator_le_moving (h := h) p).trans inf_le_left |>.trans
      (DistanceEight.U_le_Z d.radical a))) (inclusion_injective _)
  let : Finite (D ⊓ C : Subgroup (FreeAmalgam d.radical)) := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have hcard : Nat.card D = 2 := small_critical_commutator_card s hc p hsmall
  by_contra hne
  have hl : 1 < Nat.card (D ⊓ C : Subgroup (FreeAmalgam d.radical)) := (one_lt_card_iff_ne_bot _).mpr hne
  have hD : D ⊓ C = D := eq_of_le_of_card_ge inf_le_left (by omega)
  apply critical_commutator_not_central s hc p
  change D ≤ C
  rw [←hD]
  exact inf_le_right

include s in
/-- A small opposite-radius index supplies the noncentral critical line
needed for the shifted-path argument, on the same critical pair. -/
theorem small_opposite_radius_critical_line (hc : DistanceTwo.CentralLayer d)
    (hb : 2 < replacementDistance h d) {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a).relIndex (V d.radical a') ≤ 8) :
    (Q d.radical a').relIndex (Z d.radical a) = 2 ∧
    (Q d.radical a).relIndex (Z d.radical a') = 2 ∧
    Nat.card (⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
    ⁅Z d.radical a,Z d.radical a'⁆ ⊓
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) = ⊥ := by
  have hi := critical_index_two_of_small_opposite_radius s hc hb p hsmall
  have hlt : (Q d.radical a').relIndex (Z d.radical a) < 4 := by omega
  exact ⟨hi,(small_critical_indices s hc p hlt).2,
    small_critical_commutator_card s hc p hlt,
    small_critical_commutator_inf_centralizer s hc p hlt⟩

/-- Original-replacement application with the earlier producers discharged. -/
theorem small_opposite_radius_critical_line_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a a')
    (hsmall : (Q d.radical a).relIndex (V d.radical a') ≤ 8) :
    (Q d.radical a').relIndex (Z d.radical a) = 2 ∧
    (Q d.radical a).relIndex (Z d.radical a') = 2 ∧
    Nat.card (⁅Z d.radical a,Z d.radical a'⁆ : Subgroup (FreeAmalgam d.radical)) = 2 ∧
    ⁅Z d.radical a,Z d.radical a'⁆ ⊓
      centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) = ⊥ :=
  small_opposite_radius_critical_line (fullSymmetricAction_knownSimple h e hz hn d hb)
    (DistanceTwo.centralLayer_knownSimple G L R h e hz hn d) hb p hsmall


private theorem exists_swap_of_small_codim (A : Subgroup (Equiv.Perm (Fin 6)))
    (hA : IsElementaryTwo A) (hsmall : fixedCodim (naturalRepresentation (Fin 6)) A ≤ 1) :
    ∃ a ∈ A, a.IsSwap := by
  rcases elementaryTwo_conjugacy hA with h | h | h | h | h | h | h | h | h | h
  · obtain ⟨g,rfl⟩ := h
    refine ⟨(MulAut.conj g) (Equiv.swap 0 1),mem_map_of_mem _ ?_,?_⟩
    · exact (mem_disjointTranspositions_iff (1:Fin 4) _).mpr ⟨1,by decide⟩
    · change (g*Equiv.swap 0 1*g⁻¹).IsSwap
      rw [←Equiv.swap_apply_apply]
      exact ⟨_,_,g.injective.ne (by decide),rfl⟩
  all_goals obtain ⟨g,he⟩ := h; rw [he,fixedCodim_map_conj] at hsmall
  · rw [fixedCodim_A2.2.2.2] at hsmall; omega
  · rw [fixedCodim_D.2.2.2] at hsmall; omega
  · rw [fixedCodim_exceptional.2.2.2] at hsmall; omega
  · rw [fixedCodim_evenPart.2.2.2] at hsmall; omega
  · rw [fixedCodim_plus.2.2.2] at hsmall; omega
  · rw [fixedCodim_double.2.2.2] at hsmall; omega
  · rw [fixedCodim_triple.2.2.2] at hsmall; omega
  · rw [fixedCodim_klein.2.2.2] at hsmall; omega
  · rw [fixedCodim_twisted.2.2.2] at hsmall; omega

include s in
/-- Small critical images are generated by an actual transposition in the
same marked quotient, for either central-cover order. -/
theorem small_critical_image_swap (hc : DistanceTwo.CentralLayer d) {a' : Vertex d.radical}
    (p : DistanceEight.PathCentrality.CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ a ∈ ((Z d.radical a').comap (embedM d.radical)).map s.projection, a.IsSwap := by
  let A := (Z d.radical a').comap (embedM d.radical)
  have hAe : A.map (embedM d.radical) = Z d.radical a' := map_comap_eq_self
    ((critical_Z_le_stabilizer d.radical (replacementGeometry h d) (alpha d.radical) rfl (replacementDistance_pos h d) p.critical).trans_eq
      (stabilizer_m_base d.radical))
  have hreverse := critical_reverse d.radical (replacementGeometry h d) (edgeCentralizerCondition s hc)
    (alpha d.radical) rfl (replacementDistance_pos h d) a' p.end_color p.critical
  have hne : A.map s.projection ≠ ⊥ := by
    intro hz
    have hk := (map_eq_bot_iff A).mp hz
    rw [s.projection_kernel] at hk
    have hh := map_mono (f := embedM d.radical) hk
    rw [hAe,←Q_alpha d.radical (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)] at hh
    exact hreverse.2 hh
  let := (replacementGeometry h d).Z_elementary (replacementDistance_pos h d) a' p.end_color
  let := IsElementaryAbelian.comap_of_injective (p := 2) (embedM d.radical) (embedM_injective d.radical) (Z d.radical a')
  let := IsElementaryAbelian.map (p := 2) (A := A) s.projection
  have hC : (Q d.radical a').comap (embedM d.radical) ≤ centralizer (A : Set d.overgroup) := by
    intro x hx a ha
    apply embedM_injective d.radical
    simp only [map_mul]
    exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical a' p.end_color)) hx) (embedM d.radical a) ha
  let : Finite (stabilizer d.radical (alpha d.radical)) := finite_stabilizer d.radical (alpha d.radical)
  let : Finite (Z d.radical (alpha d.radical)) := Finite.of_injective
    (inclusion (Z_le_stabilizer d.radical (alpha d.radical))) (inclusion_injective _)
  have hindex : (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) < 4 := by
    calc
      (centralizer (A : Set d.overgroup)).relIndex (replacementMoved d) ≤
          ((Q d.radical a').comap (embedM d.radical)).relIndex (replacementMoved d) :=
        relIndex_le_of_le_left hC index_ne_zero_of_finite
      _ = (Q d.radical a').relIndex ((replacementMoved d).map (embedM d.radical)) := relIndex_comap (Q d.radical a') (embedM d.radical) (replacementMoved d)
      _ ≤ (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) :=
        relIndex_le_of_le_right (hc.U_eq_moved ▸ DistanceEight.U_le_Z d.radical (alpha d.radical)) index_ne_zero_of_finite
      _ < 4 := hsmall
  let := replacementMoved_normal h d
  have hcover : fixedCodim (coverAction s) (A.map s.projection) ≤ 1 := by
    rw [NormalElementaryQuotient.centralizer_index_eq_fixedCodim
      (replacementMoved d) s.projection s.surjective
      (s.projection_kernel.trans (moved_centralizer s).symm)] at hindex
    have hh : fixedCodim (coverAction s) (A.map s.projection) < 2 :=
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp hindex
    omega
  have hcodim : fixedCodim (naturalRepresentation (Fin 6)) (A.map s.projection) ≤ 1 :=
    (fixedCodim_le_of_equivariant_surjection (coverAction s) (naturalRepresentation (Fin 6))
      (coverMap (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_surjective (h := h) (e := e) (hz := hz) (hn := hn) (d := d))
      (coverMap_equivariant s) (A.map s.projection)).trans hcover
  exact exists_swap_of_small_codim (A.map s.projection) ⟨hne,inferInstance⟩ hcodim

include s in
/-- The full opposite seed has precisely the cyclic transposition image;
this identifies the actor, not just its order or parity. -/
theorem small_critical_image_eq_swap (hc : DistanceTwo.CentralLayer d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical a').relIndex (Z d.radical (alpha d.radical)) < 4) :
    ∃ t : Equiv.Perm (Fin 6), t.IsSwap ∧ graphImage s (Z d.radical a') = zpowers t := by
  obtain ⟨t,ht,hswap⟩ := small_critical_image_swap s hc p hsmall
  have hcard : Nat.card (graphImage s (Z d.radical a')) = 2 := by
    rw [graphImage_card s _ (critical_Z_le_stabilizer d.radical (replacementGeometry h d)
      (alpha d.radical) rfl (replacementDistance_pos h d) p.critical)]
    exact (small_critical_indices s hc p hsmall).2
  refine ⟨t,hswap,?_⟩
  symm
  apply eq_of_le_of_card_ge (zpowers_le.mpr ht)
  change Nat.card (graphImage s (Z d.radical a')) ≤ Nat.card (zpowers t)
  rw [hcard,Nat.card_zpowers,hswap.orderOf]

/-- The same full-seed transposition image for the original replacement,
using its canonical projection and the actual small opposite radius. -/
theorem small_opposite_radius_image_eq_swap_knownSimple
    {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
    {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
    {d : Replacement L R} (hb : 2 < replacementDistance h d)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (hsmall : (Q d.radical (alpha d.radical)).relIndex (V d.radical a') ≤ 8) :
    ∃ t : Equiv.Perm (Fin 6), t.IsSwap ∧
      ((Z d.radical a').comap (embedM d.radical)).map
        (SourceReduction.projection h e hz hn d) = zpowers t := by
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hc := DistanceTwo.centralLayer_knownSimple G L R h e hz hn d
  have hi := critical_index_two_of_small_opposite_radius s hc hb p hsmall
  obtain ⟨t,ht,him⟩ := small_critical_image_eq_swap s hc p (by omega)
  refine ⟨t,ht,?_⟩
  change ((Z d.radical a').comap (embedM d.radical)).map s.projection = _ at him
  rwa [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at him




end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
