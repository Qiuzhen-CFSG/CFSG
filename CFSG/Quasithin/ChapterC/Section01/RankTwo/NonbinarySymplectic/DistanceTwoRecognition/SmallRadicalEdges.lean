module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.ProperImages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.XDecomposition
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# Whole-kernel control in the proper replacement-root branch

If the replacement image has order q, both critical images fill their
incident edge quotient. The literal edge therefore factors in both ways as
Q_a Z_z = Q_z Z_a. Since Q_z centralizes Z_z, this identifies the full
Q_a displacement with [Z_a,Z_z] and gives its exact centralizer index q.
The bound applies to all of Q_a, including its fixed attachments.

The existing marked four-root argument then gives X_a = U_a C_Xa(L_a),
without assuming failure of the whole-core bound. The final consumer obtains
the order-q premise from the original odd-index witness whenever its image
is nonsylow and the replacement image is proper. No assertion that the
replacement remains radical, and no field-degree restriction, is used.

This supplies whole-layer control for the proper-root case left by the
replacement comparison in MS93 (3.7), printed pp.872--877, using the
critical-root argument of (3.3), printed p.867. The original Sylow case
and the terminal field restriction still require their source proofs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
open Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

private theorem sup_eq_of_index_eq {G : Type*} [Group G]
    {A B S : Subgroup G} [Finite S] (hAS : A ≤ S) (hBS : B ≤ S)
    (hi : B.relIndex A = B.relIndex S) : A ⊔ B = S := by
  have hs := sup_le hAS hBS
  let : Finite (A ⊔ B : Subgroup G) :=
    Finite.of_injective (inclusion hs) (inclusion_injective _)
  have he : B.relIndex (A ⊔ B) = B.relIndex S := le_antisymm
    (relIndex_le_of_le_right hs index_ne_zero_of_finite)
    (hi ▸ relIndex_le_of_le_right le_sup_left index_ne_zero_of_finite)
  have hm := relIndex_mul_relIndex B (A ⊔ B) S le_sup_right hs
  rw [he] at hm
  have hp : 0 < B.relIndex S := Nat.pos_of_ne_zero index_ne_zero_of_finite
  have hu : (A ⊔ B).relIndex S = 1 := by nlinarith
  exact le_antisymm hs (relIndex_eq_one.mp hu)

/-- The proper nonsylow comparison has exactly the original field order. -/
theorem replacement_proper_nonsylow_card
    (g : Geometry d.radical) (hb : g.b d.radical = 2)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n := by
  rcases replacement_original_radical_or_root_or_sylow h d g hb with he | ⟨u,hu⟩ | hs
  · exact (hne he).elim
  · have hc := card_map_of_injective
      (K := (d.ambient.subgroupOf K).map (componentProjection h))
      (f := (MulAut.conj u).toMonoidHom) (MulAut.conj u).injective
    rcases hu with ⟨_,hD⟩ | ⟨_,hD⟩ <;>
      rw [hD,RootSubgroup.card,h.field_card] at hc <;> exact hc.symm
  · exact (hnsyl hs).elim

/-- A field-sized replacement image is filled by the opposite critical layer. -/
theorem replacement_field_sized_edge_factorization
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcard : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    (Q d.radical a).relIndex (Z d.radical z) = 2^n ∧
      Q d.radical a ⊔ Z d.radical z = Q d.radical t := by
  have hi : (Q d.radical a).relIndex (Z d.radical z) = 2^n :=
    le_antisymm ((replacement_critical_index_le_radical_card h d path hb).trans_eq hcard)
      (replacement_critical_indices_ge_field h d path (by omega)).2
  refine ⟨hi,?_⟩
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases ht : color d.radical t <;> simp_all [path.start_color]
  have hZt : Z d.radical z ≤ Q d.radical t :=
    Z_le_Q_of_dist_lt d.radical z (g.exists_critical z path.end_color) (by
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
        g.distance_constant z path.end_color]
      change 1 < g.b d.radical
      omega)
  let := finite_stabilizer d.radical t
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion (show Q d.radical t ≤ stabilizer d.radical t from fun _ hx => hx.1))
    (inclusion_injective _)
  rw [sup_comm]
  apply sup_eq_of_index_eq hZt (Q_le_adjacent_h d.radical ht hat)
  rw [hi,replacement_edge_index h d path.start_color hat]
  obtain ⟨f,hf,hk,hm,he⟩ := exists_replacement_marked_projection h d g (by omega)
  rw [←hk,relIndex_ker,he,hcard]

private theorem centralizer_index_of_fixed_supplement {G : Type*} [Group G]
    (T A B C : Subgroup G) [Finite T]
    (hAB : A ⊔ B = T) (hTC : T ≤ normalizer (C : Set G))
    (hAC : A ≤ centralizer (C : Set G)) :
    (centralizer (C : Set G)).relIndex T =
      (centralizer (C : Set G)).relIndex B := by
  let N := (centralizer (C : Set G)).subgroupOf T
  let : N.Normal := normal_subgroupOf_of_le_normalizer
    (hTC.trans (normalizer_le_normalizer_centralizer C))
  have hBT : B ≤ T := le_sup_right.trans_eq hAB
  have htop : B.subgroupOf T ⊔ N = ⊤ := by
    apply top_unique
    have hAT : A ≤ T := le_sup_left.trans_eq hAB
    have hjoin : A.subgroupOf T ⊔ B.subgroupOf T = ⊤ := by
      rw [←subgroupOf_sup hAT hBT,hAB,subgroupOf_self]
    rw [←hjoin]
    exact sup_le (fun x hx => mem_sup_right (hAC hx)) le_sup_left
  calc
    _ = N.relIndex (⊤ : Subgroup T) := by
      rw [relIndex_top_right]
      rfl
    _ = N.relIndex (B.subgroupOf T) := by
      rw [←htop,relIndex_sup_right]
    _ = _ := relIndex_subgroupOf hBT

/-- Both literal edge factorizations hold, with the full vertex kernels retained. -/
theorem replacement_field_sized_paired_edges
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcard : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    Q d.radical a ⊔ Z d.radical z = Q d.radical t ∧
      Q d.radical z ⊔ Z d.radical a = Q d.radical t := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  exact ⟨(replacement_field_sized_edge_factorization h d path hb hat hzt hcard).2,
    (replacement_field_sized_edge_factorization h d rev hb hzt hat hcard).2⟩

/-- The entire vertex kernel has centralizer index q on the opposite critical layer. -/
theorem replacement_field_sized_whole_kernel_index
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcard : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (Q d.radical a) = 2^n := by
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases ht : color d.radical t <;> simp_all [path.start_color]
  let := finite_stabilizer d.radical t
  let : Finite (Q d.radical t) := Finite.of_injective
    (inclusion (show Q d.radical t ≤ stabilizer d.radical t from fun _ hx => hx.1))
    (inclusion_injective _)
  have hZa : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le (Q d.radical a))
  have hZT : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  have hCZ : (C d.radical z).subgroupOf (Z d.radical a) =
      (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).subgroupOf (Z d.radical a) := by
    ext x
    exact ⟨fun hx => hx.2,fun hx => ⟨hZT x.property,hx⟩⟩
  have hi : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical a) = 2^n := by
    change ((centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).subgroupOf
      (Z d.radical a)).index = _
    rw [←hCZ,MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) z path.end_color]
    change (Q d.radical z).relIndex (Z d.radical a) = _
    apply le_antisymm _ (replacement_critical_indices_ge_field h d path (by omega)).1
    have hi := relIndex_le_of_le_right (H := Q d.radical z)
      (hZa.trans (Q_le_adjacent_h d.radical ht hat)) index_ne_zero_of_finite
    rw [replacement_edge_index h d path.end_color hzt] at hi
    obtain ⟨f,hf,hk,hm,he⟩ := exists_replacement_marked_projection h d g (by omega)
    rwa [←hk,relIndex_ker,he,hcard] at hi
  have hfac := (replacement_field_sized_paired_edges h d path hb hat hzt hcard).2
  have he := centralizer_index_of_fixed_supplement (Q d.radical t)
    (Q d.radical z) (Z d.radical a) (Z d.radical z) hfac
    ((Q_h_eq_edge d.radical ht hzt).le.trans inf_le_left |>.trans (Z_normalized d.radical z))
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (Z_centralizes_Q d.radical z path.end_color)))
  apply le_antisymm
  · exact (relIndex_le_of_le_right (Q_le_adjacent_h d.radical ht hat)
      index_ne_zero_of_finite).trans_eq (he.trans hi)
  · let : Finite (Q d.radical a) := Finite.of_injective
      (inclusion (Q_le_adjacent_h d.radical ht hat)) (inclusion_injective _)
    exact hi.symm.trans_le (relIndex_le_of_le_right hZa index_ne_zero_of_finite)

open Representation Representation.BinaryOffender Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open scoped IsMulCommutative
/-- Four marked roots decompose the full central omega layer, retaining its fixed factor. -/
theorem replacement_field_sized_X_decomposition
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hsize : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) := by
  let := replacementComponent_normal h d
  let ρ := replacementRepresentation h d
  let s := replacementMovedSection h d
  obtain ⟨E,hE,e,he⟩ := replacement_centralOmega_initial_cover h d
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  obtain ⟨j,hj,hjr,hjUr,κ,hκ,hκQ,hκC,hκL,hfull,f,hf,hfconj⟩ :=
    replacement_fullX_coordinates_at_vertex h d path.start_color E e
  let jU := j.comp s.space.toSubmodule.subtype.toAddMonoidHom.toMultiplicative
  have hjU : Function.Injective jU := by
    intro x y hh
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (hj hh)
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
  have haq := (replacement_field_sized_edge_factorization h d rev hb hzt hat hsize).1
  have hzq := (replacement_field_sized_edge_factorization h d path hb hat hzt hsize).1
  have hZA : Z d.radical z ≤ stabilizer d.radical a := by
    apply Z_le_stabilizer_of_dist_le z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,g.distance_constant a path.start_color,
      g.distance_constant z path.end_color]
  let δ := κ.comp (inclusion hZA)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (quotient_image_card _ _ _ hZA κ hκQ).trans (hzq.trans hFc.symm)
  have hδ : ∀ x : Z d.radical z, ∀ v : s.space.toSubmodule,
      jU (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam d.radical)*jU (Multiplicative.ofAdd v)*(x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hfull (inclusion hZA x) v.val
  obtain ⟨β,hβcard,hβmark,hβ,hβdim,hβquad⟩ := inner_root_actor_of_field_index rev (by omega)
    (MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d) (replacement_core_le h d)
      (replacement_omegaOrbit_centralizer h d) z path.end_color)
    h.nonbinary hFc s e he (replacement_component_image_structure h d).2.2.2.2
    jU hjU hjUr δ hδ hδcard (haq.trans hFc.symm)
  let σ : Representation (ZMod 2) (L (K := E.Carrier))
      (Additive (omegaCenterIn (pCore 2 d.overgroup))) :=
    ρ.comp ((replacementComponent d).subtype.comp e.groupEquiv.symm.toMonoidHom)
  let W : Subrepresentation σ :=
    { toSubmodule := s.space.toSubmodule
      apply_mem_toSubmodule _g _v hv := s.space.apply_mem_toSubmodule _ hv }
  have hβfull (x : Z d.radical z) (v : Additive (omegaCenterIn (pCore 2 d.overgroup))) :
      j (Multiplicative.ofAdd (σ (β x) v)) =
        (x : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam d.radical)⁻¹ := by
    change j (Multiplicative.ofAdd (ρ (e.groupEquiv.symm (β x)) v)) = _
    rw [hβmark]
    exact hfull (inclusion hZA x) v
  have hbound : (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
      (X d.radical a) ≤ 2^n := by
    let := finite_stabilizer d.radical a
    let : Finite (Q d.radical a) := Finite.of_injective
      (inclusion (show Q d.radical a ≤ stabilizer d.radical a from fun _ hx => hx.1))
      (inclusion_injective _)
    exact (relIndex_le_of_le_right (omegaCenter_le (Q d.radical a))
      index_ne_zero_of_finite).trans_eq
        (replacement_field_sized_whole_kernel_index h d path hb hat hzt hsize)
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  exact X_eq_moving_sup_centralizer_of_movement hcard σ W
    (MovedSection.coverProjection s e) he (Z d.radical z) β hβcard
    hβdim hβquad j hj hjr hjUr hβfull (by rwa [hFc]) f hfconj

/-- The full vertex kernel and its central layer have exactly the same critical displacement. -/
theorem replacement_field_sized_whole_kernel_commutator
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcard : Nat.card ((d.ambient.subgroupOf K).map (componentProjection h)) = 2^n) :
    ⁅Q d.radical a,Z d.radical z⁆ = ⁅Z d.radical a,Z d.radical z⁆ := by
  have ht : color d.radical t = true := by
    have hn := adjacent_color_ne d.radical hat
    cases ht : color d.radical t <;> simp_all [path.start_color]
  have hZa : Z d.radical a ≤ Q d.radical a :=
    (g.omega_bound a path.start_color (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)).trans
      (omegaCenter_le (Q d.radical a))
  have hQa := Q_le_adjacent_h d.radical ht hat
  have hQz := Q_le_adjacent_h d.radical ht hzt
  have hTa : Q d.radical t ≤ stabilizer d.radical a :=
    (Q_h_eq_edge d.radical ht hat).le.trans inf_le_left
  have hTz : Q d.radical t ≤ stabilizer d.radical z :=
    (Q_h_eq_edge d.radical ht hzt).le.trans inf_le_left
  have hn : Q d.radical t ≤ normalizer
      (⁅Z d.radical a,Z d.radical z⁆ : Subgroup (FreeAmalgam d.radical)) := by
    intro x hx
    rw [mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical a (hTa hx)),
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical z (hTz hx))]
  have he := (replacement_field_sized_paired_edges h d path hb hat hzt hcard).2
  apply le_antisymm _ (commutator_mono hZa le_rfl)
  apply (commutator_mono hQa le_rfl).trans
  rw [←he]
  apply commutator_sup_le_of_relative_normal (Q d.radical t)
    (Q d.radical z) (Z d.radical a) (Z d.radical z) _ hn hQz (hZa.trans hQa)
  · rw [commutator_comm,Z_centralizes_Q d.radical z path.end_color]
    exact bot_le
  · exact le_rfl

/-- Application to the original odd-index comparison: all root-size premises are discharged in the proper nonsylow branch. -/
theorem replacement_proper_nonsylow_kernel_control
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hnsyl : ¬ ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (hne : (d.ambient.subgroupOf K).map (componentProjection h) ≠
      (R.subgroupOf K).map (componentProjection h)) :
    (Q d.radical a ⊔ Z d.radical z = Q d.radical t) ∧
      (Q d.radical z ⊔ Z d.radical a = Q d.radical t) ∧
      ⁅Q d.radical a,Z d.radical z⁆ = ⁅Z d.radical a,Z d.radical z⁆ ∧
      (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex
        (Q d.radical a) = 2^n ∧
      X d.radical a = U d.radical a ⊔
        (X d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) := by
  have hc := replacement_proper_nonsylow_card h d g hb hnsyl hne
  have he := replacement_field_sized_paired_edges h d path hb hat hzt hc
  exact ⟨he.1,he.2,replacement_field_sized_whole_kernel_commutator h d path hb hat hzt hc,
    replacement_field_sized_whole_kernel_index h d path hb hat hzt hc,
    replacement_field_sized_X_decomposition h d path hb hat hzt hc⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.DistanceTwoRecognition
