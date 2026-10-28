module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceThree
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceFive
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.FixedAttachment

/-!
# Central omega and overlap layers for an order-q critical image

The actual critical Z-image of order q gives a long-root action on the
opposite natural cover. Its fixed hyperplane bounds movement of the entire
central omega layer X by q. Four conjugate roots then give
X = U C_X(L); the full fixed attachment belongs to the incident edge center,
so X = Z and Z = U Z_t. No whole-core containment is needed for these facts.

In the contained-core branch Q_a ≤ Z_a Q_z, an element of Z_z ∩ Q_a
centralizes both factors of Z_a Q_z, hence belongs to X_a = Z_a. This
identifies the actual overlap and proves both overlap indices equal q.
It completes the overlap clause in that subcase of source (3.7)(3).
The same X = Z result completes (3.7)(5) when an order-q critical image is
available, preserving its three original comparison antecedents.

Source: Meierfrankenfeld--Stellmacher (1993), (3.3)(ii)(2), printed p.867,
and (3.7)(3),(5), printed pp.874--876. The noncontained-core branch, the
large-critical-image Q₂ count and the selection in (6) remain open. In
particular, the last comparison cannot replace the Q₂ step used to prove
(6). The order-q hypothesis concerns the critical image, never the full
saturated radical, whose image has order q³ or q⁴.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
open DistanceTwoRecognition ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual order-q critical image bounds the centralizer index on
all of X, using the same opposite quotient and marked natural cover. -/
theorem X_movement_of_critical_index
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n) :
    (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex (X d.radical a) ≤ 2^n := by
  let := replacementComponent_normal h d
  let s := replacementMovedSection h d
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < (2^n)^2 := by
    rw [hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith
  obtain ⟨he,ha⟩ := replacement_critical_indices_eq_field_of_small h d path (by omega) hsmall
  obtain ⟨⟨E,hE,e,hecov,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩⟩ :=
    replacement_ambient_initial_cover_at_vertex h d path.end_color
  have hFcard : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  let δ := κ.comp (inclusion hAZ)
  have hδcard : Nat.card δ.range = Nat.card E.Carrier :=
    (quotient_image_card _ _ _ hAZ κ hκQ).trans (he.trans hFcard.symm)
  have hδ : ∀ x : Z d.radical a, ∀ v : s.space.toSubmodule,
      j (Multiplicative.ofAdd (s.space.toRepresentation (δ x) v)) =
        (x : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam d.radical)⁻¹ :=
    fun x v => hconj (inclusion hAZ x) v
  have hCa := MSCentralOrbit.C_eq_Q d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d) a path.start_color
  obtain ⟨β,hβcard,hβmark,hβ,hd,hquad⟩ := inner_root_actor_of_field_index path (by omega)
    hCa h.nonbinary hFcard s e hecov (replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ hδ hδcard (ha.trans hFcard.symm)
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFcard]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hh := critical_X_movement_bound_of_vertex_coordinates path (by omega)
    (MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
      (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)) hCa hcard
    s e hecov (replacement_component_image_structure h d).2.2.2.2 j hj hjr κ hκC hconj β hβ hd
  rwa [hFcard] at hh


/-- Four conjugates of the actual critical root exhaust the moving
part of X, retaining the entire component-fixed factor. -/
theorem X_decomposition_of_critical_index
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n) :
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
  obtain ⟨haq,hzq⟩ := replacement_critical_indices_eq_field_of_small h d path (by omega)
    (by
      rw [hcritical]
      have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
      nlinarith)
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (replacement_isPGroup h d)
    (replacement_core_le h d) (replacement_omegaOrbit_centralizer h d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b d.radical; omega)
        z path.end_color path.critical }
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
  have hbound := X_movement_of_critical_index h d path hb hcritical
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  exact X_eq_moving_sup_centralizer_of_movement hcard σ W
    (MovedSection.coverProjection s e) he (Z d.radical z) β hβcard
    hβdim hβquad j hj hjr hjUr hβfull (by rwa [hFc]) f hfconj


/-- An actual order-q critical image identifies the entire central omega
layer with Z. The full fixed attachment is included in the incident edge
center; no containment assumption on the whole core is needed. -/
theorem X_eq_Z_of_critical_index
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n) :
    X d.radical a = Z d.radical a := by
  apply le_antisymm
  · rw [X_decomposition_of_critical_index h d path hb hcritical]
    exact sup_le (U_le_Z a) ((replacement_fixed_X_le_edge h d (g := g)
      (by omega) path.start_color hat).trans
      (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat))
  · exact g.omega_bound a path.start_color (by
      rw [g.distance_constant a path.start_color]
      change 0 < g.b d.radical
      omega)

/-- The source Z-layer consists of its actual moving cover and the whole
common edge center once an order-q critical image is present. -/
theorem Z_eq_moving_sup_edge_of_critical_index
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n) :
    Z d.radical a = U d.radical a ⊔ Z d.radical t := by
  apply le_antisymm
  · rw [←X_eq_Z_of_critical_index h d path hb hat hcritical,
      X_decomposition_of_critical_index h d path hb hcritical]
    exact sup_le_sup_left (replacement_fixed_X_le_edge h d (g := g)
      (by omega) path.start_color hat) _
  · exact sup_le (U_le_Z a) (Sp4Four.edge_Z_le_endpoint d.radical path.start_color hat)

/-- Complete source (3.7)(5) when the first endpoint has an order-q
critical image. The original three antecedents remain explicit. This is
not the Q₂ large-critical-image branch, which needs its separate count. -/
theorem source_five_Z_equality_of_critical_index
    {g : Geometry d.radical} (hb : g.b d.radical = 2)
    {a z t w : Vertex d.radical}
    (path : CriticalPath d.radical g a w)
    (hz : color d.radical z = false)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (c : EdgeMarking h d a t) (c' : EdgeMarking h d z t)
    (hfixed : U d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ centralizer (Ltilde d.radical z : Set (FreeAmalgam d.radical)))
    (hmove : ⁅Z d.radical z,Q d.radical t⁆ = ⁅Z d.radical a,Q d.radical t⁆)
    (hinside : Z d.radical z ≤ Q d.radical a)
    (hcritical : (Q d.radical w).relIndex (Z d.radical a) = 2^n) :
    Z d.radical a = Z d.radical z := by
  have hX := (source_five_core_equality h d g hb path.start_color hz c c'
    hfixed hmove hinside).2
  have hZa := X_eq_Z_of_critical_index h d path hb hat hcritical
  have hle : Z d.radical z ≤ Z d.radical a := by
    rw [←hZa,hX]
    exact g.omega_bound z hz (by
      rw [g.distance_constant z hz]
      change 0 < g.b d.radical
      omega)
  obtain ⟨u,hu,he⟩ := stabilizer_transitive_neighbors d.radical t
    (adjacent_symm d.radical hat) (adjacent_symm d.radical hzt)
  have hcard : Nat.card (Z d.radical a) = Nat.card (Z d.radical z) := by
    rw [←he,Z_act,card_map_of_injective (MulAut.conj u⁻¹).injective]
  let := finite_Z d.radical a
  let := finite_Z d.radical z
  exact (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm

/-- The remaining overlap-index clause in the contained-core subcase of
MS93 (3.7)(3). Centrality in Z_a Q_z places Z_z ∩ Q_a in X_a = Z_a,
so the literal critical image index is the index of the actual overlap. -/
theorem source_three_contained_core_overlap
    {g : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : g.b d.radical = 2)
    (hat : Adjacent d.radical a t) (hzt : Adjacent d.radical z t)
    (hcritical : (Q d.radical z).relIndex (Z d.radical a) = 2^n)
    (hinside : Q d.radical a ≤ Z d.radical a ⊔ Q d.radical z) :
    (Z d.radical z).relIndex (Z d.radical a) = 2^n ∧
      (Z d.radical a).relIndex (Z d.radical z) = 2^n := by
  have hXa := X_eq_Z_of_critical_index h d path hb hat hcritical
  have hcentral : Z d.radical z ⊓ Q d.radical a ≤
      centralizer ((Z d.radical a ⊔ Q d.radical z :
        Subgroup (FreeAmalgam d.radical)) : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    apply sup_le
    · exact (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical a path.start_color)).trans (centralizer_le inf_le_right)
    · exact (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q d.radical z path.end_color))).trans (centralizer_le inf_le_left)
  have hZzX := g.omega_bound z path.end_color (by
    rw [g.distance_constant z path.end_color]
    change 0 < g.b d.radical
    omega)
  have hinter : Z d.radical z ⊓ Q d.radical a = Z d.radical z ⊓ Z d.radical a := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1,?_⟩
      rw [←hXa]
      exact mem_omegaCenter_iff.mpr ⟨hx.2,
        (mem_omegaCenter_iff.mp (hZzX hx.1)).2.1,
        (hcentral.trans (centralizer_le hinside)) hx⟩
    · exact inf_le_inf_left _ (hXa.symm ▸ omegaCenter_le (Q d.radical a))
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < (2^n)^2 := by
    rw [hcritical]
    have hq : 1 < 2^n := one_lt_pow₀ (by decide : 1 < (2:ℕ)) (by have := h.nonbinary; omega)
    nlinarith
  have hzq := (replacement_critical_indices_eq_field_of_small h d path (by omega) hsmall).2
  have hzindex : (Z d.radical a).relIndex (Z d.radical z) = 2^n := by
    rw [←inf_relIndex_right (Z d.radical a),inf_comm,←hinter,inf_comm,inf_relIndex_right]
    exact hzq
  have hcard : Nat.card (Z d.radical a) = Nat.card (Z d.radical z) := by
    obtain ⟨u,_,he⟩ := stabilizer_transitive_neighbors d.radical t
      (adjacent_symm d.radical hat) (adjacent_symm d.radical hzt)
    rw [←he,Z_act,card_map_of_injective (MulAut.conj u⁻¹).injective]
  let := finite_Z d.radical a
  let := finite_Z d.radical z
  let I := Z d.radical a ⊓ Z d.radical z
  let : Finite I := Finite.of_injective (inclusion inf_le_left) (inclusion_injective _)
  have haI := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) I
    (Z d.radical a) bot_le inf_le_left
  have hzI := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) I
    (Z d.radical z) bot_le inf_le_right
  have hIA : I.relIndex (Z d.radical a) = (Z d.radical z).relIndex (Z d.radical a) := by
    change (Z d.radical a ⊓ Z d.radical z).relIndex (Z d.radical a) = _
    rw [inf_comm,inf_relIndex_right]
  have hIZ : I.relIndex (Z d.radical z) = (Z d.radical a).relIndex (Z d.radical z) :=
    inf_relIndex_right _ _
  rw [relIndex_bot_left,relIndex_bot_left,hIA] at haI
  rw [relIndex_bot_left,relIndex_bot_left,hIZ,hzindex] at hzI
  have hi : (Z d.radical z).relIndex (Z d.radical a) = 2^n := by
    have hp : 0 < Nat.card I := Nat.card_pos
    nlinarith
  exact ⟨hi,hzindex⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo
