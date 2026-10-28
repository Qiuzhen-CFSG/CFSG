module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.XDecomposition
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.InnerAction

/-!
# Whole-X decomposition in the small critical-image branch

Reciprocal critical indices below q squared are both q. The marked root
fixes a natural hyperplane in the opposite cover, so it moves at most q
cosets of the entire X-layer. Four root conjugates generate the component;
the natural moving cover fills their movement bound. Consequently
X = U C_X(Ltilde), retaining the entire central attachment.

The proof reuses the arbitrary-degree whole-X coordinates and marked-root
calculation in DistanceTwoRecognition. It applies at every positive critical
distance. At distance at least four, the proved inner-action reduction gives
G_alpha = Ltilde_alpha Q_alpha, identifying the fixed factor with C_X(G_alpha).
UnequalRootLarge applies this equality to the genuine nonsplitting exception.

Source: MS93 (3.3)(ii)(2), printed pp.866--867, and (5.5)(c), pp.915--917.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open DistanceTwoRecognition
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A critical index below q squared bounds movement on the whole X-layer
by q, at the original field degree. -/
theorem Input.replacement_small_critical_X_movement
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : 0 < g.b d.radical)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2) :
    (centralizer (Z d.radical z : Set (FreeAmalgam d.radical))).relIndex (X d.radical a) ≤ 2^n := by
  let := DistanceTwoRecognition.replacementComponent_normal h d
  let s := DistanceTwoRecognition.replacementMovedSection h d
  obtain ⟨he,ha⟩ := DistanceTwoRecognition.replacement_critical_indices_eq_field_of_small h d path hb (by simpa only [h.field_card] using hsmall)
  obtain ⟨⟨E,hE,e,hecov,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩⟩ :=
    DistanceTwoRecognition.replacement_ambient_initial_cover_at_vertex h d path.end_color
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
  have hCa := MSCentralOrbit.C_eq_Q d.radical (DistanceTwoRecognition.replacement_isPGroup h d)
    (DistanceTwoRecognition.replacement_core_le h d) (DistanceTwoRecognition.replacement_omegaOrbit_centralizer h d) a path.start_color
  obtain ⟨β,hβcard,hβmark,hβ,hd,hquad⟩ := inner_root_actor_of_field_index path (by omega)
    hCa h.nonbinary hFcard s e hecov (DistanceTwoRecognition.replacement_component_image_structure h d).2.2.2.2
    j hj hjr δ hδ hδcard (ha.trans hFcard.symm)
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFcard]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hh := critical_X_movement_bound_of_vertex_coordinates path (by omega)
    (MSCentralOrbit.edgeCentralizerCondition d.radical (DistanceTwoRecognition.replacement_isPGroup h d)
      (DistanceTwoRecognition.replacement_core_le h d) (DistanceTwoRecognition.replacement_omegaOrbit_centralizer h d)) hCa hcard
    s e hecov (DistanceTwoRecognition.replacement_component_image_structure h d).2.2.2.2 j hj hjr κ hκC hconj β hβ hd
  rwa [hFcard] at hh


/-- The four-root movement budget yields the complete X decomposition
from the actual small critical index. -/
theorem Input.replacement_small_critical_X_decomposition
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : 0 < g.b d.radical)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2) :
    X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical))) := by
  let := DistanceTwoRecognition.replacementComponent_normal h d
  let ρ := DistanceTwoRecognition.replacementRepresentation h d
  let s := DistanceTwoRecognition.replacementMovedSection h d
  obtain ⟨E,hE,e,he⟩ := DistanceTwoRecognition.replacement_centralOmega_initial_cover h d
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  obtain ⟨j,hj,hjr,hjUr,κ,hκ,hκQ,hκC,hκL,hfull,f,hf,hfconj⟩ :=
    DistanceTwoRecognition.replacement_fullX_coordinates_at_vertex h d path.start_color E e
  let jU := j.comp s.space.toSubmodule.subtype.toAddMonoidHom.toMultiplicative
  have hjU : Function.Injective jU := by
    intro x y hh
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (hj hh)
  obtain ⟨haq,hzq⟩ := DistanceTwoRecognition.replacement_critical_indices_eq_field_of_small h d path (by omega)
    (by simpa only [h.field_card] using hsmall)
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical (DistanceTwoRecognition.replacement_isPGroup h d)
    (DistanceTwoRecognition.replacement_core_le h d) (DistanceTwoRecognition.replacement_omegaOrbit_centralizer h d)
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
    (MSCentralOrbit.C_eq_Q d.radical (DistanceTwoRecognition.replacement_isPGroup h d) (DistanceTwoRecognition.replacement_core_le h d)
      (DistanceTwoRecognition.replacement_omegaOrbit_centralizer h d) z path.end_color)
    h.nonbinary hFc s e he (DistanceTwoRecognition.replacement_component_image_structure h d).2.2.2.2
    jU hjU hjUr δ hδ hδcard (haq.trans hFc.symm)
  let σ : Representation (ZMod 2) (L (K := E.Carrier))
      (Additive (omegaCenterIn (pCore 2 d.overgroup))) :=
    ρ.comp ((DistanceTwoRecognition.replacementComponent d).subtype.comp e.groupEquiv.symm.toMonoidHom)
  let W : Subrepresentation σ :=
    { toSubmodule := s.space.toSubmodule
      apply_mem_toSubmodule _g _v hv := s.space.apply_mem_toSubmodule _ hv }
  have hβfull (x : Z d.radical z) (v : Additive (omegaCenterIn (pCore 2 d.overgroup))) :
      j (Multiplicative.ofAdd (σ (β x) v)) =
        (x : FreeAmalgam d.radical)*j (Multiplicative.ofAdd v)*(x : FreeAmalgam d.radical)⁻¹ := by
    change j (Multiplicative.ofAdd (ρ (e.groupEquiv.symm (β x)) v)) = _
    exact (congrArg (fun y => j (Multiplicative.ofAdd (ρ y v))) (hβmark x)).trans
      (hfull (inclusion hZA x) v)
  have hbound := h.replacement_small_critical_X_movement d path hb hsmall
  have hcard : 2 < Nat.card E.Carrier := by
    rw [hFc]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  exact X_eq_moving_sup_centralizer_of_movement hcard σ W
    (MovedSection.coverProjection s e) he (Z d.radical z) β hβcard
    hβdim hβquad j hj hjr hjUr hβfull (by rwa [hFc]) f hfconj

/-- In the large-distance branch the residual and Q fill the whole vertex
stabilizer. The small critical index therefore splits X over the literal
ambient-fixed subgroup, with all central attachments retained. -/
theorem Input.replacement_root_X_decomposition_center
    {g : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical g a z) (hb : 4 ≤ g.b d.radical)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2) :
    X d.radical a = U d.radical a ⊔
      (X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
  have hpos : 0 < g.b d.radical := by omega
  have hedge := MSCentralOrbit.edgeCentralizerCondition d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d)
  let rev : CriticalPath d.radical g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical g hedge a path.start_color
        (by rwa [g.distance_constant a path.start_color]) z path.end_color path.critical }
  have hi := h.replacement_small_critical_indices_eq_field d rev hpos hsmall
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hforward : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2 := by
    rw [hi.2]
    nlinarith
  obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := vertex_coordinates_with_kernel d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) path.start_color
  have hS : Ltilde d.radical a ⊔ Q d.radical a = stabilizer d.radical a := by
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d g hb,←MonoidHom.range_eq_map,hir]
  have hfixed : X d.radical a ⊓ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) =
      X d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    apply le_antisymm
    · intro x hx
      refine ⟨hx.1,?_⟩
      have hL : Ltilde d.radical a ≤ centralizer ({x} : Set (FreeAmalgam d.radical)) :=
        fun y hy => mem_centralizer_singleton_iff.mpr (hx.2 y hy)
      have hQ : Q d.radical a ≤ centralizer ({x} : Set (FreeAmalgam d.radical)) :=
        fun y hy => mem_centralizer_singleton_iff.mpr
          (Q_le_centralizer_X d.radical a hy x hx.1).symm
      intro y hy
      exact mem_centralizer_singleton_iff.mp ((sup_le hL hQ) (hS.symm ▸ hy))
    · exact inf_le_inf_left _ (centralizer_le (Ltilde_le_stabilizer a))
  rw [←hfixed]
  exact h.replacement_small_critical_X_decomposition d path hpos hforward


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
