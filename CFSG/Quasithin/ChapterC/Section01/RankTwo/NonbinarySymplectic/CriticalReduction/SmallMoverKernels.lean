module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallMovers
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.SmallMovers.DegreeKernels

/-!
# The full fixed kernels in the replacement root case

The same small-mover coordinates and exact centralizer indices put the
maximum-small-mover join in the centralizer of every field-sized actor
modulo Q. Lifting through the full Q-kernel normalizes the fixed subgroup
on every normalized layer centralized by Q, in particular the full Z-layer.
At a field-sized critical pair, the final edge therefore normalizes the
literal endpoint intersection Z_end intersect Q_start. No central fixed
factor is removed.

This supplies the fixed-kernel normalization used in MS93 (5.7), p.919.
The source's special parabolic generators are still needed to extend this
normality to the full vertex stabilizer; no distance exclusion is asserted.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

theorem Input.replacement_small_mover_join_normalizes_field_fixed
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical)) (hAT : A ≤ Q d.radical t)
    (hsmall : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F)
    (W : Subgroup (FreeAmalgam d.radical))
    (hWS : W ≤ stabilizer d.radical a)
    (hnW : stabilizer d.radical a ≤ normalizer (W : Set (FreeAmalgam d.radical)))
    (hWQ : W ≤ centralizer (Q d.radical a : Set (FreeAmalgam d.radical))) :
    Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2) ≤
      normalizer ((W ⊓ centralizer (A : Set (FreeAmalgam d.radical)) :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  obtain ⟨E,hE,f,hf,hfQ,hTf,hidx⟩ := h.replacement_small_mover_coordinates d geometry hb ha hat
  have hcard : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let A₀ := A.subgroupOf S
  let W₀ := W.subgroupOf S
  let := finite_stabilizer d.radical a
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hTS : Q d.radical t ≤ S := by
    change Q d.radical t ≤ stabilizer d.radical a
    rw [←hjr,←hjR]
    exact map_le_range j _
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    apply map_injective S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le (show Q d.radical a ≤ S from fun _ hx => hx.1)]
  have hkT : f.ker ≤ T := by rw [hQeq]; exact comap_mono hQT
  have hUK : U₀ ≤ centralizer (f.ker : Set S) := by
    intro u hu k hk
    apply Subtype.val_injective
    have hkQ : k.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hk
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))
      (U_le_Z a hu) k.val hkQ)
  have hiA : (centralizer (A₀ : Set S)).relIndex U₀ ≤ Nat.card E.Carrier := by
    rw [←Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective U₀ A₀,
      map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le (hAT.trans hTS),hcard]
    exact hsmall
  have hc := Degree.Quotient.join_image_centralizes_field_actor U₀ T f unipotent.subtype
    Subtype.val_injective hkT hUK (by simpa only [range_subtype] using hTf)
    hidx A₀ (comap_mono hAT) hiA
  have hKW : f.ker ≤ centralizer (W₀ : Set S) := by
    intro k hk w hw
    apply Subtype.val_injective
    have hkQ : k.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hk
    exact (hWQ hw k.val hkQ).symm
  have hn : T ≤ normalizer (W₀ : Set S) := by
    apply le_normalizer_iff.mpr
    intro x hx w hw
    exact (mem_normalizer_iff.mp (hnW x.property) w.val).mp hw
  have hnJ := normalizes_fixed_of_commuting_action_images W₀
    (Subgroup.SmallMover.join U₀ f.ker T (Nat.card E.Carrier ^ 2)) A₀ f
    ((Subgroup.SmallMover.join_le _ _ _ _).trans hn) hKW hc
  have hm := (map_mono (f := S.subtype) hnJ).trans
    ((W₀ ⊓ centralizer (A₀ : Set S)).le_normalizer_map S.subtype)
  rw [Subgroup.SmallMover.join_map S.subtype S.subtype_injective,
    map_subgroupOf_eq_of_le hUS,hfQ,map_subgroupOf_eq_of_le hTS,
    ←map_inf_centralizer_of_injective S.subtype S.subtype_injective,
    map_subgroupOf_eq_of_le hWS,map_subgroupOf_eq_of_le (hAT.trans hTS),hcard] at hm
  exact hm

theorem Input.replacement_small_mover_join_normalizes_full_seed_fixed
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical)) (hAT : A ≤ Q d.radical t)
    (hsmall : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F) :
    Subgroup.SmallMover.join (U d.radical a) (Q d.radical a) (Q d.radical t) (Nat.card F ^ 2) ≤
      normalizer ((Z d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) :
        Subgroup (FreeAmalgam d.radical)) : Set _) :=
  h.replacement_small_mover_join_normalizes_field_fixed d geometry hb ha hat A hAT hsmall
    (Z d.radical a) (Z_le_stabilizer d.radical a) (Z_normalized d.radical a)
    (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha))

/-- In the field-sized critical case, the small-mover join at the final
edge normalizes the full endpoint intersection, with its central kernel. -/
theorem Input.replacement_root_small_movers_normalize_intersection
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hroot : (Q d.radical a).relIndex (Z d.radical z) = Nat.card F) :
    Subgroup.SmallMover.join (U d.radical z) (Q d.radical z)
      (Q d.radical (path.walk.getVert (path.walk.length - 1))) (Nat.card F ^ 2) ≤
      normalizer ((Z d.radical z ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
  have hlen := path.length_eq_b
  have hat : Adjacent d.radical z (path.walk.getVert (path.walk.length - 1)) := by
    have hh := path.walk.adj_getVert_succ (i := path.walk.length - 1) (by omega)
    rw [Nat.sub_add_cancel (by omega : 1 ≤ path.walk.length),SimpleGraph.Walk.getVert_length] at hh
    exact adjacent_symm _ ((cosetGraph_adj _ _ _).mp hh)
  have hAT : Z d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length - 1)) := by
    apply Z_le_Q_of_dist_lt _ a (geometry.exists_critical a path.start_color)
    rw [path.dist_start (Nat.sub_le _ _),geometry.distance_constant a path.start_color]
    change path.walk.length - 1 < geometry.b d.radical
    omega
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hC : C d.radical a = Q d.radical a := MSCentralOrbit.C_eq_Q _
    (h.replacement_two_group d) (h.replacement_core_le d)
    (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have he : Z d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) =
      Z d.radical z ⊓ Q d.radical a := by
    rw [←hC]
    change Z d.radical z ⊓ centralizer _ = Z d.radical z ⊓ (stabilizer _ a ⊓ centralizer _)
    ext x
    exact ⟨fun hx => ⟨hx.1,hzS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  have hidx : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z) = Nat.card F := by
    rw [←inf_relIndex_left,he,inf_relIndex_left,hroot]
  let := finite_Z d.radical z
  have hsmall : (centralizer (Z d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical z) ≤ Nat.card F :=
    (relIndex_le_of_le_right (U_le_Z z) index_ne_zero_of_finite).trans_eq hidx
  have hn := h.replacement_small_mover_join_normalizes_full_seed_fixed d geometry hb
    path.end_color hat (Z d.radical a) hAT hsmall
  rwa [he] at hn

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
