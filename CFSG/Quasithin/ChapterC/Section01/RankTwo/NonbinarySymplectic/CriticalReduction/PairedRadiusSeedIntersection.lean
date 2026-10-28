module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PairedRadiusTerminalInsertion
public import Theory.SpecificGroups.SymplecticFour.QuadraticMovingPlane

/-!
# Strict movement identifies the full neighboring seed intersection

The part of a neighboring seed fixed by the original kernel lies in X at
the original vertex. Its residual displacement lies in U, so it belongs
to the literal B-preimage. Strict B-relative movement therefore forces
the kernel to move more than q cosets of the neighboring natural layer.
Inside the common quadratic mover, this identifies its fixed plane with
the full mover's fixed plane. The whole-Z decomposition retains every
vertex-central attachment when lifting that equality.

Consequently the intersection of two equal-mover seeds is exactly the
full mover-fixed part of either seed. On an actual critical path above
distance four, both mover equality and strict movement are already proved.
This supplies the seed-intersection input to MS93 (5.6), (5.11), without
assuming opposition of the original and selected parabolic planes or
the remaining preceding-vertex noncentrality.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Theory.SpecificGroups.SymplecticFour
open scoped Pointwise IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem moving_actor_fixed
    (geometry : Geometry d.radical) (hb : 4 < geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t)
    (A : Subgroup (FreeAmalgam d.radical))
    (hAJ : A ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2))
    (hmove : Nat.card F < (centralizer (A : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a)) :
    U d.radical a ⊓ centralizer (A : Set (FreeAmalgam d.radical)) =
      U d.radical a ⊓ centralizer (Subgroup.SmallMover.join (U d.radical a)
        (Q d.radical a) (Q d.radical t) (Nat.card F^2) : Set _) := by
  let S := stabilizer d.radical a
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm _ hat))
  have hAS : A ≤ S := hAJ.trans hJS
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer _ a)
  obtain ⟨E,hE,f,hf,hfQ,hTf,hindex,hJP,hcore,hTP,hquad,hmax⟩ :=
    h.replacement_maximizing_parabolic_contains_mover_of_four_lt d geometry hb ha hat
  let P := (CentralRootGeometry.wing (F := E.Carrier) true).map unipotent.subtype
  let A₀ := A.subgroupOf S
  let J₀ := J.subgroupOf S
  let σ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
  have hJf : J₀.map f ≤ P := (map_le_iff_le_comap).mpr hJP
  have hcard : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have bridge (T : Subgroup (Sp E.Carrier)) :
      fixedSpace σ T=(TwoLocalCover.fixedSpace T).restrictScalars (ZMod 2) := by
    ext v
    exact ⟨fun hv x hx => hv ⟨x,hx⟩,fun hv x => hv x.val x.property⟩
  have hAi := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
    ((U d.radical a).subgroupOf S) A₀
  rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hAS,hindex] at hAi
  have hquot : 2 ^ fixedCodim σ (A₀.map f) =
      Nat.card (Vector E.Carrier ⧸ TwoLocalCover.fixedSpace (A₀.map f)) := by
    change 2 ^ Module.finrank (ZMod 2) (Vector E.Carrier ⧸ fixedSpace σ (A₀.map f)) = _
    rw [bridge]
    have hh := Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv (ZMod 2)
      (TwoLocalCover.fixedSpace (A₀.map f))).toEquiv
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod] at hh
    exact hh
  have hbig : Nat.card E.Carrier <
      Nat.card (Vector E.Carrier ⧸ TwoLocalCover.fixedSpace (A₀.map f)) := by
    rw [hcard,←hquot]
    exact hAi ▸ hmove
  have hfixed := moving_quadratic_subactor_fixed_eq (A₀.map f) (J₀.map f)
    (map_mono (comap_mono hAJ))
    (fun x hx y hy v => CentralRootGeometry.SmallMovers.Degree.plane_radical_quadratic
      x (hJf hx) y (hJf hy) v) hbig
  have hfixed' : fixedSpace σ (A₀.map f)=fixedSpace σ (J₀.map f) := by
    rw [bridge,bridge,hfixed]
  have hJi := Subgroup.SmallMover.centralizer_index_map S.subtype S.subtype_injective
    ((U d.radical a).subgroupOf S) J₀
  rw [map_subgroupOf_eq_of_le hUS,map_subgroupOf_eq_of_le hJS,hindex] at hJi
  have hi : (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) =
      (centralizer (J : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) := by
    rw [hAi,hJi]
    change 2 ^ fixedCodim σ (A₀.map f)=2 ^ fixedCodim σ (J₀.map f)
    unfold fixedCodim
    rw [hfixed']
  let := finite_Z d.radical a
  let : Finite (U d.radical a) := Finite.of_injective
    (inclusion (U_le_Z a)) (inclusion_injective _)
  let CA := (centralizer (A : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical a)
  let CJ := (centralizer (J : Set (FreeAmalgam d.radical))).subgroupOf (U d.radical a)
  have he : CJ=CA := by
    apply eq_of_le_of_card_ge (comap_mono (centralizer_le hAJ))
    have hCA := CA.card_mul_index
    have hCJ := CJ.card_mul_index
    change CA.index=CJ.index at hi
    rw [hi] at hCA
    exact (Nat.eq_of_mul_eq_mul_right (index_ne_zero_of_finite (H := CJ)).bot_lt
      (hCA.trans hCJ.symm)).le
  apply le_antisymm
  · intro u hu
    exact ⟨hu.1,show (⟨u,hu.1⟩ : U d.radical a) ∈ CJ from he.symm ▸ hu.2⟩
  · exact inf_le_inf_left _ (centralizer_le hAJ)

omit [CharP F 2] in
private theorem core_le_mover
    {a t : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) :
    Q d.radical a ≤ Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) := by
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hh := map_mono (f := j) (Subgroup.SmallMover.kernel_le_join
    (Sp4Four.LocalPackage.initialLayer d.radical) (pCore 2 d.overgroup) d.radical
    (Nat.card F^2) (Nat.one_le_pow _ _ Nat.card_pos) (h.replacement_core_le d)
    (Sp4Four.LocalPackage.initialLayer_centralizes_core d.radical
      (h.replacement_two_group d) (h.replacement_core_le d)))
  rwa [Subgroup.SmallMover.join_map j hj,hjU,hjQ,hjR] at hh

/-- The strict original B-index identifies the full intersection of equal
mover seeds with the original mover-fixed seed, including every attachment. -/
theorem Input.replacement_equal_mover_seed_intersection_of_strict_movement
    (geometry : Geometry d.radical) (hb : 4 < geometry.b d.radical)
    {a t c : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c)) :
    Z d.radical a ⊓ Z d.radical c = Z d.radical a ⊓ centralizer
      (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have hc : color d.radical c=false := by
    have hh := adjacent_color_ne d.radical hat
    have hh' := adjacent_color_ne d.radical hct
    rw [ha] at hh
    cases ht : color d.radical t <;> cases hc : color d.radical c <;> simp_all
  have hJSa : J ≤ stabilizer d.radical a := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm _ hat))
  have hJSc : J ≤ stabilizer d.radical c := by
    dsimp only [J]
    rw [←hequal]
    exact (Subgroup.SmallMover.join_le _ _ _ _).trans
      (fun _ hx => hx.2 c (adjacent_symm _ hct))
  have hQaJ : Q d.radical a ≤ J := core_le_mover h d ha hat
  let C := U d.radical c ⊓ centralizer (Q d.radical a : Set (FreeAmalgam d.radical))
  have hZcV : Z d.radical c ≤ V d.radical a :=
    le_sup_left.trans (neighbor_seed_join_le_radius hat hct)
  have hCV : C ≤ V d.radical a := inf_le_left.trans ((U_le_Z c).trans hZcV)
  have hCX : C ≤ X d.radical a := by
    let := geometry.Z_elementary (by omega) c hc
    intro x hx
    exact mem_omegaCenter_iff.mpr ⟨(hCV.trans (geometry.V_le_Q (by omega) a ha)) hx,
      elemPow_eq_one_of_isElementaryAbelian x (U_le_Z c hx.1),hx.2⟩
  have hCB : C ≤ B d.radical a (geometry.Z_normal a) :=
    radius_le_B_of_commutator geometry (by omega) ha C hCV
      ((commutator_mono hCX le_rfl).trans
        ((h.replacement_X_commutator_eq_U d ha).le.trans (U_le_Z a)))
  let := finite_Z d.radical c
  let : Finite (U d.radical c) := Finite.of_injective
    (inclusion (U_le_Z c)) (inclusion_injective _)
  have hm : Nat.card F < (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical c) := by
    have hh := relIndex_le_of_le_left hCB (L := U d.radical c) index_ne_zero_of_finite
    dsimp only [C] at hh
    rw [inf_relIndex_left] at hh
    exact hmove.trans_le hh
  have hfixed : U d.radical c ⊓ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical c ⊓ centralizer (J : Set (FreeAmalgam d.radical)) := by
    have hh := moving_actor_fixed h d geometry hb hc hct (Q d.radical a)
      (by rw [hequal]; exact hQaJ) hm
    simpa only [hequal,J] using hh
  have hZfixed : Z d.radical c ⊓ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) ≤
      centralizer (J : Set (FreeAmalgam d.radical)) := by
    let D := Z d.radical c ⊓ centralizer (stabilizer d.radical c : Set (FreeAmalgam d.radical))
    have hDN : D ≤ normalizer (U d.radical c : Set (FreeAmalgam d.radical)) :=
      (inf_le_left.trans (Z_le_stabilizer _ c)).trans (U_normalized c)
    have hDJ : D ≤ centralizer (J : Set (FreeAmalgam d.radical)) :=
      inf_le_right.trans (centralizer_le hJSc)
    have hDQ : D ≤ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) :=
      hDJ.trans (centralizer_le hQaJ)
    intro z hz
    have hzprod : z ∈ (U d.radical c : Set (FreeAmalgam d.radical)) * (D : Set _) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ hDN]
      exact h.replacement_Z_eq_U_sup_fixed d geometry hb.le hc ▸ hz.1
    obtain ⟨u,hu,e,he,rfl⟩ := hzprod
    have huQ : u ∈ centralizer (Q d.radical a : Set (FreeAmalgam d.radical)) := by
      have hh := (centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).mul_mem hz.2
        ((centralizer (Q d.radical a : Set (FreeAmalgam d.radical))).inv_mem (hDQ he))
      simpa only [mul_inv_cancel_right] using hh
    exact (centralizer (J : Set (FreeAmalgam d.radical))).mul_mem
      (hfixed ▸ (show u ∈ U d.radical c ⊓ centralizer
        (Q d.radical a : Set (FreeAmalgam d.radical)) from ⟨hu,huQ⟩)).2 (hDJ he)
  apply le_antisymm
  · exact fun x hx => ⟨hx.1,hZfixed ⟨hx.2,
      commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a ha) hx.1⟩⟩
  · have hlarge : Nat.card F < (Q d.radical a).relIndex J := by
      have hh := h.replacement_small_mover_join_index d geometry hb.le ha hat
      have hq : 1 < Nat.card F := Finite.one_lt_card
      exact lt_of_lt_of_le (by nlinarith) hh
    have hh := h.replacement_equal_mover_large_actor_fixed_le_seed d geometry hb ha hat hct
      hequal J le_rfl hlarge (Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)))
      inf_le_left (commutator_eq_bot_iff_le_centralizer.mpr inf_le_right)
    exact le_inf inf_le_left (hh.trans inf_le_left)

/-- The actual critical path supplies both strict movement and equality of
the first two movers, so its full seed intersection has no extra premise. -/
theorem Input.replacement_path_seed_intersection_of_four_lt
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 < geometry.b d.radical) :
    Z d.radical a ⊓ Z d.radical (path.walk.getVert 2) = Z d.radical a ⊓ centralizer
      (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    have hh := (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using hh
  have hct : Adjacent d.radical (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm _ ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hequal : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
      (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 1))
      (Nat.card F^2) = Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) := by
    simpa only [pathMoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero]
      using h.replacement_mover_agreement_of_four_lt d ⟨a,z,path⟩ hb
  exact h.replacement_equal_mover_seed_intersection_of_strict_movement d geometry hb
    path.start_color hat hct hequal (h.replacement_path_moving_index_gt_field d path hb)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
