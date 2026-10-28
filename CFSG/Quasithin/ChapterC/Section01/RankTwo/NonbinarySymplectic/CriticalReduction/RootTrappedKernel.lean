module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootFixedKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootSplitting
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SmallMoverKernels
public import Theory.Representation.SymplecticFourOrthogonalCover.HyperplaneMovement

/-!
# Both generators normalize the trapped root's full fixed kernel

The full-cover hyperplane bound applies to the actual trapped neighboring
seed and the distant X-intersection. Its commutator has order at most q.
Symplectic duality bounds the kernel index on the whole moving layer by q,
so the same individual small-mover join normalizes the full Z-fixed kernel.
The saved critical-intersection calculation supplies endpoint normalization.
All central attachments and the original field degree are retained.

RootTrappedPaths uses both normalizations with individual residual generation
to exclude this trapped alternative. Source: MS93 (5.7), printed p.919,
using (3.3)(ii), p.867.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Theory.SpecificGroups.SymplecticFour.TwoLocalCover
open scoped commutatorElement IsMulCommutative

open Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
open scoped Pointwise

private theorem commutator_fixed_supplement_bound
    {G : Type*} [Group G] (X U D Y T : Subgroup G)
    (hX : X=U ⊔ D) (hDU : D ≤ normalizer (U : Set G))
    (hDY : D ≤ centralizer (Y : Set G)) (hTY : T ≤ Y) :
    ⁅Y,X ⊓ centralizer (T : Set G)⁆ ≤ ⁅Y,U ⊓ centralizer (T : Set G)⁆ := by
  apply commutator_le.mpr
  intro y hy x hx
  have hx' : x ∈ (U : Set G)*(D : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left U D hDU,←hX]
    exact hx.1
  obtain ⟨u,hu,c,hc,rfl⟩ := hx'
  have huT : u ∈ centralizer (T : Set G) := by
    have hh := (centralizer (T : Set G)).mul_mem hx.2
      ((centralizer (T : Set G)).inv_mem ((centralizer_le hTY) (hDY hc)))
    simpa only [mul_inv_cancel_right] using hh
  have hcY : ⁅y,c⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hDY hc y hy)
  rw [commutatorElement_mul_right_eq_mul_conj,hcY,mul_one,mul_inv_cancel_right]
  exact commutator_mem_commutator hy ⟨hu,huT⟩

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual trapped seed moves the full distant X-intersection in at
most q elements, retaining every central attachment. -/
theorem Input.replacement_trapped_root_commutator_card_le_field
    {geometry : Geometry d.radical} {a z t v : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    Nat.card (⁅Z d.radical v,X d.radical z ⊓ Q d.radical a⁆ :
      Subgroup (FreeAmalgam d.radical)) ≤ Nat.card F := by
  let Y := Z d.radical v ⊔ Z d.radical a
  let A := X d.radical z ⊓ Q d.radical a
  have hYV : Y ≤ V d.radical a := neighbor_seed_join_le_radius hat hvt
  have hYQ : Y ≤ Q d.radical a := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have haQ : Z d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
    apply Z_le_Q_of_dist_lt _ a (geometry.exists_critical a path.start_color)
    rw [path.dist_start (Nat.sub_le _ _),geometry.distance_constant a path.start_color]
    have hh := path.length_eq_b
    change path.walk.length-2 < geometry.b d.radical
    omega
  have hYtr : Y ≤ V d.radical a ⊓ Q d.radical (path.walk.getVert (path.walk.length-2)) :=
    le_inf hYV (sup_le htrap haQ)
  have hYS : Y ≤ stabilizer d.radical z := hYtr.trans
    (truncated_radius_le_endpoint_stabilizer path (by omega))
  have hvS : Z d.radical v ≤ stabilizer d.radical z := le_sup_left.trans hYS
  obtain ⟨hi,hi'⟩ := h.replacement_critical_indices_eq_field_of_seed_escape d path
    (by omega) (Z d.radical v) hvS (le_sup_left.trans hYQ) hn
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2 := by
    rw [hi]; nlinarith
  have hCa := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) a path.start_color
  have hUS : U d.radical z ≤ stabilizer d.radical a :=
    (U_le_Z z).trans (path.endpoint_Z_le_start_stabilizer (by omega))
  have hAU : U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) =
      U d.radical z ⊓ Q d.radical a := by
    rw [←hCa]
    ext x
    exact ⟨fun hx => ⟨hx.1,hUS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  have hZX : Z d.radical z ≤ X d.radical z := geometry.omega_bound z path.end_color
    (by rw [geometry.distance_constant z path.end_color]; exact lt_of_lt_of_le (by decide : 0 < 4) hb)
  have hUA : U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) ≤ A := by
    rw [hAU]
    exact inf_le_inf ((U_le_Z z).trans hZX) le_rfl
  have hvcolor : color d.radical v=false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hvt
    rw [path.start_color] at h1
    cases ht : color d.radical t <;> cases hv : color d.radical v <;> simp_all
  have hAnv : A ≤ normalizer (Z d.radical v : Set (FreeAmalgam d.radical)) :=
    (inf_le_right.trans (Q_le_stabilizer_of_dist_le_two a v path.start_color hvcolor
      (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hat hvt))).trans
        (Z_normalized d.radical v)
  have hAna : A ≤ normalizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    (inf_le_right.trans (fun _ hx => hx.1)).trans (Z_normalized d.radical a)
  have hAn : A ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    intro x hx
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_sup,mem_normalizer_iff_map_conj_eq.mp (hAnv hx),
      mem_normalizer_iff_map_conj_eq.mp (hAna hx)]
  have hquad : ⁅⁅A,Y⁆,Y⁆=⊥ := le_bot_iff.mp
    ((commutator_mono (commutator_mono le_rfl hYtr) hYtr).trans_eq
      (h.replacement_radius_commutator_bounds d geometry hb path.start_color z
        (path.walk.getVert (path.walk.length-2))).2)
  have hpos : 0 < geometry.b d.radical := by omega
  let rev : CriticalPath d.radical geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        a path.start_color (by rwa [geometry.distance_constant a path.start_color]) z path.end_color path.critical }
  let D := X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))
  have hsplit : X d.radical z=U d.radical z ⊔ D :=
    h.replacement_root_X_decomposition_center d rev hb hsmall
  have hDY : D ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hYS)
  have hbadU : ¬ U d.radical z ≤ normalizer (Y : Set (FreeAmalgam d.radical)) := by
    intro hh
    exact hn (hZX.trans (hsplit ▸ sup_le hh (hDY.trans (Subgroup.centralizer_le_normalizer _))))
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d path.end_color
  have hFc : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let β := (e.groupEquiv.toMonoidHom.comp κC).comp (inclusion hYS)
  let σ := MovedSection.coverAction s e
  let p := MovedSection.coverProjection s e
  have hact (y : Y) (w : s.space.toSubmodule) : j (Multiplicative.ofAdd (σ (β y) w))=
      y.val*j (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hYS y)))) w))=_
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hYS y) w
  let βT := β.comp (inclusion (show Z d.radical a ≤ Y from le_sup_right))
  have hcard : Nat.card βT.range=Nat.card E.Carrier := by
    have hmark : βT.ker=(Q d.radical z).subgroupOf (Z d.radical a) := by
      ext x
      change e.groupEquiv (κC (inclusion hYS (inclusion le_sup_right x)))=1 ↔ x.val ∈ Q d.radical z
      rw [e.groupEquiv.map_eq_one_iff]
      have heq : κC (inclusion hYS (inclusion le_sup_right x))=1 ↔
          inclusion hYS (inclusion le_sup_right x) ∈ κ.ker := Subtype.ext_iff
      rw [heq]
      constructor
      · intro hx
        exact hκQ ▸ mem_map_of_mem (stabilizer d.radical z).subtype hx
      · intro hx
        obtain ⟨y,hy,hyx⟩ := hκQ.symm ▸ hx
        have he : y=inclusion hYS (inclusion le_sup_right x) := Subtype.ext hyx
        exact he ▸ hy
    rw [←index_ker,hmark]
    exact hi.trans hFc.symm
  have hactT (x : Z d.radical a) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (βT x) w))=x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ :=
    hact (inclusion le_sup_right x) w
  obtain ⟨hd,hrootquad⟩ := critical_root_coordinates_of_reciprocal_index_field path hpos hCa hFl
    σ p he j hj hjr βT hactT hcard (hi'.trans hFc.symm)
  have hcomm : ⁅Z d.radical a,j.range⁆ ≤ Z d.radical a := by
    rw [hjr]
    exact (commutator_mono le_rfl (U_le_Z z)).trans (critical_commutator_le_start_seed path)
  have hcent : Y ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    hYQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a path.start_color)))
  have hbound := HyperplaneMovement.embedded_root_hyperplane_bound hFl p he j hj Y
    (Z d.radical a) le_sup_right β hact hcard hd hrootquad hcomm hcent
    (by rw [hjr]; exact le_bot_iff.mp ((commutator_mono (commutator_mono hUA le_rfl) le_rfl).trans_eq hquad))
    (by rw [hjr]; exact hUA.trans hAn) (by rwa [hjr])
  rw [hjr,hFc] at hbound
  have hDU : D ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans ((centralizer_le ((U_le_Z z).trans (Z_le_stabilizer d.radical z))).trans
      (Subgroup.centralizer_le_normalizer _))
  have hAX : X d.radical z ⊓ Q d.radical a ≤
      X d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    rw [←hCa]
    exact inf_le_inf_left _ inf_le_right
  have hle : ⁅Z d.radical v,A⁆ ≤
      ⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ :=
    (commutator_mono le_sup_left hAX).trans
      (commutator_fixed_supplement_bound _ _ _ _ _ hsplit hDU hDY le_sup_right)
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective (inclusion (U_le_Z z)) (inclusion_injective _)
  have hCU : ⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ ≤ U d.radical z := by
    rw [commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hYS.trans (U_normalized z)))
  let : Finite (⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ :
      Subgroup (FreeAmalgam d.radical)) := Finite.of_injective (inclusion hCU) (inclusion_injective _)
  exact (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _)).trans hbound
end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
open Representation.BinaryOffender


variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Exact natural fixed indices bound the full moving-layer index by the
literal commutator order, at the original nonbinary degree. -/
theorem Input.replacement_moving_index_le_commutator_card
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a : Vertex d.radical} (ha : color d.radical a=false)
    (A : Subgroup (FreeAmalgam d.radical)) (hAS : A ≤ stabilizer d.radical a) :
    (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤
      Nat.card (⁅A,U d.radical a⁆ : Subgroup (FreeAmalgam d.radical)) := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d ha
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let β := (e.groupEquiv.toMonoidHom.comp κC).comp (inclusion hAS)
  let σ := MovedSection.coverAction s e
  apply HyperplaneMovement.embedded_fixed_index_le_commutator_card σ (MovedSection.coverProjection s e) he
    (U d.radical a) A j hj hjr β
  intro y w
  change j (Multiplicative.ofAdd (s.space.toRepresentation
    (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hAS y)))) w))=_
  rw [e.groupEquiv.symm_apply_apply]
  exact hconj (inclusion hAS y) w
end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
open Representation.SymplecticFourOrthogonalCover
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The actual smaller individual mover normalizes the same full fixed
kernel as the endpoint, and its moving-layer kernel has index at most q. -/
theorem Input.replacement_trapped_root_kernel_index_and_normalized
    {geometry : Geometry d.radical} {a z t v : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    let A := X d.radical z ⊓ Q d.radical a
    let D := (Z d.radical v ⊓ centralizer (A : Set (FreeAmalgam d.radical))) ⊔ Z d.radical a
    (centralizer (A : Set (FreeAmalgam d.radical))).relIndex (U d.radical v) ≤ Nat.card F ∧
      Subgroup.SmallMover.join (U d.radical v) (Q d.radical v) (Q d.radical t) (Nat.card F^2) ≤
        normalizer (D : Set (FreeAmalgam d.radical)) ∧
      Z d.radical z ≤ normalizer (D : Set (FreeAmalgam d.radical)) := by
  dsimp only
  let A := X d.radical z ⊓ Q d.radical a
  have hvcolor : color d.radical v=false := by
    have h1 := adjacent_color_ne d.radical hat
    have h2 := adjacent_color_ne d.radical hvt
    rw [path.start_color] at h1
    cases ht : color d.radical t <;> cases hv : color d.radical v <;> simp_all
  have hAS : A ≤ stabilizer d.radical v := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two a v path.start_color hvcolor
      (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hat hvt))
  have hnorm : A ≤ normalizer (Z d.radical v : Set (FreeAmalgam d.radical)) :=
    hAS.trans (Z_normalized d.radical v)
  have hcommZ : ⁅A,Z d.radical v⁆ ≤ Z d.radical v := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hnorm
  let := finite_Z d.radical v
  let : Finite (⁅A,Z d.radical v⁆ : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion hcommZ) (inclusion_injective _)
  have hbound : Nat.card (⁅A,U d.radical v⁆ : Subgroup (FreeAmalgam d.radical)) ≤ Nat.card F := by
    apply (Nat.card_le_card_of_injective (inclusion (commutator_mono le_rfl (U_le_Z v)))
      (inclusion_injective _)).trans
    rw [commutator_comm]
    exact h.replacement_trapped_root_commutator_card_le_field d path hb hat hvt hn htrap
  have hi := (h.replacement_moving_index_le_commutator_card d geometry hb hvcolor A hAS).trans hbound
  have ht : color d.radical t=true := by
    have hh := adjacent_color_ne d.radical hat
    rw [path.start_color] at hh
    cases hh' : color d.radical t <;> simp_all
  have hAT : A ≤ Q d.radical t := inf_le_right.trans (Q_le_adjacent_h d.radical ht hat)
  have hE := h.replacement_small_mover_join_normalizes_full_seed_fixed d geometry hb
    hvcolor hvt A hAT hi
  have hEa : Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical t) (Nat.card F^2) ≤ normalizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    (Subgroup.SmallMover.join_le _ _ _ _).trans
      ((show Q d.radical t ≤ stabilizer d.radical a from fun _ hx => hx.2 a (adjacent_symm _ hat)).trans
        (Z_normalized d.radical a))
  exact ⟨hi,(le_inf hE hEa).trans (normalizer_inf_normalizer_le_normalizer_sup _ _),
    (h.replacement_trapped_root_endpoint_normalizes_fixed_kernel d path hb hat hvt hn htrap).2⟩
end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
