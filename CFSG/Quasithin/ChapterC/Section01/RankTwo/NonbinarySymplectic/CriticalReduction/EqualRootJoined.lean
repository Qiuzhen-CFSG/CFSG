module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EqualRootCommutator
public import Theory.Representation.SymplecticFourOrthogonalCover.SubspaceMovement

/-!
# The joined trapped actor in the equal-mover root case

The equal-mover commutator bounds put both neighboring commutators with Q
in the starting seed. Thus a failed commutator comparison for their join
would normalize the escaping individual seed join, a contradiction.
The full-cover hyperplane calculation now bounds the literal joined
commutator by q, preserving the entire central attachment. Scalar multiples
of any nonzero displacement give the matching lower bound. Thus every
nontrivial individual commutator is the full joined commutator of order q.
EqualRootJoinedPaths applies these results at the original selector.

Source: MS93 (3.3)(ii) and (5.7), printed pp.867,919.
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
    (hDY : D ≤ centralizer (Y : Set G)) (hDT : D ≤ centralizer (T : Set G)) :
    ⁅Y,X ⊓ centralizer (T : Set G)⁆ ≤ ⁅Y,U ⊓ centralizer (T : Set G)⁆ := by
  apply commutator_le.mpr
  intro y hy x hx
  have hx' : x ∈ (U : Set G)*(D : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left U D hDU,←hX]
    exact hx.1
  obtain ⟨u,hu,c,hc,rfl⟩ := hx'
  have huT : u ∈ centralizer (T : Set G) := by
    have hh := (centralizer (T : Set G)).mul_mem hx.2
      ((centralizer (T : Set G)).inv_mem (hDT hc))
    simpa only [mul_inv_cancel_right] using hh
  have hcY : ⁅y,c⁆=1 := commutatorElement_eq_one_iff_mul_comm.mpr (hDY hc y hy)
  rw [commutatorElement_mul_right_eq_mul_conj,hcY,mul_one,mul_inv_cancel_right]
  exact commutator_mem_commutator hy ⟨hu,huT⟩

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem fixed_intersection_commutator_card_ge_field
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {z : Vertex d.radical} (hz : color d.radical z=false)
    (Y T : Subgroup (FreeAmalgam d.radical))
    (hYS : Y ≤ stabilizer d.radical z) (hTS : T ≤ stabilizer d.radical z)
    (hn : ⁅Y,U d.radical z ⊓ centralizer (T : Set (FreeAmalgam d.radical))⁆ ≠ ⊥) :
    Nat.card F ≤ Nat.card (⁅Y,U d.radical z ⊓ centralizer (T : Set (FreeAmalgam d.radical))⁆ :
      Subgroup (FreeAmalgam d.radical)) := by
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d hz
  have hFc : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hb
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let σ := MovedSection.coverAction s e
  let p := MovedSection.coverProjection s e
  have hact (y : stabilizer d.radical z) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (γ y) w))=y.val*j (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC y))) w))=_
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj y w
  have hlo := embedded_fixed_subspace_commutator_card_ge_field (F := E.Carrier) (σ := σ)
    p he j hj Y T (γ.comp (inclusion hYS)) (γ.comp (inclusion hTS))
    (fun y w => hact (inclusion hYS y) w) (fun t w => hact (inclusion hTS t) w)
    (by rwa [hjr])
  rwa [hFc,hjr] at hlo

/-- The full critical X-intersection admits no nontrivial commutator
smaller than the field. The proof retains its entire fixed attachment. -/
theorem Input.replacement_root_intersection_commutator_card_ge_field
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2)
    (Y : Subgroup (FreeAmalgam d.radical)) (hYS : Y ≤ stabilizer d.radical z)
    (hn : ⁅Y,X d.radical z ⊓ Q d.radical a⁆ ≠ ⊥) :
    Nat.card F ≤ Nat.card (⁅Y,X d.radical z ⊓ Q d.radical a⁆ :
      Subgroup (FreeAmalgam d.radical)) := by
  let A := X d.radical z ⊓ Q d.radical a
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
  let rev : CriticalPath d.radical geometry z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse d.radical geometry
        (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
          (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
        a path.start_color (by rw [geometry.distance_constant a path.start_color]; exact lt_of_lt_of_le (by decide : 0 < 4) hb)
        z path.end_color path.critical }
  let D := X d.radical z ⊓ centralizer (stabilizer d.radical z : Set (FreeAmalgam d.radical))
  have hsplit : X d.radical z=U d.radical z ⊔ D :=
    h.replacement_root_X_decomposition_center d rev hb hsmall
  have hDY : D ≤ centralizer (Y : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hYS)
  have hAZ : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  have hDT : D ≤ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hAZ)
  have hDU : D ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans ((centralizer_le ((U_le_Z z).trans (Z_le_stabilizer d.radical z))).trans
      (Subgroup.centralizer_le_normalizer _))
  have hAX : A ≤ X d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    change X d.radical z ⊓ Q d.radical a ≤ _
    rw [←hCa]
    exact inf_le_inf_left _ inf_le_right
  have heq : ⁅Y,A⁆=⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ :=
    le_antisymm ((commutator_mono le_rfl hAX).trans
      (commutator_fixed_supplement_bound _ _ _ _ _ hsplit hDU hDY hDT))
      (commutator_mono le_rfl hUA)
  have hlo := fixed_intersection_commutator_card_ge_field h d geometry hb path.end_color Y
    (Z d.radical a) hYS hAZ (by rwa [←heq])
  rwa [←heq] at hlo

/-- The joined trapped seeds move the full distant X-intersection in at
most q elements, from the exact commutator noncontainment premise. -/
theorem Input.replacement_equal_trapped_join_commutator_card_le_field
    {geometry : Geometry d.radical} {a z t v r w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (har : Adjacent d.radical a r) (hwr : Adjacent d.radical w r)
    (hvcomm : ⁅Z d.radical v,Q d.radical a⁆ ≤ Z d.radical a)
    (hwcomm : ⁅Z d.radical w,Q d.radical a⁆ ≤ Z d.radical a)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)))
    (htrapw : Z d.radical w ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    Nat.card (⁅Z d.radical v ⊔ Z d.radical w,X d.radical z ⊓ Q d.radical a⁆ :
      Subgroup (FreeAmalgam d.radical)) ≤ Nat.card F := by
  let Y := (Z d.radical v ⊔ Z d.radical w) ⊔ Z d.radical a
  let A := X d.radical z ⊓ Q d.radical a
  have hvV := neighbor_seed_join_le_radius hat hvt
  have hwV := neighbor_seed_join_le_radius har hwr
  have hYV : Y ≤ V d.radical a :=
    sup_le (sup_le (le_sup_left.trans hvV) (le_sup_left.trans hwV)) (le_sup_right.trans hvV)
  have hYQ : Y ≤ Q d.radical a := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have haQ : Z d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2)) := by
    apply Z_le_Q_of_dist_lt _ a (geometry.exists_critical a path.start_color)
    rw [path.dist_start (Nat.sub_le _ _),geometry.distance_constant a path.start_color]
    have hh := path.length_eq_b
    change path.walk.length-2 < geometry.b d.radical
    omega
  have hYtr : Y ≤ V d.radical a ⊓ Q d.radical (path.walk.getVert (path.walk.length-2)) :=
    le_inf hYV (sup_le (sup_le htrap htrapw) haQ)
  have hYS : Y ≤ stabilizer d.radical z := hYtr.trans
    (truncated_radius_le_endpoint_stabilizer path (by omega))
  have hvS : Z d.radical v ≤ stabilizer d.radical z := le_sup_left.trans (le_sup_left.trans hYS)
  obtain ⟨hi,hi'⟩ := h.replacement_critical_indices_eq_field_of_seed_escape d path
    (by omega) (Z d.radical v) hvS (le_sup_left.trans (le_sup_left.trans hYQ)) hn
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
  have hYn : Y ≤ normalizer (Z d.radical a : Set (FreeAmalgam d.radical)) :=
    (hYQ.trans (fun _ hx => hx.1)).trans (Z_normalized _ a)
  have hYA : ⁅Y,A⁆ ≤ Z d.radical a := by
    apply commutator_sup_le_of_relative_normal Y (Z d.radical v ⊔ Z d.radical w)
      (Z d.radical a) A (Z d.radical a) hYn le_sup_left le_sup_right
    · exact commutator_sup_le_of_relative_normal Y (Z d.radical v) (Z d.radical w)
        A (Z d.radical a) hYn (le_sup_left.trans le_sup_left) (le_sup_right.trans le_sup_left)
        ((commutator_mono le_rfl inf_le_right).trans hvcomm)
        ((commutator_mono le_rfl inf_le_right).trans hwcomm)
    · exact (commutator_mono le_rfl inf_le_right).trans_eq
        (geometry.centralizes a path.start_color) |>.trans bot_le
  have hbadU : ¬ ⁅Y,U d.radical z⁆ ≤ Z d.radical a ⊔
      ⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ := by
    intro hc
    have hcZa : ⁅Y,U d.radical z⁆ ≤ Z d.radical a := hc.trans
      (sup_le le_rfl ((commutator_mono le_rfl hUA).trans hYA))
    apply hn
    have hUn : U d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      apply le_normalizer_iff_commutator_le_left.mpr
      exact ((commutator_mono (sup_le (le_sup_left.trans le_sup_left) le_sup_right)
        le_rfl).trans hcZa).trans le_sup_right
    have hVY : Z d.radical v ⊔ Z d.radical a ≤ Y :=
      sup_le (le_sup_left.trans le_sup_left) le_sup_right
    have hDn : D ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) :=
      (hDY.trans (centralizer_le hVY)).trans
          (Subgroup.centralizer_le_normalizer _)
    exact hZX.trans (hsplit ▸ sup_le hUn hDn)
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
  have hbound := HyperplaneMovement.embedded_root_hyperplane_bound_of_comparison hFl p he j hj Y
    (Z d.radical a) le_sup_right β hact hcard hd hrootquad hcomm hcent
    (by rw [hjr]; exact le_bot_iff.mp ((commutator_mono (commutator_mono hUA le_rfl) le_rfl).trans_eq hquad))
    (by rwa [hjr])
  rw [hjr,hFc] at hbound
  have hDU : D ≤ normalizer (U d.radical z : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans ((centralizer_le ((U_le_Z z).trans (Z_le_stabilizer d.radical z))).trans
      (Subgroup.centralizer_le_normalizer _))
  have hAX : X d.radical z ⊓ Q d.radical a ≤
      X d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical)) := by
    rw [←hCa]
    exact inf_le_inf_left _ inf_le_right
  have hle : ⁅Z d.radical v ⊔ Z d.radical w,A⁆ ≤
      ⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ :=
    (commutator_mono le_sup_left hAX).trans
      (commutator_fixed_supplement_bound _ _ _ _ _ hsplit hDU hDY (hDY.trans (centralizer_le (show Z d.radical a ≤ Y from le_sup_right))))
  let := finite_Z d.radical z
  let : Finite (U d.radical z) := Finite.of_injective (inclusion (U_le_Z z)) (inclusion_injective _)
  have hCU : ⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ ≤ U d.radical z := by
    rw [commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp (hYS.trans (U_normalized z)))
  let : Finite (⁅Y,U d.radical z ⊓ centralizer (Z d.radical a : Set (FreeAmalgam d.radical))⁆ :
      Subgroup (FreeAmalgam d.radical)) := Finite.of_injective (inclusion hCU) (inclusion_injective _)
  exact (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective _)).trans hbound

/-- For the same trapped neighboring pair, every nontrivial individual
commutator is the full joined commutator of order q. -/
theorem Input.replacement_equal_trapped_commutators
    {geometry : Geometry d.radical} {a z t v r w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hvt : Adjacent d.radical v t)
    (har : Adjacent d.radical a r) (hwr : Adjacent d.radical w r)
    (hvcomm : ⁅Z d.radical v,Q d.radical a⁆ ≤ Z d.radical a)
    (hwcomm : ⁅Z d.radical w,Q d.radical a⁆ ≤ Z d.radical a)
    (hn : ¬ Z d.radical z ≤ normalizer
      ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (htrap : Z d.radical v ≤ Q d.radical (path.walk.getVert (path.walk.length-2)))
    (htrapw : Z d.radical w ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    let A := X d.radical z ⊓ Q d.radical a
    let D := ⁅Z d.radical v ⊔ Z d.radical w,A⁆
    ⁅Z d.radical v,A⁆=D ∧ Nat.card D=Nat.card F ∧
      (⁅Z d.radical w,A⁆=⊥ ∨ ⁅Z d.radical w,A⁆=D) := by
  dsimp only
  let A := X d.radical z ⊓ Q d.radical a
  let D := ⁅Z d.radical v ⊔ Z d.radical w,A⁆
  have hvV : Z d.radical v ≤ V d.radical a :=
    le_sup_left.trans (neighbor_seed_join_le_radius hat hvt)
  have hwV : Z d.radical w ≤ V d.radical a :=
    le_sup_left.trans (neighbor_seed_join_le_radius har hwr)
  have hvS := (le_inf hvV htrap).trans (truncated_radius_le_endpoint_stabilizer path (by omega))
  have hwS := (le_inf hwV htrapw).trans (truncated_radius_le_endpoint_stabilizer path (by omega))
  have hvQ := hvV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hroot := (h.replacement_critical_indices_eq_field_of_seed_escape d path (by omega)
    (Z d.radical v) hvS hvQ hn).1
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2 := by
    rw [hroot]; nlinarith
  have hvne : ⁅Z d.radical v,A⁆ ≠ ⊥ := by
    intro he
    have hi := h.replacement_seed_actor_centralizer_index_ge_field d path (by omega)
      (Z d.radical v) hvS hvQ hn (Z d.radical v) le_rfl hvS
    have hZ : Z d.radical z ≤ X d.radical z := geometry.omega_bound z path.end_color
      (by rw [geometry.distance_constant z path.end_color]; exact lt_of_lt_of_le (by decide : 0 < 4) hb)
    have hh : Z d.radical z ⊓ Q d.radical a ≤ centralizer (Z d.radical v : Set (FreeAmalgam d.radical)) :=
      (inf_le_inf_right _ hZ).trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp he))
    rw [relIndex_eq_one.mpr hh] at hi
    exact (not_lt_of_ge hi) hq
  have hhi := h.replacement_equal_trapped_join_commutator_card_le_field d path hb
    hat hvt har hwr hvcomm hwcomm hn htrap htrapw
  have hlo := h.replacement_root_intersection_commutator_card_ge_field d path hb
    hsmall (Z d.radical v) hvS hvne
  let := finite_X d.radical z
  have hDA : D ≤ X d.radical z := by
    change ⁅Z d.radical v ⊔ Z d.radical w,A⁆ ≤ _
    rw [commutator_comm]
    exact (commutator_mono inf_le_left le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp ((sup_le hvS hwS).trans (X_normalized _ z)))
  let : Finite D := Finite.of_injective (inclusion hDA) (inclusion_injective _)
  have he : ⁅Z d.radical v,A⁆=D := eq_of_le_of_card_ge
    (commutator_mono le_sup_left le_rfl) (hhi.trans hlo)
  have hcard : Nat.card D=Nat.card F := le_antisymm hhi (he ▸ hlo)
  refine ⟨he,hcard,?_⟩
  by_cases hwne : ⁅Z d.radical w,A⁆=⊥
  · exact Or.inl hwne
  · exact Or.inr (eq_of_le_of_card_ge (commutator_mono le_sup_right le_rfl)
      (hhi.trans (h.replacement_root_intersection_commutator_card_ge_field d path hb
        hsmall (Z d.radical w) hwS hwne)))

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
