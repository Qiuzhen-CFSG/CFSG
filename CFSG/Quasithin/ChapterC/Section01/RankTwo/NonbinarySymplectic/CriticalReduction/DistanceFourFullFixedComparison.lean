module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFixedComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFixedIndices
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFixedComparison
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.TrappedTransport
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourKernelNormality

/-!
# Full-seed comparison in the fixed-radius distance-four branch

The literal actor is Z_v intersect Q_a, with its entire fixed attachment.
Its radius placement gives the independent-root comparison on the full
endpoint cover. A failed comparison then fixes the resulting commutator at
both original centers, hence at v through the actual second selector.

For this final vanishing argument only, adjoining the full vertex-fixed
part to a subgroup T of Z_v identifies its commutator with that of
(T join C_Gv(Z_v)) intersect U_v. No fixed attachment is moved through Q_a.
The internal imports reuse central-product commutator algebra and the
previous fixed-radius proof's local generation and transport steps, and
the internal kernel-normality lemma assembling two normalized factors.
Source: MS93 (5.12)(1), printed pp.924--925, in the fixed-radius branch.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem full_seed_commutator_fixed_iff
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {v : Vertex d.radical} (hv : color d.radical v=false)
    (A T : Subgroup (FreeAmalgam d.radical))
    (hAS : A ≤ stabilizer d.radical v) (hTZ : T ≤ Z d.radical v) :
    ⁅A,T⁆ ≤ centralizer (Ltilde d.radical v : Set (FreeAmalgam d.radical)) ↔ ⁅A,T⁆=⊥ := by
  let C := Z d.radical v ⊓ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical))
  let P := (T ⊔ C) ⊓ U d.radical v
  let : IsElementaryAbelian 2 (Z d.radical v) := geometry.Z_elementary (by omega) v hv
  have hCT : C ≤ centralizer (T : Set (FreeAmalgam d.radical)) :=
    inf_le_left.trans ((Z d.radical v).le_centralizer.trans (centralizer_le hTZ))
  have hCP : C ≤ centralizer (P : Set (FreeAmalgam d.radical)) :=
    inf_le_left.trans ((Z d.radical v).le_centralizer.trans
      (centralizer_le (inf_le_right.trans (U_le_Z v))))
  have hCA : C ≤ centralizer (A : Set (FreeAmalgam d.radical)) :=
    inf_le_right.trans (centralizer_le hAS)
  have hTC : T ⊔ C=P ⊔ C := by
    apply le_antisymm ?_ (sup_le inf_le_left le_sup_right)
    refine sup_le ?_ le_sup_right
    intro t ht
    have htZ := hTZ ht
    have hCn : C ≤ normalizer (U d.radical v : Set (FreeAmalgam d.radical)) :=
      (inf_le_left.trans (Z_le_stabilizer d.radical v)).trans (U_normalized v)
    have hprod : t ∈ (U d.radical v : Set (FreeAmalgam d.radical)) * (C : Set _) := by
      rw [←coe_mul_of_right_le_normalizer_left _ _ hCn]
      exact h.replacement_Z_eq_U_sup_fixed d geometry hb hv ▸ htZ
    obtain ⟨u,hu,c,hc,rfl⟩ := hprod
    have huTC : u ∈ T ⊔ C := by
      have hh := (T ⊔ C).mul_mem (mem_sup_left ht) ((T ⊔ C).inv_mem (mem_sup_right hc))
      simpa only [mul_inv_cancel_right] using hh
    exact (P ⊔ C).mul_mem (mem_sup_left ⟨huTC,hu⟩) (mem_sup_right hc)
  have hcomm : ⁅A,T⁆=⁅A,P⁆ := by
    rw [←commutator_sup_of_central A T C hCT hCA,hTC,
      commutator_sup_of_central A P C hCP hCA]
  rw [hcomm]
  exact h.replacement_natural_commutator_fixed_iff d geometry hb hv A P hAS inf_le_right

private theorem full_comparison_actor
    {geometry : Geometry d.radical} {a z u v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t) :
    let e := path.walk.getVert 2
    let W := Z d.radical v ⊓ Q d.radical a
    let A := X d.radical e ⊓ Q d.radical u
    W ≤ Q d.radical u ∧ W ≤ stabilizer d.radical e ∧
      W ≤ centralizer ((⁅Z d.radical u,Z d.radical e⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ⁅⁅A,W⁆,W⁆=⊥ ∧ A ≤ normalizer (W : Set (FreeAmalgam d.radical)) := by
  dsimp only
  let e := path.walk.getVert 2
  let W := Z d.radical v ⊓ Q d.radical a
  let A := X d.radical e ⊓ Q d.radical u
  have hWVu : W ≤ V d.radical u :=
    inf_le_left.trans (le_sup_left.trans (neighbor_seed_join_le_radius hut hvt))
  have hWQu : W ≤ Q d.radical u :=
    hWVu.trans (geometry.V_le_Q (by omega) u back.start_color)
  have hea : (cosetGraph d.radical).dist e a=2 := by
    rw [SimpleGraph.dist_comm]
    exact path.dist_start (by rw [path.length_eq_b,hb]; omega)
  have hWSe : W ≤ stabilizer d.radical e := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two a e path.start_color back.end_color
      (by rw [SimpleGraph.dist_comm,hea]))
  have hcent : W ≤ centralizer ((⁅Z d.radical u,Z d.radical e⁆ : Subgroup (FreeAmalgam d.radical)) : Set _) :=
    (hWQu.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes u back.start_color)))).trans
        (centralizer_le (critical_commutator_le_start_seed back))
  have hquad : ⁅⁅A,W⁆,W⁆=⊥ := le_bot_iff.mp
    ((commutator_mono (commutator_mono le_rfl (le_inf hWVu inf_le_right))
      (le_inf hWVu inf_le_right)).trans_eq
        (h.replacement_radius_commutator_bounds d geometry (by omega) back.start_color e a).2)
  refine ⟨hWQu,hWSe,hcent,hquad,?_⟩
  have hv : color d.radical v=false := by
    have h1 := adjacent_color_ne d.radical hut
    have h2 := adjacent_color_ne d.radical hvt
    rw [back.start_color] at h1
    have ht : color d.radical t=true := by
      cases ht : color d.radical t
      · exact (h1 ht.symm).elim
      · rfl
    cases hv : color d.radical v
    · rfl
    · exact (h2 (hv.trans ht.symm)).elim
  have hASv : A ≤ stabilizer d.radical v := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two u v back.start_color hv
      (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hut hvt))
  have hASa : A ≤ stabilizer d.radical a :=
    (inf_le_left.trans (omegaCenter_le (Q d.radical e))).trans
      (Q_le_stabilizer_of_dist_le_two e a back.end_color path.start_color hea.le)
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  change W.map (MulAut.conj x).toMonoidHom=W
  dsimp only [W]
  rw [map_inf _ _ _ (MulAut.conj x).injective,MulEquiv.toMonoidHom_eq_coe,
    mem_normalizer_iff_map_conj_eq.mp (Z_normalized d.radical v (hASv hx)),
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized d.radical a (hASa hx))]

private theorem full_root_comparison_of_failure
    {geometry : Geometry d.radical} {a z u v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hbad : ¬ ⁅Z d.radical v ⊓ Q d.radical a,Z d.radical (path.walk.getVert 2)⁆ ≤
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
        ⁅Z d.radical v ⊓ Q d.radical a,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆) :
    let e := path.walk.getVert 2
    let W := Z d.radical v ⊓ Q d.radical a
    ⁅W,X d.radical e ⊓ Q d.radical u⁆ ≤ ⁅Z d.radical u,Z d.radical e⁆ := by
  dsimp only
  let e := path.walk.getVert 2
  let W := Z d.radical v ⊓ Q d.radical a
  obtain ⟨_,hWS,hcent,hquad,_⟩ :=
    full_comparison_actor h d path hb back hut hvt
  obtain ⟨hi,hi'⟩ :=
    h.replacement_distance_four_fixed_critical_indices d hb path.start_color hfixed back
  have hfour : 4 ≤ geometry.b d.radical := by omega
  have hpos : 0 < geometry.b d.radical := by omega
  have hsmall : (Q d.radical e).relIndex (Z d.radical u) < Nat.card F^2 := by
    rw [hi]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  have hCu := MSCentralOrbit.C_eq_Q d.radical (h.replacement_two_group d)
    (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d) u back.start_color
  have hUS : U d.radical e ≤ stabilizer d.radical u :=
    (U_le_Z e).trans (back.endpoint_Z_le_start_stabilizer hpos)
  have hAU : U d.radical e ⊓ centralizer (Z d.radical u : Set (FreeAmalgam d.radical)) =
      U d.radical e ⊓ Q d.radical u := by
    rw [←hCu]
    ext x
    exact ⟨fun hx => ⟨hx.1,hUS hx.1,hx.2⟩,fun hx => ⟨hx.1,hx.2.2⟩⟩
  have hZX : Z d.radical e ≤ X d.radical e := geometry.omega_bound e back.end_color
    (by rwa [geometry.distance_constant e back.end_color])
  have hUA : U d.radical e ⊓ centralizer (Z d.radical u : Set (FreeAmalgam d.radical)) ≤
      X d.radical e ⊓ Q d.radical u := by
    rw [hAU]
    exact inf_le_inf ((U_le_Z e).trans hZX) le_rfl
  have hTS : Z d.radical u ≤ stabilizer d.radical e :=
    Z_le_stabilizer_of_dist_le u (geometry.exists_critical u back.start_color) back.critical.1.le
  let q := QuotientGroup.mk' (pCore 2 d.overgroup)
  let C := (K.subgroupOf d.overgroup).map q
  let : C.Normal := (h.replacement_component_image_structure d).2.1
  let : IsElementaryAbelian 2 (omegaCenterIn (pCore 2 d.overgroup)) := omegaCenterIn_elementary _
  let s := MovedSection.ofNormal (NormalElementaryQuotient.representation
    (omegaCenterIn (pCore 2 d.overgroup)) q (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans (h.replacement_centralOmega_centralizer d).symm)) C
  obtain ⟨E,hE,coord,hcover,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hψ,hsemi,hconj,hproj,hker⟩ :=
    h.replacement_ambient_initial_cover_at_vertex d back.end_color
  have hFc : Nat.card E.Carrier=Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hFl : 2 < Nat.card E.Carrier := by
    rw [E.card_eq,hE]
    exact (by decide : 2 < 2^2).trans_le (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hCtop : C=⊤ := by
    have hh : C.comap q=⊤ := by
      rw [show C=(K.subgroupOf d.overgroup).map q from rfl,comap_map_eq,QuotientGroup.ker_mk']
      exact h.replacement_inner_of_four_le d geometry hfour
    rw [←map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) C,hh,
      ←MonoidHom.range_eq_map,MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
  let κC := κ.codRestrict C (fun x => hCtop ▸ mem_top (κ x))
  let β := coord.groupEquiv.toMonoidHom.comp κC
  let σ := MovedSection.coverAction s coord
  let p := MovedSection.coverProjection s coord
  have hact (y : stabilizer d.radical e) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (β y) w))=y.val*j (Multiplicative.ofAdd w)*y.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (coord.groupEquiv.symm (coord.groupEquiv (κC y))) w))=_
    rw [coord.groupEquiv.symm_apply_apply]
    exact hconj y w
  let βT := β.comp (inclusion hTS)
  have hcard : Nat.card βT.range=Nat.card E.Carrier := by
    have hmark : βT.ker=(Q d.radical e).subgroupOf (Z d.radical u) := by
      ext x
      change coord.groupEquiv (κC (inclusion hTS x))=1 ↔ x.val ∈ Q d.radical e
      rw [coord.groupEquiv.map_eq_one_iff]
      have heq : κC (inclusion hTS x)=1 ↔ inclusion hTS x ∈ κ.ker := Subtype.ext_iff
      rw [heq]
      constructor
      · intro hx
        exact hκQ ▸ mem_map_of_mem (stabilizer d.radical e).subtype hx
      · intro hx
        obtain ⟨y,hy,hyx⟩ := hκQ.symm ▸ hx
        have he : y=inclusion hTS x := Subtype.ext hyx
        exact he ▸ hy
    rw [←index_ker,hmark]
    exact hi.trans hFc.symm
  have hactT (x : Z d.radical u) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (σ (βT x) w))=x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ :=
    hact (inclusion hTS x) w
  obtain ⟨hd,hrootquad⟩ := critical_root_coordinates_of_reciprocal_index_field back hpos hCu hFl
    σ p hcover j hj hjr βT hactT hcard (hi'.trans hFc.symm)
  have hwhole : ⁅W,X d.radical e ⊓ Q d.radical u⁆ =
      ⁅W,U d.radical e ⊓ centralizer (Z d.radical u : Set (FreeAmalgam d.radical))⁆ := by
    rw [(h.replacement_root_intersection_fixed_and_commutator d back hfour hsmall W hWS).1,hAU]
  have hWU : ⁅W,Z d.radical e⁆=⁅W,U d.radical e⁆ := by
    rw [commutator_comm W (Z d.radical e),
      h.replacement_Z_commutator_eq_U d geometry hfour back.end_color W hWS,
      commutator_comm (U d.radical e)]
  have hTU : ⁅Z d.radical u,Z d.radical e⁆=⁅Z d.radical u,U d.radical e⁆ := by
    rw [commutator_comm (Z d.radical u) (Z d.radical e),
      h.replacement_Z_commutator_eq_U d geometry hfour back.end_color (Z d.radical u) hTS,
      commutator_comm (U d.radical e)]
  have hbadU : ¬ ⁅W,U d.radical e⁆ ≤ ⁅Z d.radical u,U d.radical e⁆ ⊔
      ⁅W,U d.radical e ⊓ centralizer (Z d.radical u : Set (FreeAmalgam d.radical))⁆ := by
    rw [←hWU,←hTU,←hwhole]
    exact hbad
  have hbound := IndependentRootComparison.embedded_independent_root_comparison hFl p hcover j hj
    (stabilizer d.radical e) (Z d.radical u) W hTS hWS β hact hcard hd hrootquad
    (by rw [hjr]; exact hcent.trans (centralizer_le (commutator_mono le_rfl (U_le_Z e))))
    (by rw [hjr]; exact le_bot_iff.mp ((commutator_mono (commutator_mono hUA le_rfl) le_rfl).trans_eq hquad))
    (by rw [hjr]; exact hbadU)
  rw [hjr,←hwhole,←hTU,hFc] at hbound
  exact hbound.1

/-- Radius fixedness proves the comparison on the entire neighboring Z-seed
intersection for the same actual backward path and second-selector orbit. -/
theorem Input.replacement_distance_four_full_fixed_comparison
    {geometry : Geometry d.radical} {a z u v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical u)
    (hya : act d.radical y a=v)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ⁅Z d.radical v ⊓ Q d.radical a,Z d.radical (path.walk.getVert 2)⁆ ≤
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
        ⁅Z d.radical v ⊓ Q d.radical a,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ := by
  by_contra hbad
  let e := path.walk.getVert 2
  let W := Z d.radical v ⊓ Q d.radical a
  let A := X d.radical e ⊓ Q d.radical u
  let D := ⁅W,A⁆
  let C := ⁅Z d.radical u,Z d.radical e⁆
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hDC : D ≤ C :=
    full_root_comparison_of_failure h d path hb back hut hvt hfixed hbad
  have hfixed_u := radius_fixed_at d path.start_color back.start_color hfixed
  have huv : (cosetGraph d.radical).dist v u ≤ 2 := neighbor_distance_le_two hut hvt
  have hZv : Z d.radical v ≤ V d.radical u :=
    le_iSup_of_le v (le_iSup_of_le huv le_rfl)
  have hWVu : W ≤ V d.radical u :=
    inf_le_left.trans hZv
  have hDu : D ≤ fixedCore d.radical u :=
    (commutator_mono hWVu inf_le_right).trans hfixed_u
  have hDZu : D ≤ Z d.radical u := hDC.trans (critical_commutator_le_start_seed back)
  have hCu := fixed_core_centralizes_vertex h d geometry hb4 back.start_color D hDu
    (hDZu.trans (commutator_eq_bot_iff_le_centralizer.mp
      (geometry.centralizes u back.start_color)))
  have hl := path.length_eq_b
  have hbl := back.length_eq_b
  have hua : (cosetGraph d.radical).dist u a=2 := by
    rw [←hmid]
    exact back.dist_start (by omega)
  have hea : (cosetGraph d.radical).dist e a=2 := by
    rw [SimpleGraph.dist_comm]
    exact path.dist_start (by omega)
  have hCV : C ≤ ⁅V d.radical a,V d.radical a⁆ :=
    commutator_mono (le_iSup_of_le u (le_iSup_of_le hua.le le_rfl))
      (le_iSup_of_le e (le_iSup_of_le hea.le le_rfl))
  have hDa : D ≤ fixedCore d.radical a := hDC.trans (hCV.trans
    ((commutator_mono le_rfl (geometry.V_le_Q (by omega) a path.start_color)).trans hfixed))
  have hDX : D ≤ X d.radical a := hDC.trans (hCV.trans
    (h.replacement_radius_commutator_bounds d geometry hb4 path.start_color u e).1)
  have hCa := fixed_core_centralizes_vertex h d geometry hb4 path.start_color D hDa
    (le_centralizer_iff.mp ((Q_le_centralizer_X d.radical a).trans (centralizer_le hDX)))
  have hDy : D.map (MulAut.conj y⁻¹).toMonoidHom=D :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hCu ((stabilizer d.radical u).inv_mem hy)))
  have hCv : D ≤ centralizer (stabilizer d.radical v : Set (FreeAmalgam d.radical)) := by
    have hh := (map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hCa).trans
      (map_centralizer_le_centralizer_image _ _)
    change D.map (MulAut.conj y⁻¹).toMonoidHom ≤ centralizer
      ((stabilizer d.radical a).map (MulAut.conj y⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) at hh
    rwa [hDy,←stabilizer_act,hya] at hh
  have hv : color d.radical v=false := by
    rw [←hya,action_preserves_color]
    exact path.start_color
  have hAS : A ≤ stabilizer d.radical v := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two u v back.start_color hv
      (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hut hvt))
  have hzero : ⁅A,W⁆=⊥ := (full_seed_commutator_fixed_iff h d geometry hb4 hv A W hAS inf_le_left).mp (by
    rw [commutator_comm]
    exact hCv.trans (centralizer_le (Ltilde_le_stabilizer v)))
  obtain ⟨hWQ,hWS,_,_,_⟩ := full_comparison_actor h d path hb back hut hvt
  have hZX : Z d.radical e ≤ X d.radical e := geometry.omega_bound e back.end_color
    (by rw [geometry.distance_constant e back.end_color]; exact lt_of_lt_of_le (by decide : 0 < 4) hb4)
  have hfix : W ≤ centralizer
      ((Z d.radical e ⊓ Q d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    have hz : ⁅W,A⁆=⊥ := by rw [commutator_comm,hzero]
    exact (commutator_eq_bot_iff_le_centralizer.mp hz).trans
      (centralizer_le (inf_le_inf_right _ hZX))
  have hle := h.replacement_critical_fixed_intersection_displacement d back (by omega) W hWS hWQ hfix
  apply hbad
  rw [commutator_comm W]
  exact hle.trans le_sup_left

/-- The actual critical endpoint normalizes the full neighboring kernel joined
with the backward seed, without a mover equality or movement-index premise. -/
theorem Input.replacement_distance_four_full_fixed_kernel_normalized
    {geometry : Geometry d.radical} {a z u v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical u)
    (hya : act d.radical y a=v)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    Z d.radical (path.walk.getVert 2) ≤ normalizer
      (((Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  let W := Z d.radical v ⊓ Q d.radical a
  let e := path.walk.getVert 2
  have hcompare := h.replacement_distance_four_full_fixed_comparison d path hb back hmid
    hut hvt y hy hya hfixed
  have hAn := (full_comparison_actor h d path hb back hut hvt).2.2.2.2
  have hAW : ⁅W,X d.radical e ⊓ Q d.radical u⁆ ≤ W :=
    le_normalizer_iff_commutator_le_left.mp hAn
  have hR : ⁅Z d.radical u,Z d.radical e⁆ ≤ Z d.radical u :=
    critical_commutator_le_start_seed back
  have hEW : ⁅Z d.radical e,W⁆ ≤ W ⊔ Z d.radical u := by
    rw [commutator_comm]
    exact hcompare.trans (sup_le (hR.trans le_sup_right) (hAW.trans le_sup_left))
  have hEu : ⁅Z d.radical e,Z d.radical u⁆ ≤ W ⊔ Z d.radical u := by
    rw [commutator_comm]
    exact hR.trans le_sup_right
  exact normalizes_join_of_commutators (Z d.radical e) W (Z d.radical u) hEW hEu

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
