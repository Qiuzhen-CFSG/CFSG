module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullFixedComparison
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullFixedComparison

/-!
# Failed comparison for the full original critical kernel

Keep W = Z_v intersect Q_a and A = X_e intersect Q_u for the actual backward
critical path from u to e. Failure of the full comparison makes W an escaping
actor and forces both critical images to have field order. In one endpoint
cover the independent-root calculation then gives [W,A] ≤ [Z_u,Z_e] and
|[W,A]| = q. All fixed attachments remain in the full original actors.

No radius-fixed premise is used. Source: MS93 (5.12)(1), pp.924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open scoped Pointwise IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The literal failed comparison places its full intersection commutator
in the critical root displacement, with order exactly the field size. -/
theorem Input.replacement_distance_four_full_root_comparison_of_failure
    {geometry : Geometry d.radical} {a z u v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t)
    (hbad : ¬ ⁅Z d.radical v ⊓ Q d.radical a,Z d.radical (path.walk.getVert 2)⁆ ≤
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
        ⁅Z d.radical v ⊓ Q d.radical a,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆) :
    let e := path.walk.getVert 2
    let W := Z d.radical v ⊓ Q d.radical a
    ⁅W,X d.radical e ⊓ Q d.radical u⁆ ≤ ⁅Z d.radical u,Z d.radical e⁆ ∧
      Nat.card (⁅W,X d.radical e ⊓ Q d.radical u⁆ : Subgroup (FreeAmalgam d.radical)) = Nat.card F := by
  dsimp only
  let e := path.walk.getVert 2
  let W := Z d.radical v ⊓ Q d.radical a
  obtain ⟨hWQ,hWS,hcent,hquad,_⟩ :=
    full_comparison_actor h d path hb back hut hvt
  have hsmallRoot := h.replacement_critical_index_lt_square_of_escape d back (by omega)
    W hWS hcent (by
      rw [commutator_comm]
      exact fun hh => hbad (hh.trans le_sup_left))
  obtain ⟨hi,hi'⟩ := h.replacement_small_critical_indices_eq_field d back (by omega) hsmallRoot
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
  have hn : ⁅W,X d.radical e ⊓ Q d.radical u⁆ ≠ ⊥ := by
    intro hz
    have hfix : W ≤ centralizer
        ((Z d.radical e ⊓ Q d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) :=
      (commutator_eq_bot_iff_le_centralizer.mp hz).trans
        (centralizer_le (inf_le_inf_right _ hZX))
    have hle := h.replacement_critical_fixed_intersection_displacement d back hpos W hWS hWQ hfix
    apply hbad
    rw [commutator_comm W]
    exact hle.trans le_sup_left
  exact ⟨hbound.1,Nat.le_antisymm hbound.2
    (h.replacement_root_intersection_commutator_card_ge_field d back hfour hsmall W hWS hn)⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
