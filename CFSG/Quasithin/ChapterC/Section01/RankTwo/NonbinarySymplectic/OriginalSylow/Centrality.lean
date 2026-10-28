module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.Layers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.CentralityRoot
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SylowCentrality
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFiveCore

/-!
# Original full-Sylow critical images have field order

A hypothetical critical image of order q squared has a natural fixed plane.
The full opposite Sylow stabilizes this plane, so its fixed subgroup on the
original critical image has order q. The full cover kernel and midpoint
center are retained. A normal elementary subgroup of a symplectic Sylow
cannot have these orders, by its two elementary wings and Frattini subgroup.
Thus both original critical indices are q, and the full midpoint radical
centralizes these images modulo the entire original cores.

Source: MS93 (3.7)(1), printed p.873. All actions are on the original input;
no minimum replacement or saturation premise is introduced.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Matrix Representation
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
open DistanceTwoRecognition ChapterB.QuasisimpleSource OriginalStar
open SaturatedDistanceTwo (InnerVertexCover full_marking_surjective marked_cover_action
  large_quadratic_fixed_plane embedded_cover_fixed_iff image_centralizer_index_of_natural_plane
  sylow_normal_elementary_square_fixed_ne_field)
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
include h hshort hinner

omit hshort in
private theorem inner_vertex_actor
    {a : Vertex R}
    (ha : color R a=false) :
    Nonempty (InnerVertexCover R (originalMovedSection h) n a) := by
  let := h.component_image_structure.2.1
  let s := originalMovedSection h
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex ha
  have hFc : Nat.card E.Carrier=2^n := by rw [E.card_eq,hE]
  have hCtop : K.map (QuotientGroup.mk' (pCore 2 H))=⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q=⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (K.map (QuotientGroup.mk' (pCore 2 H))) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let α := (commutator (Sp E.Carrier)).subtype.comp γ
  have hγker : γ.ker=κ.ker := by
    ext x
    change e.groupEquiv (κC x)=1 ↔ κ x=1
    rw [e.groupEquiv.map_eq_one_iff]
    exact Subtype.ext_iff
  have hαker : α.ker=κ.ker :=
    (MonoidHom.ker_comp_of_injective _ _ (commutator (Sp E.Carrier)).subtype_injective).trans hγker
  have hαQ : α.ker.map (stabilizer R a).subtype=Q R a := by
    rw [hαker,hκQ]
  have hcomm : commutator (Sp E.Carrier)=⊤ :=
    Representation.OneCohomology.SymplecticFour.LargeField.commutator_eq_top (by
      rw [hFc]
      exact lt_of_lt_of_le (by decide : 2<2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary))
  have hαonto : Function.Surjective α :=
    full_marking_surjective _ _ hCtop hcomm e.groupEquiv κ hκ
  refine ⟨⟨E,hE,e,he,j,hj,hjr,γ,hαonto,hαQ,?_⟩⟩
  intro x w
  exact (congrArg (fun y => j (Multiplicative.ofAdd y))
    (marked_cover_action s e (κC x) w)).trans (hconj x w)

omit hshort hinner in
private theorem edge_action_fixed_iff {a t : Vertex R}
    (ha : color R a=false) (hat : Adjacent R a t)
    (χ : Q R t →* Sp F) (hχ : χ.ker=(Q R a).subgroupOf (Q R t)) (x : Q R t) :
    χ x=1 ↔ x.val ∈ centralizer (Z R a : Set (FreeAmalgam R)) := by
  change x ∈ χ.ker ↔ _
  rw [hχ]
  change x.val ∈ Q R a ↔ _
  rw [←MSCentralOrbit.C_eq_Q R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer a ha]
  exact ⟨And.right,fun hx => ⟨original_edge_le_stabilizer R hat x.property,hx⟩⟩

variable (hsyl : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
  (R.subgroupOf K).map (componentProjection h))
include hshort hsyl

private theorem large_sylow_critical_image_fixed_index
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R=2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (χ : Q R t →* Sp F) (hχ : χ.ker=(Q R a).subgroupOf (Q R t))
    (hlarge : (Q R z).relIndex (Z R a)=(2^n)^2) :
    (centralizer (χ.range : Set (Sp F))).relIndex
      (((Z R z).subgroupOf (Q R t)).map χ)=2^n := by
  let := h.component_image_structure.2.1
  let := finite_stabilizer R z
  let s := originalMovedSection h
  obtain ⟨⟨E,hE,e,he,j,hj,hjr,γ,hαonto,hαQ,hconj⟩⟩ :=
    inner_vertex_actor h hinner path.end_color
  have hFc : Nat.card E.Carrier=2^n := by rw [E.card_eq,hE]
  let α := (commutator (Sp E.Carrier)).subtype.comp γ
  have hZaT : Z R a ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R a (g.exists_critical a path.start_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hat),
      g.distance_constant a path.start_color]
    change 1<g.b R
    omega
  have hZzT : Z R z ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1<g.b R
    omega
  have hZaS := hZaT.trans (original_edge_le_stabilizer R hzt)
  have hUzT : U R z ≤ Q R t := (U_le_Z z).trans hZzT
  let δ := γ.comp (inclusion hZaS)
  let β := α.comp (inclusion (original_edge_le_stabilizer R hzt))
  let A := (α.comp (inclusion hZaS)).range
  have hδ (x : Z R a) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (δ x) w))=
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    exact hconj (inclusion hZaS x) w
  have hquad := Sp4Four.SourceComparison.critical_embedded_natural_actor_quadratic
    path (by omega) (MovedSection.coverAction s e) (MovedSection.coverProjection s e) he
    j hj hjr δ hδ
  have hquadA : ∀ x ∈ A, ∀ y ∈ A, ∀ v : Vector E.Carrier,
      x • (y • v-v)=y • v-v := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ v
    exact hquad (δ x) ⟨x,rfl⟩ (δ y) ⟨y,rfl⟩ v
  have hcardA : Nat.card A=Nat.card E.Carrier^2 :=
    (Sp4Four.SourceComparison.quotient_image_card _ _ _ hZaS α hαQ).trans
      (hlarge.trans (by rw [hFc]))
  obtain ⟨hdim,hNnorm⟩ := large_quadratic_fixed_plane A hquadA (by
    rw [hcardA]
    have hq : 1<Nat.card E.Carrier := by
      rw [hFc]
      exact one_lt_pow₀ (by decide) (by have := h.nonbinary; omega)
    nlinarith)
  obtain ⟨P,hP⟩ := original_exists_edge_sylow h hsyl path.end_color hzt
  let S := P.mapSurjective (f := α) hαonto
  have hS : β.range=(S : Subgroup (Sp E.Carrier)) := by
    rw [MonoidHom.range_comp,inclusion_range]
    change _=(P : Subgroup (stabilizer R z)).map α
    rw [hP]
  have hnorm : (S : Subgroup (Sp E.Carrier)) ≤ normalizer (A : Set (Sp E.Carrier)) := by
    let A₀ := (Z R a).subgroupOf (stabilizer R z)
    let T₀ := (Q R t).subgroupOf (stabilizer R z)
    have hn : T₀ ≤ normalizer (A₀ : Set (stabilizer R z)) :=
      (comap_mono ((original_edge_le_stabilizer R hat).trans (Z_normalized R a))).trans
        (le_normalizer_comap (stabilizer R z).subtype)
    have hh := (map_mono (f := α) hn).trans (le_normalizer_map α)
    have hAr : A=A₀.map α := by
      change (α.comp (inclusion hZaS)).range=A₀.map α
      rw [MonoidHom.range_comp,inclusion_range]
    rw [←hS,MonoidHom.range_comp,inclusion_range,hAr]
    exact hh
  let p := MovedSection.coverProjection s e
  let σ := (MovedSection.coverAction s e).comp (γ.comp (inclusion (original_edge_le_stabilizer R hzt)))
  let jT := j.codRestrict (Q R t)
    (fun w => hUzT (hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)))
  let η := χ.comp jT
  have hη (x : Q R t) (w : s.space.toSubmodule) :
      η (Multiplicative.ofAdd (σ x w))=
        χ x*η (Multiplicative.ofAdd w)*(χ x)⁻¹ := by
    have hh : jT (Multiplicative.ofAdd (σ x w))=
        x*jT (Multiplicative.ofAdd w)*x⁻¹ := by
      apply Subtype.ext
      exact hconj (inclusion (original_edge_le_stabilizer R hzt) x) w
    change χ (jT (Multiplicative.ofAdd (σ x w)))=_
    rw [hh,map_mul,map_mul,map_inv]
    rfl
  have hηker (w : s.space.toSubmodule) :
      η (Multiplicative.ofAdd w)=1 ↔ p w ∈ TwoLocalCover.fixedSpace A := by
    have hk := edge_action_fixed_iff h path.start_color hat χ hχ (jT (Multiplicative.ofAdd w))
    have hAeq : A=δ.range.map (commutator (Sp E.Carrier)).subtype := by
      change ((commutator (Sp E.Carrier)).subtype.comp δ).range=_
      exact MonoidHom.range_comp _ _
    rw [hAeq]
    have hh := embedded_cover_fixed_iff (MovedSection.coverAction s e) p he j hj
      (Z R a) δ hδ w
    exact hk.trans hh
  have hi := image_centralizer_index_of_natural_plane σ β S hS p.toLinearMap he.1
    (fun x w => LinearMap.congr_fun (p.isIntertwining' (γ (inclusion (original_edge_le_stabilizer R hzt) x))) w)
    η χ hη (TwoLocalCover.fixedSpace A) hdim (hnorm.trans hNnorm) hηker
  have hjTr : jT.range=(U R z).subgroupOf (Q R t) := by
    ext x
    constructor
    · rintro ⟨w,rfl⟩
      exact hjr ▸ (show j w ∈ j.range from ⟨w,rfl⟩)
    · intro hx
      obtain ⟨w,hw⟩ := (show x.val ∈ j.range from hjr.symm ▸ hx)
      exact ⟨w,Subtype.ext hw⟩
  have hZtZ := Sp4Four.edge_Z_le_endpoint R path.start_color hat
  have hZaQ := (g.omega_bound a path.start_color (by
    rw [g.distance_constant a path.start_color]
    change 0<g.b R
    omega)).trans (omegaCenter_le _)
  have hZtQa := hZtZ.trans hZaQ
  have hZtT := hZtQa.trans (original_core_le_edge R path.start_color hat)
  have hηr : η.range=((Z R z).subgroupOf (Q R t)).map χ := by
    rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt,subgroupOf_sup hUzT hZtT,
      Subgroup.map_sup,show ((Z R t).subgroupOf (Q R t)).map χ=⊥ from
        (Subgroup.map_eq_bot_iff _).mpr (by rw [hχ]; exact comap_mono hZtQa),sup_bot_eq]
    rw [MonoidHom.range_comp,hjTr]
  rw [hηr,hFc] at hi
  exact hi

/-- The fixed-centralizer count in the large-image Sylow branch of
MS93 (3.7)(1), computed using the opposite endpoint's actual natural cover. -/
private theorem large_sylow_critical_image_fixed_card
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R=2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (χ : Q R t →* Sp F) (hχ : χ.ker=(Q R a).subgroupOf (Q R t))
    (hlarge : (Q R z).relIndex (Z R a)=(2^n)^2) :
    Nat.card ((((Z R z).subgroupOf (Q R t)).map χ) ⊓
      centralizer (χ.range : Set (Sp F)) : Subgroup (Sp F))=2^n := by
  have hi := large_sylow_critical_image_fixed_index h hshort hinner hsyl path hb hat hzt χ hχ hlarge
  have hZzT : Z R z ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1<g.b R
    omega
  have hlarge' : (Q R a).relIndex (Z R z)=(2^n)^2 := by
    rcases original_paired_critical_indices h hshort hinner path hb hat hzt with hs | hl
    · have hq : 1<2^n := one_lt_pow₀ (by decide) (by have := h.nonbinary; omega)
      have hh := hs.1
      rw [hlarge] at hh
      nlinarith only [hq,hh]
    · exact hl.2
  let B := ((Z R z).subgroupOf (Q R t)).map χ
  have hBcard : Nat.card B=(2^n)^2 := by
    rw [←relIndex_ker,hχ,relIndex_subgroupOf hZzT,hlarge']
  have hh := relIndex_mul_relIndex (⊥ : Subgroup (Sp F))
    (B ⊓ centralizer (χ.range : Set (Sp F))) B bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hi,hBcard] at hh
  have hq : 0<2^n := by positivity
  nlinarith only [hh,hq]


/-- Both actual critical images have order q when the common full radical
has Sylow image. The order-q conclusion is derived from the source geometry. -/
private theorem critical_indices_eq_field_of_full_sylow
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R=2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (χ : Q R t →* Sp F) (hχ : χ.ker=(Q R a).subgroupOf (Q R t))
    (S₀ : Sylow 2 (Sp F)) (hS₀ : (S₀ : Subgroup (Sp F))=χ.range) :
    (Q R z).relIndex (Z R a)=2^n ∧
      (Q R a).relIndex (Z R z)=2^n := by
  rcases original_paired_critical_indices h hshort hinner path hb hat hzt with hs | hl
  · exact hs
  exfalso
  have hZzT : Z R z ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1<g.b R
    omega
  let A₀ := (Z R z).subgroupOf (Q R t)
  let : A₀.Normal := normal_subgroupOf_of_le_normalizer
    ((original_edge_le_stabilizer R hzt).trans (Z_normalized R z))
  let := g.Z_elementary (by omega : 0<g.b R) z path.end_color
  let : IsElementaryAbelian 2 A₀ := IsElementaryAbelian.subgroupOf hZzT
  let A := A₀.map χ
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map χ
  have hAS : A ≤ S₀ := (map_le_range _ _).trans_eq hS₀.symm
  have hn : (S₀ : Subgroup (Sp F)) ≤ normalizer (A : Set (Sp F)) := by
    rw [hS₀,MonoidHom.range_eq_map]
    exact (map_mono (show (⊤ : Subgroup (Q R t)) ≤ normalizer (A₀ : Set (Q R t)) from
      le_normalizer_of_normal)).trans (le_normalizer_map χ)
  have hA : Nat.card A=Nat.card F^2 := by
    rw [←relIndex_ker,hχ,relIndex_subgroupOf hZzT,hl.2,h.field_card]
  have hfix : Nat.card (A ⊓ centralizer (S₀ : Set (Sp F)) : Subgroup (Sp F))=Nat.card F := by
    change Nat.card (A ⊓ centralizer ((S₀ : Subgroup (Sp F)) : Set (Sp F)) : Subgroup (Sp F))=Nat.card F
    rw [hS₀]
    exact (large_sylow_critical_image_fixed_card h hshort hinner hsyl path hb hat hzt χ hχ hl.1).trans h.field_card.symm
  exact sylow_normal_elementary_square_fixed_ne_field h.field_card h.nonbinary S₀ A hAS hn hA hfix

/-- Both full original critical indices are q in the literal marked Sylow case. -/
theorem original_critical_indices_eq_field_of_full_sylow
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R=2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    (Q R z).relIndex (Z R a)=2^n ∧
      (Q R a).relIndex (Z R z)=2^n := by
  obtain ⟨χ,hχ,hχr⟩ := original_edge_marked_action h hinner path.start_color hat
  obtain ⟨S,hS⟩ := hsyl
  exact critical_indices_eq_field_of_full_sylow h hshort hinner ⟨S,hS⟩ path hb hat hzt
    χ hχ S (hS.trans hχr.symm)

/-- Source (3.7)(1) for the full original Sylow radical and both entire cores. -/
theorem original_full_radical_centralizes_critical_images
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R=2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    ⁅Z R z,Q R t⁆ ≤ Q R a ∧ ⁅Z R a,Q R t⁆ ≤ Q R z := by
  have hi := original_critical_indices_eq_field_of_full_sylow h hshort hinner hsyl path hb hat hzt
  have hc := original_full_radical_centralizes_critical_root h hinner path hb hat hzt hi.1
  exact ⟨hc.1,hc.2.1⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
