module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoPointDisplacement
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SylowLayers
public import Theory.SpecificGroups.SymplecticFour.QuadraticSmallMovers
public import Theory.Representation.SymplecticFourOrthogonalCover.FixedIndex

/-!
# Original critical indices and full edge Sylow groups

The natural quadratic action bounds a literal critical image by q squared.
The existing original midpoint supplement transfers that bound from U to Z;
the reciprocal small-image theorem then makes both indices q or both q squared.
These index conclusions require shortness and innerness but hold before the
Sylow/nonsylow split. A literal marked Sylow radical also lifts to a full
Sylow group at each incident original endpoint.

The internal imports intentionally reuse the original midpoint supplement
and the generic central-factor index calculation.
Source: MS93 (3.7)(1), printed p.873.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
open DistanceTwoRecognition ChapterB.QuasisimpleSource OriginalStar
open Theory.SpecificGroups.SymplecticFour
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

omit h [Finite H] in
private theorem component_eq_top (hinner : K ⊔ pCore 2 H = ⊤) :
    K.map (QuotientGroup.mk' (pCore 2 H)) = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 H)
  have hh := congrArg (fun A : Subgroup H => A.map q)
    hinner
  rw [Subgroup.map_sup,show (pCore 2 H).map q = ⊥ from
    (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
  exact hh

omit [Finite F] [CharP F 2] in
/-- A literal Sylow marking makes the entire incident radical Sylow in the
original endpoint stabilizer. No replacement or saturation is used. -/
theorem original_exists_edge_sylow
    (hsyl : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    ∃ P : Sylow 2 (stabilizer R a),
      (P : Subgroup (stabilizer R a)) = (Q R t).subgroupOf (stabilizer R a) := by
  obtain ⟨S,hS⟩ := (original_sylow_iff_marked_sylow h).mpr hsyl
  obtain ⟨u,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩ := (adjacent_iff_exists_common R a t).mp hat
  swap
  · cases ha
  let i := (MulAut.conj u⁻¹).toMonoidHom.comp (embedM R)
  have hir : i.range = stabilizer R (mVertex R u) := by
    dsimp only [i]
    rw [MonoidHom.range_comp]
    change (Mbar R).map (MulAut.conj u⁻¹).toMonoidHom = _
    rw [←stabilizer_m_base,←stabilizer_act,act_mVertex,one_mul]
  have hiT : R.map i = Q R (hVertex R u) := by
    dsimp only [i]
    rw [←map_map,←Q_beta,←Q_act]
    simp only [beta,act_hVertex,one_mul]
  let f := i.codRestrict (stabilizer R (mVertex R u))
    (fun x => hir ▸ MonoidHom.mem_range.mpr ⟨x,rfl⟩)
  have hf : Function.Surjective f := by
    intro x
    have hx : x.val ∈ i.range := by rw [hir]; exact x.property
    obtain ⟨y,hy⟩ := hx
    exact ⟨y,Subtype.ext hy⟩
  refine ⟨S.mapSurjective hf,?_⟩
  rw [Sylow.coe_mapSurjective,hS]
  apply (map_injective (show Function.Injective (stabilizer R (mVertex R u)).subtype
    from Subtype.val_injective))
  rw [map_map,map_subgroupOf_eq_of_le (show Q R (hVertex R u) ≤ stabilizer R (mVertex R u) from
    fun _ hx => hx.2 _ (adjacent_symm R hat))]
  exact hiT

omit [CharP F 2] in
/-- The full incident radical has quartic quotient order in the literal
original Sylow branch, with the entire endpoint core as kernel. -/
theorem original_sylow_full_radical_card
    (hinner : K ⊔ pCore 2 H = ⊤)
    (hsyl : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    (Q R a).relIndex (Q R t) = (2^n)^4 := by
  obtain ⟨δ,hδk,hδr⟩ := original_edge_marked_action h hinner ha hat
  obtain ⟨S,hS⟩ := hsyl
  rw [relIndex,←hδk,index_ker,hδr,←hS]
  rw [Nat.card_congr (S.equiv (unipotentSylow h.field_card
    (by have := h.nonbinary; omega))).toEquiv,coe_unipotentSylow,card_unipotent,h.field_card]

open Representation.SymplecticFourOrthogonalCover in
private theorem critical_moving_centralizer_index_le_square
    (hinner : K ⊔ pCore 2 H = ⊤)
    {g : Geometry R} {a z : Vertex R}
    (path : CriticalPath R g a z) (hb : 0 < g.b R) :
    (centralizer (Z R a : Set (FreeAmalgam R))).relIndex
      (U R z) ≤ (2^n)^2 := by
  let := h.component_normal
  let s := originalMovedSection h
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex path.end_color
  have hFc : Nat.card E.Carrier = 2^n := by rw [E.card_eq,hE]
  have hCtop := component_eq_top hinner
  let κC := κ.codRestrict ((K.map (QuotientGroup.mk' (pCore 2 H)))) (fun x => hCtop ▸ mem_top (κ x))
  have hZS : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  let β := e.groupEquiv.toMonoidHom.comp (κC.comp (inclusion hZS))
  have hβ (x : Z R a) (v : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (β x) v)) =
        x.val*j (Multiplicative.ofAdd v)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC (inclusion hZS x)))) v)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj (inclusion hZS x) v
  let α := (commutator (Sp E.Carrier)).subtype.comp β
  have hαr : α.range=β.range.map (commutator (Sp E.Carrier)).subtype :=
    MonoidHom.range_comp _ _
  have hquad := CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison.critical_embedded_natural_actor_quadratic
    path hb (MovedSection.coverAction s e) (MovedSection.coverProjection s e) he
    j hj hjr β hβ
  have hquadα : ∀ x ∈ α.range, ∀ y ∈ α.range, ∀ v : Vector E.Carrier,
      x • (y • v-v)=y • v-v := by
    rintro _ ⟨x,rfl⟩ _ ⟨y,rfl⟩ v
    exact hquad (β x) ⟨x,rfl⟩ (β y) ⟨y,rfl⟩ v
  have hbound := quadratic_natural_fixed_index_le_square α.range hquadα
  have hi := embedded_centralizer_index (MovedSection.coverAction s e)
    (U R z) (Z R a) j hj hjr β hβ
  rw [hi,fixedCodim_of_binaryCover (MovedSection.coverProjection s e) he]
  let τ := restrictScalars (k := ZMod 2) (symplecticNatural (k := E.Carrier) 2)
  have hm := fixedCodim_map_equivariant (binaryNatural (K := E.Carrier)) τ
    (commutator (Sp E.Carrier)).subtype (LinearEquiv.refl _ _) (fun _ _ => rfl) β.range
  rw [←hαr] at hm
  rw [hm]
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hFc] at hbound
  exact hbound

/-- The original natural quadratic action bounds the full critical Z-image
by q squared, using the full original central-layer decomposition. -/
theorem original_critical_index_le_field_square
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    (Q R z).relIndex (Z R a) ≤ (2^n)^2 := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  have hZaS : Z R a ≤ stabilizer R z :=
    Z_le_stabilizer_of_dist_le a (g.exists_critical a path.start_color) path.critical.1.le
  have hZzT : Z R z ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1 < g.b R
    omega
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hZt : Z R t = omegaCenter (Q R t) := by simp [Z,ht,edgeOmega]
  have hfix : Z R t ≤ centralizer (Z R z : Set (FreeAmalgam R)) := by
    rw [hZt]
    intro x hx y hy
    exact (mem_omegaCenter_iff.mp hx).2.2 y (hZzT hy)
  let := finite_Z R a
  have hi := SaturatedDistanceTwo.centralizer_index_of_central_factor (Z R a) (Z R t)
    (U R a) (Z R z)
    (by rw [sup_comm]; exact (original_Z_eq_moving_sup_edge h hshort hinner g hb path.start_color hat).symm)
    (hZaS.trans (Z_normalized R z)) hfix
  have hCZ : (centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf
      (Z R a) = (Q R z).subgroupOf (Z R a) := by
    rw [←MSCentralOrbit.C_eq_Q R h.radical.isPGroup
      h.radical.twoCore_le h.omegaOrbit_centralizer z path.end_color]
    ext x
    exact ⟨fun hx => ⟨hZaS x.property,hx⟩,fun hx => hx.2⟩
  have he : (centralizer (Z R z : Set (FreeAmalgam R))).relIndex
      (Z R a) = (Q R z).relIndex (Z R a) := by
    change ((centralizer (Z R z : Set (FreeAmalgam R))).subgroupOf
      (Z R a)).index = _
    rw [hCZ]
    rfl
  rw [he] at hi
  rw [hi]
  exact critical_moving_centralizer_index_le_square h hinner rev (by omega)

/-- The two literal critical images are simultaneously of order q or of
order q squared, including the full Sylow branch. -/
theorem original_paired_critical_indices
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    {g : Geometry R} {a z t : Vertex R}
    (path : CriticalPath R g a z) (hb : g.b R = 2)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    ((Q R z).relIndex (Z R a) = 2^n ∧
      (Q R a).relIndex (Z R z) = 2^n) ∨
    ((Q R z).relIndex (Z R a) = (2^n)^2 ∧
      (Q R a).relIndex (Z R z) = (2^n)^2) := by
  have hedge := MSCentralOrbit.edgeCentralizerCondition R h.radical.isPGroup
    h.radical.twoCore_le h.omegaOrbit_centralizer
  let rev : CriticalPath R g z a :=
    { start_color := path.end_color
      walk := path.walk.reverse
      shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
      critical := critical_reverse R g hedge a path.start_color
        (by rw [g.distance_constant a path.start_color]; change 0 < g.b R; omega)
        z path.end_color path.critical }
  have ha := original_critical_index_le_field_square h hshort hinner path hb hat hzt
  have hz := original_critical_index_le_field_square h hshort hinner rev hb hzt hat
  by_cases hsmall : (Q R z).relIndex (Z R a) < (2^n)^2
  · apply Or.inl
    simpa only [h.field_card] using h.original_small_critical_indices_eq_field path (by omega)
      (by simpa only [h.field_card] using hsmall)
  by_cases hsmall' : (Q R a).relIndex (Z R z) < (2^n)^2
  · apply Or.inl
    simpa only [h.field_card] using (h.original_small_critical_indices_eq_field rev (by omega)
      (by simpa only [h.field_card] using hsmall')).symm
  exact Or.inr ⟨by omega,by omega⟩


end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
