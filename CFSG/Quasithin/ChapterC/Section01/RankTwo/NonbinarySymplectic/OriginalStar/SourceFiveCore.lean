module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceFourFixedKernels
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic

/-!
# The original full-core comparison in MS93 (3.7)(5)

Equal fixed attachments and equal midpoint movements place the mixed core
commutator in the Frattini subgroup and in the opposite fixed attachment.
Fixed-vector lifting makes it trivial. Faithfulness then identifies the
whole cores, and hence their central omega subgroups. All groups belong to
the original radical; no characteristic-replacement saturation is assumed.

Source: Meierfrankenfeld--Stellmacher (1993), (3.7)(5), printed p.875.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open scoped commutatorElement IsMulCommutative
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
open DistanceTwoRecognition ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
include h hshort hinner

omit hshort [Finite F] [CharP F 2] in
private theorem original_stabilizer_eq_residual_sup_core
    {a : Vertex R} (ha : color R a=false) :
    stabilizer R a=Ltilde R a ⊔ Q R a := by
  obtain ⟨x,rfl⟩ := exists_mVertex_of_color R ha
  have he : mVertex R x=act R x (alpha R) := by simp [alpha,act_mVertex]
  rw [he,stabilizer_act,Ltilde_act,Q_act,←Subgroup.map_sup,
    Ltilde_alpha,h.residual_eq,Q_alpha R h.radical.isPGroup h.radical.twoCore_le,
    ←Subgroup.map_sup,hinner]
  simp only [alpha,stabilizer_m_base,Mbar,MonoidHom.range_eq_map]

omit h hshort hinner [Finite H] in
private theorem original_edge_le_stabilizer (R : Subgroup H)
    {a t : Vertex R} (hat : Adjacent R a t) : Q R t ≤ stabilizer R a :=
  fun _ hx => hx.2 _ (adjacent_symm R hat)

omit h hshort hinner in
private theorem original_core_le_edge (R : Subgroup H)
    {a t : Vertex R} (ha : color R a=false) (hat : Adjacent R a t) : Q R a ≤ Q R t := by
  apply Q_le_adjacent_h R _ hat
  apply Bool.eq_true_of_not_eq_false
  intro ht
  exact adjacent_color_ne R hat (ha.trans ht.symm)

omit hinner in
private theorem original_short_frattini_le_fixedCore
    {a : Vertex R} (ha : color R a=false) :
    (frattini (Q R a)).map (Q R a).subtype ≤ fixedCore R a := by
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  let : IsElementaryAbelian 2 (U R a) := h.vertex_moving_elementary ha
  have hmove : ⁅Q R a,Ltilde R a⁆ ≤ U R a := (short_original_core_eq_U h hshort ha).le
  have hc : U R a ≤ centralizer (Q R a : Set (FreeAmalgam R)) :=
    (U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha))
  exact le_inf (map_subtype_le _)
    (frattini_image_le_centralizer_of_elementary_commutator
      (Q R a) (Ltilde R a) (U R a)
      (Q_isPGroup R h.radical.isPGroup h.radical.twoCore_le a ha)
      hmove (le_centralizer_iff.mp hc))

omit hshort in
/-- Any individual moving displacement fixed by the component is trivial,
for the whole endpoint stabilizer and with the complete cover kernel. -/
theorem original_stabilizer_value_in_fixed_eq_one
    {a : Vertex R} (ha : color R a = false)
    (b : FreeAmalgam R) (hbS : b ∈ stabilizer R a)
    (u : FreeAmalgam R) (hu : u ∈ U R a)
    (hfix : ⁅b,u⁆ ∈ centralizer (Ltilde R a : Set (FreeAmalgam R))) :
    ⁅b,u⁆ = 1 := by
  let := h.component_normal
  obtain ⟨E,hE,e,he,j,hj,hr,β,hβ,haction,hker⟩ := h.initial_cover_at_vertex ha
  let v : VertexCover R (originalMovedSection h) n a :=
    ⟨E,hE,e,he,j,hj,hr,β,hβ,haction,hker⟩
  have hbprod : b ∈ Ltilde R a ⊔ Q R a :=
    (original_stabilizer_eq_residual_sup_core h hinner ha).symm ▸ hbS
  have hn : Ltilde R a ≤ normalizer (Q R a : Set (FreeAmalgam R)) :=
    (Ltilde_le_stabilizer _).trans (Q_normalized _ _)
  rw [←SetLike.mem_coe,coe_mul_of_left_le_normalizer_right _ _ hn] at hbprod
  obtain ⟨l,hl,q,hq,rfl⟩ := hbprod
  have hqu : Commute q u :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha)
      (U_le_Z a hu) q hq)
  have heq : ⁅l*q,u⁆ = ⁅l,u⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul,
      commutatorElement_eq_one_iff_commute.mpr hqu]
    simp only [mul_one,mul_inv_cancel,one_mul]
  rw [heq] at hfix ⊢
  have hk : (MovedSection.coverProjection (originalMovedSection h) v.equiv).toLinearMap.ker.toAddSubgroup.toSubgroup.map v.embedding =
      U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) := by
    apply le_antisymm
    · rintro x ⟨w,hw,rfl⟩
      exact ⟨v.range_eq ▸ ⟨w,rfl⟩,(v.kernel w.toAdd).mp hw⟩
    · rintro x ⟨hx,hc⟩
      obtain ⟨w,rfl⟩ := v.range_eq.symm ▸ hx
      exact ⟨w,(v.kernel w.toAdd).mpr hc,rfl⟩
  apply embedded_cover_value_in_kernel_eq_one (U R a) (Ltilde R a)
    (MovedSection.coverProjection (originalMovedSection h) v.equiv) v.cover
    v.embedding v.injective v.range_eq v.actor v.conjugation l hl u hu
  rw [hk]
  exact ⟨le_normalizer_iff_commutator_le_right.mp
    ((Ltilde_le_stabilizer _).trans (U_normalized a)) (commutator_mem_commutator hl hu),hfix⟩

omit hshort hinner in
/-- Centralizing the actual moving group detects the entire endpoint core. -/
theorem original_stabilizer_centralizer_moving_eq_core
    {a : Vertex R} (ha : color R a = false) :
    stabilizer R a ⊓ centralizer (U R a : Set (FreeAmalgam R)) =
      Q R a := by
  let := h.component_normal
  obtain ⟨E,hE,e,he,j,hj,hr,κ,hκ,hQ,hC,hL,hf,hs,hc,hp,hk⟩ := h.ambient_initial_cover_at_vertex ha
  let v : AmbientVertexCover R (originalMovedSection h) n a :=
    ⟨E,hE,e,he,j,hj,hr,κ,hκ,hQ,hC,hL,hf,hs,hc,hp,hk⟩
  apply le_antisymm
  · rintro b ⟨hb,hc⟩
    have hact (w : (originalMovedSection h).space.toSubmodule) :
        (originalMovedSection h).space.toRepresentation (v.quotient ⟨b,hb⟩) w = w := by
      apply Multiplicative.ofAdd.injective
      apply v.injective
      rw [v.conjugation]
      have hw : v.embedding (Multiplicative.ofAdd w) ∈ U R a :=
        v.range_eq ▸ (show v.embedding (Multiplicative.ofAdd w) ∈ v.embedding.range from
          ⟨Multiplicative.ofAdd w,rfl⟩)
      have he := hc _ hw
      rw [←he,mul_inv_cancel_right]
    have hnat : MovedSection.ambientAction (originalMovedSection h) v.equiv
        (v.quotient ⟨b,hb⟩) = 1 := by
      apply LinearMap.ext
      intro w
      obtain ⟨w,rfl⟩ := v.cover.1 w
      exact (v.projection ⟨b,hb⟩ w).symm.trans
        (congrArg (MovedSection.coverProjection (originalMovedSection h) v.equiv) (hact w))
    have hv : v.quotient ⟨b,hb⟩ = 1 := v.faithful (hnat.trans (map_one _).symm)
    exact v.kernel_Q ▸ (show b ∈ v.quotient.ker.map (stabilizer R a).subtype from
      ⟨⟨b,hb⟩,hv,rfl⟩)
  · exact le_inf (fun _ hx => hx.1) (le_centralizer_iff.mp
      ((U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R a ha))))

omit hshort [Finite F] [CharP F 2] in
/-- The complete radical moves Z into U, using the literal LQ factorization. -/
theorem original_full_radical_Z_displacement_le_moving
    {a t : Vertex R} (ha : color R a = false)
    (hat : Adjacent R a t) :
    ⁅Z R a,Q R t⁆ ≤ U R a := by
  rw [commutator_comm]
  apply (commutator_mono (original_edge_le_stabilizer R hat) le_rfl).trans
  rw [←(original_stabilizer_eq_residual_sup_core h hinner ha).symm]
  apply commutator_sup_le_of_relative_normal (stabilizer R a)
    (Ltilde R a) (Q R a) (Z R a) (U R a)
    (U_normalized a) (Ltilde_le_stabilizer _) (fun _ hx => hx.1)
  · rw [commutator_comm]
    exact le_rfl
  · rw [commutator_comm,Z_centralizes_Q R a ha]
    exact bot_le

/-- The full-core part of MS93 (3.7)(5), with exactly its equal-attachment,
equal-displacement and contained-Z hypotheses. All intersections and
commutators are in the original free amalgam. -/
theorem original_source_five_core_equality
    {a z t : Vertex R}
    (ha : color R a = false) (hz : color R z = false)
    (hat : Adjacent R a t) (hzt : Adjacent R z t)
    (hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) =
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)))
    (hmove : ⁅Z R z,Q R t⁆ = ⁅Z R a,Q R t⁆)
    (hinside : Z R z ≤ Q R a) :
    Q R a = Q R z ∧ X R a = X R z := by
  let := finite_stabilizer R a
  let := finite_stabilizer R z
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1))
    (inclusion_injective _)
  let : Fact (IsPGroup 2 (Q R a)) := ⟨Q_isPGroup R
    h.radical.isPGroup h.radical.twoCore_le a ha⟩
  have hder : ⁅Q R a,Q R a⁆ ≤
      (frattini (Q R a)).map (Q R a).subtype := by
    have hh := map_mono (f := (Q R a).subtype)
      (commutator_le_frattini_of_isPGroup (R := Q R a) (p := 2))
    simpa only [commutator_def,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hh
  have hbound : ⁅Q R a,U R z⁆ ≤
      U R z ⊓ centralizer (Ltilde R z : Set (FreeAmalgam R)) := by
    rw [←hfixed]
    apply le_inf
    · rw [commutator_comm]
      exact (commutator_mono (U_le_Z z) (original_core_le_edge R ha hat)).trans
        (hmove.le.trans (original_full_radical_Z_displacement_le_moving h hinner ha hat))
    · exact ((commutator_mono le_rfl ((U_le_Z z).trans hinside)).trans hder).trans
        ((original_short_frattini_le_fixedCore h hshort ha).trans inf_le_right)
  have hcentral : Q R a ≤ centralizer (U R z : Set (FreeAmalgam R)) := by
    intro b hbq u hu
    exact (commutatorElement_eq_one_iff_commute.mp
      (original_stabilizer_value_in_fixed_eq_one h hinner hz b
        ((original_edge_le_stabilizer R hzt) ((original_core_le_edge R ha hat) hbq)) u hu
        (hbound (commutator_mem_commutator hbq hu)).2)).eq.symm
  have hle : Q R a ≤ Q R z := by
    rw [←original_stabilizer_centralizer_moving_eq_core h hz]
    exact le_inf ((original_core_le_edge R ha hat).trans (original_edge_le_stabilizer R hzt)) hcentral
  have hcard : Nat.card (Q R z) = Nat.card (Q R a) := by
    obtain ⟨u,_,hu⟩ := stabilizer_transitive_neighbors R t
      (adjacent_symm R hat) (adjacent_symm R hzt)
    rw [←hu,Q_act,card_map_of_injective (MulAut.conj u⁻¹).injective]
  let : Finite (Q R z) := Finite.of_injective
    (inclusion (show Q R z ≤ stabilizer R z from fun _ hx => hx.1))
    (inclusion_injective _)
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard.le
  exact ⟨heq,congrArg omegaCenter heq⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
