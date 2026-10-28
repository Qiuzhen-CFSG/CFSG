module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalSylow.Centrality
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.SourceOne
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceTwoFixedCoreQuadratic

/-!
# Original Sylow component triples

The full-radical containment puts [Z′,T₀] in the original moving layer U.
Reversal of mixed displacement in the symplectic cover then gives
[Z′,Q,T₀] = 1. The whole edge center is retained when lifting from U′ to Z′.
All vertices and kernels belong to the literal original input.
Source: MS93 (3.7)(1), printed p.873.
-/

public noncomputable section
open scoped IsMulCommutative commutatorElement
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open Theory.SpecificGroups.SymplecticFour
open Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
open DistanceTwoRecognition ChapterB.QuasisimpleSource OriginalStar
open SaturatedDistanceTwo (triple_sup_of_central_factor)
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

private theorem original_moving_reversed_triple
    (hinner : K ⊔ pCore 2 H = ⊤)
    {z : Vertex R} (hz : color R z = false)
    (A B : Subgroup (FreeAmalgam R))
    (hA : A ≤ stabilizer R z) (hB : B ≤ stabilizer R z)
    (htriple : ⁅⁅U R z,A⁆,B⁆ = ⊥) :
    ⁅⁅U R z,B⁆,A⁆ = ⊥ := by
  let := h.component_normal
  let s := originalMovedSection h
  obtain ⟨E,hE,e,he,j,hj,hjr,κ,hκ,hκQ,hκC,hκL,hfaith,hsemi,hconj,hproj,hker⟩ :=
    h.ambient_initial_cover_at_vertex hz
  change Multiplicative s.space.toSubmodule →* FreeAmalgam R at j
  change j.range = U R z at hjr
  have hCtop : K.map (QuotientGroup.mk' (pCore 2 H)) = ⊤ := by
    let q := QuotientGroup.mk' (pCore 2 H)
    have hh := congrArg (fun A : Subgroup H => A.map q)
      hinner
    rw [Subgroup.map_sup,show (pCore 2 H).map q = ⊥ from
      (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk']),sup_bot_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at hh
    exact hh
  let κC := κ.codRestrict (K.map (QuotientGroup.mk' (pCore 2 H))) (fun x => hCtop ▸ mem_top (κ x))
  let γ := e.groupEquiv.toMonoidHom.comp κC
  let S := stabilizer R z
  have haction (x : S) (w : s.space.toSubmodule) :
      j (Multiplicative.ofAdd (MovedSection.coverAction s e (γ x) w)) =
        x.val*j (Multiplicative.ofAdd w)*x.val⁻¹ := by
    change j (Multiplicative.ofAdd (s.space.toRepresentation
      (e.groupEquiv.symm (e.groupEquiv (κC x))) w)) = _
    rw [e.groupEquiv.symm_apply_apply]
    exact hconj x w
  have hAm : (A.subgroupOf S).map S.subtype = A := map_subgroupOf_eq_of_le hA
  have hBm : (B.subgroupOf S).map S.subtype = B := map_subgroupOf_eq_of_le hB
  have hh := embedded_cover_reverse_triple (MovedSection.coverAction s e)
    (MovedSection.coverProjection s e) he j hj S.subtype γ haction
    (A.subgroupOf S) (B.subgroupOf S) (by
      rwa [hjr,hAm,hBm])
  simpa only [hjr,hAm,hBm] using hh

/-- The original full-Sylow radical satisfies both component clauses of
MS93 (3.7)(1), with the full opposite Z-layer and the whole original core. -/
theorem original_component_radical_triples
    (hshort : IsShort K) (hinner : K ⊔ pCore 2 H = ⊤)
    (hsy : ∃ S : Sylow 2 (Sp F), (S : Subgroup (Sp F)) =
      (R.subgroupOf K).map (componentProjection h))
    (g : Geometry R) (hb : g.b R = 2)
    {a z t : Vertex R} (path : CriticalPath R g a z)
    (hat : Adjacent R a t) (hzt : Adjacent R z t) :
    ⁅Z R z,Q R t ⊓ Ltilde R a⁆ ≤ U R a ∧
      ⁅⁅Z R z,Q R a⁆,Q R t ⊓ Ltilde R a⁆ = ⊥ := by
  let T := Q R t
  let B := T ⊓ Ltilde R a
  have ht : color R t = true := by
    have hn := adjacent_color_ne R hat
    cases he : color R t <;> simp_all [path.start_color]
  have hQT : Q R a ≤ T := Q_le_adjacent_h R ht hat
  have hTS : T ≤ stabilizer R a := fun _ hx => hx.2 _ (adjacent_symm R hat)
  have hTSz : T ≤ stabilizer R z := fun _ hx => hx.2 _ (adjacent_symm R hzt)
  have hTB : T ≤ normalizer (B : Set (FreeAmalgam R)) :=
    (le_inf T.le_normalizer (hTS.trans (original_residual_normalized a))).trans
      inf_normalizer_le_normalizer_inf
  have hZzT : Z R z ≤ T := by
    apply Z_le_Q_of_dist_lt R z (g.exists_critical z path.end_color)
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj _ _ _).mpr hzt),
      g.distance_constant z path.end_color]
    change 1 < g.b R
    omega
  have hfull := (original_full_radical_centralizes_critical_images
    h hshort hinner hsy path hb hat hzt).1
  have hBQ : B ⊓ Q R a ≤ U R a :=
    (inf_le_inf_right _ inf_le_right).trans_eq
      (original_component_core_intersection h hshort path.start_color)
  have hmove : ⁅Z R z,B⁆ ≤ U R a :=
    (le_inf (le_normalizer_iff_commutator_le_right.mp (hZzT.trans hTB))
      ((commutator_mono le_rfl inf_le_left).trans hfull)).trans hBQ
  have hquad : ⁅⁅U R z,B⁆,Q R a⁆ = ⊥ := by
    apply commutator_eq_bot_iff_le_centralizer.mpr
    exact ((commutator_mono (U_le_Z z) le_rfl).trans hmove).trans
      ((U_le_Z a).trans (commutator_eq_bot_iff_le_centralizer.mp
        (Z_centralizes_Q R a path.start_color)))
  have hrev := original_moving_reversed_triple h hinner path.end_color B (Q R a)
    (inf_le_left.trans hTSz) (hQT.trans hTSz) hquad
  have hZt : Z R t = omegaCenter T := by simp [T,Z,ht,edgeOmega]
  have hcentral : Z R t ≤ centralizer (T : Set (FreeAmalgam R)) := by
    rw [hZt]
    exact fun x hx => (mem_omegaCenter_iff.mp hx).2.2
  refine ⟨hmove,?_⟩
  rw [original_Z_eq_moving_sup_edge h hshort hinner g hb path.end_color hzt]
  exact triple_sup_of_central_factor T (U R z) (Z R t) (Q R a) B
    ((U_le_Z z).trans hZzT) (hZt ▸ omegaCenter_le _) hQT inf_le_left hTB hcentral hrev

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalSylow
