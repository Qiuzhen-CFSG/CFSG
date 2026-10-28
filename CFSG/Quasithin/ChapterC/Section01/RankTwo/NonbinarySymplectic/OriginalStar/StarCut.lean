module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.OriginalStar.SourceSeed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StarCut

/-!
# The original characteristic-star cut

The original moving-plus-fixed star inclusion bounds the commutator with
its core intersection. The literal graph centralizer cut then descends to
the original ambient group. Normality of the actual star overgroup converts
that intersection bound into containment of its full intrinsic two-core.
The original Sylow-seed theorem supplies the complementary inner-action
containment.

Source: MS93 (3.4), printed pp.868--869. The star-span inclusion remains
explicit for its original-graph producer; marked-image preservation in
(3.7) is a separate source obligation.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
include h

omit [Finite F] [CharP F 2] in
/-- The actual original star overgroup is normal in the original ambient group.
Only characteristicity of the centralizer is needed, not minimality. -/
theorem star_overgroup_normal (Y : Subgroup R) :
    (K ⊔ (starCentralizer R Y).map R.subtype).Normal := by
  let := h.component_normal
  have hgen : K ⊔ R = ⊤ := by
    apply top_le_iff.mp
    intro x _
    obtain ⟨k,hk,r,hr,rfl⟩ := h.product x
    exact mul_mem_sup hk hr
  have hn : R ≤ normalizer ((starCentralizer R Y).map R.subtype : Set H) :=
    R.le_normalizer.trans (normalizer_le_normalizer_characteristic_image R (starCentralizer R Y))
  apply normalizer_eq_top_iff.mp
  apply top_le_iff.mp
  rw [←hgen]
  apply sup_le
  · exact le_sup_left.trans (K ⊔ (starCentralizer R Y).map R.subtype).le_normalizer
  · intro r hr
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (show r ∈ normalizer (K : Set H) by
        rw [normalizer_eq_top]; trivial),
      mem_normalizer_iff_map_conj_eq.mp (hn hr)]

/-- The original moving-plus-fixed star inclusion supplies the source cut.
The cover, displacement estimate, original residual and core maps are derived.
The stronger marked-image preservation remains a separate source theorem. -/
theorem star_cut_of_span_le
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hZ : (starSpan R Y).map (embedS R) ≤ U R (alpha R) ⊔ fixedCore R (alpha R)) :
    (K ⊔ (starCentralizer R Y).map R.subtype) ⊓ pCore 2 H ≤
      (starCentralizer R Y).map R.subtype ∧
    (starCentralizer R Y).map R.subtype ≤ K ⊔ pCore 2 H := by
  let := h.vertex_moving_elementary (a := alpha R) rfl
  let := finite_stabilizer R (alpha R)
  let : Finite (U R (alpha R)) := Finite.of_injective
    (inclusion ((DistanceEight.U_le_Z R _).trans (Z_le_stabilizer R _)))
    (inclusion_injective _)
  obtain ⟨E,_,σ,p,hp,f,hf,hact,_⟩ := h.initial_subgroup_cover_at_vertex
    (a := alpha R) rfl
  have hcomm : ⁅(starSpan R Y).map (embedS R),
      (Ltilde R (alpha R) ⊔ (Q R (beta R) ⊓ centralizer
        ((starSpan R Y).map (embedS R) : Set (FreeAmalgam R)))) ⊓ Q R (alpha R)⁆ ≤
      fixedCore R (alpha R) := (commutator_mono le_rfl inf_le_right).trans
    (star_core_commutator_le_fixed_of_le R rfl _ hZ)
  have hcut := graph_centralizer_cut R (alpha R) (beta R) rfl
    (base_adjacent R) f hf σ hact p hp _ hZ hcomm
  have hpull := centralizer_cut_of_graph_cut K R ((starSpan R Y).map R.subtype)
    h.radical.isPGroup h.radical.twoCore_le h.residual_eq (by
      simpa only [map_map,embedM_comp_subtype] using hcut)
  rw [←starCentralizer_map] at hpull
  exact ⟨hpull,starCentralizer_le_component_core h P Y hY⟩

/-- The literal star pair has its full intrinsic two-core inside its star
radical, and that radical acts through the original component quotient.
The only extra source premise is the original star inclusion used in (3.4). -/
theorem star_pair_core_le_of_span_le
    (P : Sylow 2 (Ltilde R (alpha R))) (Y : Subgroup R)
    (hY : Y.map (embedS R) = componentSylowSeed R (alpha R) P)
    (hZ : (starSpan R Y).map (embedS R) ≤ U R (alpha R) ⊔ fixedCore R (alpha R)) :
    let Tstar := (starCentralizer R Y).map R.subtype
    let Mstar := K ⊔ Tstar
    Mstar.Normal ∧ pCore 2 Mstar ≤ Tstar.subgroupOf Mstar ∧
      Tstar ≤ K ⊔ pCore 2 H := by
  let Tstar := (starCentralizer R Y).map R.subtype
  let Mstar := K ⊔ Tstar
  have hnormal : Mstar.Normal := star_overgroup_normal h Y
  obtain ⟨hcut,hinner⟩ := star_cut_of_span_le h P Y hY hZ
  refine ⟨hnormal,?_,hinner⟩
  rw [pCore_subnormal_eq_comap 2 hnormal.isSubnormal]
  intro x hx
  exact hcut ⟨x.property,hx⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.OriginalStar
