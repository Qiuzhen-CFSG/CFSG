module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.SeedChoice
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.OuterReduction.CutPullback

/-!
# Outer removal from the two source star bounds

On the minimum replacement, the natural cover supplies fixed lifting for
MS93 (3.4)'s final centralizer cut. Pulling that cut back to the replacement
and using characteristic minimality makes the radical centralize the star
span. The constructed full-Sylow seed then puts it over the component.

Only the earlier graph bounds Z-star <= U D and its central displacement
remain explicit. This is their actual outer-removal consumer, not a proof
of those bounds or of the subsequent large-distance exclusion.
Source: MS93 (3.4), p.869, and Section 7, p.933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.OneCohomology
open Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)

include h

/-- The two preceding star bounds imply innerness of the actual replacement.
All cover, seed and characteristic-minimality premises are discharged. -/
theorem Input.replacement_inner_of_seed_star_bounds
    (P : Sylow 2 (Ltilde d.radical (alpha d.radical))) (Y : Subgroup d.radical)
    (hY : Y.map (embedS d.radical) =
      Sp4Four.componentSylowSeed d.radical (alpha d.radical) P)
    (hZ : ((Sp4Four.starSpan d.radical Y).map d.radical.subtype).map (embedM d.radical) ≤
      U d.radical (alpha d.radical) ⊔ fixedCore d.radical (alpha d.radical))
    (hcomm : ⁅((Sp4Four.starSpan d.radical Y).map d.radical.subtype).map (embedM d.radical),
      (Ltilde d.radical (alpha d.radical) ⊔ (Q d.radical (beta d.radical) ⊓ centralizer
        (((Sp4Four.starSpan d.radical Y).map d.radical.subtype).map (embedM d.radical) :
          Set (FreeAmalgam d.radical)))) ⊓ Q d.radical (alpha d.radical)⁆ ≤
      fixedCore d.radical (alpha d.radical)) :
    K.subgroupOf d.overgroup ⊔ pCore 2 d.overgroup = ⊤ := by
  let := h.replacement_vertex_moving_elementary d (a := alpha d.radical) rfl
  let := finite_stabilizer d.radical (alpha d.radical)
  let : Finite (U d.radical (alpha d.radical)) := Finite.of_injective
    (inclusion ((DistanceEight.U_le_Z _ _).trans (Z_le_stabilizer _ _))) (inclusion_injective _)
  obtain ⟨E,_,σ,p,hp,f,hf,hact,_⟩ := h.replacement_initial_subgroup_cover_at_vertex d
    (a := alpha d.radical) rfl
  have hcut := Sp4Four.graph_centralizer_cut d.radical (alpha d.radical) (beta d.radical)
    rfl (base_adjacent d.radical) f hf σ hact p hp _ hZ hcomm
  have hstar := Sp4Four.star_span_central_of_minimal (K.subgroupOf d.overgroup) d.radical
    (h.replacement_minimal d) Y
    (Sp4Four.centralizer_cut_of_graph_cut _ _ _ (h.replacement_two_group d)
      (h.replacement_core_le d) (h.replacement_residual d) hcut)
  have hseed : d.radical ≤ centralizer (Y.map d.radical.subtype : Set d.overgroup) :=
    hstar.trans (centralizer_le (map_mono (Sp4Four.le_starSpan d.radical Y)))
  have hinner : Q d.radical (beta d.radical) ≤
      Ltilde d.radical (alpha d.radical) ⊔ Q d.radical (alpha d.radical) := by
    intro x hx
    apply h.replacement_componentSylowSeed_centralizer_le d rfl P
    refine ⟨?_,?_⟩
    · exact hx.2 _ (adjacent_symm _ (base_adjacent _))
    · change x ∈ centralizer
        (Sp4Four.componentSylowSeed d.radical (alpha d.radical) P : Set (FreeAmalgam d.radical))
      rw [←hY]
      rw [Q_beta] at hx
      obtain ⟨r,hr,rfl⟩ := hx
      rintro y ⟨s,hs,rfl⟩
      have hc := hseed hr (s : d.overgroup) (mem_map_of_mem d.radical.subtype hs)
      simpa only [←embedM_comp_subtype,MonoidHom.comp_apply,subtype_apply,map_mul]
        using congrArg (embedM d.radical) hc
  have hT : d.radical ≤ K.subgroupOf d.overgroup ⊔ pCore 2 d.overgroup := by
    apply (map_le_map_iff_of_injective (embedM_injective d.radical)).mp
    rw [Subgroup.map_sup]
    simpa only [Q_beta,Ltilde_alpha,h.replacement_residual d,
      Q_alpha d.radical (h.replacement_two_group d) (h.replacement_core_le d)] using hinner
  apply top_unique
  intro x _
  obtain ⟨k,hk,r,hr,rfl⟩ := h.replacement_product d x
  exact mul_mem (mem_sup_left hk) (hT hr)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
