module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StarCut

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.StarDualCover
public import Theory.Representation.SymplecticFourOrthogonalCover.DualFixed

/-!
# The second star bound and removal of the outer action

The full holomorph star centralizes the critical endpoint. Its image in the
source star quotient is therefore fixed by the refinement-free critical actor.
Dual-cover fixedness puts that image in the natural submodule, and the literal
kernel lifts it into U-alpha D-alpha. The existing characteristic cut now
removes outer action whenever the replacement distance is at least four.

The intrinsic input consequently constructs a minimum replacement with distance
two or a large distance and inner ambient quotient. Section 5's exclusion of
the latter branch remains necessary; this module does not assert distance two.
Source: MS93 (3.4), printed p.869, and Section 7, printed pp.932--933.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Representation.OneCohomology Representation.SymplecticFourOrthogonalCover
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The second source star bound, for the actual minimum replacement at
arbitrary nonbinary degree. The entire fixed core is retained. -/
theorem Input.replacement_starSpan_le_moving_fixed
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    (Y : Subgroup d.radical) (P : Sylow 2 (Ltilde d.radical (alpha d.radical)))
    (hY : Y.map (embedS d.radical) = componentSylowSeed d.radical (alpha d.radical) P)
    (hn : Q d.radical (beta d.radical) ≤
      normalizer (Y.map (embedS d.radical) : Set (FreeAmalgam d.radical))) :
    (starSpan d.radical Y).map (embedS d.radical) ≤
      U d.radical (alpha d.radical) ⊔ fixedCore d.radical (alpha d.radical) := by
  obtain ⟨E,hE,s,γ,hγ,hγC,hmap,i,hi,hdual,hrange,hcritical⟩ :=
    h.exists_replacement_sourceStarDualCover d geometry hb Y P hY hn
  obtain ⟨z,path,hfirst⟩ := exists_replacement_critical_path_through_beta d geometry (by omega)
  obtain ⟨β,hβ,hno⟩ := hcritical z path
  have hc := h.replacement_starSpan_centralizes_endpoint d geometry (by omega)
    path hfirst Y P hY hn
  have hBA : (starSpan d.radical Y).map (embedS d.radical) ≤ sourceStarAlpha d.radical Y := by
    have hh := (sourceStarAlpha_le_iff d.radical Y (sourceStarAlpha d.radical Y)).mp
      le_rfl (1 : Mbar d.radical)
    have he : (MulAut.conj (1 : FreeAmalgam d.radical)).toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change 1*x*1⁻¹=x
      simp
    simpa only [OneMemClass.coe_one,he,Subgroup.map_id] using hh
  have hZS : Z d.radical z ≤ stabilizer d.radical (alpha d.radical) := by
    apply Z_le_stabilizer_of_dist_le z (geometry.exists_critical z path.end_color)
    rw [SimpleGraph.dist_comm,path.critical.1,geometry.distance_constant _ rfl,
      geometry.distance_constant _ path.end_color]
  intro b hbB
  let bA : sourceStarAlpha d.radical Y := ⟨b,hBA hbB⟩
  have hfix : (s.sectionData.coordinates bA).toAdd ∈
      OneCohomology.fixed ((s.action.comp γ).comp β.range.subtype) := by
    rintro ⟨a,⟨x,rfl⟩⟩
    change s.action (γ (β x)) (s.sectionData.coordinates bA).toAdd = _
    rw [hβ x (hZS x.property)]
    have he := s.sectionData.equivariant ⟨x,hZS x.property⟩ bA
    change (s.sectionData.coordinates ⟨(x : FreeAmalgam d.radical)*b*
      (x : FreeAmalgam d.radical)⁻¹,_⟩).toAdd =
        s.action (s.quotient ⟨x,hZS x.property⟩) (s.sectionData.coordinates bA).toAdd at he
    rw [←he]
    congr 2
    apply Subtype.ext
    have hcomm := hc hbB x x.property
    exact (congrArg (fun t => t*(x : FreeAmalgam d.radical)⁻¹) hcomm).trans
      (mul_inv_cancel_right b (x : FreeAmalgam d.radical))
  have hmem := dualCover_fixed_le_natural_of_no_refinement i hi hdual β.range hno hfix
  obtain ⟨u,hu,he⟩ := (hrange _).mp hmem
  have hdiff : (u⁻¹*bA : sourceStarAlpha d.radical Y) ∈ s.sectionData.coordinates.ker := by
    change s.sectionData.coordinates (u⁻¹*bA) = 1
    rw [map_mul,map_inv,show s.sectionData.coordinates u = s.sectionData.coordinates bA
      from Multiplicative.toAdd.injective he,inv_mul_cancel]
  rw [s.sectionData.kernel_eq] at hdiff
  have hd : ((u⁻¹*bA : sourceStarAlpha d.radical Y) : FreeAmalgam d.radical) ∈
      fixedCore d.radical (alpha d.radical) := hdiff.2
  have hmul := mul_mem (mem_sup_left hu) (mem_sup_right hd)
  simpa only [Subgroup.coe_mul,Subgroup.coe_inv,mul_inv_cancel_left] using hmul

/-- The two proved star bounds remove all outer action in the large-distance
branch, on the same characteristic replacement. -/
theorem Input.replacement_inner_of_four_le
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical) :
    K.subgroupOf d.overgroup ⊔ pCore 2 d.overgroup = ⊤ := by
  obtain ⟨P,Y,hY,hn,_,_⟩ := h.exists_replacement_source_seed d
  apply h.replacement_inner_of_seed_star_inclusion d P Y hY
  simpa only [Subgroup.map_map,embedM_comp_subtype] using
    h.replacement_starSpan_le_moving_fixed d geometry hb Y P hY hn

/-- Every geometry on the characteristic replacement has distance two or
an inner ambient quotient. Section 5 must still exclude the latter large-distance branch. -/
theorem Input.replacement_distance_two_or_inner (geometry : Geometry d.radical) :
    geometry.b d.radical = 2 ∨
      (4 ≤ geometry.b d.radical ∧ K.subgroupOf d.overgroup ⊔ pCore 2 d.overgroup = ⊤) := by
  obtain ⟨g,hpos,_⟩ := h.replacement_positive_even_geometry d
  have hb : 0 < geometry.b d.radical := hpos
  have heven : Even (geometry.b d.radical) := geometry.even (alpha d.radical) rfl
  by_cases htwo : geometry.b d.radical = 2
  · exact Or.inl htwo
  · obtain ⟨k,hk⟩ := heven
    have hfour : 4 ≤ geometry.b d.radical := by omega
    exact Or.inr ⟨hfour,h.replacement_inner_of_four_le d geometry hfour⟩

omit d in
/-- The intrinsic input constructs this alternative on an actual minimum
characteristic replacement, without an extra radicality hypothesis. -/
theorem Input.exists_replacement_distance_two_or_inner :
    ∃ d : CharacteristicReduction K R, ∃ geometry : Geometry d.radical,
      geometry.b d.radical = 2 ∨
        (4 ≤ geometry.b d.radical ∧ K.subgroupOf d.overgroup ⊔ pCore 2 d.overgroup = ⊤) := by
  obtain ⟨d⟩ := exists_characteristicReduction_of_core_le (L := K) h.radical.twoCore_le
  obtain ⟨geometry,_,_⟩ := h.replacement_positive_even_geometry d
  exact ⟨d,geometry,h.replacement_distance_two_or_inner d geometry⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
