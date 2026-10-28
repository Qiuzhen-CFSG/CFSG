module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourUnequalRootCentrality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourCoherentPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootTrappedPaths
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourComparisonEscape

/-!
# Actual coherent paths from a strict unequal first selector

The unequal individual selector supplies both its own residual generation
and centrality of the entire backward root at the original vertex. Strict
movement excludes first trapping. Its actual unequal pair is transported
to the backward edge, where the second selector's individual generation
forces movement of the full critical commutator. The full-displacement
trapping argument then supplies an actual second backward path.

The private import is an intentional internal proof boundary: it reuses the
full fixed-attachment trapping argument without changing the frozen module
or exposing private declarations in this module's public statement. This
proves path existence; the restricted-actor unequal comparison remains a
separate assertion. Source: MS93 (5.8) and (5.12), pp.920,925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem individual_generation_moves_root
    {geometry : Geometry d.radical} {u e v s : Vertex d.radical}
    (back : CriticalPath d.radical geometry u e) (hb : 4 ≤ geometry.b d.radical)
    (hres : Ltilde d.radical u ≤ Subgroup.SmallMover.join (U d.radical v)
      (Q d.radical v) (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical e) :
    ¬ ⁅Z d.radical e,U d.radical u⁆ ≤ centralizer
      (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical s) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  intro hfix
  let T := ⁅Z d.radical u,Z d.radical e⁆
  let J := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
    (Q d.radical s) (Nat.card F^2)
  have hTJ : T ≤ centralizer (J : Set (FreeAmalgam d.radical)) := by
    have heq := h.replacement_Z_commutator_eq_U d geometry hb back.start_color
      (Z d.radical e) (back.endpoint_Z_le_start_stabilizer (by omega))
    change ⁅Z d.radical u,Z d.radical e⁆ ≤ _
    rw [heq,commutator_comm]
    exact hfix
  let : IsElementaryAbelian 2 (Z d.radical e) :=
    geometry.Z_elementary (by omega) e back.end_color
  have hTe : T ≤ centralizer (Z d.radical e : Set (FreeAmalgam d.radical)) :=
    (critical_commutator_le_endpoint_seed back).trans (Z d.radical e).le_centralizer
  have hTL : T ≤ centralizer (Ltilde d.radical u : Set (FreeAmalgam d.radical)) :=
    le_centralizer_iff.mp (hres.trans (sup_le (le_centralizer_iff.mp hTJ)
      (le_centralizer_iff.mp hTe)))
  have hTZ : T ≤ Z d.radical u := critical_commutator_le_start_seed back
  have hTQ : T ≤ centralizer (Q d.radical u : Set (FreeAmalgam d.radical)) :=
    hTZ.trans (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes u back.start_color))
  have hwhole : Ltilde d.radical u ⊔ Q d.radical u=stabilizer d.radical u := by
    obtain ⟨i,hi,hir,hiL,hiU,hiQ⟩ := Sp4Four.SourceComparison.vertex_coordinates_with_kernel
      d.radical (h.replacement_two_group d) (h.replacement_core_le d) back.start_color
    rw [←hiL,←hiQ,←Subgroup.map_sup,h.replacement_residual d,
      h.replacement_inner_of_four_le d geometry hb,←MonoidHom.range_eq_map,hir]
  have hTS : T ≤ centralizer (stabilizer d.radical u : Set (FreeAmalgam d.radical)) := by
    apply le_centralizer_iff.mp
    rw [←hwhole]
    exact sup_le (le_centralizer_iff.mp hTL) (le_centralizer_iff.mp hTQ)
  have hi := h.replacement_critical_commutator_central_index d back hb
  rw [relIndex_eq_one.mpr (le_inf (hTZ.trans (Z_le_stabilizer _ _)) hTS)] at hi
  have hlo := (h.replacement_critical_indices_ge_field d back (by omega)).1
  have hq : 1 < Nat.card F := Finite.one_lt_card
  omega

/-- A strict unequal initial mover supplies two actual backward critical
paths, retaining the same first selector and the prescribed second orbit.
No second small-image, movement, centrality, or nontrapping premise is
required. All path overlaps and full fixed attachments are retained. -/
theorem Input.replacement_distance_four_strict_unequal_root_coherent_paths
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hct : Adjacent d.radical c t)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c))
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2)
    (hne : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) ≠
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2)) :
    distanceFourCoherentPaths path c t := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hn
    have hidx := (neighbor_seed_join_index_le geometry (by omega) path.start_color hat hct).trans
      (h.replacement_root_neighbor_seed_index_le_cube d path hb4 hat hct hsmall)
    have hq : 1 < Nat.card F := Finite.one_lt_card
    have hBY := h.replacement_small_radius_le_B d geometry (by omega) path.start_color
      (Z d.radical c ⊔ Z d.radical a) (neighbor_seed_join_le_radius hat hct)
      ((Ltilde_le_stabilizer a).trans hn)
      (lt_of_le_of_lt hidx ((pow_lt_pow_iff_right₀ hq).mpr (by decide)))
    have hone := relIndex_eq_one.mpr (((U_le_Z c).trans le_sup_left).trans hBY)
    rw [hone] at hmove
    exact (not_lt_of_ge hq.le) hmove
  obtain ⟨g,hg,haw,huw,hindex,htransport,hgen,hres,hfixed,hindividual,
    hquad,hquadU,hcube,hnot,hlarge,hn,hnext,hCa⟩ :=
    h.replacement_distance_four_unequal_first_root_centrality d path hb hat hfirst hct
      hnormal hsmall hne
  let u := act d.radical g⁻¹ c
  let w := act d.radical g⁻¹ t
  have hmoveU : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical u) := by
    rwa [hindex]
  have hnotrap := h.replacement_unequal_trapped_root_excluded d path hb4 haw huw hn hres hmoveU
  have hbackexists := hnext.resolve_right (fun ht => hnotrap ht.1)
  have hlen : path.walk.length=4 := path.length_eq_b.trans hb
  have hend : path.walk.getVert (path.walk.length-2)=path.walk.getVert 2 := by rw [hlen]
  rw [hend] at hbackexists
  obtain ⟨back,hback,hoverlap⟩ := hbackexists
  have hmid : back.walk.getVert 2=a := by simpa using hoverlap 0 (by omega)
  have hlast : back.walk.getVert 3=path.walk.getVert 1 := by
    simpa using hoverlap 1 (by omega)
  have hbacklen : back.walk.length=4 := back.length_eq_b.trans hb
  have hnextend : back.walk.getVert (back.walk.length-2)=a := by rw [hbacklen]; exact hmid
  have hga : act d.radical g⁻¹ a=a :=
    (stabilizer d.radical a).inv_mem (Ltilde_le_stabilizer a hg)
  have hbackne : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) ≠
    Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
      (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) := by
    intro he
    rw [hback] at he
    have hm := mover_act (Nat.card F^2) g⁻¹ a t
    rw [hga,inv_inv] at hm
    have hc := mover_act (Nat.card F^2) g⁻¹ c t
    rw [inv_inv] at hc
    apply hne
    apply map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
    exact hc.symm.trans (he.symm.trans hm)
  have hut : Adjacent d.radical u (back.walk.getVert 1) := by rwa [hback]
  have hat' : Adjacent d.radical a (back.walk.getVert 1) := by rwa [hback]
  have hun : ¬ stabilizer d.radical u ≤ normalizer
      ((Z d.radical a ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    simpa only [hmid] using h.replacement_path_neighbor_join_not_normal_of_four_le d back hb4
  refine ⟨g,hg,1,(Ltilde d.radical a).one_mem,u,w,Or.inl ⟨rfl,rfl⟩,haw,huw,
    back,hback,hoverlap,?_⟩
  by_cases hsmall₂ : (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2)) < Nat.card F^2
  · obtain ⟨g₂,hg₂,hus,hvs,hidx₂,htransport₂,hgen₂,hres₂,hfixed₂,hindividual₂,
      hquad₂,hquadV₂,hcube₂,hnot₂,hlarge₂,hn₂,hnext₂⟩ :=
      h.replacement_unequal_individual_generation_root_at_neighbor d back hb4 hut rfl hat'
        hun hsmall₂ hbackne
    have hmove₂ := individual_generation_moves_root h d back hb4 hres₂
    have hnotrap₂ := second_selector_not_trapped h d path hb back hus hvs g₂⁻¹
      ((stabilizer d.radical u).inv_mem (Ltilde_le_stabilizer u hg₂)) rfl hn₂
      (hCa back hback hmid hlast hsmall₂) hmove₂
    have hnext₂ := exists_backward_path_of_not_le geometry (by omega) back hus hvs hnotrap₂
    rw [hnextend] at hnext₂
    exact ⟨_,_,g₂⁻¹,(Ltilde d.radical u).inv_mem hg₂,rfl,rfl,hus,hvs,hn₂,hnext₂⟩
  · have hJm := (h.replacement_unequal_original_quadratic d geometry hb4
      back.start_color hut hat' hbackne).1.le
    obtain ⟨E,hE,f,hf,hfQ,hTf,hidx,hcore,hTP,hquad,hmax⟩ :=
      h.replacement_maximizing_parabolic d geometry hb4 back.start_color hut
    have hJP := h.replacement_small_mover_le_maximizing_plane_of_index_le d
      geometry hb4 back.start_color hut E hE f hfQ hTf hidx hmax hJm
    obtain ⟨g₂,hg₂,x₂,hx₂,hu₁,ha₁,hu₂,ha₂,hgen₁,hgen₂,hfixed₂,hxn,hxp,
      v,hv,s,hwhich,hus,hvs,hn₂,hidx₂,hnext₂⟩ :=
      h.replacement_original_smaller_large_backward_path d back hb4 hut rfl hat' hun
        E hE f hf hfQ hTf hidx (le_of_not_gt hsmall₂) hJP
    rw [hnextend] at hnext₂
    rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨_,_,g₂⁻¹,(Ltilde d.radical u).inv_mem hg₂,rfl,rfl,hus,hvs,hn₂,
        hnext₂⟩
    · refine ⟨_,_,g₂⁻¹*x₂,(Ltilde d.radical u).mul_mem
        ((Ltilde d.radical u).inv_mem hg₂) hx₂,?_,?_,hus,hvs,hn₂,
        hnext₂⟩ <;> rw [act_mul]

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
