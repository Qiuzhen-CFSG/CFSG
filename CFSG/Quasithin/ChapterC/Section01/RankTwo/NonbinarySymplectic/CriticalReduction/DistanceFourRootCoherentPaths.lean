module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPointCoherentPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootSelectorCompatibility
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourCoherentPaths

/-!
# Coherent backward paths for every root critical image at distance four

A strict neighboring index uses the actual equal, unequal or point selector.
Otherwise the local bound transports to every edge. Under this bound every
actual nonnormal selector is untrapped. This supplies both backward paths,
retaining the first pair's original g,x and the second source in the residual
orbit of the original midpoint. No movement, mover equality, or mover-size
premise is imposed.

The private import reuses only the internal edge-transitivity bound, without
copying it or changing its frozen owner. Public statements use public names.
This establishes compatible paths, not the subsequent commutator comparison
or exclusion of distance four. Source: MS93 (5.8), (5.12), pp.920,925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

private theorem prescribed_backward_of_uniform_bound
    {geometry : Geometry d.radical} {a z t c : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hct : Adjacent d.radical c t)
    (hnormal : ¬ stabilizer d.radical a ≤ normalizer
      ((Z d.radical c ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _))
    (hbound : ∀ v w c : Vertex d.radical, color d.radical v=false →
      Adjacent d.radical v w → Adjacent d.radical c w →
      (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F) :
    ∃ y ∈ Ltilde d.radical a,
      Adjacent d.radical a (act d.radical y t) ∧
      Adjacent d.radical (act d.radical y c) (act d.radical y t) ∧
      ¬ Z d.radical z ≤ normalizer
        ((Z d.radical (act d.radical y c) ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
      ∃ back : CriticalPath d.radical geometry (act d.radical y c)
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1=act d.radical y t ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i := by
  have complete (g x : FreeAmalgam d.radical)
      (hg : g ∈ Ltilde d.radical a) (hx : x ∈ Ltilde d.radical a)
      (v w : Vertex d.radical)
      (hwhich : (v=act d.radical g⁻¹ c ∧ w=act d.radical g⁻¹ t) ∨
        (v=act d.radical x (act d.radical g⁻¹ c) ∧
          w=act d.radical x (act d.radical g⁻¹ t)))
      (haw : Adjacent d.radical a w) (hvw : Adjacent d.radical v w)
      (hn : ¬ Z d.radical z ≤ normalizer
        ((Z d.radical v ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _)) :
      ∃ y ∈ Ltilde d.radical a,
        Adjacent d.radical a (act d.radical y t) ∧
        Adjacent d.radical (act d.radical y c) (act d.radical y t) ∧
        ¬ Z d.radical z ≤ normalizer
          ((Z d.radical (act d.radical y c) ⊔ Z d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) ∧
        ∃ back : CriticalPath d.radical geometry (act d.radical y c)
            (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=act d.radical y t ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i := by
    have hnext := h.replacement_selected_seed_backward_of_uniform_bound d path hb haw hvw hn hbound
    rcases hwhich with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact ⟨g⁻¹,(Ltilde d.radical a).inv_mem hg,haw,hvw,hn,hnext⟩
    · refine ⟨g⁻¹*x,(Ltilde d.radical a).mul_mem ((Ltilde d.radical a).inv_mem hg) hx,?_⟩
      rw [act_mul,act_mul]
      exact ⟨haw,hvw,hn,hnext⟩
  by_cases hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2
  · by_cases hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical a) ≤ Nat.card F^2
    · by_cases hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
          (Q d.radical t) (Nat.card F^2) =
        Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical t) (Nat.card F^2)
      · obtain ⟨E,hE,f,hf,hfQ,hTf,hidx,g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,
          hgen₁,hgen₂,hfixed,hmove₁,hmove₂,hxn,hxp,v,hv,w,hwhich,haw,hvw,hn,hnext⟩ :=
          h.replacement_equal_small_index_selected_root_alternative d path hb hat hfirst hct
            hnormal hequal hsmall hJm
        exact complete g x hg hx v w hwhich haw hvw hn
      · obtain ⟨g,hg,haw,hvw,hidx,htransport,hgen,hres,hfixed,hindividual,
          hquadA,hquadC,hcube,hnot,hlarge,hn,hnext⟩ :=
          h.replacement_unequal_individual_generation_root_at_neighbor d path hb hat hfirst hct
            hnormal hsmall hequal
        exact complete g 1 hg (Ltilde d.radical a).one_mem _ _ (Or.inl ⟨rfl,rfl⟩) haw hvw hn
    · obtain ⟨g,hg,haw,hvw,hidx,htransport,hgen,hfixed,hn,hnext⟩ :=
        h.replacement_large_movement_selected_root_at_neighbor d path hb hat hfirst hct
          hnormal hsmall (lt_of_not_ge hJm)
      exact complete g 1 hg (Ltilde d.radical a).one_mem _ _ (Or.inl ⟨rfl,rfl⟩) haw hvw hn
  · by_cases hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
          (U d.radical a) ≤ Nat.card F^2
    · obtain ⟨E,hE,f,hf,hfQ,hTf,hidx,hcore,hTP,hquad,hmax⟩ :=
        h.replacement_maximizing_parabolic d geometry hb path.start_color hat
      have hJP := h.replacement_small_mover_le_maximizing_plane_of_index_le d
        geometry hb path.start_color hat E hE f hfQ hTf hidx hmax hJm
      obtain ⟨g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,hgen₁,hgen₂,hfixed,hxn,hxp,
          v,hv,w,hwhich,haw,hvw,hn,hidx',hnext⟩ :=
        h.replacement_original_smaller_large_backward_path d path hb hat hfirst hct hnormal
          E hE f hf hfQ hTf hidx (le_of_not_gt hsmall) hJP
      exact complete g x hg hx v w hwhich haw hvw hn
    · have hq : 1 < Nat.card F := Finite.one_lt_card
      have hlarge : Nat.card F < (Q d.radical a).relIndex (Z d.radical z) := by
        have hh := le_of_not_gt hsmall
        nlinarith
      obtain ⟨g,hg,haw,hvw,hidx,htransport,hgen,hfixed,hn,hnext⟩ :=
        h.replacement_large_movement_selected_large_at_neighbor d path hb hat hfirst hct
          hnormal hlarge (lt_of_not_ge hJm)
      exact complete g 1 hg (Ltilde d.radical a).one_mem _ _ (Or.inl ⟨rfl,rfl⟩) haw hvw hn

/-- Every root critical image at distance four supplies two compatible
actual backward paths. The original neighbor is selected internally; no
strict movement, mover equality, size bound or uniform-bound premise
remains. Both selector markings and all overlaps are retained. -/
theorem Input.replacement_distance_four_root_coherent_paths
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (hsmall : (Q d.radical a).relIndex (Z d.radical z) < Nat.card F^2) :
    ∃ c, Adjacent d.radical c t ∧ distanceFourCoherentPaths path c t := by
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  by_cases hstrict : ∃ c, Adjacent d.radical c t ∧
      Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c)
  · obtain ⟨c,hct,hmove⟩ := hstrict
    exact ⟨c,hct,h.replacement_distance_four_strict_root_coherent_paths d path hb
      hat hfirst hct hmove hsmall⟩
  · have hlocal : ∀ c, Adjacent d.radical c t →
        (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) ≤ Nat.card F := by
      intro c hct
      exact le_of_not_gt (fun hm => hstrict ⟨c,hct,hm⟩)
    have hbound : ∀ v w c : Vertex d.radical, color d.radical v=false →
        Adjacent d.radical v w → Adjacent d.radical c w →
        (B d.radical v (geometry.Z_normal v)).relIndex (U d.radical c) ≤ Nat.card F := by
      intro v w c hv hvw hcw
      exact global_neighbor_bound_of_edge geometry (by omega) path.start_color hat
        (Nat.card F) hlocal hv hvw hcw
    let c := path.walk.getVert 2
    have hct : Adjacent d.radical c t := by
      rw [←hfirst]
      exact adjacent_symm _ ((cosetGraph_adj _ _ _).mp
        (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 1 < path.walk.length)))
    have hmove : 1 < (B d.radical a (geometry.Z_normal a)).relIndex (U d.radical c) :=
      (Finite.one_lt_card (α := F)).trans_le (h.replacement_path_moving_index_ge_field d path hb4)
    obtain ⟨g,hg,x,hx,ha₁,hc₁,ha₂,hc₂,hi₁,hi₂,hkind,u,hu,w,hwhich,haw,huw,hbackexists⟩ :=
      h.replacement_root_backward_selection_of_uniform_bound d path hb4 hat hfirst hct
        hmove hsmall hbound
    have hlen : path.walk.length=4 := path.length_eq_b.trans hb
    have hend : path.walk.getVert (path.walk.length-2)=path.walk.getVert 2 := by rw [hlen]
    rw [hend] at hbackexists
    obtain ⟨back,hback,hoverlap⟩ := hbackexists
    have hmid : back.walk.getVert 2=a := by simpa using hoverlap 0 (by omega)
    have hbacklen : back.walk.length=4 := back.length_eq_b.trans hb
    have hnextend : back.walk.getVert (back.walk.length-2)=a := by rw [hbacklen]; exact hmid
    have hut : Adjacent d.radical u (back.walk.getVert 1) := by rwa [hback]
    have hat' : Adjacent d.radical a (back.walk.getVert 1) := by rwa [hback]
    have hun : ¬ stabilizer d.radical u ≤ normalizer
        ((Z d.radical a ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) := by
      simpa only [hmid] using h.replacement_path_neighbor_join_not_normal_of_four_le d back hb4
    obtain ⟨y,hy,hus,hvs,hn,hnext⟩ :=
      prescribed_backward_of_uniform_bound h d back hb4 hut rfl hat' hun hbound
    rw [hnextend] at hnext
    exact ⟨c,hct,g,hg,x,hx,u,w,hwhich,haw,huw,back,hback,hoverlap,
      _,_,y,hy,rfl,rfl,hus,hvs,hn,hnext⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
