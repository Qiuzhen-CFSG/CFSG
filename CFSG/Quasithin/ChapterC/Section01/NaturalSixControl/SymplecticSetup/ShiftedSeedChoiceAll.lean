module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.ShiftedSeedChoice

/-!
# Shifted critical line choices beyond distance two

Reverse the critical path and apply the native radius escape at its second
predecessor. This requires only critical distance greater than two. The
existing moving-line choice then supplies one conjugator for generation and
noncentral movement at the shifted endpoint.

The distance-four instance supplies the second starred choice of MS93 (5.9),
printed pp.920--922, to the terminal argument (5.12). Every subgroup, path and
conjugation map is retained on the literal characteristic replacement.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)

/-- Shift the endpoint while retaining the original second vertex. -/
theorem exists_shifted_critical_endpoint_of_two_lt (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e) :
    ∃ d, color R d=false ∧ (cosetGraph R).dist e d=2 ∧
      CriticalPair R (p.walk.getVert 2) d
        (s.geometry.exists_critical _ ((p.vertex_color (by rw [p.length_eq_b]; omega)).mpr (by decide))) := by
  have hlen : 2 ≤ p.walk.length := by rw [p.length_eq_b]; omega
  have hc : color R (p.walk.getVert 2)=false := (p.vertex_color hlen).mpr (by decide)
  have hrev := critical_reverse R s.geometry s.edgeCentralizerCondition
    (alpha R) rfl s.criticalDistance_pos e p.end_color p.critical
  have hca : (cosetGraph R).dist (p.walk.getVert 2) (alpha R)=2 := by
    rw [SimpleGraph.dist_comm,p.dist_start hlen]
  have hec : (cosetGraph R).dist e (p.walk.getVert 2)+2=s.geometry.b R := by
    rw [SimpleGraph.dist_comm,p.dist_end,p.length_eq_b]
    omega
  have hpath : (cosetGraph R).dist e (p.walk.getVert 2)+2=(cosetGraph R).dist e (alpha R) := by
    rw [hec,SimpleGraph.dist_comm,←p.shortest,p.length_eq_b]
  have hescape := s.criticalEscape h u hfull (by omega) e p.end_color
    (alpha R) hrev (p.walk.getVert 2) hca hpath
  obtain ⟨d,hd,hde,hcrit⟩ := exists_critical_shift R p.end_color hec hescape
  refine ⟨d,hd,by simpa only [SimpleGraph.dist_comm] using hde,?_⟩
  apply critical_reverse R s.geometry s.edgeCentralizerCondition d hd _ _ hc hcrit
  rw [s.geometry.distance_constant d hd]
  change 0<s.geometry.b R
  omega

/-- The exact shifted endpoint and line choice used in source (5.9). -/
theorem exists_shifted_seed_choice_of_two_lt (h : NativeCentralLayer s) (u : Model.S)
    (hfull : R.map s.projection = Model.E.map (MulAut.conj u).toMonoidHom)
    (hb : 2 < s.geometry.b R) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (H : Subgroup (FreeAmalgam R)) (hHU : H ≤ U R (p.walk.getVert 2))
    (hH : H ≠ ⊥) (hcard : Nat.card H ≤ 2) :
    ∃ d, color R d=false ∧ (cosetGraph R).dist e d=2 ∧
      CriticalPair R (p.walk.getVert 2) d
        (s.geometry.exists_critical _ ((p.vertex_color (by rw [p.length_eq_b]; omega)).mpr (by decide))) ∧
      ∃ y ∈ stabilizer R (p.walk.getVert 2),
        (stabilizer R (p.walk.getVert 2) ⊓
          centralizer (H.map (MulAut.conj y).toMonoidHom : Set (FreeAmalgam R))) ⊔ Z R d =
            stabilizer R (p.walk.getVert 2) ∧
        ¬ H.map (MulAut.conj y).toMonoidHom ≤ centralizer (Z R d : Set (FreeAmalgam R)) := by
  obtain ⟨d,hd,hed,hcrit⟩ := s.exists_shifted_critical_endpoint_of_two_lt h u hfull hb p
  refine ⟨d,hd,hed,hcrit,?_⟩
  exact s.exists_moving_line_generator_at h u hfull
    ((p.vertex_color (by rw [p.length_eq_b]; omega)).mpr (by decide)) hcrit H hHU hH hcard

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source

namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
variable {K : Type*} [Group K] [Finite K]
  {L W : Subgroup K} [L.Normal] [W.Normal] {T : Sylow 2 K}
  (d : NaturalSixControl.SourceData L W T) (h : IntrinsicMSPair d)
local notation "J" => (L ⊔ d.B : Subgroup K)
local notation "R" => d.B.subgroupOf J

/-- The original characteristic replacement supplies the shifted choice or
its literal alternating-block alternative. -/
theorem reducedSource_block_or_shifted_seed_choice_of_two_lt
    (r : CharacteristicReduction (L.subgroupOf J) R) {e : Vertex r.radical}
    (p : CriticalPath r.radical ((originalSource d h).reduce r).geometry (alpha r.radical) e)
    (hb : 2 < ((originalSource d h).reduce r).geometry.b r.radical)
    (H : Subgroup (FreeAmalgam r.radical)) (hHU : H ≤ U r.radical (p.walk.getVert 2))
    (hH : H ≠ ⊥) (hcard : Nat.card H ≤ 2) :
    IsAlternatingBlock L 6 ∨
      ∃ f, color r.radical f=false ∧ (cosetGraph r.radical).dist e f=2 ∧
        CriticalPair r.radical (p.walk.getVert 2) f
          (((originalSource d h).reduce r).geometry.exists_critical _
            ((p.vertex_color (by rw [p.length_eq_b]; omega)).mpr (by decide))) ∧
        ∃ y ∈ stabilizer r.radical (p.walk.getVert 2),
          (stabilizer r.radical (p.walk.getVert 2) ⊓
            centralizer (H.map (MulAut.conj y).toMonoidHom : Set (FreeAmalgam r.radical))) ⊔
              Z r.radical f = stabilizer r.radical (p.walk.getVert 2) ∧
          ¬ H.map (MulAut.conj y).toMonoidHom ≤ centralizer (Z r.radical f : Set (FreeAmalgam r.radical)) := by
  rcases reducedSource_block_or_full_point_image d h r with hblock | hf
  · exact Or.inl hblock
  · let s := (originalSource d h).reduce r
    have hn := reduced_nativeCentralLayer d h r
    have he : r.radical.map s.projection = Model.E.map
        (MulAut.conj d.relabeler.val⁻¹).toMonoidHom := by
      simpa only [Model.pointCore_eq_exceptional] using hf
    exact Or.inr (s.exists_shifted_seed_choice_of_two_lt hn _ he hb p H hHU hH hcard)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.SourceData
