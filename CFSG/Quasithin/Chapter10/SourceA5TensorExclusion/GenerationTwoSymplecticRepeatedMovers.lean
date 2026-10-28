module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticPositionedSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.DistanceReduction.LargeDistance.MoverPropagation

/-!
# Original repeated movers and intermediate critical roots

The full original movers retain the same equality or inequality along
orbit-preserving backward choices and their exact overlaps. In the equal
branch, a small shifted critical root lies in the fourth full seed and
centralizes both movers at the intermediate vertex. The vanishing original
fixed core then obstructs generation of the residual by those two movers.

Construct the actual infinite sequence so that every small critical image
is followed by an image of order at least sixteen. It retains the preceding
mover control, full-kernel displacement, paired commutator centrality and
the numerical radius alternative on that same sequence. This discharges
the repeated mover comparisons and intermediate-root centrality; the
remaining source generation and terminal distance exclusions are separate.

Source: MS93 (5.10)--(5.11), printed pp.922--924;
Aschbacher--Smith 9.3.10, printed pp.734--735.
-/

public noncomputable section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

open Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterC.Sp4Four.DistanceReduction.LargeDistance
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

/-- On every shifted original path the two equal-mover premises in the
small-root fourth-seed theorem come from the same initial comparison.
The full X identity and strict movement remain proved internally. -/
theorem original_shifted_small_root_le_fourth_seed
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ (s : ℕ → CriticalSegment geometry),
      (∀ n, BackwardLink geometry OrbitChoice (s n) (s (n+1))) →
      MoverAgreement (s 0) 0 → ∀ n,
      (Q R (s (n+1)).last).relIndex (Z R (s (n+1)).first) < 16 →
      ⁅Z R (s (n+1)).first,Z R (s (n+1)).last⁆ ≤ Z R ((s (n+1)).path.walk.getVert 4) := by
  intro R geometry hb s hs heq n hsmall
  apply c.original_small_critical_root_le_fourth_seed eK geometry hb (s (n+1)).path hsmall
  · simpa only [MoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
      (sequence_first_mover_agreement_iff (by omega) s hs (n+1)).mpr heq
  · exact (sequence_mover_agreement_iff (by omega) s hs n 1 (by omega)).mpr heq


/-- A small shifted root is fixed by both literal movers at the intermediate
vertex. The fourth-seed inclusion and both mover equalities come from the
original sequence; neither is an additional hypothesis. -/
theorem original_shifted_small_root_fixed_movers
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ (s : ℕ → CriticalSegment geometry),
      (∀ n, BackwardLink geometry OrbitChoice (s n) (s (n+1))) →
      MoverAgreement (s 0) 0 → ∀ n,
      (Q R (s (n+1)).last).relIndex (Z R (s (n+1)).first) < 16 →
      ⁅Z R (s (n+1)).first,Z R (s (n+1)).last⁆ ≤
        Z R (s n).first ⊓ centralizer
          ((LocalPackage.J R (s (n+1)).first ((s (n+1)).path.walk.getVert 1) ⊔
            LocalPackage.J R (s n).first ((s n).path.walk.getVert 1) :
              Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  intro R geometry hb s hs heq n hsmall
  let p := (s (n+1)).path
  have hpLen : 4 < p.walk.length := by rw [p.length_eq_b]; exact hb
  have hqLen : 4 < (s n).path.walk.length := by rw [(s n).path.length_eq_b]; exact hb
  have htwo : p.walk.getVert 2 = (s n).first := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using (hs n).overlap 0 (by omega)
  have hfour : p.walk.getVert 4 = (s n).path.walk.getVert 2 := (hs n).overlap 2 (by omega)
  have hpeq := (sequence_first_mover_agreement_iff (by omega) s hs (n+1)).mpr heq
  have hqeq := (sequence_first_mover_agreement_iff (by omega) s hs n).mpr heq
  simp only [MoverAgreement,Nat.mul_zero,Nat.zero_add,SimpleGraph.Walk.getVert_zero] at hpeq hqeq
  have hroot2 := c.original_small_critical_root_le_second_seed eK geometry hb p hsmall hpeq
  have hroot4 := c.original_shifted_small_root_le_fourth_seed eK geometry hb s hs heq n hsmall
  change ⁅Z R (s (n+1)).first,Z R (s (n+1)).last⁆ ≤ Z R (p.walk.getVert 4) at hroot4
  rw [htwo] at hroot2
  rw [hfour] at hroot4
  have hatp : Adjacent R (s (n+1)).first (p.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp (p.walk.adj_getVert_succ (by omega : 0 < p.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hsmall4 := (c.original_small_critical_data eK geometry p hsmall).1
  have hJp := c.original_critical_small_commutator_centralizes_mover eK geometry p hatp
    (by
      rw [SimpleGraph.dist_comm,p.dist_end,p.length_eq_b]
      change geometry.b R - 1 < geometry.b R
      omega) hsmall4.le
  have hatq : Adjacent R (s n).first ((s n).path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      ((s n).path.walk.adj_getVert_succ (by omega : 0 < (s n).path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdtq : Adjacent R ((s n).path.walk.getVert 2) ((s n).path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      ((s n).path.walk.adj_getVert_succ (by omega : 1 < (s n).path.walk.length)))
  have hX := c.original_X_eq_Z_at_of_eq p.start_color (s n).path.start_color
    (c.original_small_critical_data eK geometry p hsmall).2.2
  have hfixed := c.original_equal_mover_seed_intersection_fixed_plane eK geometry
    (by change 2 < geometry.b R; omega) (s n).path.start_color hatq hdtq hqeq hX
    (c.original_critical_strict_movement eK geometry hb (s n).path)
  have hJq := ((le_inf hroot2 hroot4).trans_eq hfixed).trans inf_le_right
  refine le_inf hroot2 ?_
  exact le_centralizer_iff.mp (sup_le (le_centralizer_iff.mp hJp) (le_centralizer_iff.mp hJq))

/-- Thus a small shifted root obstructs generation by the two actual movers,
with the obstruction measured in the full original residual. -/
theorem original_shifted_small_root_not_generated
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ (s : ℕ → CriticalSegment geometry),
      (∀ n, BackwardLink geometry OrbitChoice (s n) (s (n+1))) →
      MoverAgreement (s 0) 0 → ∀ n,
      (Q R (s (n+1)).last).relIndex (Z R (s (n+1)).first) < 16 →
      ¬ Ltilde R (s n).first ≤
        LocalPackage.J R (s (n+1)).first ((s (n+1)).path.walk.getVert 1) ⊔
          LocalPackage.J R (s n).first ((s n).path.walk.getVert 1) := by
  intro R geometry hb s hs heq n hsmall hgen
  have h := c.original_shifted_small_root_fixed_movers eK geometry hb s hs heq n hsmall
  have hzero : ⁅Z R (s (n+1)).first,Z R (s (n+1)).last⁆ ≤ fixedCore R (s n).first := by
    refine le_inf ?_ ((h.trans inf_le_right).trans (centralizer_le hgen))
    apply (h.trans inf_le_left).trans
    exact ((geometry.omega_bound (s n).first (s n).path.start_color
      (by rw [geometry.distance_constant _ (s n).path.start_color]; change 0 < geometry.b R; omega)).trans
      (omegaCenter_le _))
  rw [c.original_fixedCore_eq_bot (s n).first (s n).path.start_color] at hzero
  exact c.original_critical_commutator_not_le_vertex_center eK geometry (s (n+1)).path
    (s n).path.start_color (hzero.trans bot_le)

/-- Repeat the original choices while improving every small critical image
at the next step. All first-edge mover comparisons and all newly covered
even-edge comparisons are inherited from the starting path. -/
theorem original_image_improving_mover_sequence
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R → ∀ p : CriticalSegment geometry,
      ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
        (∀ n, BackwardLink geometry OrbitChoice (s n) (s (n+1))) ∧
        (∀ n k i, i+2*k ≤ geometry.b R →
          (s (n+k)).path.walk.getVert (i+2*k) = (s n).path.walk.getVert i) ∧
        (∀ n k, 2*k+2 ≤ geometry.b R →
          (MoverAgreement (s (n+k)) k ↔ MoverAgreement p 0)) ∧
        (∀ n, (Q R (s n).last).relIndex (Z R (s n).first) < 16 →
          16 ≤ (Q R (s (n+1)).last).relIndex (Z R (s (n+1)).first)) ∧
        (∀ n, 16 ≤ (Q R (s n).last).relIndex (Z R (s n).first) →
          ⁅V R (s n).first ⊓ Q R (s (n+1)).last,Z R (s n).last⁆ ≤ Z R (s n).first) ∧
        (MoverAgreement p 0 → ∀ n,
          (Q R (s (n+1)).last).relIndex (Z R (s (n+1)).first) < 16 →
          ¬ Ltilde R (s n).first ≤
            LocalPackage.J R (s (n+1)).first ((s (n+1)).path.walk.getVert 1) ⊔
              LocalPackage.J R (s n).first ((s n).path.walk.getVert 1)) ∧
        ⁅⁅Z R (s 2).first,Z R (s 2).last⁆ ⊔
          ⁅Z R (s 3).first,Z R (s 3).last⁆,V R (s 2).last⁆ = ⊥ ∧
        (4 < (Q R (s 1).first).relIndex (V R (s 2).last) ∨
          4 < (Q R (s 2).first).relIndex (V R (s 2).last ⊓ Q R (s 1).first)) := by
  intro R geometry hb p
  let Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop := fun q d t =>
    OrbitChoice q d t ∧
      ((Q R q.last).relIndex (Z R q.first) < 16 →
        16 ≤ (Q R (q.path.walk.getVert (geometry.b R-2))).relIndex (Z R d))
  have step (q : CriticalSegment geometry) :
      ∃ d t, Chosen q d t ∧ Adjacent R q.first t ∧ Adjacent R d t ∧
        ¬ Z R d ≤ Q R (q.path.walk.getVert (geometry.b R-2)) := by
    have select : ∃ g ∈ stabilizer R q.first,
        ∃ back : CriticalPath R geometry (act R g (q.path.walk.getVert 2))
          (q.path.walk.getVert (q.path.walk.length-2)),
          back.walk.getVert 1 = act R g (q.path.walk.getVert 1) ∧
          ((Q R q.last).relIndex (Z R q.first) < 16 →
            16 ≤ (Q R (q.path.walk.getVert (q.path.walk.length-2))).relIndex
              (Z R (act R g (q.path.walk.getVert 2)))) := by
      by_cases hsmall : (Q R q.last).relIndex (Z R q.first) < 16
      · obtain ⟨g,hg,back,hbt,_,hlarge,_⟩ :=
          c.original_small_critical_backward_large_image eK geometry hb q.path hsmall
        exact ⟨g,hg,back,hbt,fun _ => hlarge⟩
      · obtain ⟨g,hg,back,hbt,_⟩ := c.original_backward_path_with_conjugator eK geometry hb q.path
        exact ⟨g,hg,back,hbt,fun h => (hsmall h).elim⟩
    obtain ⟨g,hg,back,hbt,hlarge⟩ := select
    have hga : act R g q.first = q.first := hg
    have hqt : Adjacent R q.first (act R g (q.path.walk.getVert 1)) := by
      have h := (cosetGraph_adj R _ _).mp (q.path.walk.adj_getVert_succ
        (by rw [q.path.length_eq_b]; omega : 0 < q.path.walk.length))
      simp only [SimpleGraph.Walk.getVert_zero] at h
      simpa only [hga] using (adjacent_act_iff R g _ _).mpr h
    have hdt : Adjacent R (act R g (q.path.walk.getVert 2))
        (act R g (q.path.walk.getVert 1)) := by
      have h := (cosetGraph_adj R _ _).mp (back.walk.adj_getVert_succ
        (by rw [back.length_eq_b]; omega : 0 < back.walk.length))
      simpa only [SimpleGraph.Walk.getVert_zero,hbt] using h
    refine ⟨_,_,⟨⟨g,hg,rfl,rfl⟩,?_⟩,hqt,hdt,?_⟩
    · simpa only [q.path.length_eq_b] using hlarge
    · simpa only [q.path.length_eq_b] using back.critical.2
  obtain ⟨s,hs0,hs,hover⟩ := exists_chosen_sequence (by omega) Chosen step p
  have hsOrbit (n : ℕ) : BackwardLink geometry OrbitChoice (s n) (s (n+1)) := by
    obtain ⟨t,hchosen,hat,hdt,ht⟩ := (hs n).choice
    exact ⟨⟨t,hchosen.1,hat,hdt,ht⟩,(hs n).last_eq,(hs n).overlap⟩
  refine ⟨s,hs0,hsOrbit,hover,?_,?_,?_,?_,
    paired_critical_commutators_centralize_radius hb OrbitChoice s hsOrbit,?_⟩
  · intro n k hk
    simpa only [hs0] using sequence_mover_agreement_iff (by omega) s hsOrbit n k hk
  · intro n hsmall
    obtain ⟨t,hchosen,_,_,_⟩ := (hs n).choice
    rw [(hs n).last_eq]
    exact hchosen.2 hsmall
  · intro n hlarge
    rw [(hs n).last_eq,←(s n).path.length_eq_b]
    exact c.original_radius_displacement_of_large_critical_index eK geometry (s n).path hlarge

  · intro heq n hsmall
    exact c.original_shifted_small_root_not_generated eK geometry hb s hsOrbit
      (hs0.symm ▸ heq) n hsmall
  · have h := c.original_critical_radius_index_split eK geometry hb (s 2).path
    have hv := (hs 1).overlap 0 (by omega)
    simp only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] at hv
    rwa [hv] at h

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
