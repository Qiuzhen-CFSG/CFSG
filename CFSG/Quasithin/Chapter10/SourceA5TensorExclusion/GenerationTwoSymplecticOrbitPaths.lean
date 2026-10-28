module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticMovingRadius

/-!
# Original backward paths with their local conjugators

The displacement alternative applies source 2.1(vii) to the prescribed
neighboring join. The equal-mover pair and unequal-mover generator retain
their actual conjugators as well. Thus the backward critical vertex is a
stabilizer conjugate of the literal second vertex of the old path, and its
edge and every overlap vertex are retained. Iteration now gives the local
orbit condition in MS93 (5.10)(iii), not only an arbitrary backward sequence.

The full original vertex centers are trivial: the seed centralizer puts
them in Q, and the residual-fixed core is trivial. Hence the actual critical
commutators satisfy (5.11)(2). The final original-geometry application keeps
these noncentrality statements, paired commutator centrality, local orbits
and movement of the full truncated kernels together on the same sequence.
The selected-generator normalization, stronger radius-image estimate and
both terminal distance exclusions remain to be proved; no unconditional
SymplecticPlaneRecognition is asserted here.

Source: MS93 (2.1)(vii), (5.5)--(5.11), pp.856,915--924;
Aschbacher--Smith 9.3.10, pp.734--735.
-/

public noncomputable section


open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open ChapterC.Sp4Four.DistanceReduction.StrictIndex
open ChapterC.Sp4Four.DistanceReduction.LargeDistance
open scoped commutatorElement
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

/-- The displacement branch preserves the prescribed neighboring seed's
orbit, instead of selecting a new unrelated neighbor. -/
theorem original_backward_conjugate_of_radius_displacement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      1 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      ⁅V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)),Z R z⁆ ≤ Z R a →
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g d) (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = act R g t ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i := by
  intro R geometry hb a z d t path hat hdt hmove hdisp
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,_,_,_⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  have hgen : pResidual 2 c.M ⊔ R = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    obtain ⟨k,hk,r,hr,rfl⟩ := c.component_product.2.2.2 x
    exact Subgroup.mul_mem _ (mem_sup_left hk) (mem_sup_right hr)
  let N := Z R d ⊔ Z R a
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [path.start_color] at h
    cases he : color R t <;> simp_all
  have hNQ : N ≤ Q R a := (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt).trans
    (geometry.V_le_Q (by omega) a path.start_color)
  have hNS : N ≤ stabilizer R a := hNQ.trans (fun _ hx => hx.1)
  have hnQ := ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat hdt
  have hnS : ¬ (N.subgroupOf (stabilizer R a)).Normal := by
    intro hn
    have hi := c.original_normal_neighbor_join_moving_index_eq_one eK geometry
      (by change 2 < geometry.b R; omega) path.start_color hat hdt
      ((Ltilde_le_stabilizer a).trans ((normal_subgroupOf_iff_le_normalizer hNS).mp hn))
    change (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d)=1 at hi
    omega
  have hpos : 0 < geometry.b R := by omega
  have hrev := c.original_critical_reverse eK geometry hpos path
  have hegen := edge_conjugate_generation_of_centric_component R hodd.isPGroup hodd.twoCore_le
    hgen q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _) hBC
    path.start_color hat (Z R z) (path.endpoint_Z_le_start_stabilizer hpos) hrev.critical.2
  obtain ⟨g,hg,hbad,_⟩ := source_2_1_vii R a z t path.start_color hat N N
    (hNQ.trans (Q_le_adjacent_h R ht hat)) (hNQ.trans (Q_le_adjacent_h R ht hat))
    (normal_subgroupOf_of_le_normalizer hnQ) (normal_subgroupOf_of_le_normalizer hnQ)
    hnS hnS hegen
  have hga : act R g a = a := hg
  have hatg : Adjacent R a (act R g t) := by
    rw [←hga]
    exact (adjacent_act_iff R g _ _).mpr hat
  have hdtg := (adjacent_act_iff R g _ _).mpr hdt
  change ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a).map (MulAut.conj g⁻¹).toMonoidHom) at hbad
  rw [Subgroup.map_sup,←Z_act,←Z_act,hga] at hbad
  have hV : Z R (act R g d) ≤ V R a := le_sup_left.trans
    (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hatg hdtg)
  have hnot : ¬ Z R (act R g d) ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
    intro hk
    apply hbad
    exact normalizes_sup_of_displacement (Z R z) (Z R (act R g d)) (Z R a)
      ((path.endpoint_Z_le_start_stabilizer hpos).trans (Z_normalized R a))
      ((commutator_mono (le_inf hV hk) le_rfl).trans hdisp)
  exact ⟨g,hg,ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
    geometry (by omega) path hatg hdtg hnot⟩

/-- Both mover branches retain a conjugator from the prescribed neighboring
seed, together with its edge and every vertex of the overlapping path. -/
theorem original_backward_conjugate_of_strict_mover
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g d) (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = act R g t ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i := by
  intro R geometry hb a z d t path hat hdt hmove
  rcases c.original_radius_displacement_or_root eK geometry path with hdisp | ⟨haz,hza,hXa,_⟩
  · exact c.original_backward_conjugate_of_radius_displacement eK geometry hb path hat hdt
      (by change 1 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d); omega) hdisp
  by_cases heq : LocalPackage.J R d t = LocalPackage.J R a t
  · obtain ⟨g,hg,x,hx,_,_,hback | hback⟩ :=
      c.original_equal_mover_strict_backward_selection eK geometry hb path hat hdt heq
        hza haz hXa hmove
    · exact ⟨g⁻¹,(stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg),hback⟩
    · refine ⟨g⁻¹*x,(stabilizer R a).mul_mem
        ((stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)) (Ltilde_le_stabilizer a hx),?_⟩
      rw [act_mul R g⁻¹ x d]
      simpa only [act_mul] using hback
  · obtain ⟨g,hg,hgen⟩ := c.original_unequal_mover_generator eK geometry path hat hdt heq hza haz
    have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
    have hga : act R g⁻¹ a = a := hgS
    have hatg : Adjacent R a (act R g⁻¹ t) := by
      rw [←hga]
      exact (adjacent_act_iff R g⁻¹ _ _).mpr hat
    have hdtg := (adjacent_act_iff R g⁻¹ _ _).mpr hdt
    have hgen' : Ltilde R a ≤ LocalPackage.J R (act R g⁻¹ d) (act R g⁻¹ t) ⊔ Z R z := by
      rwa [smallMoverJoin_act,inv_inv]
    have hmove' : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
        (geometry.Z_normal a)).relIndex (U R (act R g⁻¹ d)) := by
      rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega)
        path.start_color g⁻¹ hgS]
      exact hmove
    have hbad : ¬ Z R z ≤ normalizer ((Z R (act R g⁻¹ d) ⊔ Z R a :
        Subgroup (FreeAmalgam R)) : Set _) := by
      intro hn
      have hJ := (LocalPackage.J_le_radical R (act R g⁻¹ d) (act R g⁻¹ t)).trans
        (ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hatg hdtg)
      have hi := c.original_normal_neighbor_join_moving_index_eq_one eK geometry
        (by change 2 < geometry.b R; omega) path.start_color hatg hdtg
        (hgen'.trans (sup_le hJ hn))
      change (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
        (geometry.Z_normal a)).relIndex (U R (act R g⁻¹ d))=1 at hi
      omega
    exact ⟨g⁻¹,hgS,(c.original_small_movers_backward_path eK geometry hb path
      hatg hdtg hbad hgen' hmove').1⟩

/-- The literal second vertex supplies the moving neighbor. Thus every
original critical path has a backward shift in that same local orbit. -/
theorem original_backward_path_with_conjugator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g (path.walk.getVert 2))
            (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1 = act R g (path.walk.getVert 1) ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i := by
  intro R geometry hb a z path
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  exact c.original_backward_conjugate_of_strict_mover eK geometry hb path hat hdt
    (c.original_critical_strict_movement eK geometry hb path)

/-- Iterate the actual orbit-preserving choices. In particular each third
start is a stabilizer conjugate of the preceding start at the middle vertex,
the source (5.10)(iii) condition needed for central propagation. -/
theorem original_overlapping_sequence_with_conjugators
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R → ∀ p : CriticalSegment geometry,
      ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
        (∀ n, BackwardLink geometry
          (fun q d t => ∃ g ∈ stabilizer R q.first,
            d=act R g (q.path.walk.getVert 2) ∧ t=act R g (q.path.walk.getVert 1))
          (s n) (s (n+1))) ∧
        (∀ n k i, i+2*k ≤ geometry.b R →
          (s (n+k)).path.walk.getVert (i+2*k) = (s n).path.walk.getVert i) ∧
        (∀ n, ∃ g ∈ stabilizer R (s (n+1)).first,
          act R g (s n).first=(s (n+2)).first) ∧
        ⁅⁅Z R (s 2).first,Z R (s 2).last⁆ ⊔
          ⁅Z R (s 3).first,Z R (s 3).last⁆,V R (s 2).last⁆ = ⊥ := by
  intro R geometry hb p
  let Chosen : CriticalSegment geometry → Vertex R → Vertex R → Prop :=
    fun q d t => ∃ g ∈ stabilizer R q.first,
      d=act R g (q.path.walk.getVert 2) ∧ t=act R g (q.path.walk.getVert 1)
  have hstep (q : CriticalSegment geometry) :
      ∃ d t, Chosen q d t ∧ Adjacent R q.first t ∧ Adjacent R d t ∧
        ¬ Z R d ≤ Q R (q.path.walk.getVert (geometry.b R-2)) := by
    obtain ⟨g,hg,back,hbt,_⟩ := c.original_backward_path_with_conjugator eK geometry hb q.path
    have hlen : 0 < back.walk.length := by
      rw [back.length_eq_b]
      change 0 < geometry.b R
      omega
    have hdt : Adjacent R (act R g (q.path.walk.getVert 2))
        (act R g (q.path.walk.getVert 1)) := by
      have ht := (cosetGraph_adj R _ _).mp (back.walk.adj_getVert_succ hlen)
      simpa only [SimpleGraph.Walk.getVert_zero,hbt] using ht
    have hqt : Adjacent R q.first (act R g (q.path.walk.getVert 1)) := by
      have ht := (cosetGraph_adj R _ _).mp (q.path.walk.adj_getVert_succ
        (by rw [q.path.length_eq_b]; omega : 0 < q.path.walk.length))
      simp only [SimpleGraph.Walk.getVert_zero] at ht
      have hf : act R g q.first=q.first := hg
      simpa only [hf] using (adjacent_act_iff R g _ _).mpr ht
    exact ⟨_,_,⟨g,hg,rfl,rfl⟩,hqt,hdt,by simpa only [q.path.length_eq_b] using back.critical.2⟩
  obtain ⟨s,hs0,hs,hover⟩ := exists_chosen_sequence (by omega) Chosen hstep p
  refine ⟨s,hs0,hs,hover,?_,paired_critical_commutators_centralize_radius hb Chosen s hs⟩
  intro n
  obtain ⟨t,⟨g,hg,hd,_⟩,_,_,_⟩ := (hs (n+1)).choice
  refine ⟨g,hg,?_⟩
  have hv := shifted_start_vertex Chosen s hs n 1 (by omega)
  simpa only [Nat.add_assoc,show 1+1=2 from rfl,hv] using hd.symm

/-- The entire center of every original M-vertex stabilizer is trivial.
This uses its actual seed centralizer Q and the full residual-fixed core. -/
theorem original_vertex_center_eq_bot
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a : Vertex R}, color R a = false →
      stabilizer R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R)) = ⊥ := by
  intro R a ha
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  apply le_bot_iff.mp
  rw [←c.original_fixedCore_eq_bot a ha]
  apply le_inf
  · rw [←C_eq_Q R hodd.isPGroup hodd.twoCore_le hfaith a ha]
    exact inf_le_inf_left _ (centralizer_le (Z_le_stabilizer R a))
  · exact inf_le_right.trans (centralizer_le (Ltilde_le_stabilizer a))

/-- A critical commutator cannot lie in any original vertex center.
This discharges the noncentrality conclusion (5.11)(2) directly in the
center-free tensor specialization, retaining the actual commutator. -/
theorem original_critical_commutator_not_le_vertex_center
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z v : Vertex R} (_path : CriticalPath R geometry a z),
      color R v = false →
      ¬ ⁅Z R a,Z R z⁆ ≤
        stabilizer R v ⊓ centralizer (stabilizer R v : Set (FreeAmalgam R)) := by
  intro R geometry a z v path hv hle
  rw [c.original_vertex_center_eq_bot eK hv] at hle
  have hzero : ⁅Z R a,Z R z⁆ = ⊥ := le_bot_iff.mp hle
  have hcard := c.original_critical_commutator_card_four_of_small eK geometry path
    (by rw [hzero,card_bot]; decide)
  rw [hzero,card_bot] at hcard
  omega

/-- The original large-distance consumer now has the full local orbits,
truncated-kernel movement, paired centrality and source (5.11)(2) on one
sequence. The stronger radius bound and selected-generator normalization
are not assumptions of this construction and still need their source proofs. -/
theorem original_large_distance_configuration
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R → ∀ p : CriticalSegment geometry,
      ∃ s : ℕ → CriticalSegment geometry, s 0 = p ∧
        (∀ n, BackwardLink geometry
          (fun q d t => ∃ g ∈ stabilizer R q.first,
            d=act R g (q.path.walk.getVert 2) ∧ t=act R g (q.path.walk.getVert 1))
          (s n) (s (n+1))) ∧
        (∀ n k i, i+2*k ≤ geometry.b R →
          (s (n+k)).path.walk.getVert (i+2*k) = (s n).path.walk.getVert i) ∧
        (∀ n, ∃ g ∈ stabilizer R (s (n+1)).first,
          act R g (s n).first=(s (n+2)).first) ∧
        (∀ n, 4 ≤ (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R (s n).first
          (geometry.Z_normal (s n).first)).relIndex
            (V R (s n).first ⊓ Q R (s (n+1)).last)) ∧
        ⁅⁅Z R (s 2).first,Z R (s 2).last⁆ ⊔
          ⁅Z R (s 3).first,Z R (s 3).last⁆,V R (s 2).last⁆ = ⊥ ∧
        (¬ ⁅Z R (s 2).first,Z R (s 2).last⁆ ≤
          stabilizer R (s 1).first ⊓ centralizer (stabilizer R (s 1).first : Set (FreeAmalgam R))) ∧
        (¬ ⁅Z R (s 3).first,Z R (s 3).last⁆ ≤
          stabilizer R (s 2).first ⊓ centralizer (stabilizer R (s 2).first : Set (FreeAmalgam R))) := by
  intro R geometry hb p
  obtain ⟨s,hs0,hs,hover,horbit,hcent⟩ :=
    c.original_overlapping_sequence_with_conjugators eK geometry hb p
  refine ⟨s,hs0,hs,hover,horbit,?_,hcent,
    c.original_critical_commutator_not_le_vertex_center eK geometry (s 2).path (s 1).path.start_color,
    c.original_critical_commutator_not_le_vertex_center eK geometry (s 3).path (s 2).path.start_color⟩
  intro n
  rw [(hs n).last_eq]
  simpa only [(s n).path.length_eq_b] using
    (c.original_truncated_radius_kernel_movement eK geometry hb (s n).path).1

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
