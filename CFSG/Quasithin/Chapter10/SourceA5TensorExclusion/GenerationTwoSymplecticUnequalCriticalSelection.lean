module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticLargeSelection

/-!
# Escaping original large-image choices with unequal full movers

The full neighbor commutator is proper in the order-256 seed: nilpotent
saturation forbids a finite two-group from moving that seed onto itself.
Its order is therefore at most 128, so the original residual cannot normalize
a nonzero such commutator. Source 2.1(vii) selects an escaping conjugate.
The proved large-image endpoint normalization forces that conjugate to extend
the literal critical path backwards, without an equal-mover hypothesis.

For unequal first movers the backward image has order sixteen. Otherwise
its small-image mover equality transports back to the original edge. The
full backward kernel is the critical root of order sixteen and is centralized
by the old endpoint. It is properly contained in the escaping commutator;
in particular the original neighbor commutator has order greater than sixteen.
The selected-kernel application retains the actual conjugator, every overlap
vertex and normalization of the full kernel joined with the original seed.

This supplies large-image escaping choices and their full-kernel control.
Residual-generator positioning, the terminal large-distance exclusions,
distance four and SymplecticPlaneRecognition remain to be proved.

Source: MS93 (2.1)(vii), (5.7)--(5.10), printed pp.856,919--923;
Aschbacher--Smith 9.3.10 and the final paragraph of9.3, pp.734--735.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

private theorem neighbor_kernel_commutator_le_seed
    {M : Type*} [Group M] [Finite M] {R : Subgroup M} {a d t : Vertex R}
    (ha : color R a = false) (hat : Adjacent R a t) (hdt : Adjacent R d t) :
    ⁅Z R d,Q R a⁆ ≤ Z R d := by
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [ha] at h
    cases he : color R t <;> simp_all
  exact le_normalizer_iff_commutator_le_left.mp
    (((Q_le_adjacent_h R ht hat).trans
      (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt))).trans
        (Z_normalized R d))


/-- The neighbor-kernel commutator is proper in the original natural seed. -/
theorem original_neighbor_commutator_card_le_128
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      Nat.card (⁅Z R d,Q R a⁆ : Subgroup (FreeAmalgam R)) ≤ 128 := by
  intro R geometry hb a d t ha hat hdt
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [ha] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let N := ⁅Z R d,Q R a⁆
  have hNZ : N ≤ Z R d := neighbor_kernel_commutator_le_seed ha hat hdt
  have hZQ : Z R d ≤ Q R a :=
    (le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)).trans
      (geometry.V_le_Q hb a ha)
  let := finite_stabilizer R a
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)) (inclusion_injective _)
  let := finite_Z R d
  let : Finite N := Finite.of_injective (inclusion hNZ) (inclusion_injective _)
  have hc : Nat.card (Z R d) = 256 := c.original_Z_card eK d hd
  have hne : N ≠ Z R d := by
    intro he
    have hzero := le_of_le_sup_commutator_of_isNilpotent (Q R a) (Z R d) ⊥ (Q R a)
      (Q_isPGroup R hodd.isPGroup hodd.twoCore_le a ha).isNilpotent hZQ bot_le le_rfl
      (le_normalizer_of_normal) (by change Z R d ≤ ⊥ ⊔ N; rw [he,bot_sup_eq])
    rw [le_bot_iff.mp hzero,card_bot] at hc
    omega
  have hm := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R)) N (Z R d) bot_le hNZ
  rw [relIndex_bot_left,relIndex_bot_left,hc] at hm
  have hi : 2 ≤ N.relIndex (Z R d) := by
    have hpos : 0 < N.relIndex (Z R d) := by nlinarith
    have hnot : N.relIndex (Z R d) ≠ 1 := fun he => hne
      (le_antisymm hNZ (relIndex_eq_one.mp he))
    omega
  change Nat.card N ≤ 128
  nlinarith

/-- The original large-image branch has an actual backward conjugate whose
full neighbor commutator escapes endpoint normalization, regardless of
whether the first two full movers agree. -/
theorem original_large_critical_commutator_escaping_backward
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      4 < (Q R z).relIndex (Z R a) →
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g (path.walk.getVert 2))
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act R g (path.walk.getVert 1) ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ¬ Z R z ≤ normalizer (⁅Z R (act R g (path.walk.getVert 2)),Q R a⁆ :
          Subgroup (FreeAmalgam R)) := by
  intro R geometry hb a z path hlarge
  let d := path.walk.getVert 2
  let t := path.walk.getVert 1
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a t := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R d t := adjacent_symm R ((cosetGraph_adj R _ _).mp
    (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hd : color R d = false := (path.vertex_color (by omega)).mpr (by decide)
  have hmove := c.original_critical_strict_movement eK geometry hb path
  have hne : ⁅Z R d,Q R a⁆ ≠ ⊥ := by
    intro hz
    have hc := commutator_eq_bot_iff_le_centralizer.mp hz
    have hB := c.original_neighbor_core_fixed_eq_B eK geometry (by change 2 < geometry.b R; omega) path.start_color hat hdt
      (lt_trans (by decide : 1 < 4) hmove)
    have hle : Z R d ≤ CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a) :=
      (le_inf le_rfl hc).trans (hB.le.trans inf_le_right)
    rw [c.original_Z_eq_U d hd] at hle
    rw [relIndex_eq_one.mpr hle] at hmove
    omega
  have hbound := c.original_neighbor_commutator_card_le_128 eK geometry (by change 2 < geometry.b R; omega)
    path.start_color hat hdt
  obtain ⟨g,hg,hbad⟩ := c.original_neighbor_commutator_escape eK geometry (by change 2 < geometry.b R; omega)
    path hat hdt hne (hbound)
  have hga : act R g a = a := hg
  have hatg : Adjacent R a (act R g t) := by
    simpa only [hga] using (adjacent_act_iff R g _ _).mpr hat
  have hdtg := (adjacent_act_iff R g _ _).mpr hdt
  let H := ⁅Z R (act R g d),Q R a⁆
  change ¬ Z R z ≤ normalizer (H : Set (FreeAmalgam R)) at hbad
  have hZlocal := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b R)
  have hnot : ¬ Z R (act R g d) ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
    intro hkernel
    have hn := c.original_critical_kernel_endpoint_normalized_of_large eK geometry hb
      path hatg hdtg hlarge
    rw [inf_eq_left.mpr hkernel] at hn
    apply hbad
    have hV := ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hatg hdtg
    have hHZd : H ≤ Z R (act R g d) := neighbor_kernel_commutator_le_seed path.start_color hatg hdtg
    have hVH : V R a ≤ normalizer (H : Set _) :=
      ((le_centralizer_iff_isMulCommutative.mpr (V_abelian_of_four_lt R path.start_color hb)).trans
        (centralizer_le (hHZd.trans (le_sup_left.trans hV)))).trans (Subgroup.centralizer_le_normalizer _)
    have hjoin : ⁅Z R (act R g d) ⊔ Z R a,Q R a⁆ = H := le_antisymm
      (commutator_sup_le_of_relative_normal (V R a) (Z R (act R g d)) (Z R a) (Q R a) H
        hVH (le_sup_left.trans hV) (Z_le_VBall R a 2) le_rfl
        ((geometry.centralizes a path.start_color).le.trans bot_le))
      (commutator_mono le_sup_left le_rfl)
    intro x hx
    rw [←hjoin,mem_normalizer_iff_map_conj_eq,map_commutator,
      mem_normalizer_iff_map_conj_eq.mp (hn hx),
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a (hZlocal hx))]
  obtain ⟨back,hbt,hover⟩ := ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
    geometry (by omega) path hatg hdtg hnot
  exact ⟨g,hg,back,hbt,hover,hbad⟩


/-- Unequal full movers admit an escaping backward choice with image exactly
sixteen; equality cannot reappear across the literal overlapping edge. -/
theorem original_unequal_critical_escaping_backward
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) ≠
        LocalPackage.J R a (path.walk.getVert 1) →
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g (path.walk.getVert 2))
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act R g (path.walk.getVert 1) ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        (Q R (path.walk.getVert (path.walk.length-2))).relIndex
          (Z R (act R g (path.walk.getVert 2))) = 16 ∧
        ¬ Z R z ≤ normalizer (⁅Z R (act R g (path.walk.getVert 2)),Q R a⁆ :
          Subgroup (FreeAmalgam R)) := by
  intro R geometry hb a z path hne
  have hlarge : 4 < (Q R z).relIndex (Z R a) := by
    rcases c.original_critical_indices_four_or_sixteen eK geometry path with h | h
    · exact (hne (c.original_small_critical_first_movers_eq eK geometry hb path
        (by rw [h.1]; decide))).elim
    · rw [h.1]; decide
  obtain ⟨g,hg,back,hbt,hover,hbad⟩ :=
    c.original_large_critical_commutator_escaping_backward eK geometry hb path hlarge
  refine ⟨g,hg,back,hbt,hover,?_,hbad⟩
  rcases c.original_critical_indices_four_or_sixteen eK geometry back with h | h
  · have heq := c.original_small_critical_first_movers_eq eK geometry hb back
      (by rw [h.1]; decide)
    have htwo : back.walk.getVert 2 = a := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using
        hover 0 (Nat.zero_le _)
    have hga : act R g a = a := hg
    have hJa : LocalPackage.J R a (act R g (path.walk.getVert 1)) =
        (LocalPackage.J R a (path.walk.getVert 1)).map (MulAut.conj g⁻¹).toMonoidHom := by
      simpa only [hga] using smallMoverJoin_act R g a (path.walk.getVert 1)
    rw [htwo,hbt,hJa,smallMoverJoin_act] at heq
    exact (hne (Subgroup.map_injective (MulAut.conj g⁻¹).injective heq).symm).elim
  · exact h.1

/-- In the remaining unequal-mover branch the whole neighbor commutator
has more than sixteen elements. A smaller commutator would be filled by
the selected backward critical root and hence centralized by the endpoint. -/
theorem original_unequal_critical_neighbor_commutator_gt_sixteen
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) ≠
        LocalPackage.J R a (path.walk.getVert 1) →
      16 < Nat.card (⁅Z R (path.walk.getVert 2),Q R a⁆ : Subgroup (FreeAmalgam R)) := by
  intro R geometry hb a z path hne
  by_contra! hsmall
  obtain ⟨g,hg,back,hbt,hover,hi,hbad⟩ :=
    c.original_unequal_critical_escaping_backward eK geometry hb path hne
  let d := path.walk.getVert 2
  let t := path.walk.getVert 1
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a t := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R d t := adjacent_symm R ((cosetGraph_adj R _ _).mp
    (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hga : act R g a = a := hg
  have hatg : Adjacent R a (act R g t) := by
    simpa only [hga] using (adjacent_act_iff R g _ _).mpr hat
  have hdtg := (adjacent_act_iff R g _ _).mpr hdt
  let H := ⁅Z R (act R g d),Q R a⁆
  have hm : (⁅Z R d,Q R a⁆).map (MulAut.conj g⁻¹).toMonoidHom = H := by
    rw [map_commutator,←Z_act,MulEquiv.toMonoidHom_eq_coe,
      mem_normalizer_iff_map_conj_eq.mp (Q_normalized R a ((stabilizer R a).inv_mem hg))]
  have hbound : Nat.card H ≤ 16 := by
    rw [←hm,card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact hsmall
  have hr := c.original_large_critical_root_eq_kernels eK geometry back (by rw [hi]; decide)
  have hwQ : Z R (path.walk.getVert (path.walk.length-2)) ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ back.end_color)
    rw [geometry.distance_constant _ back.end_color,SimpleGraph.dist_comm,
      path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hrootH : ⁅Z R (act R g d),Z R (path.walk.getVert (path.walk.length-2))⁆ ≤ H :=
    commutator_mono le_rfl hwQ
  let := finite_Z R (act R g d)
  let : Finite H := Finite.of_injective
    (inclusion (neighbor_kernel_commutator_le_seed path.start_color hatg hdtg)) (inclusion_injective _)
  have he : ⁅Z R (act R g d),Z R (path.walk.getVert (path.walk.length-2))⁆ = H :=
    eq_of_le_of_card_ge hrootH (by rw [hr.2.2.2]; exact hbound)
  apply hbad
  change Z R z ≤ normalizer (H : Set (FreeAmalgam R))
  rw [←he]
  have hwQz : Z R (path.walk.getVert (path.walk.length-2)) ≤ Q R z := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ back.end_color)
    rw [geometry.distance_constant _ back.end_color,path.dist_end,path.length_eq_b]
    change geometry.b R-(geometry.b R-2) < geometry.b R
    omega
  exact (le_centralizer_iff.mp
    ((ChapterC.Sp4Four.DistanceReduction.LargeDistance.critical_commutator_le_endpoint
      ⟨_,_,back⟩).trans (hwQz.trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color)))))).trans
          (Subgroup.centralizer_le_normalizer _)


/-- The actual unequal-mover selection retains the full backward kernel.
It has order sixteen, is centralized by the original endpoint, and is
properly contained in the escaping neighbor commutator. In particular the
endpoint normalization of the kernel joined with the original seed is
proved, while the larger commutator is not normalized. -/
theorem original_unequal_critical_selected_full_kernel
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) ≠
        LocalPackage.J R a (path.walk.getVert 1) →
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g (path.walk.getVert 2))
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act R g (path.walk.getVert 1) ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        let K := Z R (act R g (path.walk.getVert 2)) ⊓ Q R (path.walk.getVert (path.walk.length-2))
        let H := ⁅Z R (act R g (path.walk.getVert 2)),Q R a⁆
        K = ⁅Z R (act R g (path.walk.getVert 2)),Z R (path.walk.getVert (path.walk.length-2))⁆ ∧
        Nat.card K = 16 ∧ K < H ∧
        K ≤ centralizer (Z R z : Set (FreeAmalgam R)) ∧
        Z R z ≤ normalizer ((K ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) ∧
        ¬ Z R z ≤ normalizer (H : Set (FreeAmalgam R)) := by
  intro R geometry hb a z path hne
  obtain ⟨g,hg,back,hbt,hover,hi,hbad⟩ :=
    c.original_unequal_critical_escaping_backward eK geometry hb path hne
  let K := Z R (act R g (path.walk.getVert 2)) ⊓ Q R (path.walk.getVert (path.walk.length-2))
  let H := ⁅Z R (act R g (path.walk.getVert 2)),Q R a⁆
  have hr := c.original_large_critical_root_eq_kernels eK geometry back (by rw [hi]; decide)
  have hKeq : K = ⁅Z R (act R g (path.walk.getVert 2)),Z R (path.walk.getVert (path.walk.length-2))⁆ :=
    hr.1.symm
  have hKcard : Nat.card K = 16 := hKeq ▸ hr.2.2.2
  have hwQ : Z R (path.walk.getVert (path.walk.length-2)) ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ back.end_color)
    rw [geometry.distance_constant _ back.end_color,SimpleGraph.dist_comm,
      path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hKH : K ≤ H := hKeq ▸ commutator_mono le_rfl hwQ
  have hwQz : Z R (path.walk.getVert (path.walk.length-2)) ≤ Q R z := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ back.end_color)
    rw [geometry.distance_constant _ back.end_color,path.dist_end,path.length_eq_b]
    change geometry.b R-(geometry.b R-2) < geometry.b R
    omega
  have hKC : K ≤ centralizer (Z R z : Set (FreeAmalgam R)) := by
    rw [hKeq]
    exact (ChapterC.Sp4Four.DistanceReduction.LargeDistance.critical_commutator_le_endpoint
      ⟨_,_,back⟩).trans (hwQz.trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color))))
  have hKN : Z R z ≤ normalizer (K : Set (FreeAmalgam R)) :=
    (le_centralizer_iff.mp hKC).trans (Subgroup.centralizer_le_normalizer _)
  have hlt : K < H := lt_of_le_of_ne hKH (fun he => hbad (by
    change Z R z ≤ normalizer (H : Set (FreeAmalgam R))
    rw [←he]
    exact hKN))
  have hZaN : Z R z ≤ normalizer (Z R a : Set (FreeAmalgam R)) :=
    (path.endpoint_Z_le_start_stabilizer (by omega)).trans (Z_normalized R a)
  exact ⟨g,hg,back,hbt,hover,hKeq,hKcard,hlt,hKC,
    (le_inf hKN hZaN).trans (normalizer_inf_normalizer_le_normalizer_sup _ _),hbad⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
