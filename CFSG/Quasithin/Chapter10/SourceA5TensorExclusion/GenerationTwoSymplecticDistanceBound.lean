module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticEqualMoverExclusion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalLargeSylowGeneration

/-!
# The original symplectic critical distance is four

The large quadratic critical image generates the marked Sp₄(4) with a
conjugate of the full edge Sylow. Lift that conjugator inside the original
residual, retaining the full original kernel. Strict movement and endpoint
normalization force a literal overlapping backward critical path.

Its image is sixteen by the equal-mover exclusion. The nontrivial fixed
subgroup of its starting seed under the edge Sylow lies in the full backward
kernel, so the old endpoint also fixes it. The two generating subgroups
would put it in the vanishing original fixed core, a contradiction.
Thus both large-distance branches are excluded and the original distance
is exactly four. Whole-core and original marked-plane recognition remain.

Source: MS93 (3.3), (5.5)--(5.11), pp.867,915--924, specialized to the
original center-free natural geometry in Aschbacher--Smith 9.3.10, p.734.
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

/-- A conjugate of the full edge Sylow generates with the original
large critical endpoint, with no mover-equality or extra kernel premise. -/
theorem original_large_distance_edge_sylow_generator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      ∃ g ∈ Ltilde R a,
        Ltilde R a ≤ (Q R (path.walk.getVert 1)).map
          (MulAut.conj g).toMonoidHom ⊔ Z R z := by
  intro R geometry hb a z path
  let t := path.walk.getVert 1
  have hat : Adjacent R a t := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hza : 4 < (Q R a).relIndex (Z R z) := by
    have h := (c.original_large_distance_unequal_sixteen eK geometry hb path).2.2
    rw [h]; decide
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hcard,hsq,hQne⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hself : centralizer (pCore 2 c.M : Set c.M) ≤ pCore 2 c.M := by
    simpa only [c.fitting_center.1] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := c.M))
  have hne : R ≠ ⊥ := fun hr => hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [path.start_color] at h
    cases he : color R t <;> simp_all
  obtain ⟨P,hP⟩ := c.sylow
  have hPR : (P : Subgroup c.M) = R := by
    apply Subgroup.map_injective c.M.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (c.generated ▸ le_sup_right)]
  obtain ⟨i,hi,hir,hiR,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le path.start_color hat
  let iS := i.codRestrict (stabilizer R a) (fun x => hir ▸ (show i x ∈ i.range from ⟨x,rfl⟩))
  have hiS : Function.Surjective iS := by
    intro x
    obtain ⟨y,hy⟩ := (show x.val ∈ i.range from hir.symm ▸ x.property)
    exact ⟨y,Subtype.ext hy⟩
  have hSylow : ∃ S : Sylow 2 (stabilizer R a),
      (S : Subgroup _) = (Q R t).subgroupOf (stabilizer R a) := by
    refine ⟨P.mapSurjective (f := iS) hiS,?_⟩
    apply Subgroup.map_injective (stabilizer R a).subtype_injective
    rw [Sylow.coe_mapSurjective,Subgroup.map_map,hPR,
      map_subgroupOf_eq_of_le (show Q R t ≤ stabilizer R a from
        fun _ hx => hx.2 a (adjacent_symm R hat))]
    exact hiR
  exact original_large_critical_sylow_generator R hms hodd.isPGroup hne hodd.twoCore_le
    hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path (by omega) hza (Q R t)
    (fun _ hx => hx.2 a (adjacent_symm R hat)) (Q_le_adjacent_h R ht hat) hSylow

private theorem false_of_large_sylow_generated_backward
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t → back.walk.getVert 1 = t →
      Ltilde R a ≤ Q R t ⊔ Z R z →
      4 < (Q R (path.walk.getVert (path.walk.length-2))).relIndex (Z R d) → False := by
  intro R geometry hb a z d t path back hat hdt hbt hgen hlarge
  let w := path.walk.getVert (path.walk.length-2)
  let H := Z R d ⊓ centralizer (Q R t : Set (FreeAmalgam R))
  have hpos : 0 < geometry.b R := by omega
  have rev := c.original_critical_reverse eK geometry hpos back
  have hlarge' : 4 < (Q R d).relIndex (Z R w) := by
    by_contra! hsmall
    have hdata := c.original_small_critical_data eK geometry rev (lt_of_le_of_lt hsmall (by decide : 4 < 16))
    rw [hdata.2.1] at hlarge
    omega
  have hwQt : Z R w ≤ Q R t := by
    apply Z_le_Q_of_dist_lt R w (geometry.exists_critical w back.end_color)
    rw [geometry.distance_constant w back.end_color,←hbt,SimpleGraph.dist_comm,back.dist_end,back.length_eq_b]
    change geometry.b R - 1 < geometry.b R
    omega
  have hHroot : H ≤ ⁅Z R d,Z R w⁆ :=
    (inf_le_inf_left _ (centralizer_le hwQt)).trans
      (c.original_large_critical_fixed_le_root eK geometry back hlarge')
  have hwQz : Z R w ≤ Q R z := by
    apply Z_le_Q_of_dist_lt R w (geometry.exists_critical w back.end_color)
    rw [geometry.distance_constant w back.end_color,path.dist_end,path.length_eq_b]
    change geometry.b R - (geometry.b R - 2) < geometry.b R
    omega
  have hHZ : H ≤ centralizer (Z R z : Set (FreeAmalgam R)) :=
    (hHroot.trans (ChapterC.Sp4Four.DistanceReduction.LargeDistance.critical_commutator_le_endpoint
      ⟨d,w,back⟩)).trans (hwQz.trans (le_centralizer_iff.mp
        (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color))))
  have hHJ : H ≤ centralizer (Q R t : Set (FreeAmalgam R)) := inf_le_right
  have hHL : H ≤ centralizer (Ltilde R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (hgen.trans
      (sup_le (le_centralizer_iff.mp hHJ) (le_centralizer_iff.mp hHZ)))
  have hHQ : H ≤ Q R a := inf_le_left.trans
    ((le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)).trans
      (geometry.V_le_Q (by omega) a path.start_color))
  have hHbot : H = ⊥ := by
    apply le_bot_iff.mp
    rw [←c.original_fixedCore_eq_bot a path.start_color]
    exact le_inf hHQ hHL
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨i,_,_,hiT,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le
    back.start_color hdt
  have hpT : IsPGroup 2 (Q R t) := hiT ▸ hodd.isPGroup.map i
  have ht : color R t = true := by
    have h := adjacent_color_ne R hdt
    rw [back.start_color] at h
    cases he : color R t <;> simp_all
  have hZdT : Z R d ≤ Q R t :=
    ((geometry.omega_bound d back.start_color
      (by rw [geometry.distance_constant d back.start_color]; exact hpos)).trans (omegaCenter_le _)).trans
        (Q_le_adjacent_h R ht hdt)
  have hn : Q R t ≤ normalizer (Z R d : Set (FreeAmalgam R)) :=
    (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt)).trans
      (Z_normalized R d)
  have hne : Z R d ≠ ⊥ := by
    intro heq
    have hc := c.original_Z_card eK d back.start_color
    rw [heq,card_bot] at hc
    omega
  let := finite_stabilizer R t
  let : Finite (Q R t) := Finite.of_injective
    (inclusion (show Q R t ≤ stabilizer R t from fun _ hx => hx.1)) (inclusion_injective _)
  let N := (Z R d).subgroupOf (Q R t)
  let : N.Normal := normal_subgroupOf_of_le_normalizer hn
  let : Nontrivial (Z R d) := (nontrivial_iff_ne_bot _).mpr hne
  let : Nontrivial N := (subgroupOfEquivOfLe hZdT).toEquiv.nontrivial
  let : Fact (IsPGroup 2 (Q R t)) := ⟨hpT⟩
  obtain ⟨x,hxne,hxc⟩ := exists_nontrivial_center_mem_normal N (p := 2)
  have hxH : ((x : Q R t) : FreeAmalgam R) ∈ H := by
    refine ⟨x.property,?_⟩
    intro y hy
    exact congrArg Subtype.val ((mem_center_iff.mp hxc) ⟨y,hy⟩)
  rw [hHbot] at hxH
  exact hxne (Subtype.ext (Subtype.ext (mem_bot.mp hxH)))

/-- No original critical path has distance greater than four. -/
theorem false_of_original_large_distance
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (_path : CriticalPath R geometry a z),
      False := by
  intro R geometry hb a z path
  have hlarge : 4 < (Q R z).relIndex (Z R a) := by
    rw [(c.original_large_distance_unequal_sixteen eK geometry hb path).2.1]; decide
  obtain ⟨g,hg,hgen⟩ := c.original_large_distance_edge_sylow_generator eK geometry hb path
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hga : act R g⁻¹ a = a := hgS
  let d := act R g⁻¹ (path.walk.getVert 2)
  let t := act R g⁻¹ (path.walk.getVert 1)
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat₀ : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt₀ : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hat : Adjacent R a t := by
    simpa only [hga] using (adjacent_act_iff R g⁻¹ _ _).mpr hat₀
  have hdt : Adjacent R d t := (adjacent_act_iff R g⁻¹ _ _).mpr hdt₀
  have hgen' : Ltilde R a ≤ Q R t ⊔ Z R z := by
    change Ltilde R a ≤ Q R (act R g⁻¹ (path.walk.getVert 1)) ⊔ Z R z
    rw [Q_act,inv_inv]
    exact hgen
  have hmove : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R d) := by
    rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega)
      path.start_color g⁻¹ hgS]
    exact c.original_critical_strict_movement eK geometry hb path
  have hbad : ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
    intro hn
    have hJ := ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat hdt
    have hh := c.original_normal_neighbor_join_moving_index_eq_one eK geometry
      (by change 2 < geometry.b R; omega) path.start_color hat hdt
      (hgen'.trans (sup_le hJ hn))
    change (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R d) = 1 at hh
    omega
  have hnot : ¬ Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
    intro hkernel
    have hn := c.original_critical_kernel_endpoint_normalized_of_large eK geometry hb
      path hat hdt hlarge
    rw [inf_eq_left.mpr hkernel] at hn
    exact hbad hn
  obtain ⟨back,hbt,hover⟩ := ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
    geometry (by omega) path hat hdt hnot
  have hbacklarge : 4 < (Q R (path.walk.getVert (path.walk.length-2))).relIndex (Z R d) := by
    rw [(c.original_large_distance_unequal_sixteen eK geometry hb back).2.1]; decide
  exact false_of_large_sylow_generated_backward c eK geometry hb path back hat hdt hbt hgen' hbacklarge

/-- The distance is that of the original geometry, with no replacement
amalgam or additional positioning input. -/
theorem original_geometry_eq_four
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 4 := by
  intro R geometry
  apply Nat.le_antisymm _ (c.original_geometry_four_le eK geometry)
  by_contra! hb
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := R) (geometry := geometry) (a := alpha R) rfl
  exact c.false_of_original_large_distance eK geometry hb path

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
