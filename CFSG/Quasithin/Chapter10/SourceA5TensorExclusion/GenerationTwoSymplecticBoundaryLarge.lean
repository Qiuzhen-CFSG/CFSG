module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticBoundaryKernel

/-!
# All original critical images have order four

The large-image generators and their full-kernel lifts work at distance four.
With equal first movers, the generated neighboring seed lies in the full
penultimate kernel. The large-image displacement then makes its join with
the starting seed locally normal, contradicting strict movement.

A small critical path anywhere transports mover agreement to every original
vertex of the same color. If there is no small path, the full edge-Sylow
selector instead supplies a large backward path. Its nontrivial fixed
subgroup would lie in the original zero residual-fixed core. Thus every
critical image has order four, X equals Z at both endpoints, and all
neighboring movers agree, without replacing the original geometry.

These results remove the large-image alternative from the terminal original
distance-four argument. The remaining small-image contradiction and full
marked-plane recognition are not asserted here.
Source: MS93 (5.12)(2), printed pp.925--926, specialized to the center-free
natural geometry of Aschbacher--Smith 9.3.10, printed pp.734--735.
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

/-- The large endpoint and a conjugate of the common first mover generate
the original residual, also at distance four. -/
theorem original_boundary_large_equal_mover_generator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      4 < (Q R z).relIndex (Z R a) →
      ∃ g ∈ Ltilde R a,
        Ltilde R a ≤ ((LocalPackage.J R a (path.walk.getVert 1)).map
          (MulAut.conj g).toMonoidHom) ⊔ Z R z := by
  intro R geometry hb a z path heq hlarge
  have hlen : 2 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hd : color R (path.walk.getVert 2) = false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have hza : 4 < (Q R a).relIndex (Z R z) := by
    rcases c.original_critical_indices_four_or_sixteen eK geometry path with h | h
    · rw [h.1] at hlarge; omega
    · rw [h.2]; decide
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
  have hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hcore : x ∈ fixedCore R a := ⟨
      ((U_le_Z a).trans (geometry.omega_bound a path.start_color
        (by
          rw [geometry.distance_constant a path.start_color]
          change 0 < geometry.b R
          exact (by omega : 0 < geometry.b R))) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot a path.start_color] at hcore
  have ht : color R (path.walk.getVert 1) = true := by
    have h := adjacent_color_ne R hat
    rw [path.start_color] at h
    cases he : color R (path.walk.getVert 1) <;> simp_all
  obtain ⟨i,_,_,hiT,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le
    path.start_color hat
  have hQt : IsPGroup 2 (Q R (path.walk.getVert 1)) := hiT ▸ hodd.isPGroup.map i
  have hindices := c.original_small_mover_join_indices eK path.start_color hat
  have hzQd : Z R z ≤ Q R (path.walk.getVert 2) := by
    apply Z_le_Q_of_dist_lt R z (geometry.exists_critical z path.end_color)
    rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,path.dist_end,path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hzE : Z R z ≤ LocalPackage.J R a (path.walk.getVert 1) := by
    rw [←heq]
    exact hzQd.trans (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le hd hdt)
  exact original_small_mover_large_subactor_generator R hms hodd.isPGroup hne hodd.twoCore_le
    hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path (by omega) hza hfixed (LocalPackage.J R a (path.walk.getVert 1))
    ((LocalPackage.J_le_radical R a (path.walk.getVert 1)).trans
      (fun _ hx => hx.2 a (adjacent_symm R hat)))
    (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le path.start_color hat)
    (hQt.to_le (LocalPackage.J_le_radical R a (path.walk.getVert 1))) hindices.2.1 hindices.2.2.le hzE

/-- The large endpoint and an actual residual conjugate of the full edge
Sylow generate through the entire original kernel. -/
theorem original_boundary_large_sylow_generator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      4 < (Q R a).relIndex (Z R z) →
      ∃ g ∈ Ltilde R a,
        Ltilde R a ≤ (Q R (path.walk.getVert 1)).map
          (MulAut.conj g).toMonoidHom ⊔ Z R z := by
  intro R geometry hb a z path hza
  let t := path.walk.getVert 1
  have hat : Adjacent R a t := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
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

private theorem boundary_large_sylow_generated_backward_impossible
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
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


private theorem boundary_movers_eq_of_small_path
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {u v : Vertex R} (_path : CriticalPath R geometry u v),
      (Q R v).relIndex (Z R u) < 16 →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t := by
  intro R geometry u v path hs a d t ha hat hdt
  obtain ⟨g,hg⟩ : ∃ g : FreeAmalgam R, act R g u = a := by
    obtain ⟨x,rfl⟩ := exists_mVertex_of_color R path.start_color
    obtain ⟨y,rfl⟩ := exists_mVertex_of_color R ha
    exact ⟨x⁻¹*y,by simp only [act_mVertex,mul_inv_cancel_left]⟩
  have hga : act R g⁻¹ a = u := by
    rw [←hg,←act_mul,mul_inv_cancel,act_one]
  have hat' : Adjacent R u (act R g⁻¹ t) := by
    simpa only [hga] using (adjacent_act_iff R g⁻¹ _ _).mpr hat
  have hdt' := (adjacent_act_iff R g⁻¹ _ _).mpr hdt
  have he := c.original_small_critical_neighbor_movers_eq eK geometry path hat' hdt' hs
  rw [←hga,smallMoverJoin_act,smallMoverJoin_act] at he
  exact Subgroup.map_injective (MulAut.conj (g⁻¹)⁻¹).injective he

/-- A large critical image is impossible when its two first movers agree,
including at distance four. The generated seed lies in the full kernel,
so the large-image displacement makes its neighbor join locally normal. -/
theorem original_boundary_large_equal_movers_impossible
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      4 < (Q R z).relIndex (Z R a) → False := by
  intro R geometry a z path heq hlarge
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  have hlen : 2 < path.walk.length := by rwa [path.length_eq_b]
  have h16 : 16 ≤ (Q R z).relIndex (Z R a) := by
    rcases c.original_critical_indices_four_or_sixteen eK geometry path with h | h
    · have hh : (Q R z).relIndex (Z R a) = 4 := h.1
      omega
    · exact h.1.ge
  obtain ⟨g,hg,hgen⟩ := c.original_boundary_large_equal_mover_generator eK geometry hb path heq hlarge
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hga : act R g⁻¹ a = a := hgS
  let d := act R g⁻¹ (path.walk.getVert 2)
  let t := act R g⁻¹ (path.walk.getVert 1)
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
  have hgen' : Ltilde R a ≤ LocalPackage.J R d t ⊔ Z R z := by
    change Ltilde R a ≤ LocalPackage.J R (act R g⁻¹ (path.walk.getVert 2))
      (act R g⁻¹ (path.walk.getVert 1)) ⊔ Z R z
    rw [smallMoverJoin_act,inv_inv,heq]
    exact hgen
  have hmove : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R d) := by
    rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega)
      path.start_color g⁻¹ hgS]
    exact c.original_boundary_critical_strict_movement eK geometry hb path
  have hkernel := c.original_generated_neighbor_seed_le_penultimate_kernel
    eK geometry path hat hdt hgen'
  have hZdY : Z R d ≤ V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) :=
    le_inf (le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)) hkernel
  have hZd : ⁅Z R d,Z R z⁆ ≤ Z R a := (commutator_mono hZdY le_rfl).trans
    (c.original_radius_displacement_of_large_critical_index eK geometry path h16)
  have hZa : ⁅Z R a,Z R z⁆ ≤ Z R a :=
    ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path
  have hZn : Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
    apply le_normalizer_iff_commutator_le_left.mpr
    exact commutator_sup_le_of_relative_normal (Z R d ⊔ Z R a)
      (Z R d) (Z R a) (Z R z) (Z R d ⊔ Z R a)
      le_normalizer le_sup_left le_sup_right
      (hZd.trans le_sup_right) (hZa.trans le_sup_right)
  have hJn := (LocalPackage.J_le_radical R d t).trans
    (ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat hdt)
  have hone := c.original_normal_neighbor_join_moving_index_eq_one eK geometry hb
    path.start_color hat hdt (hgen'.trans (sup_le hJn hZn))
  change (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
    (geometry.Z_normal a)).relIndex (U R d) = 1 at hone
  omega

/-- No original critical image has order sixteen, including at distance four.
A small path anywhere transports mover agreement to the large path. If no
small path exists, the actual Sylow-generated backward path is large and
its nontrivial fixed subgroup contradicts the full residual-fixed core. -/
theorem original_boundary_large_critical_impossible
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (_path : CriticalPath R geometry a z),
      4 < (Q R z).relIndex (Z R a) → False := by
  intro R geometry a z path hlarge
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  have hlen : 2 < path.walk.length := by rwa [path.length_eq_b]
  have hat₀ : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt₀ : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  by_cases hs : ∃ u v : Vertex R, ∃ _p : CriticalPath R geometry u v,
      (Q R v).relIndex (Z R u) < 16
  · obtain ⟨u,v,p,hp⟩ := hs
    exact c.original_boundary_large_equal_movers_impossible eK geometry path
      (c.boundary_movers_eq_of_small_path eK geometry p hp path.start_color hat₀ hdt₀) hlarge
  have h16 : 16 ≤ (Q R z).relIndex (Z R a) := by
    by_contra! h
    exact hs ⟨a,z,path,h⟩
  have hza : 4 < (Q R a).relIndex (Z R z) := by
    have rev := c.original_critical_reverse eK geometry (by change 0 < geometry.b R; omega) path
    by_contra! h
    exact hs ⟨z,a,rev,lt_of_le_of_lt h (by decide : 4 < 16)⟩
  obtain ⟨g,hg,hgen⟩ := c.original_boundary_large_sylow_generator eK geometry hb path hza
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hga : act R g⁻¹ a = a := hgS
  let d := act R g⁻¹ (path.walk.getVert 2)
  let t := act R g⁻¹ (path.walk.getVert 1)
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
    exact c.original_boundary_critical_strict_movement eK geometry hb path
  have hnot : ¬ Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
    intro hkernel
    have hZdY : Z R d ≤ V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) :=
      le_inf (le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)) hkernel
    have hZd : ⁅Z R d,Z R z⁆ ≤ Z R a := (commutator_mono hZdY le_rfl).trans
      (c.original_radius_displacement_of_large_critical_index eK geometry path h16)
    have hZa : ⁅Z R a,Z R z⁆ ≤ Z R a :=
      ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path
    have hZn : Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
      apply le_normalizer_iff_commutator_le_left.mpr
      exact commutator_sup_le_of_relative_normal (Z R d ⊔ Z R a)
        (Z R d) (Z R a) (Z R z) (Z R d ⊔ Z R a)
        le_normalizer le_sup_left le_sup_right
        (hZd.trans le_sup_right) (hZa.trans le_sup_right)
    have hone := c.original_normal_neighbor_join_moving_index_eq_one eK geometry hb
      path.start_color hat hdt (hgen'.trans (sup_le
        (ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat hdt) hZn))
    change (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R d) = 1 at hone
    omega
  obtain ⟨back,hbt,_⟩ := ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
    geometry hb.le path hat hdt hnot
  have hbacklarge : 4 < (Q R (path.walk.getVert (path.walk.length-2))).relIndex (Z R d) := by
    by_contra! h
    exact hs ⟨d,_,back,lt_of_le_of_lt h (by decide : 4 < 16)⟩
  exact c.boundary_large_sylow_generated_backward_impossible eK geometry hb
    path back hat hdt hbt hgen' hbacklarge

/-- Both literal critical images have order four; the complete central
omega layers at both endpoints are the original natural seeds. -/
theorem original_critical_images_four
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (_path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) = 4 ∧ (Q R a).relIndex (Z R z) = 4 ∧
        X R a = Z R a ∧ X R z = Z R z := by
  intro R geometry a z path
  have hsmall : (Q R z).relIndex (Z R a) < 16 := by
    by_contra! h
    exact c.original_boundary_large_critical_impossible eK geometry path
      (lt_of_lt_of_le (by decide : 4 < 16) h)
  obtain ⟨ha4,hz4,hX⟩ := c.original_small_critical_data eK geometry path hsmall
  exact ⟨ha4,hz4,hX,c.original_X_eq_Z_at_of_eq path.start_color path.end_color hX⟩

/-- Every pair of original neighboring movers agrees, with no small-image
premise left for the terminal distance-four argument. -/
theorem original_neighbor_movers_eq
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (_geometry : Geometry R) {a d t : Vertex R}, color R a = false →
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t := by
  intro R geometry a d t ha hat hdt
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := R) (geometry := geometry) (a := a) ha
  apply c.original_small_critical_neighbor_movers_eq eK geometry path hat hdt
  rw [(c.original_critical_images_four eK geometry path).1]
  decide

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
