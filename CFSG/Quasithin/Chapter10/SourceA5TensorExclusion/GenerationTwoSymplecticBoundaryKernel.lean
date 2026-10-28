module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticBoundaryMovement

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalBoundedKernelDisplacement

/-!
# The selected original critical kernels at distance four

For an equal-mover neighboring seed, the critical-hyperplane displacement
lies in the starting seed and is fixed by the common mover. The bounded
hyperplane comparison forces any escaping endpoint displacement to be the
critical root. The actual three residual generators forbid that root from
being fixed by the mover. Thus both complete selected kernels have endpoint
displacement in the starting seed.

Every small original critical path now supplies the actual separated
conjugators, strict movement and those two kernel displacements at b = 4.
If both selected seeds lay in the penultimate kernel, the same three
residual generators would normalize the neighboring join and force moving
index one. Hence one member supplies a backward critical path with its
literal common edge and every overlap vertex retained.

The terminal original distance-four exclusion and marked plane recognition
remain unproved. This is the original-kernel input to that final argument.

Source: MS93 (3.3)(ii), (5.6)--(5.7), (5.12)(1), printed pp.866--867,
917--919,924--925; Aschbacher--Smith 9.3.10, pp.734--735.
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

private theorem boundary_truncated_section_root_of_escape
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z)
        (Y : Subgroup (FreeAmalgam R)),
      Z R a ≤ Y → Y ≤ V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) →
      ⁅Y,Z R z ⊓ Q R a⁆ ≤ Z R a → ¬ ⁅Y,Z R z⁆ ≤ Z R a →
      ⁅Y,Z R z ⊓ Q R a⁆ = ⁅Z R a,Z R z⁆ := by
  intro R geometry hb a z path Y hZa hY hbound hbad
  have hn : ¬ ⁅V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)),Z R z⁆ ≤ Z R a :=
    fun h => hbad ((commutator_mono hY le_rfl).trans h)
  obtain h | ⟨ha4,hz4,_,_⟩ := c.original_radius_displacement_or_root eK geometry path
  · exact (hn h).elim
  obtain ⟨F,hF,f,hf,hr,π,hπ⟩ := c.original_truncated_radius_root_action eK geometry path ha4 hz4
  let fY := f.comp (inclusion hY)
  have hfY : fY.ker = (Q R z).subgroupOf Y := by
    ext y
    change f (inclusion hY y) = 1 ↔ y.val ∈ Q R z
    change inclusion hY y ∈ f.ker ↔ _
    rw [hf]
    rfl
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hCa : C R a = Q R a := C_eq_Q R hodd.isPGroup hodd.twoCore_le hfaith a path.start_color
  exact (critical_root_kernel_commutator_of_seed_bound path (by omega) hCa
    (c.original_Z_eq_U z path.end_color) Y
    (hY.trans (inf_le_left.trans (geometry.V_le_Q (by omega) a path.start_color))) hZa
    (hY.trans (truncated_radius_le_endpoint_stabilizer path (by omega)))
    fY hfY (fun y hy => hr (inclusion hY y) hy)
    π (fun y u => hπ (inclusion hY y) u) hbound hbad).1

/-- The selected three generators force endpoint displacement of the
complete backward kernel into the original starting seed. -/
theorem original_boundary_generated_kernel_displacement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      ∀ x ∈ Ltilde R a,
      Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) →
      ⁅(Z R d ⊓ Q R (path.walk.getVert (path.walk.length-2))) ⊔ Z R a,Z R z⁆ ≤ Z R a := by
  intro R geometry hb a z d t path hat hdt heq x hx hgen
  let w := path.walk.getVert (path.walk.length-2)
  let K := Z R d ⊓ Q R w
  let Y := K ⊔ Z R a
  let A := Z R z ⊓ Q R a
  by_contra hn
  change ¬ ⁅Y,Z R z⁆ ≤ Z R a at hn
  have hZaQ : Z R a ≤ Q R w := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a path.start_color)
    rw [geometry.distance_constant a path.start_color,path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hYV : Y ≤ V R a := (sup_le_sup inf_le_left le_rfl).trans
    (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)
  have hY : Y ≤ V R a ⊓ Q R w := le_inf hYV (sup_le inf_le_right hZaQ)
  have hbad : ¬ ⁅V R a ⊓ Q R w,Z R z⁆ ≤ Z R a :=
    fun h => hn ((commutator_mono hY le_rfl).trans h)
  obtain h | ⟨ha4,hz4,hX,_⟩ := c.original_radius_displacement_or_root eK geometry path
  · exact hbad h
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [path.start_color] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hAJ : A ≤ LocalPackage.J R d t := inf_le_right.trans
    (heq ▸ LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le path.start_color hat)
  let P := Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))
  have hKP : ⁅K,A⁆ ≤ P := le_inf
    ((commutator_mono inf_le_left inf_le_right).trans
      ((c.original_equal_mover_displacement_le_X eK geometry (by change 2 < geometry.b R; omega)
        path.start_color hat hdt heq).trans_eq hX))
    (by
      rw [commutator_comm]
      exact (commutator_mono hAJ inf_le_left).trans
        (c.original_edge_mover_quadratic eK hd hdt))
  have hZaA : ⁅Z R a,A⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono le_rfl inf_le_right).trans (geometry.centralizes a path.start_color).le)
  have hVP : V R a ≤ normalizer (P : Set (FreeAmalgam R)) :=
    (((geometry.V_le_Q hb a path.start_color).trans
      (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes a path.start_color)))).trans
      (centralizer_le inf_le_left)).trans (Subgroup.centralizer_le_normalizer _)
  have hYP : ⁅Y,A⁆ ≤ P := commutator_sup_le_of_relative_normal (V R a) K (Z R a) A P
    hVP (le_sup_left.trans hYV) (Z_le_VBall R a 2) hKP (hZaA ▸ bot_le)
  have hroot := c.boundary_truncated_section_root_of_escape eK geometry hb path Y
    le_sup_right hY (hYP.trans inf_le_left) hn
  have hfix : ⁅Z R a,Z R z⁆ ≤ centralizer (LocalPackage.J R a t : Set (FreeAmalgam R)) := by
    rw [←heq,←hroot]
    exact hYP.trans inf_le_right
  exact c.original_generated_critical_root_not_fixed eK geometry path hat hz4 ha4 x hx
    (heq ▸ hgen) hfix

private theorem original_conjugate_three_generators
    {R : Subgroup c.M} {a z d t : Vertex R} {x : FreeAmalgam R}
    (hx : x ∈ Ltilde R a)
    (hgen : Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z)) :
    Ltilde R a ≤ (LocalPackage.J R (act R x d) (act R x t) ⊔ Z R z) ⊔
      Z R (act R x z) := by
  have h := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hgen
  have hL : (Ltilde R a).map (MulAut.conj x⁻¹).toMonoidHom = Ltilde R a :=
    mem_normalizer_iff_map_conj_eq.mp
    ((Ltilde R a).le_normalizer ((Ltilde R a).inv_mem hx))
  rw [hL,Subgroup.map_sup,Subgroup.map_sup,←smallMoverJoin_act,←Z_act,←Z_act,
    ←act_mul,inv_mul_cancel,act_one] at h
  simpa only [sup_assoc,sup_comm,sup_left_comm] using h

/-- Both kernels of the same generated pair have endpoint displacement
in the starting seed, including the order-four-image branch. -/
theorem original_boundary_generated_pair_displacement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      ∀ x ∈ Ltilde R a,
      Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) →
      let w := path.walk.getVert (path.walk.length-2)
      ⁅(Z R d ⊓ Q R w) ⊔ Z R a,Z R z⁆ ≤ Z R a ∧
      ⁅(Z R (act R x d) ⊓ Q R w) ⊔ Z R a,Z R z⁆ ≤ Z R a := by
  intro R geometry hb a z d t path hat hdt heq x hx hgen w
  refine ⟨c.original_boundary_generated_kernel_displacement eK geometry hb path hat hdt heq x hx hgen,?_⟩
  have hxS : x ∈ stabilizer R a := Ltilde_le_stabilizer a hx
  have hfix : act R x a = a := hxS
  have hat₂ : Adjacent R a (act R x t) := by
    rw [←hfix]
    exact (adjacent_act_iff R x _ _).mpr hat
  have hdt₂ := (adjacent_act_iff R x _ _).mpr hdt
  have heq₂ : LocalPackage.J R (act R x d) (act R x t) = LocalPackage.J R a (act R x t) := by
    rw [←hfix,smallMoverJoin_act,smallMoverJoin_act,heq]
  apply c.original_boundary_generated_kernel_displacement eK geometry hb path hat₂ hdt₂ heq₂
    x⁻¹ ((Ltilde R a).inv_mem hx)
  rw [inv_inv]
  exact c.original_conjugate_three_generators hx hgen

/-- A small original critical image gives the actual separated residual
choice at distance four, with strict movement, an overlapping backward path
and displacement of both full penultimate kernels into the starting seed. -/
theorem original_boundary_small_critical_kernel_selection
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) < 16 →
      ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
        let d := act R g⁻¹ (path.walk.getVert 2)
        let t := act R g⁻¹ (path.walk.getVert 1)
        let w := path.walk.getVert (path.walk.length-2)
        Adjacent R a t ∧ Adjacent R d t ∧
        LocalPackage.J R d t = LocalPackage.J R a t ∧
        Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) ∧
        ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
          centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ ∧
        4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) ∧
        ((∃ back : CriticalPath R geometry d w,
          back.walk.getVert 1=t ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∨
        (∃ back : CriticalPath R geometry (act R x d) w,
          back.walk.getVert 1=act R x t ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i)) ∧
        ⁅(Z R d ⊓ Q R w) ⊔ Z R a,Z R z⁆ ≤ Z R a ∧
        ⁅(Z R (act R x d) ⊓ Q R w) ⊔ Z R a,Z R z⁆ ≤ Z R a := by
  intro R geometry a z path hsmall
  have hb : 2 < geometry.b R := lt_of_lt_of_le (by decide : 2 < 4)
    (c.original_geometry_four_le eK geometry)
  have hlen : 2 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have heq := c.original_small_critical_neighbor_movers_eq eK geometry path hat hdt hsmall
  change LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
    LocalPackage.J R a (path.walk.getVert 1) at heq
  obtain ⟨haz,hza,_⟩ := c.original_small_critical_data eK geometry path hsmall
  obtain ⟨g,hg,x,hx,hgen,hsep⟩ := c.original_root_small_mover_separated_generators
    eK geometry path hat hza haz
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hfix : act R g⁻¹ a = a := hgS
  let d := act R g⁻¹ (path.walk.getVert 2)
  let t := act R g⁻¹ (path.walk.getVert 1)
  have hat' : Adjacent R a t := by
    simpa only [hfix] using (adjacent_act_iff R g⁻¹ _ _).mpr hat
  have hdt' : Adjacent R d t := (adjacent_act_iff R g⁻¹ _ _).mpr hdt
  have heq' := c.original_small_critical_neighbor_movers_eq eK geometry path hat' hdt' hsmall
  have hgen' : Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) := by
    dsimp only [d,t]
    rw [smallMoverJoin_act,Z_act,inv_inv,inv_inv,heq]
    exact hgen
  have hsep' : ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
      centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ := by
    simpa only [d,t,smallMoverJoin_act,inv_inv,heq] using hsep
  have hmove : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R d) := by
    rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega)
      path.start_color g⁻¹ hgS]
    exact c.original_boundary_critical_strict_movement eK geometry hb path
  have hdisp := c.original_boundary_generated_pair_displacement eK geometry hb path hat' hdt' heq' x hx hgen'
  have hnot : ¬ Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) ∨
      ¬ Z R (act R x d) ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
    by_contra! hk
    have hd₁ := hdisp.1
    have hd₂ := hdisp.2
    rw [inf_eq_left.mpr hk.1] at hd₁
    rw [inf_eq_left.mpr hk.2] at hd₂
    have hxS := Ltilde_le_stabilizer a hx
    have hZaMap : (Z R a).map (MulAut.conj x).toMonoidHom = Z R a :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized R a hxS)
    have hdMap : (Z R (act R x d)).map (MulAut.conj x).toMonoidHom = Z R d := by
      have hh := Z_act R x⁻¹ (act R x d)
      rw [←act_mul,mul_inv_cancel,act_one] at hh
      simpa only [inv_inv] using hh.symm
    have heMap : (Z R z).map (MulAut.conj x).toMonoidHom = Z R (act R x⁻¹ z) := by
      simpa only [inv_inv] using (Z_act R x⁻¹ z).symm
    have hthird := map_mono (f := (MulAut.conj x).toMonoidHom) hd₂
    rw [map_commutator,Subgroup.map_sup,hZaMap,hdMap,heMap] at hthird
    have hn : Ltilde R a ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) :=
      hgen'.trans (sup_le (sup_le
        ((LocalPackage.J_le_radical R d t).trans
          (ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat' hdt'))
        (le_normalizer_iff_commutator_le_left.mpr (hd₁.trans le_sup_right)))
        (le_normalizer_iff_commutator_le_left.mpr (hthird.trans le_sup_right)))
    have hone := c.original_normal_neighbor_join_moving_index_eq_one eK geometry hb
      path.start_color hat' hdt' hn
    change (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R d) = 1 at hone
    omega
  have hback : (∃ back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2)),
      back.walk.getVert 1=t ∧
      ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∨
      (∃ back : CriticalPath R geometry (act R x d) (path.walk.getVert (path.walk.length-2)),
      back.walk.getVert 1=act R x t ∧
      ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) := by
    rcases hnot with hd | hd
    · exact Or.inl (ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
        geometry hb.le path hat' hdt' hd)
    · have hxa : act R x a = a := Ltilde_le_stabilizer a hx
      have hatx : Adjacent R a (act R x t) := by
        simpa only [hxa] using (adjacent_act_iff R x _ _).mpr hat'
      exact Or.inr (ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
        geometry hb.le path hatx ((adjacent_act_iff R x _ _).mpr hdt') hd)
  exact ⟨g,hg,x,hx,hat',hdt',heq',hgen',hsep',hmove,hback,hdisp⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
