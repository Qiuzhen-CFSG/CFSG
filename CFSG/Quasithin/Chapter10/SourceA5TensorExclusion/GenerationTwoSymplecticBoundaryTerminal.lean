module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticBoundaryLarge

/-!
# The terminal original distance-four contradiction

Retain the positioned source selector: it normalizes the full forward
mover, which contains the actual critical endpoint. Hence the selected
mover and the forward mover generate the original residual. Strict
B-movement identifies both seed intersections with their mover-fixed
planes. At distance four the penultimate seed is the forward second seed,
so any selected backward critical commutator lies in both planes. It
centralizes the residual and lies in its full original fixed core, which
is trivial; criticality forbids this.

If neither selected seed gives a backward path, both lie in the full
penultimate kernel. The proved endpoint displacement and the same three
residual generators then normalize their neighboring seed join, forcing
B-index one instead of the strict lower bound. This closes the original
small-image branch. No order-sixteen joint image is substituted for an
individual critical seed, and no new positioning premise is introduced.

Source: MS93 (5.6), (5.12)(1)--(3), printed pp.917--918,924--927,
specialized to the original zero fixed core of Aschbacher--Smith 9.3.10,
printed pp.734--735. GenerationTwoSymplecticComplete constructs the whole
block and original marked plane model and applies both tensor consumers.
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

private theorem boundary_positioned_backward_impossible
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), geometry.b R = 4 →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (_back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      (Q R z).relIndex (Z R a) < 16 →
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      Ltilde R a ≤ LocalPackage.J R d t ⊔ LocalPackage.J R a (path.walk.getVert 1) →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      False := by
  intro R geometry hb a z d t path back hat hdt heq hsmall heq0 hgen hmove
  let H := ⁅Z R d,Z R (path.walk.getVert (path.walk.length-2))⁆
  have hXa := (c.original_small_critical_data eK geometry path hsmall).2.2
  have hwQ : Z R (path.walk.getVert (path.walk.length-2)) ≤ Q R a := by
    apply Z_le_Q_of_dist_lt R _ (geometry.exists_critical _ back.end_color)
    rw [geometry.distance_constant _ back.end_color,SimpleGraph.dist_comm,
      path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hHZ : H ≤ Z R a := (commutator_mono le_rfl hwQ).trans
    (c.original_equal_mover_displacement_le_Z eK geometry (by change 2 < geometry.b R; omega)
      path.start_color hat hdt heq)
  have hle : H ≤ Z R (path.walk.getVert 2) := by
    have h := ChapterC.Sp4Four.DistanceReduction.LargeDistance.critical_commutator_le_endpoint
      (R := R) (geometry := geometry) ⟨d,_,back⟩
    simpa only [H,path.length_eq_b,hb,Nat.reduceSub] using h
  have hfix := c.original_equal_mover_seed_intersection_fixed_plane eK geometry
    (by change 2 < geometry.b R; omega) path.start_color hat hdt heq hXa hmove
  have hHE : H ≤ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R)) := by
    rw [heq]
    exact ((le_inf hHZ (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed back)).trans_eq hfix).trans inf_le_right
  have hlen : path.walk.length = 4 := path.length_eq_b.trans hb
  have hat0 : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt0 : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hfix0 := c.original_equal_mover_seed_intersection_fixed_plane eK geometry
    (by change 2 < geometry.b R; omega) path.start_color hat0 hdt0 heq0 hXa
    (c.original_boundary_critical_strict_movement eK geometry (by change 2 < geometry.b R; omega) path)
  have hHE0 : H ≤ centralizer (LocalPackage.J R a (path.walk.getVert 1) : Set (FreeAmalgam R)) :=
    ((le_inf hHZ hle).trans_eq hfix0).trans inf_le_right
  have hHL : H ≤ centralizer (Ltilde R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (hgen.trans
      (sup_le (le_centralizer_iff.mp hHE) (le_centralizer_iff.mp hHE0)))
  have hzero : H ≤ fixedCore R a := le_inf
    (hHZ.trans ((geometry.omega_bound a path.start_color
      (by rw [geometry.distance_constant a path.start_color]; change 0 < geometry.b R; omega)).trans (omegaCenter_le _))) hHL
  rw [c.original_fixedCore_eq_bot a path.start_color] at hzero
  exact c.original_critical_commutator_not_le_vertex_center eK geometry back path.start_color
    (hzero.trans bot_le)

/-- The original distance-four configuration is impossible. -/
theorem false_of_original_boundary_distance
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z : Vertex R} (_path : CriticalPath R geometry a z), False := by
  intro R geometry a z path
  have hb : geometry.b R = 4 := c.original_geometry_eq_four eK geometry
  have hb2 : 2 < geometry.b R := by omega
  have hsmall : (Q R z).relIndex (Z R a) < 16 := by
    rw [(c.original_critical_images_four eK geometry path).1]; decide
  obtain ⟨ha4,hz4,_⟩ := c.original_small_critical_data eK geometry path hsmall
  let d := path.walk.getVert 2
  let t := path.walk.getVert 1
  have hlen : path.walk.length = 4 := path.length_eq_b.trans hb
  have hat : Adjacent R a t := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R d t := adjacent_symm R ((cosetGraph_adj R _ _).mp
    (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have heq0 := c.original_neighbor_movers_eq eK geometry path.start_color hat hdt
  have hd : color R d = false := (path.vertex_color (by omega)).mpr (by decide)
  have hzQd : Z R z ≤ Q R d := by
    apply Z_le_Q_of_dist_lt R z (geometry.exists_critical z path.end_color)
    rw [geometry.distance_constant z path.end_color,SimpleGraph.dist_comm,path.dist_end,path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hzE : Z R z ≤ LocalPackage.J R a t := by
    rw [←heq0]
    exact hzQd.trans (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le hd hdt)
  obtain ⟨g,hg,x,hx,hgen,_,hpos⟩ :=
    c.original_root_small_mover_positioned_generators eK geometry path hat hz4 ha4
  have hxN := hpos hzE
  have hxS := Ltilde_le_stabilizer a hx
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hga : act R g⁻¹ a = a := hgS
  have hxa : act R x a = a := hxS
  let d₁ := act R g⁻¹ d
  let t₁ := act R g⁻¹ t
  have hat₁ : Adjacent R a t₁ := by
    simpa only [hga] using (adjacent_act_iff R g⁻¹ _ _).mpr hat
  have hdt₁ := (adjacent_act_iff R g⁻¹ _ _).mpr hdt
  have heq₁ : LocalPackage.J R d₁ t₁ = LocalPackage.J R a t₁ := by
    change LocalPackage.J R (act R g⁻¹ d) (act R g⁻¹ t) = _
    rw [smallMoverJoin_act,heq0,←smallMoverJoin_act,hga]
  have hE₁ : LocalPackage.J R d₁ t₁ =
      (LocalPackage.J R a t).map (MulAut.conj g).toMonoidHom := by
    rw [smallMoverJoin_act,inv_inv,heq0]
  have hgen' : Ltilde R a ≤ (LocalPackage.J R d₁ t₁ ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) := by
    rw [hE₁,Z_act,inv_inv]
    exact hgen
  have hmove : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d₁) := by
    rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega) path.start_color g⁻¹ hgS]
    exact c.original_boundary_critical_strict_movement eK geometry hb2 path
  have hAx : (Z R z).map (MulAut.conj x).toMonoidHom ≤ LocalPackage.J R a t :=
    (map_mono hzE).trans_eq (mem_normalizer_iff_map_conj_eq.mp hxN)
  have htwo : Ltilde R a ≤ LocalPackage.J R d₁ t₁ ⊔ LocalPackage.J R a t := by
    rw [hE₁]
    exact hgen.trans (sup_le (sup_le le_sup_left (hzE.trans le_sup_right)) (hAx.trans le_sup_right))
  have htwoX : Ltilde R a ≤ LocalPackage.J R (act R x d₁) (act R x t₁) ⊔ LocalPackage.J R a t := by
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) htwo
    have hLa : (Ltilde R a).map (MulAut.conj x⁻¹).toMonoidHom = Ltilde R a :=
      mem_normalizer_iff_map_conj_eq.mp
        ((Ltilde R a).le_normalizer ((Ltilde R a).inv_mem hx))
    have hE0 : (LocalPackage.J R a t).map (MulAut.conj x⁻¹).toMonoidHom =
        LocalPackage.J R a t := mem_normalizer_iff_map_conj_eq.mp
          ((normalizer (LocalPackage.J R a t : Set (FreeAmalgam R))).inv_mem hxN)
    rw [hLa,Subgroup.map_sup,hE0,←smallMoverJoin_act] at hh
    exact hh
  have hdisp := c.original_boundary_generated_pair_displacement eK geometry hb2 path hat₁ hdt₁ heq₁ x hx hgen'
  have hnot : ¬ Z R d₁ ≤ Q R (path.walk.getVert (path.walk.length-2)) ∨
      ¬ Z R (act R x d₁) ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
    by_contra! hk
    have hd₁ := hdisp.1
    have hd₂ := hdisp.2
    rw [inf_eq_left.mpr hk.1] at hd₁
    rw [inf_eq_left.mpr hk.2] at hd₂
    have hxS := Ltilde_le_stabilizer a hx
    have hZaMap : (Z R a).map (MulAut.conj x).toMonoidHom = Z R a :=
      mem_normalizer_iff_map_conj_eq.mp (Z_normalized R a hxS)
    have hdMap : (Z R (act R x d₁)).map (MulAut.conj x).toMonoidHom = Z R d₁ := by
      have hh := Z_act R x⁻¹ (act R x d₁)
      rw [←act_mul,mul_inv_cancel,act_one] at hh
      simpa only [inv_inv] using hh.symm
    have heMap : (Z R z).map (MulAut.conj x).toMonoidHom = Z R (act R x⁻¹ z) := by
      simpa only [inv_inv] using (Z_act R x⁻¹ z).symm
    have hthird := map_mono (f := (MulAut.conj x).toMonoidHom) hd₂
    rw [map_commutator,Subgroup.map_sup,hZaMap,hdMap,heMap] at hthird
    have hn : Ltilde R a ≤ normalizer ((Z R d₁ ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) :=
      hgen'.trans (sup_le (sup_le
        ((LocalPackage.J_le_radical R d₁ t₁).trans
          (ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat₁ hdt₁))
        (le_normalizer_iff_commutator_le_left.mpr (hd₁.trans le_sup_right)))
        (le_normalizer_iff_commutator_le_left.mpr (hthird.trans le_sup_right)))
    have hone := c.original_normal_neighbor_join_moving_index_eq_one eK geometry hb2
      path.start_color hat₁ hdt₁ hn
    change (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R d₁) = 1 at hone
    omega
  rcases hnot with hn | hn
  · obtain ⟨back,_,_⟩ := ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
      geometry hb2.le path hat₁ hdt₁ hn
    exact c.boundary_positioned_backward_impossible eK geometry hb path back
      hat₁ hdt₁ heq₁ hsmall heq0 htwo hmove
  · have hatX : Adjacent R a (act R x t₁) := by
      simpa only [hxa] using (adjacent_act_iff R x _ _).mpr hat₁
    have hdtX := (adjacent_act_iff R x _ _).mpr hdt₁
    have heqX := c.original_neighbor_movers_eq eK geometry path.start_color hatX hdtX
    have hmoveX : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
        (geometry.Z_normal a)).relIndex (U R (act R x d₁)) := by
      rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega)
        path.start_color x hxS]
      exact hmove
    obtain ⟨back,_,_⟩ := ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
      geometry hb2.le path hatX hdtX hn
    exact c.boundary_positioned_backward_impossible eK geometry hb path back
      hatX hdtX heqX hsmall heq0 htwoX hmoveX

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
