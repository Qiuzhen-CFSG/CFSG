module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticIntermediateSeeds

/-!
# Positioned original generators and large backward critical images

The literal critical endpoint lies in the forward edge mover in the
small-image equal-mover branch. The marked selector therefore normalizes
that whole mover, with the entire original action kernel retained. The
selected mover and the forward mover generate the residual. Their common
fixed seed is zero, so the selected backward critical root escapes the
original forward seed.

This eliminates the second radius-index alternative and places a small
critical root in the fourth seed on two equal-mover edges. Applying that
conclusion to the selected backward path excludes a small backward image.
The unequal-mover branch already has the same exclusion. Thus every small
original critical path at distance greater than four admits an actual
overlapping backward path with critical image at least sixteen and the
full truncated-radius displacement, without equal-mover, positioning or
strict-movement hypotheses in the final export.

The large-image configurations, the complete large-distance and distance-four
exclusions, and SymplecticPlaneRecognition remain open.

Source: MS93 (5.6)(b--d), (5.7), (5.10)--(5.11), printed pp.917--924;
Aschbacher--Smith 9.3.10 and the final paragraph of 9.3, printed pp.734--735.
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

/-- Simultaneous original residual generation, separation and full-mover
normalization, using the original natural marking. -/
theorem original_root_small_mover_positioned_generators
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → (Q R a).relIndex (Z R z) = 4 → (Q R z).relIndex (Z R a) = 4 →
      ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
        Ltilde R a ≤ ((LocalPackage.J R a t).map (MulAut.conj g).toMonoidHom ⊔ Z R z) ⊔
          (Z R z).map (MulAut.conj x).toMonoidHom ∧
        ((Z R a ⊓ centralizer ((LocalPackage.J R a t).map
          (MulAut.conj g).toMonoidHom : Set (FreeAmalgam R))) ⊓
          centralizer (((LocalPackage.J R a t).map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam R))) = ⊥ ∧
        (Z R z ≤ LocalPackage.J R a t →
          x ∈ normalizer (LocalPackage.J R a t : Set (FreeAmalgam R))) := by
  intro R geometry a z t path hat hza haz
  have hb : 0 < geometry.b R := lt_of_lt_of_le (by decide : 0 < 4)
    (c.original_geometry_four_le eK geometry)
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
          exact hb)) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot a path.start_color] at hcore
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [path.start_color] at h
    cases he : color R t <;> simp_all
  obtain ⟨i,_,_,hiT,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le
    path.start_color hat
  have hQt : IsPGroup 2 (Q R t) := hiT ▸ hodd.isPGroup.map i
  have hindices := c.original_small_mover_join_indices eK path.start_color hat
  rw [c.original_Z_eq_U a path.start_color]
  exact original_small_mover_root_positioned_generators R hms hodd.isPGroup hne hodd.twoCore_le
    hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path hb hza haz hfixed (LocalPackage.J R a t)
    ((LocalPackage.J_le_radical R a t).trans (fun _ hx => hx.2 a (adjacent_symm R hat)))
    (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le path.start_color hat)
    (hQt.to_le (LocalPackage.J_le_radical R a t)) hindices.2.1 hindices.2.2.le


private theorem positioned_backward_root_escapes_forward
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (_back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      (Q R z).relIndex (Z R a) < 16 →
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      Ltilde R a ≤ LocalPackage.J R d t ⊔ LocalPackage.J R a (path.walk.getVert 1) →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      ¬ ⁅Z R d,Z R (path.walk.getVert (path.walk.length-2))⁆ ≤ Z R (path.walk.getVert 2) := by
  intro R geometry hb a z d t path back hat hdt heq hsmall heq0 hgen hmove hle
  let H := ⁅Z R d,Z R (path.walk.getVert (path.walk.length-2))⁆
  have hXa := (c.original_small_critical_data eK geometry path hsmall).2.2
  have hHZ : H ≤ Z R a := c.original_equal_mover_backward_root_le_intermediate_seed
    eK geometry hb path back hat hdt heq hXa
  have hfix := c.original_equal_mover_seed_intersection_fixed_plane eK geometry
    (by change 2 < geometry.b R; omega) path.start_color hat hdt heq hXa hmove
  have hHE : H ≤ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R)) := by
    rw [heq]
    exact ((le_inf hHZ (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed back)).trans_eq hfix).trans inf_le_right
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat0 : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt0 : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hfix0 := c.original_equal_mover_seed_intersection_fixed_plane eK geometry
    (by change 2 < geometry.b R; omega) path.start_color hat0 hdt0 heq0 hXa
    (c.original_critical_strict_movement eK geometry hb path)
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

/-- The source selector supplies an overlapping backward path whose critical
root escapes the original forward seed. Its conjugator and full mover remain
literal, and strict movement and parabolic positioning are discharged. -/
theorem original_small_critical_backward_escaping_forward
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) < 16 →
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g (path.walk.getVert 2))
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act R g (path.walk.getVert 1) ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        LocalPackage.J R (act R g (path.walk.getVert 2)) (back.walk.getVert 1) =
          LocalPackage.J R a (back.walk.getVert 1) ∧
        ¬ ⁅Z R (act R g (path.walk.getVert 2)),Z R (path.walk.getVert (path.walk.length-2))⁆ ≤
          Z R (path.walk.getVert 2) := by
  intro R geometry hb a z path hsmall heq0
  obtain ⟨ha4,hz4,hXa⟩ := c.original_small_critical_data eK geometry path hsmall
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
  obtain ⟨g,hg,x,hx,hgen,hsep,hpos⟩ :=
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
  have hsep' : ((Z R a ⊓ centralizer (LocalPackage.J R d₁ t₁ : Set (FreeAmalgam R))) ⊓
      centralizer (LocalPackage.J R (act R x d₁) (act R x t₁) : Set (FreeAmalgam R))) = ⊥ := by
    rw [smallMoverJoin_act R x d₁ t₁,hE₁]
    exact hsep
  have hmove : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d₁) := by
    rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega) path.start_color g⁻¹ hgS]
    exact c.original_critical_strict_movement eK geometry hb path
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
  rcases c.original_equal_mover_pair_backward_path eK geometry hb path hat₁ hdt₁ heq₁ hXa
    ha4 hz4 x hx hgen' hsep' hmove with ⟨back,hbt,hover⟩ | ⟨back,hbt,hover⟩
  · refine ⟨g⁻¹,hgS,back,hbt,hover,?_,?_⟩
    · rw [hbt]
      exact heq₁
    · exact positioned_backward_root_escapes_forward c eK geometry hb path back
        hat₁ hdt₁ heq₁ hsmall heq0 htwo hmove
  · have hatX : Adjacent R a (act R x t₁) := by
      simpa only [hxa] using (adjacent_act_iff R x _ _).mpr hat₁
    have hdtX := (adjacent_act_iff R x _ _).mpr hdt₁
    have heqX : LocalPackage.J R (act R x d₁) (act R x t₁) = LocalPackage.J R a (act R x t₁) := by
      rw [smallMoverJoin_act R x d₁ t₁,heq₁,←smallMoverJoin_act R x a t₁,hxa]
    have hmoveX : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R (act R x d₁)) := by
      rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega) path.start_color x hxS]
      exact hmove
    refine ⟨g⁻¹*x,(stabilizer R a).mul_mem hgS hxS,?_⟩
    rw [act_mul R g⁻¹ x (path.walk.getVert 2)]
    simp only [act_mul]
    refine ⟨back,hbt,hover,?_,?_⟩
    · rw [hbt]
      exact heqX
    · exact positioned_backward_root_escapes_forward c eK geometry hb path back
        hatX hdtX heqX hsmall heq0 htwoX hmoveX

/-- The positioned backward choice eliminates the second radius alternative.
With the two literal equal-mover edges, the original small critical root lies
in the fourth seed, without a further positioning or seed-containment premise. -/
theorem original_small_critical_root_le_fourth_seed
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) < 16 →
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      LocalPackage.J R (path.walk.getVert 4) (path.walk.getVert 3) =
        LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 3) →
      ⁅Z R a,Z R z⁆ ≤ Z R (path.walk.getVert 4) := by
  intro R geometry hb a z path hsmall heq2 heq4
  obtain ⟨g,hg,back,hbt,_,heqback,hescape⟩ :=
    c.original_small_critical_backward_escaping_forward eK geometry hb path hsmall heq2
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have hat : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have hdt : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  have hga : act R g a = a := hg
  have hatg : Adjacent R a (back.walk.getVert 1) := by
    rw [hbt]
    simpa only [hga] using (adjacent_act_iff R g _ _).mpr hat
  have hdtg : Adjacent R (act R g (path.walk.getVert 2)) (back.walk.getVert 1) := by
    rw [hbt]
    exact (adjacent_act_iff R g _ _).mpr hdt
  exact (c.original_small_critical_radius_root_containment eK geometry hb path back
    hatg hdtg heqback hsmall heq2 heq4).resolve_right hescape

/-- In the equal-mover branch, a selected backward image below sixteen
would put its root into the very forward seed that positioning excludes.
Thus this actual backward path has a large critical image. -/
theorem original_equal_mover_small_critical_backward_large_image
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) < 16 →
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g (path.walk.getVert 2))
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act R g (path.walk.getVert 1) ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        LocalPackage.J R (act R g (path.walk.getVert 2)) (back.walk.getVert 1) =
          LocalPackage.J R a (back.walk.getVert 1) ∧
        16 ≤ (Q R (path.walk.getVert (path.walk.length-2))).relIndex
          (Z R (act R g (path.walk.getVert 2))) ∧
        ¬ ⁅Z R (act R g (path.walk.getVert 2)),Z R (path.walk.getVert (path.walk.length-2))⁆ ≤
          Z R (path.walk.getVert 2) := by
  intro R geometry hb a z path hsmall heq
  obtain ⟨g,hg,back,hbt,hover,heqback,hescape⟩ :=
    c.original_small_critical_backward_escaping_forward eK geometry hb path hsmall heq
  refine ⟨g,hg,back,hbt,hover,heqback,?_,hescape⟩
  by_contra! hsmallback
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have htwo : back.walk.getVert 2 = a := by
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
  have hthree : back.walk.getVert 3 = path.walk.getVert 1 := hover 1 (by omega)
  have hfour : back.walk.getVert 4 = path.walk.getVert 2 := hover 2 (by omega)
  apply hescape
  have h := c.original_small_critical_root_le_fourth_seed eK geometry hb back hsmallback
    (by rw [htwo]; exact heqback.symm) (by rw [hfour,hthree,htwo]; exact heq)
  rwa [hfour] at h

/-- Both mover alternatives now give a literal overlapping backward path
with image at least sixteen and the full truncated-radius displacement.
No equal-mover, strict-movement or selector-positioning premise remains. -/
theorem original_small_critical_backward_large_image
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      (Q R z).relIndex (Z R a) < 16 →
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g (path.walk.getVert 2))
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act R g (path.walk.getVert 1) ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        16 ≤ (Q R (path.walk.getVert (path.walk.length-2))).relIndex
          (Z R (act R g (path.walk.getVert 2))) ∧
        ⁅V R (act R g (path.walk.getVert 2)) ⊓ Q R (back.walk.getVert (back.walk.length-2)),
          Z R (path.walk.getVert (path.walk.length-2))⁆ ≤ Z R (act R g (path.walk.getVert 2)) := by
  intro R geometry hb a z path hsmall
  by_cases heq : LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
      LocalPackage.J R a (path.walk.getVert 1)
  · obtain ⟨g,hg,back,hbt,hover,_,hlarge,_⟩ :=
      c.original_equal_mover_small_critical_backward_large_image eK geometry hb path hsmall heq
    refine ⟨g,hg,back,hbt,hover,hlarge,?_⟩
    rcases c.original_radius_displacement_or_root eK geometry back with h | h
    · exact h
    · rw [h.1] at hlarge
      omega
  · obtain ⟨ha4,hz4,_⟩ := c.original_small_critical_data eK geometry path hsmall
    obtain ⟨g,hg,back,hbt,hover,_,_,hlarge,hdisp⟩ :=
      c.original_unequal_root_backward_large_image eK geometry hb path heq hz4 ha4
    refine ⟨g,hg,back,hbt,hover,?_,hdisp⟩
    by_contra! hsmallback
    have h := (c.original_small_critical_data eK geometry back hsmallback).1
    rw [h] at hlarge
    omega

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
