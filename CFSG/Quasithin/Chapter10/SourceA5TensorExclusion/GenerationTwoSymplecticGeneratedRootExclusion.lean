module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticEndpointKernel

/-!
# Excluding small roots on generated original overlaps

A critical image of order at most four has its whole commutator centralized
by the canonical first-edge mover. On a backward overlap, the original
endpoint centralizes the same commutator by its distance from the new
endpoint. If these two subgroups generate the full original residual, the
commutator lies in the earlier vertex's residual-fixed two-core, which is
trivial. Criticality rules this out.

Apply this to the actual unequal-mover choice, retaining its conjugator,
all overlap vertices and full residual generation. Its backward critical
image is greater than four, and hence the entire truncated radius has the
proved displacement into the original seed. This excludes the small-root
case for these generated overlaps; the equal-mover branch, stronger radius
bound, both distance exclusions and SymplecticPlaneRecognition remain open.

Source: MS93 (5.5)(c), (5.7), (5.10), pp.915--919,922--923, specialized to
the vanishing original fixed core in Aschbacher--Smith 9.3.10, pp.734--735.
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

/-- A critical image of order at most four has its entire commutator fixed
by the canonical mover of the first edge. -/
theorem original_critical_small_commutator_centralizes_mover
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → (cosetGraph R).dist z t < geometry.b R →
      (Q R z).relIndex (Z R a) ≤ 4 →
      ⁅Z R a,Z R z⁆ ≤ centralizer (LocalPackage.J R a t : Set (FreeAmalgam R)) := by
  intro R geometry a z t path hat hdist hsmall
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
  have hb : 0 < geometry.b R := lt_of_lt_of_le (by decide : 0 < 4)
    (c.original_geometry_four_le eK geometry)
  have hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hcore : x ∈ fixedCore R a := ⟨
      ((U_le_Z a).trans (geometry.omega_bound a path.start_color
        (by rwa [geometry.distance_constant a path.start_color])) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot a path.start_color] at hcore
  have hcentral : (centralizer (Z R z : Set (FreeAmalgam R))).relIndex (U R a) ≤ 4 := by
    rw [←c.original_Z_eq_U a path.start_color,←inf_relIndex_left,
      ←c.original_critical_seed_kernel_eq_centralizer eK geometry path,inf_relIndex_left]
    exact hsmall
  obtain ⟨i,_,_,hiT,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le
    path.start_color hat
  have hQt : IsPGroup 2 (Q R t) := hiT ▸ hodd.isPGroup.map i
  have hzT : Z R z ≤ Q R t := Z_le_Q_of_dist_lt R z
    (geometry.exists_critical z path.end_color)
    (by rwa [geometry.distance_constant z path.end_color])
  have hindices := (c.original_small_mover_join_indices eK path.start_color hat).2
  have hn := original_large_small_mover_centralizes_commutator R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path.start_color hfixed (Q R t) (LocalPackage.J R a t) (Z R z) hQt
    (fun _ hx => hx.2 a (adjacent_symm R hat)) (LocalPackage.J_le_radical R a t)
    hzT hindices.1 hindices.2.le (Or.inl hcentral)
  rw [c.original_Z_eq_U a path.start_color,commutator_comm]
  exact hn

/-- The full selected generators exclude a small backward critical root:
its mover and the nearby endpoint both fix it, so it would lie in the
vanishing fixed core at the original starting vertex. -/
theorem original_generated_backward_small_root_impossible
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t → back.walk.getVert 1 = t →
      Ltilde R a ≤ LocalPackage.J R d t ⊔ Z R z →
      (Q R (path.walk.getVert (path.walk.length-2))).relIndex (Z R d) ≤ 4 → False := by
  intro R geometry hb a z d t path back hat hdt hbt hsmallgen hsmall
  let w := path.walk.getVert (path.walk.length-2)
  let H := ⁅Z R d,Z R w⁆
  have hdist : (cosetGraph R).dist w t < geometry.b R := by
    rw [←hbt,SimpleGraph.dist_comm,back.dist_end,back.length_eq_b]
    omega
  have hJ : H ≤ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R)) :=
    c.original_critical_small_commutator_centralizes_mover eK geometry back hdt hdist hsmall
  have hwQ : Z R w ≤ Q R z := by
    apply Z_le_Q_of_dist_lt R w (geometry.exists_critical w back.end_color)
    rw [geometry.distance_constant w back.end_color,path.dist_end,path.length_eq_b]
    change geometry.b R-(geometry.b R-2) < geometry.b R
    omega
  have hHw : H ≤ Z R w := critical_commutator_le_endpoint ⟨d,w,back⟩
  have hZ : H ≤ centralizer (Z R z : Set (FreeAmalgam R)) :=
    hHw.trans (hwQ.trans (le_centralizer_iff.mp
      (commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color))))
  have hL : H ≤ centralizer (Ltilde R a : Set (FreeAmalgam R)) :=
    le_centralizer_iff.mp (hsmallgen.trans
      (sup_le (le_centralizer_iff.mp hJ) (le_centralizer_iff.mp hZ)))
  have hHQ : H ≤ Q R a :=
    (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed back).trans
      ((le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)).trans
        (geometry.V_le_Q (by omega) a path.start_color))
  have hzero : H ≤ fixedCore R a := le_inf hHQ hL
  rw [c.original_fixedCore_eq_bot a path.start_color] at hzero
  exact c.original_critical_commutator_not_le_vertex_center eK geometry back path.start_color
    (hzero.trans bot_le)

/-- Unequal movers in the root branch now give a backward path with a
strictly larger critical image and a proved radius displacement. All maps,
full residual generators and overlap vertices are those of the same choice. -/
theorem original_unequal_root_backward_large_image
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) ≠
        LocalPackage.J R a (path.walk.getVert 1) →
      (Q R a).relIndex (Z R z) = 4 → (Q R z).relIndex (Z R a) = 4 →
      ∃ g ∈ stabilizer R a,
        ∃ back : CriticalPath R geometry (act R g (path.walk.getVert 2))
          (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1 = act R g (path.walk.getVert 1) ∧
        (∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        Ltilde R a ≤ LocalPackage.J R (act R g (path.walk.getVert 2))
          (back.walk.getVert 1) ⊔ Z R z ∧
        LocalPackage.J R (act R g (path.walk.getVert 2)) (back.walk.getVert 1) ≠
          LocalPackage.J R a (back.walk.getVert 1) ∧
        4 < (Q R (path.walk.getVert (path.walk.length-2))).relIndex
          (Z R (act R g (path.walk.getVert 2))) ∧
        ⁅V R (act R g (path.walk.getVert 2)) ⊓ Q R (back.walk.getVert (back.walk.length-2)),
          Z R (path.walk.getVert (path.walk.length-2))⁆ ≤ Z R (act R g (path.walk.getVert 2)) := by
  intro R geometry hb a z path hne hza haz
  obtain ⟨g,hg,back,hbt,hover,hgen,hne'⟩ :=
    c.original_unequal_root_backward_generators eK geometry hb path hne hza haz
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
  have hi : 4 < (Q R (path.walk.getVert (path.walk.length-2))).relIndex
      (Z R (act R g (path.walk.getVert 2))) := by
    by_contra! hsmall
    exact c.original_generated_backward_small_root_impossible eK geometry hb path back
      hatg hdtg rfl hgen hsmall
  refine ⟨g,hg,back,hbt,hover,hgen,hne',hi,?_⟩
  rcases c.original_radius_displacement_or_root eK geometry back with h | h
  · exact h
  · change 4 < (Q R (path.walk.getVert (path.walk.length-2))).relIndex
      (Z R (act R g (path.walk.getVert 2))) at hi
    rw [h.1] at hi
    omega

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
