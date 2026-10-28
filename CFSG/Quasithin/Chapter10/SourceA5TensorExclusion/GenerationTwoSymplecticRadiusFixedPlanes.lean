module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticRadiusGrowth
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalFixedPlane

/-!
# Fixed planes for the original radius-index alternatives

More than four images of a subgroup of the canonical quadratic mover
saturate its fixed plane on the original natural seed. When adjacent movers
agree, the same fixed subgroup belongs to the neighboring omega-center.
The two alternatives of the proved radius-index split apply this at the
literal second and fourth vertices, with the entire radius kernel retained.

These implications keep the equal-mover conditions explicit. The selected
generators and insertion of critical commutators into the intermediate
seeds are still required to close MS93 (5.11); X is not identified with Z
without a separate argument. Distance four and marked plane recognition
also remain outstanding.

Source: MS93 (5.11), printed p.924; Aschbacher--Smith 9.3.10,
printed pp.734--735.
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

/-- A large subgroup of the canonical mover fixes exactly the same part of
 the original natural seed as the entire mover. -/
theorem original_large_edge_subactor_fixed_eq
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a t : Vertex R}, color R a = false → Adjacent R a t →
      ∀ A : Subgroup (FreeAmalgam R), A ≤ LocalPackage.J R a t →
      4 < (Q R a).relIndex A →
      Z R a ⊓ centralizer (A : Set (FreeAmalgam R)) =
        Z R a ⊓ centralizer (LocalPackage.J R a t : Set (FreeAmalgam R)) := by
  intro R a t ha hat A hAJ hlarge
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
  obtain ⟨geometry,hpos,_⟩ := c.exists_positive_even_geometry eK
  have hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hcore : x ∈ fixedCore R a := ⟨
      ((U_le_Z a).trans (geometry.omega_bound a ha
        (by
          rw [geometry.distance_constant a ha]
          change 0 < geometry.b R
          exact hpos)) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot a ha] at hcore
  have hquad := c.original_edge_mover_quadratic eK ha hat
  rw [c.original_Z_eq_U a ha] at hquad ⊢
  exact original_large_quadratic_subactor_fixed_eq R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq ha hfixed A (LocalPackage.J R a t) hAJ
    ((LocalPackage.J_le_radical R a t).trans (fun _ hx => hx.2 a (adjacent_symm R hat)))
    hlarge hquad

/-- Along equal movers, fixation by more than four original action images
puts a vector in the full neighboring omega-center. -/
theorem original_equal_mover_large_subactor_fixed_le_X
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false →
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      ∀ A : Subgroup (FreeAmalgam R), A ≤ LocalPackage.J R a t →
      4 < (Q R a).relIndex A →
      Z R a ⊓ centralizer (A : Set (FreeAmalgam R)) ≤ X R d := by
  intro R geometry hb a d t ha hat hdt heq A hAJ hlarge
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [ha] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hQdJ : Q R d ≤ LocalPackage.J R a t := heq ▸
    LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le hd hdt
  have hZaQd : Z R a ≤ Q R d :=
    (le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hdt hat)).trans
      (geometry.V_le_Q hb d hd)
  rw [c.original_large_edge_subactor_fixed_eq eK ha hat A hAJ hlarge]
  let := geometry.Z_elementary (by omega) a ha
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hZaQd hx.1,
    elemPow_eq_one_of_isElementaryAbelian x hx.1,
    (centralizer_le hQdJ) hx.2⟩

/-- The first numerical branch on the literal original path fixes the
canonical plane at vertex two and therefore lies in X at vertex four,
when the two movers across vertex three agree. -/
theorem original_critical_radius_first_fixed_plane
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 4) (path.walk.getVert 3) =
        LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 3) →
      4 < (Q R (path.walk.getVert 2)).relIndex (V R z) →
      Z R (path.walk.getVert 2) ⊓ centralizer (V R z : Set (FreeAmalgam R)) ≤
        X R (path.walk.getVert 4) := by
  intro R geometry hb a z path heq hlarge
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have htwo : color R (path.walk.getVert 2) = false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have hfour : color R (path.walk.getVert 4) = false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have h23 : Adjacent R (path.walk.getVert 2) (path.walk.getVert 3) :=
    (cosetGraph_adj R _ _).mp (path.walk.adj_getVert_succ (by omega : 2 < path.walk.length))
  have h43 : Adjacent R (path.walk.getVert 4) (path.walk.getVert 3) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 3 < path.walk.length)))
  have hVQ : V R z ≤ Q R (path.walk.getVert 4) := by
    apply (V_le_iff R path.end_color _).mpr
    intro d hd hdz
    apply Z_le_Q_of_dist_lt R d (geometry.exists_critical d hd)
    rw [geometry.distance_constant d hd]
    change (cosetGraph R).dist d (path.walk.getVert 4) < geometry.b R
    have ht := (cosetGraph_connected R).dist_triangle (u := d) (v := z)
      (w := path.walk.getVert 4)
    have he := path.dist_end 4
    rw [SimpleGraph.dist_comm] at he
    rw [he,path.length_eq_b] at ht
    omega
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hVJ := hVQ.trans (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le hfour h43)
  rw [heq] at hVJ
  exact c.original_equal_mover_large_subactor_fixed_le_X eK geometry
    (by change 2 < geometry.b R; omega)
    htwo h23 h43 heq (V R z) hVJ hlarge

/-- The second numerical branch uses the entire radius kernel at the
literal second vertex, not a truncated subgroup. -/
theorem original_critical_radius_second_fixed_plane
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      4 < (Q R a).relIndex (V R z ⊓ Q R (path.walk.getVert 2)) →
      Z R a ⊓ centralizer ((V R z ⊓ Q R (path.walk.getVert 2) :
        Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) ≤ X R (path.walk.getVert 2) := by
  intro R geometry hb a z path heq hlarge
  have hlen : 4 < path.walk.length := by rwa [path.length_eq_b]
  have htwo : color R (path.walk.getVert 2) = false :=
    (path.vertex_color (by omega)).mpr (by decide)
  have h01 : Adjacent R a (path.walk.getVert 1) := by
    have h := (cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0 < path.walk.length))
    simpa only [SimpleGraph.Walk.getVert_zero] using h
  have h21 : Adjacent R (path.walk.getVert 2) (path.walk.getVert 1) :=
    adjacent_symm R ((cosetGraph_adj R _ _).mp
      (path.walk.adj_getVert_succ (by omega : 1 < path.walk.length)))
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hKJ : V R z ⊓ Q R (path.walk.getVert 2) ≤ LocalPackage.J R a (path.walk.getVert 1) := by
    rw [←heq]
    exact inf_le_right.trans (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le htwo h21)
  exact c.original_equal_mover_large_subactor_fixed_le_X eK geometry
    (by change 2 < geometry.b R; omega)
    path.start_color h01 h21 heq _ hKJ hlarge

/-- On a path with both indicated equal-mover pairs, the proved numerical
split forces one of the two exact fixed-subgroup inclusions. No extra
radius bound is assumed. This does not identify X with Z or insert a
critical commutator into the intermediate seed. -/
theorem original_critical_radius_fixed_plane_alternative
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 4) (path.walk.getVert 3) =
        LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 3) →
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      (Z R (path.walk.getVert 2) ⊓ centralizer (V R z : Set (FreeAmalgam R)) ≤
        X R (path.walk.getVert 4)) ∨
      (Z R a ⊓ centralizer ((V R z ⊓ Q R (path.walk.getVert 2) :
        Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) ≤ X R (path.walk.getVert 2)) := by
  intro R geometry hb a z path heq4 heq2
  rcases c.original_critical_radius_index_split eK geometry hb path with h | h
  · exact Or.inl (c.original_critical_radius_first_fixed_plane eK geometry hb path heq4 h)
  · exact Or.inr (c.original_critical_radius_second_fixed_plane eK geometry hb path heq2 h)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
