module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticSylowMovers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalAbelianMoverGeneration
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticUnequalMovers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSmallMoverSylow
public import Theory.GroupTheory.RelativeProductBound

/-!
# Original unequal-mover selection for an abelian inner cross image

The neighboring mover has at least sixty-four images modulo the starting
kernel, and unequal movers have cross moving index greater than sixteen.
If this cross image is abelian and inner, the marked point-radical
calculation supplies a single original residual conjugator and proves
containment of the full starting kernel.

The selected neighbor retains its original moving index. If its join were
normalized by the endpoint, the two actual generators would normalize it,
forcing moving index one. Otherwise the proved selected-kernel calculation
produces the overlapping backward critical path. Thus this subcase needs
no selection, root-index or normalization callback.

Abelian cross image, inner placement and strict movement are still explicit
hypotheses. The general unequal-mover case, strict movement, both distance
exclusions and SymplecticPlaneRecognition remain open. Source: MS93 (5.5)(c)
and (5.7), pp.915--919; Aschbacher--Smith 9.3.10, pp.734--735.
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

theorem original_unequal_abelian_mover_generator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z d t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t ≠ LocalPackage.J R a t →
      LocalPackage.J R d t ≤ Ltilde R a ⊔ Q R a →
      ⁅LocalPackage.J R d t,LocalPackage.J R d t⁆ ≤ Q R a →
      (Q R a).relIndex (Z R z) = 4 → (Q R z).relIndex (Z R a) = 4 →
      Q R a ≤ LocalPackage.J R d t ∧
      ∃ g ∈ Ltilde R a,
        Ltilde R a ≤ (LocalPackage.J R d t).map (MulAut.conj g).toMonoidHom ⊔ Z R z := by
  intro R geometry a z d t path hat hdt hneJ hinner hcomm hza haz
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
  have hd : color R d = false := by
    have h := adjacent_color_ne R hdt
    rw [ht] at h
    cases he : color R d <;> simp_all
  exact original_large_abelian_mover_root_generator R hms hodd.isPGroup hne hodd.twoCore_le
    hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path hb hza haz hfixed (LocalPackage.J R d t)
    ((LocalPackage.J_le_radical R d t).trans (fun _ hx => hx.2 a (adjacent_symm R hat)))
    (hQt.to_le (LocalPackage.J_le_radical R d t))
    (c.original_neighbor_mover_cross_index_ge_64 eK path.start_color hat hdt)
    (by rw [c.original_kernel_card_eq path.start_color];
        exact c.original_small_mover_card eK hd hdt)
    hinner hcomm
    (c.original_unequal_mover_cross_action_gt_sixteen eK path.start_color hat hdt hneJ)

/-- The abelian inner cross-image branch supplies the actual selected
neighbor and the overlapping backward path under strict movement. -/
theorem original_backward_path_of_unequal_abelian_strict_mover
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t ≠ LocalPackage.J R a t →
      LocalPackage.J R d t ≤ Ltilde R a ⊔ Q R a →
      ⁅LocalPackage.J R d t,LocalPackage.J R d t⁆ ≤ Q R a →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      ∃ d' t', Adjacent R a t' ∧ Adjacent R d' t' ∧
        (∃ back : CriticalPath R geometry d' (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t' ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry hb a z d t path hat hdt hne hinner hcomm hmove
  rcases c.original_radius_displacement_or_root eK geometry path with hdisp | ⟨haz,hza,_,_⟩
  · exact c.original_backward_path_of_radius_displacement eK geometry path hat hdisp
  obtain ⟨_,g,hg,hgen⟩ := c.original_unequal_abelian_mover_generator eK geometry path
    hat hdt hne hinner hcomm hza haz
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hfix : act R g⁻¹ a = a := hgS
  let d' := act R g⁻¹ d
  let t' := act R g⁻¹ t
  have hat' : Adjacent R a t' := by
    rw [←hfix]
    exact (adjacent_act_iff R g⁻¹ _ _).mpr hat
  have hdt' : Adjacent R d' t' := (adjacent_act_iff R g⁻¹ _ _).mpr hdt
  have hgen' : Ltilde R a ≤ LocalPackage.J R d' t' ⊔ Z R z := by
    dsimp [d',t']
    rw [smallMoverJoin_act,inv_inv]
    exact hgen
  have hmove' : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R d') := by
    rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega)
      path.start_color g⁻¹ hgS]
    exact hmove
  have hbad : ¬ Z R z ≤ normalizer ((Z R d' ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) := by
    intro hn
    have hJ := (LocalPackage.J_le_radical R d' t').trans
      (ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat' hdt')
    have he := c.original_normal_neighbor_join_moving_index_eq_one eK geometry
      (by change 2 < geometry.b R; omega) path.start_color hat' hdt'
      (hgen'.trans (sup_le hJ hn))
    change (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a
      (geometry.Z_normal a)).relIndex (U R d') = 1 at he
    omega
  exact ⟨d',t',hat',hdt',c.original_small_movers_backward_path eK geometry hb path
    hat' hdt' hbad hgen' hmove'⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
