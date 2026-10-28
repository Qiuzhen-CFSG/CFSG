module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticCrossKernelLift
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalNormalMoverGeneration

/-!
# Original backward selection for all inner cross images

The canonical neighboring mover is normal in the actual common Sylow edge.
Its cross image has order at least 64, and unequal movers have natural
moving index above sixteen. The normal-mover calculation therefore selects
a generator modulo the original kernel without an abelian-image premise.
The checked small-index lift restores containment of the full residual.

Applying that generator to the original critical path constructs the
backward path with every overlapping vertex retained, under strict
movement. Equal movers use the previously checked paired selection.
A remaining failure gives an actual mover element outside the original
residual times its kernel. The outer cross-image case, strict movement,
both distance exclusions and SymplecticPlaneRecognition remain open.

Source: MS93 (5.5)--(5.7), pp.915--919; Aschbacher--Smith 9.3.10,
pp.734--735. This supplies the inner selection branch, not the full
source theorem or its strict-movement premise.
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

theorem original_unequal_inner_mover_quotient_generator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z d t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t ≠ LocalPackage.J R a t →
      LocalPackage.J R d t ≤ Ltilde R a ⊔ Q R a →
      (Q R a).relIndex (Z R z) = 4 → (Q R z).relIndex (Z R a) = 4 →
      ∃ g ∈ Ltilde R a,
        Ltilde R a ≤ ((LocalPackage.J R d t).map (MulAut.conj g).toMonoidHom ⊔ Z R z) ⊔ Q R a := by
  intro R geometry a z d t path hat hdt hneJ hinner hza haz
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
  exact original_large_normal_mover_root_generator R hms hodd.isPGroup hne hodd.twoCore_le
    hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path hb hza haz hfixed (LocalPackage.J R d t)
    ((LocalPackage.J_le_radical R d t).trans (fun _ hx => hx.2 a (adjacent_symm R hat)))
    (Q R t) (LocalPackage.J_le_radical R d t)
    (c.original_edge_normalizes_mover hdt) hSylow
    (c.original_neighbor_mover_cross_index_ge_64 eK path.start_color hat hdt)
    hinner
    (c.original_unequal_mover_cross_action_gt_sixteen eK path.start_color hat hdt hneJ)


/-- The small cross-kernel index lifts the selected quotient generator to
containment of the full original residual, even for nonabelian cross images. -/
theorem original_unequal_inner_mover_generator
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z d t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t ≠ LocalPackage.J R a t →
      LocalPackage.J R d t ≤ Ltilde R a ⊔ Q R a →
      (Q R a).relIndex (Z R z) = 4 → (Q R z).relIndex (Z R a) = 4 →
      ∃ g ∈ Ltilde R a,
        Ltilde R a ≤ (LocalPackage.J R d t).map (MulAut.conj g).toMonoidHom ⊔ Z R z := by
  intro R geometry a z d t path hat hdt hne hinner hza haz
  obtain ⟨g,hg,hgen⟩ := c.original_unequal_inner_mover_quotient_generator eK geometry
    path hat hdt hne hinner hza haz
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hfix : act R g⁻¹ a = a := hgS
  have hat' : Adjacent R a (act R g⁻¹ t) := by
    rw [←hfix]
    exact (adjacent_act_iff R g⁻¹ _ _).mpr hat
  have hdt' := (adjacent_act_iff R g⁻¹ _ _).mpr hdt
  have hh := c.original_mover_root_generation_of_mod_kernel eK geometry path hat' hdt'
    (by rw [smallMoverJoin_act,inv_inv]; exact hgen)
  rw [smallMoverJoin_act,inv_inv] at hh
  exact ⟨g,hg,hh⟩

/-- Both equal and unequal inner movers supply the actual overlapping
backward path under the strict movement premise. -/
theorem original_backward_path_of_inner_strict_mover
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t ≤ Ltilde R a ⊔ Q R a →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      ∃ d' t', Adjacent R a t' ∧ Adjacent R d' t' ∧
        (∃ back : CriticalPath R geometry d' (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t' ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry hb a z d t path hat hdt hinner hmove
  by_cases heq : LocalPackage.J R d t = LocalPackage.J R a t
  · exact c.original_backward_path_of_equal_strict_mover eK geometry hb path hat hdt heq hmove
  rcases c.original_radius_displacement_or_root eK geometry path with hdisp | ⟨haz,hza,_,_⟩
  · exact c.original_backward_path_of_radius_displacement eK geometry path hat hdisp
  exact c.original_backward_path_of_quotient_generator_strict_mover eK geometry hb path hat hdt
    (c.original_unequal_inner_mover_quotient_generator eK geometry path hat hdt heq hinner hza haz)
    hmove

/-- With strict movement, a failure of backward selection forces a literal
mover element outside the original residual times its original kernel. -/
theorem original_backward_path_or_outer_mover
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      (∃ d' t', Adjacent R a t' ∧ Adjacent R d' t' ∧
        (∃ back : CriticalPath R geometry d' (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t' ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2))) ∨
      ∃ x ∈ LocalPackage.J R d t, x ∉ Ltilde R a ⊔ Q R a := by
  intro R geometry hb a z d t path hat hdt hmove
  by_cases hi : LocalPackage.J R d t ≤ Ltilde R a ⊔ Q R a
  · exact Or.inl (c.original_backward_path_of_inner_strict_mover eK geometry hb path hat hdt hi hmove)
  · exact Or.inr (SetLike.not_le_iff_exists.mp hi)
end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
