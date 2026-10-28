module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticMoverComparison
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticPairedSelection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalQuadraticActors


/-!
# The original unequal-mover branch is nonquadratic

The complete neighboring mover has at least sixty-four images modulo the
starting kernel. If its action on the original natural seed is quadratic,
the marked ambient action has moving index at most sixteen. Maximum-mover
uniqueness then identifies it with the starting mover. Conversely the
starting mover is quadratic. Thus unequal movers, and their join, are
nonquadratic; explicit original elements witness the second displacement.
The original edge radical normalizes each entire mover.

The backward-path consumer applies this characterization to its quadratic
case while retaining every overlapping vertex. Selection of the actual
residual generators in the unequal case and the strict moving index remain
open, as do the large-distance and distance-four exclusions and plane
recognition. The quadratic criterion does not prove strict movement.

Source: MS93 (5.5), pp.915--917, and (5.7), p.919;
Aschbacher--Smith 9.3.10, p.734.
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

/-- Equality of the literal neighboring movers is equivalent to quadratic cross action. -/
theorem original_neighbor_mover_eq_iff_quadratic
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      (LocalPackage.J R d t = LocalPackage.J R a t ↔
        ⁅LocalPackage.J R d t,Z R a⁆ ≤
          centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) := by
  intro R a d t ha hat hdt
  constructor
  · intro he
    rw [he]
    exact c.original_edge_mover_quadratic eK ha hat
  intro hquad
  apply (c.original_neighbor_mover_eq_iff_small_cross_action eK ha hat hdt).mpr
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
  have hlarge := c.original_neighbor_mover_cross_index_ge_64 eK ha hat hdt
  have hZU := c.original_Z_eq_U a ha
  rw [hZU] at hquad
  exact original_quadratic_actor_fixed_index_le_sixteen R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq ha hfixed (LocalPackage.J R d t)
    ((LocalPackage.J_le_radical R d t).trans (fun _ hx => hx.2 a (adjacent_symm R hat)))
    (lt_of_lt_of_le (by decide : 2 < 64) hlarge) hquad

/-- The source pair is quadratic on the original seed precisely in the
already handled equal-mover case. -/
theorem original_mover_pair_eq_iff_quadratic
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      (LocalPackage.J R d t = LocalPackage.J R a t ↔
        ⁅LocalPackage.J R a t ⊔ LocalPackage.J R d t,Z R a⁆ ≤
          centralizer ((LocalPackage.J R a t ⊔ LocalPackage.J R d t :
            Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R))) := by
  intro R a d t ha hat hdt
  constructor
  · intro he
    rw [he,sup_idem]
    exact c.original_edge_mover_quadratic eK ha hat
  · intro hquad
    apply (c.original_neighbor_mover_eq_iff_quadratic eK ha hat hdt).mpr
    exact ((commutator_mono le_sup_right le_rfl).trans hquad).trans
      (centralizer_le (show LocalPackage.J R d t ≤ LocalPackage.J R a t ⊔ LocalPackage.J R d t from le_sup_right))

/-- Unequal neighboring movers have the literal nonquadratic action used
at the start of source (5.5), including both complete kernels. -/
theorem original_unequal_mover_pair_not_quadratic
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t ≠ LocalPackage.J R a t →
        ¬ ⁅LocalPackage.J R a t ⊔ LocalPackage.J R d t,Z R a⁆ ≤
          centralizer ((LocalPackage.J R a t ⊔ LocalPackage.J R d t :
            Subgroup (FreeAmalgam R)) : Set (FreeAmalgam R)) := by
  intro R a d t ha hat hdt hne hquad
  exact hne ((c.original_mover_pair_eq_iff_quadratic eK ha hat hdt).mpr hquad)

/-- The actual backward-path application now accepts the original quadratic
cross action, and derives equality of the movers from the full marking. -/
theorem original_backward_path_of_quadratic_strict_mover
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      ⁅LocalPackage.J R d t,Z R a⁆ ≤
        centralizer (LocalPackage.J R d t : Set (FreeAmalgam R)) →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      ∃ d' t', Adjacent R a t' ∧ Adjacent R d' t' ∧
        (∃ back : CriticalPath R geometry d' (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t' ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry hb a z d t path hat hdt hquad hmove
  exact c.original_backward_path_of_equal_strict_mover eK geometry hb path hat hdt
    ((c.original_neighbor_mover_eq_iff_quadratic eK path.start_color hat hdt).mpr hquad) hmove

/-- The original edge radical normalizes the entire canonical mover. -/
theorem original_edge_normalizes_mover :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a t : Vertex R}, Adjacent R a t →
      Q R t ≤ normalizer (LocalPackage.J R a t : Set (FreeAmalgam R)) := by
  intro R a t hat x hx
  rw [mem_normalizer_iff_map_conj_eq]
  have hx' := (Q R t).inv_mem hx
  have ha : act R x⁻¹ a = a := hx'.2 a (adjacent_symm R hat)
  have ht : act R x⁻¹ t = t := hx'.1
  have hh := smallMoverJoin_act R x⁻¹ a t
  simpa only [ha,ht,inv_inv,MulEquiv.toMonoidHom_eq_coe] using hh.symm

open scoped commutatorElement in
/-- Unequal movers supply actual original elements with nonzero second
natural displacement, not merely a quotient-family label. -/
theorem original_unequal_mover_nontrivial_double_displacement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t ≠ LocalPackage.J R a t →
      ∃ x ∈ LocalPackage.J R d t, ∃ y ∈ LocalPackage.J R d t, ∃ v ∈ Z R a,
        x * ⁅y,v⁆ ≠ ⁅y,v⁆ * x := by
  intro R a d t ha hat hdt hne
  by_contra! h
  apply hne
  apply (c.original_neighbor_mover_eq_iff_quadratic eK ha hat hdt).mpr
  apply commutator_le.mpr
  intro y hy v hv x hx
  exact h x hx y hy v hv
end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
