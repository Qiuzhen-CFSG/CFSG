module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticElementarySelection
public import Theory.SpecificGroups.SymplecticFour.SmallIndexLift
public import Theory.GroupTheory.ComponentSmallIndex

/-!
# Original residual generation across the two unequal kernels

The original marked component embeds its full ambient quotient in
Aut(Sp4(4)). Its edge two-group has relative order at most 1024, whereas
every canonical mover has relative order sixty-four. Thus its edge index,
and its cross index in the other original kernel, are at most sixteen.

If a subgroup containing that mover generates the original residual modulo
Q_a, its coset action has degree at most sixteen. The simple residual
quotient has order divisible by seventeen; the coset action is trivial.
This restores actual residual containment without assuming Q_a lies in the
mover, including non-elementary cross images and possible outer actions.

The final theorem applies this lift to the literal selected conjugator and
constructs the original overlapping backward critical path under strict
movement. Construction of the quotient generator in the remaining cases,
strict movement, both distance exclusions and SymplecticPlaneRecognition
remain open.
Source: MS93 (5.5)--(5.7), pp.915--919; Aschbacher--Smith 9.3.10, pp.734--735.
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

/-- The full original edge quotient has two-order at most 1024. -/
theorem original_edge_kernel_index_le_1024
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a t : Vertex R}, color R a = false → Adjacent R a t →
      (Q R a).relIndex (Q R t) ≤ 1024 := by
  intro R a t ha hat
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,_,_,hBC,hcard,_,_⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  let := hKN
  let := hBN
  let eB := (cComponentTwoCoreQuotientEquiv c.component_product.1).symm.trans eK
  have hbound := two_subgroup_card_le_1024_of_centric_four_component
    BinaryField.four.card_eq ((pResidual 2 c.M).map q) eB hcard hBC (R.map q)
    (hodd.isPGroup.map q)
  obtain ⟨i,hi,_,hiT,hiQ,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le ha hat
  rw [←hiT,←hiQ,relIndex_map_map_of_injective _ _ hi,←QuotientGroup.ker_mk' (pCore 2 c.M),relIndex_ker]
  exact hbound

/-- Each canonical mover has index at most sixteen in its entire edge group. -/
theorem original_mover_edge_index_le_sixteen
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a t : Vertex R}, color R a = false → Adjacent R a t →
      (LocalPackage.J R a t).relIndex (Q R t) ≤ 16 := by
  intro R a t ha hat
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have h := relIndex_mul_relIndex (Q R a) (LocalPackage.J R a t) (Q R t)
    (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le ha hat)
    (LocalPackage.J_le_radical R a t)
  rw [(c.original_small_mover_join_indices eK ha hat).2.1] at h
  have hb := c.original_edge_kernel_index_le_1024 eK ha hat
  change (Q R a).relIndex (Q R t) ≤ 1024 at hb
  omega

/-- The two original kernels need not agree: the missing cross index is small. -/
theorem original_neighbor_mover_kernel_index_le_sixteen
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      (LocalPackage.J R d t).relIndex (Q R a) ≤ 16 := by
  intro R a d t ha hat hdt
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [ha] at h
    cases ht : color R t <;> simp_all
  have hd : color R d = false := by
    have h := adjacent_color_ne R hdt
    rw [ht] at h
    cases hd : color R d <;> simp_all
  let := finite_stabilizer R t
  let : Finite (Q R t) := Finite.of_injective
    (inclusion (show Q R t ≤ stabilizer R t from fun _ hx => hx.1)) (inclusion_injective _)
  exact (relIndex_le_of_le_right (Q_le_adjacent_h R ht hat) index_ne_zero_of_finite).trans
    (c.original_mover_edge_index_le_sixteen eK hd hdt)

/-- A mover-containing supplement to Q_a contains the actual residual. -/
theorem original_residual_le_of_mover_kernel_supplement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      ∀ N : Subgroup (FreeAmalgam R), LocalPackage.J R d t ≤ N →
        N ≤ stabilizer R a → Ltilde R a ≤ N ⊔ Q R a → Ltilde R a ≤ N := by
  intro R a d t ha hat hdt N hJN hNS hcover
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hcard,_,_⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨π,hπ,hπker⟩ := local_residual_projection R hodd.isPGroup hodd.twoCore_le
    q (QuotientGroup.ker_mk' _) ha
  let := finite_stabilizer R a
  let : Finite (Ltilde R a) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer a)) (inclusion_injective _)
  let : Finite (Q R a) := Finite.of_injective
    (inclusion (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)) (inclusion_injective _)
  let : Finite (N ⊔ Q R a : Subgroup (FreeAmalgam R)) := Finite.of_injective
    (inclusion (sup_le hNS (show Q R a ≤ stabilizer R a from fun _ hx => hx.1)))
    (inclusion_injective _)
  exact component_le_of_kernel_supplement_small_index (Ltilde R a) N (Q R a)
    (hNS.trans (Q_normalized R a)) (isPPerfect_embedded_pResidual_of_finite 2 _)
    π hπ hπker (by decide : Nat.Prime 17) (by rw [hcard]; decide) hcover
    (lt_of_le_of_lt ((relIndex_le_of_le_left hJN index_ne_zero_of_finite).trans
      (c.original_neighbor_mover_kernel_index_le_sixteen eK ha hat hdt)) (by decide))
/-- Generation modulo the original kernel already gives actual residual
containment for the neighboring mover and the critical endpoint seed. -/
theorem original_mover_root_generation_of_mod_kernel
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z d t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Q R a →
      Ltilde R a ≤ LocalPackage.J R d t ⊔ Z R z := by
  intro R geometry a z d t path hat hdt hgen
  exact c.original_residual_le_of_mover_kernel_supplement eK path.start_color hat hdt
    (LocalPackage.J R d t ⊔ Z R z) le_sup_left
    (sup_le ((LocalPackage.J_le_radical R d t).trans
      (fun _ hx => hx.2 a (adjacent_symm R hat)))
      (path.endpoint_Z_le_start_stabilizer
        (lt_of_lt_of_le (by decide : 0 < 4) (c.original_geometry_four_le eK geometry)))) hgen

/-- In the remaining selection branch, it suffices to construct a generator
modulo Q_a. This theorem restores the full residual and every overlapping
vertex of the original backward path. Strict movement remains explicit. -/
theorem original_backward_path_of_quotient_generator_strict_mover
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      (∃ g ∈ Ltilde R a,
        Ltilde R a ≤ ((LocalPackage.J R d t).map (MulAut.conj g).toMonoidHom ⊔ Z R z) ⊔ Q R a) →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      ∃ d' t', Adjacent R a t' ∧ Adjacent R d' t' ∧
        (∃ back : CriticalPath R geometry d' (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t' ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry hb a z d t path hat hdt hselect hmove
  obtain ⟨g,hg,hgen⟩ := hselect
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hfix : act R g⁻¹ a = a := hgS
  let d' := act R g⁻¹ d
  let t' := act R g⁻¹ t
  have hat' : Adjacent R a t' := by
    rw [←hfix]
    exact (adjacent_act_iff R g⁻¹ _ _).mpr hat
  have hdt' : Adjacent R d' t' := (adjacent_act_iff R g⁻¹ _ _).mpr hdt
  have hgen' : Ltilde R a ≤ LocalPackage.J R d' t' ⊔ Z R z := by
    apply c.original_mover_root_generation_of_mod_kernel eK geometry path hat' hdt'
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
