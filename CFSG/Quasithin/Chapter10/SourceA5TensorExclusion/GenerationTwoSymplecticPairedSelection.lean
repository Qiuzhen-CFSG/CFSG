module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticPairedKernel
public import Theory.GroupAction.TwoPerfectSection128
/-!
# The equal-mover branch of the original selected backward path

The nontrivial common edge center bounds a neighboring join modulo Z_a by
128. A two-perfect cover of Sp4(4) fixes this section, so a pair of normalized
joins contradicts strict movement. If just the second join escapes, conjugate
by the exact source element and interchange the two seeds. The paired-kernel
calculation then supplies one of the original overlapping backward paths.

Applying this to the previously constructed simultaneous generators removes
all normalization, root-comparison and generator callbacks in the equal-mover
branch. The original displacement alternative also removes the critical-root
indices. Equality of the movers and strict movement remain explicit: their
remaining source branches, the large-distance and distance-four exclusions,
and SymplecticPlaneRecognition are not asserted here.

Source: MS93 (5.7), p.919; Aschbacher--Smith 9.3.10, p.734.
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



/-- The actual nontrivial common edge center bounds the neighboring join
modulo the starting seed, allowing even a center of order two. -/
theorem original_neighbor_join_index_le_128
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 0 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      (Z R a).relIndex (Z R d ⊔ Z R a) ≤ 128 := by
  intro R geometry hb a d t ha hat hdt
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [ha] at h
    cases hc : color R t <;> simp_all
  have hd : color R d = false := by
    have h := adjacent_color_ne R hdt
    rw [ht] at h
    cases hc : color R d <;> simp_all
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨i,_,_,hiT,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le hd hdt
  have hp : IsPGroup 2 (Q R t) := hiT ▸ hodd.isPGroup.map i
  let := finite_stabilizer R d
  let : Finite (Q R t) := Finite.of_injective
    (inclusion (show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt)))
    (inclusion_injective _)
  have hZd : Z R d ≤ Q R t :=
    ((geometry.omega_bound d hd (by rwa [geometry.distance_constant d hd])).trans
      (omegaCenter_le _)).trans (Q_le_adjacent_h R ht hdt)
  have hcD := c.original_Z_card eK d hd
  have hQt : Q R t ≠ ⊥ := by
    intro h
    have hz := le_bot_iff.mp (h ▸ hZd)
    rw [hz,card_bot] at hcD
    omega
  have hZt : Z R t ≠ ⊥ := by
    simpa only [Z,ht,Bool.true_eq_false,if_false,edgeOmega] using omegaCenter_ne_bot (Q R t) hp hQt
  let := finite_Z R t
  have hcT : 2 ≤ Nat.card (Z R t) := (Z R t).one_lt_card_iff_ne_bot.mpr hZt
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam R)) (Z R t) (Z R d)
    bot_le (adjacent_Z_le R hd hdt)
  rw [relIndex_bot_left,relIndex_bot_left,hcD] at hmul
  have hi : (Z R t).relIndex (Z R d) ≤ 128 := by nlinarith
  exact (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_index_le geometry hb ha hat hdt).trans hi

/-- If the local residual normalizes a neighboring join, its original
moving index is one. The small-section action uses the actual simple quotient. -/
theorem original_normal_neighbor_join_moving_index_eq_one
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false → Adjacent R a t → Adjacent R d t →
      Ltilde R a ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) = 1 := by
  intro R geometry hb a d t ha hat hdt hn
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
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
  obtain ⟨π,hπ,hπker⟩ := local_residual_projection R hodd.isPGroup hodd.twoCore_le
    q (QuotientGroup.ker_mk' _) ha
  let H := Z R d ⊔ Z R a
  have hHV : H ≤ V R a := ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt
  have hHQ := hHV.trans (geometry.V_le_Q hb a ha)
  have hHG : H ≤ stabilizer R a := hHQ.trans (fun _ hx => hx.1)
  let := finite_stabilizer R a
  let : Finite (Ltilde R a) := Finite.of_injective
    (inclusion (Ltilde_le_stabilizer a)) (inclusion_injective _)
  let : Finite H := Finite.of_injective (inclusion hHG) (inclusion_injective _)
  have hcomm : ⁅H,Ltilde R a⁆ ≤ Z R a :=
    commutator_le_of_twoPerfect_simple_seventeen_section_le_128
      (Ltilde R a) H (Z R a) (isPPerfect_embedded_pResidual_of_finite 2 _) π hπ hπker
      (by rw [hcard]; decide)
      ((Q_isPGroup R hodd.isPGroup hodd.twoCore_le a ha).to_le hHQ) hn
      ((Ltilde_le_stabilizer a).trans (Z_normalized R a))
      (normal_subgroupOf_of_le_normalizer (hHG.trans (Z_normalized R a)))
      (c.original_neighbor_join_index_le_128 eK geometry (by change 0 < geometry.b R; omega) ha hat hdt)
  apply relIndex_eq_one.mpr
  exact (U_le_Z d).trans (le_sup_left.trans
    (ChapterC.Sp4Four.DistanceReduction.radius_le_B_of_commutator geometry hb ha H hHV hcomm))

/-- The equal-mover selected pair supplies a backward critical path under
strict movement, with all endpoint normalization alternatives discharged. -/
theorem original_equal_mover_pair_backward_path
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t → X R a = Z R a →
      (Q R z).relIndex (Z R a) = 4 → (Q R a).relIndex (Z R z) = 4 →
      ∀ x ∈ Ltilde R a,
      Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) →
      ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
        centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      (∃ back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1=t ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∨
      (∃ back : CriticalPath R geometry (act R x d) (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1=act R x t ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) := by
  intro R geometry hb a z d t path hat hdt heq hX ha4 hz4 x hx hgen hsep hmove
  have hxS : x ∈ stabilizer R a := Ltilde_le_stabilizer a hx
  by_cases hn₁ : Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)
  · by_cases hn₂ : Z R z ≤ normalizer ((Z R (act R x d) ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)
    · have hthird := ChapterC.Sp4Four.DistanceReduction.paired_endpoint_normalizes_first_join x hxS hn₂
      have hJ : LocalPackage.J R d t ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) :=
        (LocalPackage.J_le_radical R d t).trans
          (ChapterC.Sp4Four.DistanceReduction.edge_normalizes_neighbor_seed_join hat hdt)
      have he := c.original_normal_neighbor_join_moving_index_eq_one eK geometry (by change 2 < geometry.b R; omega)
        path.start_color hat hdt (hgen.trans (sup_le (sup_le hJ hn₁) hthird))
      change (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) = 1 at he
      omega
    · have hfix : act R x a = a := hxS
      have hat₂ : Adjacent R a (act R x t) := by
        rw [←hfix]
        exact (adjacent_act_iff R x _ _).mpr hat
      have hdt₂ := (adjacent_act_iff R x _ _).mpr hdt
      have heq₂ : LocalPackage.J R (act R x d) (act R x t) = LocalPackage.J R a (act R x t) := by
        rw [←hfix,smallMoverJoin_act,smallMoverJoin_act,heq]
      have hbackd : act R x⁻¹ (act R x d) = d := by rw [←act_mul,mul_inv_cancel,act_one]
      have hbackt : act R x⁻¹ (act R x t) = t := by rw [←act_mul,mul_inv_cancel,act_one]
      have hLa : (Ltilde R a).map (MulAut.conj x⁻¹).toMonoidHom = Ltilde R a :=
        mem_normalizer_iff_map_conj_eq.mp ((Ltilde R a).le_normalizer ((Ltilde R a).inv_mem hx))
      have hgen₂ := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hgen
      rw [hLa,Subgroup.map_sup,Subgroup.map_sup,←smallMoverJoin_act,←Z_act,←Z_act,
        ←act_mul,inv_mul_cancel,act_one] at hgen₂
      have hgen₂' : Ltilde R a ≤ (LocalPackage.J R (act R x d) (act R x t) ⊔ Z R z) ⊔
          Z R (act R (x⁻¹)⁻¹ z) := by
        simpa only [inv_inv,sup_right_comm] using hgen₂
      have hsep₂ : ((Z R a ⊓ centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) ⊓
          centralizer (LocalPackage.J R (act R x⁻¹ (act R x d)) (act R x⁻¹ (act R x t)) : Set (FreeAmalgam R))) = ⊥ := by
        rw [hbackd,hbackt,inf_right_comm]
        exact hsep
      have hmove₂ : 4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex
          (U R (act R x d)) := by
        rwa [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega) path.start_color x hxS]
      have hh := c.original_equal_mover_paired_backward_path eK geometry hb path hat₂ hdt₂ heq₂ hX
        ha4 hz4 x⁻¹ ((stabilizer R a).inv_mem hxS) hn₂ hgen₂' hsep₂ hmove₂
      rw [hbackd,hbackt] at hh
      exact hh.symm
  · exact c.original_equal_mover_paired_backward_path eK geometry hb path hat hdt heq hX
      ha4 hz4 x hxS hn₁ hgen hsep hmove

/-- Apply the paired-kernel calculation to the original simultaneous
source-generator selection, preserving the selected edge and path overlap. -/
theorem original_equal_mover_strict_backward_selection
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      (Q R a).relIndex (Z R z) = 4 → (Q R z).relIndex (Z R a) = 4 → X R a = Z R a →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
        let d₁ := act R g⁻¹ d
        let t₁ := act R g⁻¹ t
        Adjacent R a t₁ ∧ Adjacent R d₁ t₁ ∧
        ((∃ back : CriticalPath R geometry d₁ (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t₁ ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∨
        (∃ back : CriticalPath R geometry (act R x d₁) (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=act R x t₁ ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i)) := by
  intro R geometry hb a z d t path hat hdt heq hza haz hX hmove
  obtain ⟨g,hg,x,hx,hat₁,hdt₁,hgen,hindex,hsep⟩ :=
    c.original_equal_mover_root_separated_selection eK geometry hb path hat hdt heq hza haz
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hfix : act R g⁻¹ a = a := hgS
  have heq₁ : LocalPackage.J R (act R g⁻¹ d) (act R g⁻¹ t) = LocalPackage.J R a (act R g⁻¹ t) := by
    rw [←hfix,smallMoverJoin_act,smallMoverJoin_act,heq]
  refine ⟨g,hg,x,hx,hat₁,hdt₁,?_⟩
  exact c.original_equal_mover_pair_backward_path eK geometry hb path hat₁ hdt₁ heq₁ hX
    haz hza x hx hgen hsep (hindex ▸ hmove)


/-- The original equal-mover branch of (5.7), with the root indices,
common root and all selected normalization premises discharged. The only
remaining local premises are equality of the movers and strict movement. -/
theorem original_backward_path_of_equal_strict_mover
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      ∃ d' t', Adjacent R a t' ∧ Adjacent R d' t' ∧
        (∃ back : CriticalPath R geometry d' (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t' ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry hb a z d t path hat hdt heq hmove
  rcases c.original_radius_displacement_or_root eK geometry path with hdisp | ⟨haz,hza,hXa,_⟩
  · exact c.original_backward_path_of_radius_displacement eK geometry path hat hdisp
  obtain ⟨g,hg,x,hx,hat₁,hdt₁,hback | hback⟩ :=
    c.original_equal_mover_strict_backward_selection eK geometry hb path hat hdt heq hza haz hXa hmove
  · refine ⟨act R g⁻¹ d,act R g⁻¹ t,hat₁,hdt₁,hback,?_⟩
    intro hV
    obtain ⟨back,_,_⟩ := hback
    exact back.critical.2 ((le_sup_left.trans
      (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat₁ hdt₁)).trans hV)
  · have hfix : act R x a = a := Ltilde_le_stabilizer a hx
    have hat₂ : Adjacent R a (act R x (act R g⁻¹ t)) := by
      rw [←hfix]
      exact (adjacent_act_iff R x _ _).mpr hat₁
    have hdt₂ := (adjacent_act_iff R x _ _).mpr hdt₁
    refine ⟨act R x (act R g⁻¹ d),act R x (act R g⁻¹ t),hat₂,hdt₂,hback,?_⟩
    intro hV
    obtain ⟨back,_,_⟩ := hback
    exact back.critical.2 ((le_sup_left.trans
      (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat₂ hdt₂)).trans hV)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
