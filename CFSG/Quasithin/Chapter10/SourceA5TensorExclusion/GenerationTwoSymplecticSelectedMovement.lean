module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticSelectedGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSelectedMovement

/-!
# The original selected movers fix the common root

The canonical order-64 edge mover fixes every small displacement on the
neighboring natural seed. The existing original root comparison identifies
this displacement with the critical commutator. Applied to a separated
pair, its two movers cannot both fix that nontrivial common root.

This uses the full original natural marking and central kernel. The
remaining selected-pair alternatives and distance exclusions are separate.
Source: MS93 (5.7), printed p.919; Aschbacher--Smith 9.3.10, p.734.
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

/-- The entire canonical edge mover acts quadratically on the original
natural seed, including the full action kernel. -/
theorem original_edge_mover_quadratic
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {d t : Vertex R}, color R d = false → Adjacent R d t →
      ⁅LocalPackage.J R d t,Z R d⁆ ≤
        centralizer (LocalPackage.J R d t : Set (FreeAmalgam R)) := by
  intro R d t hd hdt
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
  have hfixed : U R d ⊓ centralizer (Ltilde R d : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hcore : x ∈ fixedCore R d := ⟨
      ((U_le_Z d).trans (geometry.omega_bound d hd
        (by
          rw [geometry.distance_constant d hd]
          change 0 < geometry.b R
          exact hpos)) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot d hd] at hcore
  have hQt : IsPGroup 2 (Q R t) := by
    obtain ⟨i,_,_,hiT,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le hd hdt
    rw [←hiT]
    exact hodd.isPGroup.map i
  have hindices := (c.original_small_mover_join_indices eK hd hdt).2
  rw [c.original_Z_eq_U d hd]
  exact original_large_small_mover_centralizes_commutator R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq hd hfixed (Q R t) (LocalPackage.J R d t) (LocalPackage.J R d t) hQt
    (fun _ hx => hx.2 d (adjacent_symm R hdt)) (LocalPackage.J_le_radical R d t)
    (LocalPackage.J_le_radical R d t) hindices.1 hindices.2.le (Or.inr le_rfl)

/-- In the equal-mover branch the original neighborhood kernel moves the
neighboring seed only into X_a. In the root branch this is exactly Z_a. -/
theorem original_equal_mover_displacement_le_X
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 2 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false →
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t → ⁅Z R d,Q R a⁆ ≤ X R a := by
  intro R geometry hb a d t ha hat hdt heq
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [ha] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hQaJ : Q R a ≤ LocalPackage.J R d t := heq ▸
    LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le ha hat
  have hZdQa : Z R d ≤ Q R a :=
    (le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)).trans
      (geometry.V_le_Q hb a ha)
  have hcomm : ⁅Z R d,Q R a⁆ ≤ centralizer (Q R a : Set (FreeAmalgam R)) := by
    rw [commutator_comm]
    exact ((commutator_mono hQaJ le_rfl).trans
      (c.original_edge_mover_quadratic eK hd hdt)).trans (centralizer_le hQaJ)
  have hZd : ⁅Z R d,Q R a⁆ ≤ Z R d :=
    le_normalizer_iff_commutator_le_left.mp
      ((hQaJ.trans (LocalPackage.J_le_radical R d t)).trans
        ((show Q R t ≤ stabilizer R d from fun _ hx => hx.2 d (adjacent_symm R hdt)).trans
          (Z_normalized R d)))
  let := geometry.Z_elementary (by omega) d hd
  intro x hx
  exact mem_omegaCenter_iff.mpr ⟨hZdQa (hZd hx),
    elemPow_eq_one_of_isElementaryAbelian x (hZd hx),hcomm hx⟩

/-- The paired equal movers supply the exact starting-seed displacement
used in the common-root calculation of (5.7). -/
theorem original_equal_mover_pair_displacement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a d t : Vertex R}, color R a = false →
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t → X R a = Z R a →
      ∀ x ∈ stabilizer R a, ⁅Z R d ⊔ Z R (act R x d),Q R a⁆ ≤ Z R a := by
  intro R geometry hb a d t ha hat hdt heq hX x hx
  have hfix : act R x a = a := hx
  have hatx : Adjacent R a (act R x t) := by
    rw [←hfix]
    exact (adjacent_act_iff R x _ _).mpr hat
  have hdtx := (adjacent_act_iff R x _ _).mpr hdt
  have heqx : LocalPackage.J R (act R x d) (act R x t) = LocalPackage.J R a (act R x t) := by
    rw [←hfix,smallMoverJoin_act,smallMoverJoin_act,heq]
  have h₁ := c.original_equal_mover_displacement_le_X eK geometry (by change 2 < geometry.b R; omega) ha hat hdt heq
  have h₂ := c.original_equal_mover_displacement_le_X eK geometry (by change 2 < geometry.b R; omega) ha hatx hdtx heqx
  rw [hX] at h₁ h₂
  exact commutator_sup_le_of_relative_normal (V R a) (Z R d) (Z R (act R x d))
    (Q R a) (Z R a)
    ((geometry.V_le_Q (by omega) a ha).trans
      ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Z_normalized R a)))
    (le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt))
    (le_sup_left.trans (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hatx hdtx)) h₁ h₂

/-- The original canonical mover fixes the common critical root, not
just its image modulo a central kernel. -/
theorem original_neighbor_small_movers_centralize_root
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      ⁅Z R a,Z R z⁆ ≤ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R)) := by
  intro R geometry hb a z d t path hat hdt hcontained hbad
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
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [path.start_color] at h
    cases he : color R t <;> simp_all
  have hd : color R d = false := by
    have h := adjacent_color_ne R hdt
    rw [ht] at h
    cases he : color R d <;> simp_all
  let A := Z R z ⊓ Q R a
  have hfixed : U R d ⊓ centralizer (Ltilde R d : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hcore : x ∈ fixedCore R d := ⟨
      ((U_le_Z d).trans (geometry.omega_bound d hd
        (by
          rw [geometry.distance_constant d hd]
          change 0 < geometry.b R
          omega)) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot d hd] at hcore
  have hsmall : (centralizer (A : Set (FreeAmalgam R))).relIndex (U R d) ≤ 4 := by
    rw [←c.original_Z_eq_U d hd]
    exact c.original_neighbor_kernel_centralizer_index eK geometry hb path hat hdt hcontained hbad
  have hQt : IsPGroup 2 (Q R t) := by
    obtain ⟨i,_,_,hiT,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le hd hdt
    rw [←hiT]
    exact hodd.isPGroup.map i
  have hindices := (c.original_small_mover_join_indices eK hd hdt).2
  have hJ := original_large_small_mover_centralizes_commutator R hms hodd.isPGroup hne
    hodd.twoCore_le hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq hd hfixed (Q R t) (LocalPackage.J R d t) A hQt
    (fun _ hx => hx.2 d (adjacent_symm R hdt)) (LocalPackage.J_le_radical R d t)
    (inf_le_right.trans (Q_le_adjacent_h R ht hat)) hindices.1 hindices.2.le (Or.inl hsmall)
  rw [←c.original_Z_eq_U d hd,commutator_comm] at hJ
  rw [(c.original_neighbor_kernel_commutator eK geometry hb path hat hdt hcontained hbad).1] at hJ
  exact hJ

/-- A separated pair with both joins escaping normalization cannot lie in
the truncated original kernel. One of its literal backward critical paths
therefore exists, with the selected common edge and overlap retained. -/
theorem original_separated_roots_backward_path
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d₁ t₁ d₂ t₂ : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t₁ → Adjacent R d₁ t₁ → Adjacent R a t₂ → Adjacent R d₂ t₂ →
      ¬ Z R z ≤ normalizer ((Z R d₁ ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      ¬ Z R z ≤ normalizer ((Z R d₂ ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      ((Z R a ⊓ centralizer (LocalPackage.J R d₁ t₁ : Set (FreeAmalgam R))) ⊓
        centralizer (LocalPackage.J R d₂ t₂ : Set (FreeAmalgam R))) = ⊥ →
      (∃ back : CriticalPath R geometry d₁ (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1=t₁ ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∨
      (∃ back : CriticalPath R geometry d₂ (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1=t₂ ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) := by
  intro R geometry hb a z d₁ t₁ d₂ t₂ path hat₁ hdt₁ hat₂ hdt₂ hn₁ hn₂ hsep
  by_cases hk₁ : Z R d₁ ≤ Q R (path.walk.getVert (path.walk.length-2))
  · by_cases hk₂ : Z R d₂ ≤ Q R (path.walk.getVert (path.walk.length-2))
    · have h₁ := c.original_neighbor_small_movers_centralize_root eK geometry hb path hat₁ hdt₁ hk₁ hn₁
      have h₂ := c.original_neighbor_small_movers_centralize_root eK geometry hb path hat₂ hdt₂ hk₂ hn₂
      have hroot : ⁅Z R a,Z R z⁆ = ⊥ := le_bot_iff.mp (hsep ▸
        le_inf (le_inf (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path) h₁) h₂)
      have hc := c.original_neighbor_kernel_commutator eK geometry hb path hat₁ hdt₁ hk₁ hn₁
      have hcard := hc.2
      rw [hc.1,hroot] at hcard
      norm_num at hcard
    · exact Or.inr (ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
        geometry (by omega) path hat₂ hdt₂ hk₂)
  · exact Or.inl (ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le
      geometry (by omega) path hat₁ hdt₁ hk₁)
/-- The actual equal-mover source selection now retains its paired
starting-seed displacement. If both paired joins escape endpoint normalization,
one of the selected overlapping backward paths exists. -/
theorem original_equal_mover_selected_paths
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      (Q R a).relIndex (Z R z) = 4 → (Q R z).relIndex (Z R a) = 4 → X R a = Z R a →
      ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
        let d₁ := act R g⁻¹ d
        let t₁ := act R g⁻¹ t
        let d₂ := act R x d₁
        let t₂ := act R x t₁
        Adjacent R a t₁ ∧ Adjacent R d₁ t₁ ∧ Adjacent R a t₂ ∧ Adjacent R d₂ t₂ ∧
        Ltilde R a ≤ (LocalPackage.J R d₁ t₁ ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) ∧
        (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d₁) =
          (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) ∧
        ⁅Z R d₁ ⊔ Z R d₂,Z R z ⊓ Q R a⁆ ≤ Z R a ∧
        ((∃ back : CriticalPath R geometry d₁ (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t₁ ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∨
        (∃ back : CriticalPath R geometry d₂ (path.walk.getVert (path.walk.length-2)),
          back.walk.getVert 1=t₂ ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∨
        Z R z ≤ normalizer ((Z R d₁ ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) ∨
        Z R z ≤ normalizer ((Z R d₂ ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)) := by
  intro R geometry hb a z d t path hat hdt heq hza haz hX
  obtain ⟨g,hg,x,hx,hat₁,hdt₁,hgen,hmove,hsep⟩ :=
    c.original_equal_mover_root_separated_selection eK geometry hb path hat hdt heq hza haz
  let d₁ := act R g⁻¹ d
  let t₁ := act R g⁻¹ t
  have hxS : x ∈ stabilizer R a := Ltilde_le_stabilizer a hx
  have hfix : act R x a = a := hxS
  have hat₂ : Adjacent R a (act R x t₁) := by
    rw [←hfix]
    exact (adjacent_act_iff R x _ _).mpr hat₁
  have hdt₂ := (adjacent_act_iff R x _ _).mpr hdt₁
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hgfix : act R g⁻¹ a = a := hgS
  have heq₁ : LocalPackage.J R d₁ t₁ = LocalPackage.J R a t₁ := by
    change LocalPackage.J R (act R g⁻¹ d) (act R g⁻¹ t) = _
    rw [←hgfix,smallMoverJoin_act,smallMoverJoin_act,heq]
  have hdisp := c.original_equal_mover_pair_displacement eK geometry hb path.start_color
    hat₁ hdt₁ heq₁ hX x hxS
  refine ⟨g,hg,x,hx,hat₁,hdt₁,hat₂,hdt₂,hgen,hmove,
    (commutator_mono le_rfl inf_le_right).trans hdisp,?_⟩
  by_cases hn₁ : Z R z ≤ normalizer ((Z R d₁ ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)
  · exact Or.inr (Or.inr (Or.inl hn₁))
  by_cases hn₂ : Z R z ≤ normalizer ((Z R (act R x d₁) ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _)
  · exact Or.inr (Or.inr (Or.inr hn₂))
  rcases c.original_separated_roots_backward_path eK geometry hb path hat₁ hdt₁ hat₂ hdt₂
    hn₁ hn₂ hsep with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
