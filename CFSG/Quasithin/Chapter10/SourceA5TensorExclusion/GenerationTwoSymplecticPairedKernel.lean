module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticSelectedMovement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalPairedDisplacement
/-!
# The original paired hyperplane kernel

For an equal-mover selected pair in the truncated kernel, the two movers'
zero common fixed seed forces the mate to centralize the critical hyperplane.
The full natural marking then puts its endpoint displacement in the starting
seed. Conjugating this equality gives the third source generator's
normalization of the first selected kernel. That kernel lies in the original
B-layer and bounds the first moving index by four.

Thus strict movement produces one of the two original overlapping backward
paths when the first join escapes endpoint normalization. No normalization
condition is imposed on its mate. Source: MS93 (5.7), p.919, using (3.3)(ii);
Aschbacher--Smith 9.3.10, p.734. The selection consumer is
GenerationTwoSymplecticPairedSelection; the distance exclusions remain separate.
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


/-- Both selected seeds in the truncated kernel have one common hyperplane
root; the separated pair forces the mate to centralize that hyperplane. -/
theorem original_equal_mover_mate_centralizes_hyperplane
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t → X R a = Z R a →
      ∀ x ∈ stabilizer R a,
      Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      Z R (act R x d) ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
        centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ →
      ⁅Z R (act R x d),Z R z ⊓ Q R a⁆ = ⊥ := by
  intro R geometry hb a z d t path hat hdt heq hX x hx hk₁ hk₂ hbad hsep
  let A := Z R z ⊓ Q R a
  let Y := (Z R d ⊔ Z R (act R x d)) ⊔ Z R a
  let Y₀ := V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))
  have hZa₀ : Z R a ≤ Y₀ := by
    apply le_inf (Z_le_VBall R a 2)
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a path.start_color)
    rw [geometry.distance_constant a path.start_color,path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hYV : Y ≤ V R a := sup_le
    (ChapterC.Sp4Four.DistanceReduction.paired_seed_le_radius hat hdt x hx) (Z_le_VBall R a 2)
  have hY₀ : Y ≤ Y₀ := le_inf hYV (sup_le (sup_le hk₁ hk₂) (hZa₀.trans inf_le_right))
  have hYQ := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hYZ := hY₀.trans (truncated_radius_le_endpoint_stabilizer path (by omega))
  have hdisp : ⁅Z R d ⊔ Z R (act R x d),A⁆ ≤ Z R a :=
    (commutator_mono le_rfl inf_le_right).trans
      (c.original_equal_mover_pair_displacement eK geometry hb path.start_color hat hdt heq hX x hx)
  have hZaA : ⁅Z R a,A⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono le_rfl inf_le_right).trans (geometry.centralizes a path.start_color).le)
  have hbound : ⁅Y,A⁆ ≤ Z R a :=
    commutator_sup_le_of_relative_normal (V R a) (Z R d ⊔ Z R (act R x d)) (Z R a) A (Z R a)
      ((geometry.V_le_Q (by omega) a path.start_color).trans
        ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Z_normalized R a)))
      (ChapterC.Sp4Four.DistanceReduction.paired_seed_le_radius hat hdt x hx)
      (Z_le_VBall R a 2) hdisp (hZaA ▸ bot_le)
  have hn : ¬ ⁅Y,Z R z⁆ ≤ Z R a := by
    intro h
    apply hbad
    apply le_normalizer_iff_commutator_le_left.mpr
    exact ((commutator_mono (sup_le (le_sup_left.trans le_sup_left) le_sup_right) le_rfl).trans h).trans le_sup_right
  have hn₀ : ¬ ⁅Y₀,Z R z⁆ ≤ Z R a := fun h => hn ((commutator_mono hY₀ le_rfl).trans h)
  obtain h | ⟨ha4,hz4,_,_⟩ := c.original_radius_displacement_or_root eK geometry path
  · exact (hn₀ h).elim
  obtain ⟨F,hF,f,hf,hr,π,hπ⟩ := c.original_truncated_radius_root_action eK geometry path ha4 hz4
  let fY := f.comp (inclusion hY₀)
  have hfY : fY.ker = (Q R z).subgroupOf Y := by
    ext y
    change f (inclusion hY₀ y) = 1 ↔ y.val ∈ Q R z
    change inclusion hY₀ y ∈ f.ker ↔ _
    rw [hf]
    rfl
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hCa : C R a = Q R a := C_eq_Q R hodd.isPGroup hodd.twoCore_le hfaith a path.start_color
  obtain ⟨_,hcard,hdich⟩ := critical_root_kernel_commutator_of_displacement path hb hCa
    (c.original_Z_eq_U z path.end_color) Y hYQ le_sup_right hYZ hYV fY hfY
    (fun y hy => hr (inclusion hY₀ y) hy) π (fun y u => hπ (inclusion hY₀ y) u) hbound hn
  rcases hdich (Z R (act R x d)) (le_sup_right.trans le_sup_left) with hzero | hroot
  · exact hzero
  exfalso
  have hfirst := c.original_neighbor_small_movers_centralize_root eK geometry hb path hat hdt hk₁ hbad
  have hfix : act R x a = a := hx
  have hat₂ : Adjacent R a (act R x t) := by
    rw [←hfix]
    exact (adjacent_act_iff R x _ _).mpr hat
  have hdt₂ := (adjacent_act_iff R x _ _).mpr hdt
  have heq₂ : LocalPackage.J R (act R x d) (act R x t) = LocalPackage.J R a (act R x t) := by
    rw [←hfix,smallMoverJoin_act,smallMoverJoin_act,heq]
  have hd₂ : color R (act R x d) = false := by
    have hh := adjacent_color_ne R hat₂
    have hh' := adjacent_color_ne R hdt₂
    rw [path.start_color] at hh
    cases hdc : color R (act R x d) <;> cases htc : color R (act R x t) <;> simp_all
  have hAJ : A ≤ LocalPackage.J R (act R x d) (act R x t) := inf_le_right.trans
    (heq₂ ▸ LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le path.start_color hat₂)
  have hsecond : ⁅Z R a,Z R z⁆ ≤ centralizer
      (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R)) := by
    rw [←hroot,commutator_comm]
    exact (commutator_mono hAJ le_rfl).trans (c.original_edge_mover_quadratic eK hd₂ hdt₂)
  have hzero : ⁅Z R a,Z R z⁆ = ⊥ := le_bot_iff.mp (hsep ▸
    le_inf (le_inf (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path) hfirst) hsecond)
  rw [hzero,F.card_eq,hF] at hcard
  norm_num at hcard

/-- Centralizing the literal critical hyperplane forces all endpoint
displacement of the neighboring join into the starting seed. -/
theorem original_neighbor_displacement_of_central_hyperplane
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      (Q R z).relIndex (Z R a) = 4 → (Q R a).relIndex (Z R z) = 4 →
      Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      ⁅Z R d,Z R z ⊓ Q R a⁆ = ⊥ →
      ⁅Z R d ⊔ Z R a,Z R z⁆ ≤ Z R a := by
  intro R geometry hb a z d t path hat hdt ha4 hz4 hk hzero
  let Y := Z R d ⊔ Z R a
  let Y₀ := V R a ⊓ Q R (path.walk.getVert (path.walk.length-2))
  have hZa₀ : Z R a ≤ Y₀ := by
    apply le_inf (Z_le_VBall R a 2)
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a path.start_color)
    rw [geometry.distance_constant a path.start_color,path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hYV : Y ≤ V R a := ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt
  have hY₀ : Y ≤ Y₀ := le_inf hYV (sup_le hk (hZa₀.trans inf_le_right))
  have hYZ := hY₀.trans (truncated_radius_le_endpoint_stabilizer path (by omega))
  obtain ⟨F,hF,f,hf,hr,π,hπ⟩ := c.original_truncated_radius_root_action eK geometry path ha4 hz4
  let fY := f.comp (inclusion hY₀)
  have hfY : fY.ker = (Q R z).subgroupOf Y := by
    ext y
    change f (inclusion hY₀ y) = 1 ↔ y.val ∈ Q R z
    change inclusion hY₀ y ∈ f.ker ↔ _
    rw [hf]
    rfl
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hCa : C R a = Q R a := C_eq_Q R hodd.isPGroup hodd.twoCore_le hfaith a path.start_color
  have hcent := critical_root_hyperplane_centralizer path (by omega) hCa
    (c.original_Z_eq_U z path.end_color) Y le_sup_right hYZ fY hfY
    (fun y hy => hr (inclusion hY₀ y) hy) π (fun y u => hπ (inclusion hY₀ y) u)
    (by rw [F.card_eq,hF]; exact ha4)
  have hcentral : Y ≤ centralizer ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _) :=
    sup_le (commutator_eq_bot_iff_le_centralizer.mp hzero)
      ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes a path.start_color)).trans
        (centralizer_le inf_le_right))
  have hY : Y ≤ Z R a ⊔ (Y ⊓ Q R z) := (le_inf le_rfl hcentral).trans_eq hcent
  have hQ : Y ≤ Q R a := hYV.trans (geometry.V_le_Q (by omega) a path.start_color)
  have hcomm : ⁅Y ⊓ Q R z,Z R z⁆ = ⊥ := by
    rw [commutator_comm]
    exact le_bot_iff.mp ((commutator_mono le_rfl inf_le_right).trans (geometry.centralizes z path.end_color).le)
  exact (commutator_mono hY le_rfl).trans
    (commutator_sup_le_of_relative_normal (Q R a) (Z R a) (Y ⊓ Q R z) (Z R z) (Z R a)
      ((show Q R a ≤ stabilizer R a from fun _ hx => hx.1).trans (Z_normalized R a))
      (le_sup_right.trans hQ) (inf_le_left.trans hQ)
      (ChapterC.Sp4Four.SourceComparison.critical_commutator_le_start_seed path) (hcomm ▸ bot_le))


/-- The formerly normalized-mate branch supplies the third kernel
normalizer, so the original selected moving index is at most four. -/
theorem original_equal_mover_paired_kernel_index
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t → X R a = Z R a →
      (Q R z).relIndex (Z R a) = 4 → (Q R a).relIndex (Z R z) = 4 →
      ∀ x ∈ stabilizer R a,
      Z R d ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      Z R (act R x d) ≤ Q R (path.walk.getVert (path.walk.length-2)) →
      ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) →
      ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
        centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ →
      (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) ≤ 4 := by
  intro R geometry hb a z d t path hat hdt heq hX ha4 hz4 x hx hk₁ hk₂ hbad hgen hsep
  have hzero := c.original_equal_mover_mate_centralizes_hyperplane eK geometry hb path
    hat hdt heq hX x hx hk₁ hk₂ hbad hsep
  have hfix : act R x a = a := hx
  have hat₂ : Adjacent R a (act R x t) := by
    rw [←hfix]
    exact (adjacent_act_iff R x _ _).mpr hat
  have hdt₂ := (adjacent_act_iff R x _ _).mpr hdt
  have hdisp := c.original_neighbor_displacement_of_central_hyperplane eK geometry hb path
    hat₂ hdt₂ ha4 hz4 hk₂ hzero
  have hZaMap : (Z R a).map (MulAut.conj x).toMonoidHom = Z R a :=
    mem_normalizer_iff_map_conj_eq.mp ((Z_normalized R a) hx)
  have hdMap : (Z R (act R x d)).map (MulAut.conj x).toMonoidHom = Z R d := by
    have hh := Z_act R x⁻¹ (act R x d)
    rw [←act_mul,mul_inv_cancel,act_one] at hh
    simpa only [inv_inv] using hh.symm
  have heMap : (Z R z).map (MulAut.conj x).toMonoidHom = Z R (act R x⁻¹ z) := by
    simpa only [inv_inv] using (Z_act R x⁻¹ z).symm
  have hback := map_mono (f := (MulAut.conj x).toMonoidHom) hdisp
  rw [map_commutator,Subgroup.map_sup,hZaMap,hdMap,heMap] at hback
  let H := (Z R d ⊓ centralizer ((Z R z ⊓ Q R a : Subgroup (FreeAmalgam R)) : Set _)) ⊔ Z R a
  have hH : H ≤ Z R d ⊔ Z R a := sup_le_sup inf_le_left le_rfl
  have hn : Z R (act R x⁻¹ z) ≤ normalizer (H : Set (FreeAmalgam R)) :=
    le_normalizer_iff_commutator_le_left.mpr (((commutator_mono hH le_rfl).trans hback).trans le_sup_right)
  have hJ := c.original_neighbor_small_movers_normalize_kernel eK geometry hb path hat hdt hk₁ hbad
  apply c.original_neighbor_moving_index_le_four_of_generator eK geometry hb path hat hdt hk₁ hbad
    (LocalPackage.J R d t ⊔ Z R (act R x⁻¹ z))
  · simpa only [sup_assoc,sup_comm,sup_left_comm] using hgen
  · exact sup_le hJ hn

/-- If the first selected join escapes endpoint normalization, strict
movement now produces one of the two literal backward paths without any
normalization condition on its mate. -/
theorem original_equal_mover_paired_backward_path
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t → X R a = Z R a →
      (Q R z).relIndex (Z R a) = 4 → (Q R a).relIndex (Z R z) = 4 →
      ∀ x ∈ stabilizer R a,
      ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
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
  intro R geometry hb a z d t path hat hdt heq hX ha4 hz4 x hx hbad hgen hsep hmove
  by_cases hk₁ : Z R d ≤ Q R (path.walk.getVert (path.walk.length-2))
  · by_cases hk₂ : Z R (act R x d) ≤ Q R (path.walk.getVert (path.walk.length-2))
    · exact (not_le_of_gt hmove (c.original_equal_mover_paired_kernel_index eK geometry hb path
        hat hdt heq hX ha4 hz4 x hx hk₁ hk₂ hbad hgen hsep)).elim
    · have hfix : act R x a = a := hx
      have hat₂ : Adjacent R a (act R x t) := by
        rw [←hfix]
        exact (adjacent_act_iff R x _ _).mpr hat
      exact Or.inr (ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le geometry
        (by omega) path hat₂ ((adjacent_act_iff R x _ _).mpr hdt) hk₂)
  · exact Or.inl (ChapterC.Sp4Four.DistanceReduction.exists_backward_path_of_not_le geometry
      (by omega) path hat hdt hk₁)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
