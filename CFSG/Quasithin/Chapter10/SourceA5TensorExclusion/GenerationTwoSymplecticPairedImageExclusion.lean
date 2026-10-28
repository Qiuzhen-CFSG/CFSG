module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticPairedImages
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalGeneratedRootMovement

/-!
# Excluding the order-four image of the original separated pair

The three selected residual generators prevent the critical commutator
from being fixed by either canonical mover. The hyperplane comparison
therefore forces endpoint displacement of each complete backward kernel,
joined with the starting seed, into that seed.

If the paired image had order four, exactly one seed would be backward
critical and its whole mate would lie in the truncated kernel. The mate's
displacement, conjugated back, supplies the third generator's normalization
of the full critical-kernel join. Its canonical mover and the original
endpoint also normalize that join, contradicting the already proved
residual nonnormality. Thus the same selected pair has image at least
sixteen, with both kernel displacements, the full kernel splitting, image
product and every original path-overlap vertex retained.

Source: MS93 (3.3)(ii), (5.6)--(5.11), pp.867,917--924; Aschbacher--Smith
9.3.10, pp.734--735. The stronger radius bound, both original distance
exclusions and SymplecticPlaneRecognition remain to be proved.
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

theorem original_generated_critical_root_not_fixed
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → (Q R a).relIndex (Z R z) = 4 → (Q R z).relIndex (Z R a) = 4 →
      ∀ x ∈ Ltilde R a,
      Ltilde R a ≤ (LocalPackage.J R a t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) →
      ¬ ⁅Z R a,Z R z⁆ ≤ centralizer (LocalPackage.J R a t : Set (FreeAmalgam R)) := by
  intro R geometry a z t path hat hza haz x hx hgen hbad
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
  apply original_generated_root_not_centralized R hms hodd.isPGroup hne hodd.twoCore_le
    hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path hb hza haz hfixed (LocalPackage.J R a t)
    ((LocalPackage.J_le_radical R a t).trans (fun _ hx => hx.2 a (adjacent_symm R hat)))
    (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le path.start_color hat)
    (hQt.to_le (LocalPackage.J_le_radical R a t)) hindices.2.1 hindices.2.2.le
    (by rw [←c.original_Z_eq_U a path.start_color]; exact c.original_edge_mover_quadratic eK path.start_color hat)
    x hx (by simpa only [Z_act,inv_inv] using hgen)
  rwa [←c.original_Z_eq_U a path.start_color,commutator_comm]

private theorem original_truncated_section_root_of_escape
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z)
        (Y : Subgroup (FreeAmalgam R)),
      Z R a ≤ Y → Y ≤ V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)) →
      ⁅Y,Z R z ⊓ Q R a⁆ ≤ Z R a → ¬ ⁅Y,Z R z⁆ ≤ Z R a →
      ⁅Y,Z R z ⊓ Q R a⁆ = ⁅Z R a,Z R z⁆ := by
  intro R geometry hb a z path Y hZa hY hbound hbad
  have hn : ¬ ⁅V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)),Z R z⁆ ≤ Z R a :=
    fun h => hbad ((commutator_mono hY le_rfl).trans h)
  obtain h | ⟨ha4,hz4,_,_⟩ := c.original_radius_displacement_or_root eK geometry path
  · exact (hn h).elim
  obtain ⟨F,hF,f,hf,hr,π,hπ⟩ := c.original_truncated_radius_root_action eK geometry path ha4 hz4
  let fY := f.comp (inclusion hY)
  have hfY : fY.ker = (Q R z).subgroupOf Y := by
    ext y
    change f (inclusion hY y) = 1 ↔ y.val ∈ Q R z
    change inclusion hY y ∈ f.ker ↔ _
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
  exact (critical_root_kernel_commutator_of_displacement path hb hCa
    (c.original_Z_eq_U z path.end_color) Y
    (hY.trans (inf_le_left.trans (geometry.V_le_Q (by omega) a path.start_color))) hZa
    (hY.trans (truncated_radius_le_endpoint_stabilizer path (by omega)))
    (hY.trans inf_le_left) fY hfY (fun y hy => hr (inclusion hY y) hy)
    π (fun y u => hπ (inclusion hY y) u) hbound hbad).1

/-- The selected three generators force endpoint displacement of the
complete backward kernel into the original starting seed. -/
theorem original_equal_mover_generated_kernel_displacement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      ∀ x ∈ Ltilde R a,
      Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) →
      ⁅(Z R d ⊓ Q R (path.walk.getVert (path.walk.length-2))) ⊔ Z R a,Z R z⁆ ≤ Z R a := by
  intro R geometry hb a z d t path hat hdt heq x hx hgen
  let w := path.walk.getVert (path.walk.length-2)
  let K := Z R d ⊓ Q R w
  let Y := K ⊔ Z R a
  let A := Z R z ⊓ Q R a
  by_contra hn
  change ¬ ⁅Y,Z R z⁆ ≤ Z R a at hn
  have hZaQ : Z R a ≤ Q R w := by
    apply Z_le_Q_of_dist_lt R a (geometry.exists_critical a path.start_color)
    rw [geometry.distance_constant a path.start_color,path.dist_start (Nat.sub_le _ _),path.length_eq_b]
    change geometry.b R-2 < geometry.b R
    omega
  have hYV : Y ≤ V R a := (sup_le_sup inf_le_left le_rfl).trans
    (ChapterC.Sp4Four.DistanceReduction.neighbor_seed_join_le_radius hat hdt)
  have hY : Y ≤ V R a ⊓ Q R w := le_inf hYV (sup_le inf_le_right hZaQ)
  have hbad : ¬ ⁅V R a ⊓ Q R w,Z R z⁆ ≤ Z R a :=
    fun h => hn ((commutator_mono hY le_rfl).trans h)
  obtain h | ⟨ha4,hz4,hX,_⟩ := c.original_radius_displacement_or_root eK geometry path
  · exact hbad h
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [path.start_color] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  obtain ⟨hodd,_⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  have hAJ : A ≤ LocalPackage.J R d t := inf_le_right.trans
    (heq ▸ LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le path.start_color hat)
  let P := Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))
  have hKP : ⁅K,A⁆ ≤ P := le_inf
    ((commutator_mono inf_le_left inf_le_right).trans
      ((c.original_equal_mover_displacement_le_X eK geometry (by change 2 < geometry.b R; omega)
        path.start_color hat hdt heq).trans_eq hX))
    (by
      rw [commutator_comm]
      exact (commutator_mono hAJ inf_le_left).trans
        (c.original_edge_mover_quadratic eK hd hdt))
  have hZaA : ⁅Z R a,A⁆ = ⊥ := le_bot_iff.mp
    ((commutator_mono le_rfl inf_le_right).trans (geometry.centralizes a path.start_color).le)
  have hVP : V R a ≤ normalizer (P : Set (FreeAmalgam R)) :=
    ((le_centralizer_iff_isMulCommutative.mpr (V_abelian_of_four_lt R path.start_color hb)).trans
      (centralizer_le (inf_le_left.trans (Z_le_VBall R a 2)))).trans (Subgroup.centralizer_le_normalizer _)
  have hYP : ⁅Y,A⁆ ≤ P := commutator_sup_le_of_relative_normal (V R a) K (Z R a) A P
    hVP (le_sup_left.trans hYV) (Z_le_VBall R a 2) hKP (hZaA ▸ bot_le)
  have hroot := c.original_truncated_section_root_of_escape eK geometry hb path Y
    le_sup_right hY (hYP.trans inf_le_left) hn
  have hfix : ⁅Z R a,Z R z⁆ ≤ centralizer (LocalPackage.J R a t : Set (FreeAmalgam R)) := by
    rw [←heq,←hroot]
    exact hYP.trans inf_le_right
  exact c.original_generated_critical_root_not_fixed eK geometry path hat hz4 ha4 x hx
    (heq ▸ hgen) hfix

private theorem original_conjugate_three_generators
    {R : Subgroup c.M} {a z d t : Vertex R} {x : FreeAmalgam R}
    (hx : x ∈ Ltilde R a)
    (hgen : Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z)) :
    Ltilde R a ≤ (LocalPackage.J R (act R x d) (act R x t) ⊔ Z R z) ⊔
      Z R (act R x z) := by
  have h := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hgen
  have hL : (Ltilde R a).map (MulAut.conj x⁻¹).toMonoidHom = Ltilde R a :=
    mem_normalizer_iff_map_conj_eq.mp
    ((Ltilde R a).le_normalizer ((Ltilde R a).inv_mem hx))
  rw [hL,Subgroup.map_sup,Subgroup.map_sup,←smallMoverJoin_act,←Z_act,←Z_act,
    ←act_mul,inv_mul_cancel,act_one] at h
  simpa only [sup_assoc,sup_comm,sup_left_comm] using h

/-- Both kernels of the same generated pair have endpoint displacement
in the starting seed, including the order-four-image branch. -/
theorem original_equal_mover_generated_pair_displacement
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      ∀ x ∈ Ltilde R a,
      Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) →
      let w := path.walk.getVert (path.walk.length-2)
      ⁅(Z R d ⊓ Q R w) ⊔ Z R a,Z R z⁆ ≤ Z R a ∧
      ⁅(Z R (act R x d) ⊓ Q R w) ⊔ Z R a,Z R z⁆ ≤ Z R a := by
  intro R geometry hb a z d t path hat hdt heq x hx hgen w
  refine ⟨c.original_equal_mover_generated_kernel_displacement eK geometry hb path hat hdt heq x hx hgen,?_⟩
  have hxS : x ∈ stabilizer R a := Ltilde_le_stabilizer a hx
  have hfix : act R x a = a := hxS
  have hat₂ : Adjacent R a (act R x t) := by
    rw [←hfix]
    exact (adjacent_act_iff R x _ _).mpr hat
  have hdt₂ := (adjacent_act_iff R x _ _).mpr hdt
  have heq₂ : LocalPackage.J R (act R x d) (act R x t) = LocalPackage.J R a (act R x t) := by
    rw [←hfix,smallMoverJoin_act,smallMoverJoin_act,heq]
  apply c.original_equal_mover_generated_kernel_displacement eK geometry hb path hat₂ hdt₂ heq₂
    x⁻¹ ((Ltilde R a).inv_mem hx)
  rw [inv_inv]
  exact c.original_conjugate_three_generators hx hgen

/-- If the critical member has image at most four and its entire mate is
in the truncated kernel, all three residual generators normalize the full
critical kernel join, contradicting its already proved nonnormality. -/
theorem original_equal_mover_small_critical_mate_impossible
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z)
        (back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2))),
      Adjacent R a t → Adjacent R d t → back.walk.getVert 1=t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      ∀ x ∈ Ltilde R a,
      Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      (Q R (path.walk.getVert (path.walk.length-2))).relIndex (Z R d) ≤ 4 →
      Z R (act R x d) ≤ Q R (path.walk.getVert (path.walk.length-2)) → False := by
  intro R geometry hb a z d t path back hat hdt hbt heq x hx hgen hmove hsmall hmate
  let K := Z R d ⊓ Q R (path.walk.getVert (path.walk.length-2))
  let Y := K ⊔ Z R a
  have hdist : (cosetGraph R).dist (path.walk.getVert (path.walk.length-2)) t < geometry.b R := by
    rw [←hbt,SimpleGraph.dist_comm,back.dist_end,back.length_eq_b]
    omega
  obtain ⟨hJ,_,hnot⟩ := c.original_critical_small_kernel_obstruction eK geometry hb back
    hdt hat hdist hsmall hmove
  obtain ⟨hd₁,hd₂⟩ := c.original_equal_mover_generated_pair_displacement eK geometry hb path
    hat hdt heq x hx hgen
  rw [inf_eq_left.mpr hmate] at hd₂
  have hxS : x ∈ stabilizer R a := Ltilde_le_stabilizer a hx
  have hZaMap : (Z R a).map (MulAut.conj x).toMonoidHom = Z R a :=
    mem_normalizer_iff_map_conj_eq.mp ((Z_normalized R a) hxS)
  have hdMap : (Z R (act R x d)).map (MulAut.conj x).toMonoidHom = Z R d := by
    have hh := Z_act R x⁻¹ (act R x d)
    rw [←act_mul,mul_inv_cancel,act_one] at hh
    simpa only [inv_inv] using hh.symm
  have heMap : (Z R z).map (MulAut.conj x).toMonoidHom = Z R (act R x⁻¹ z) := by
    simpa only [inv_inv] using (Z_act R x⁻¹ z).symm
  have hthird := map_mono (f := (MulAut.conj x).toMonoidHom) hd₂
  rw [map_commutator,Subgroup.map_sup,hZaMap,hdMap,heMap] at hthird
  have hN₁ : Z R z ≤ normalizer (Y : Set (FreeAmalgam R)) :=
    le_normalizer_iff_commutator_le_left.mpr (hd₁.trans le_sup_right)
  have hN₂ : Z R (act R x⁻¹ z) ≤ normalizer (Y : Set (FreeAmalgam R)) :=
    le_normalizer_iff_commutator_le_left.mpr
      (((commutator_mono (sup_le_sup inf_le_left le_rfl) le_rfl).trans hthird).trans le_sup_right)
  exact hnot (hgen.trans (sup_le (sup_le hJ hN₁) hN₂))

/-- The exact generated separated pair has at least sixteen images in the
original truncated quotient. The order-four alternative is impossible. -/
theorem original_equal_mover_generated_pair_index_ge_sixteen
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t → X R a = Z R a →
      ∀ x ∈ Ltilde R a,
      Ltilde R a ≤ (LocalPackage.J R d t ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) →
      ((Z R a ⊓ centralizer (LocalPackage.J R d t : Set (FreeAmalgam R))) ⊓
        centralizer (LocalPackage.J R (act R x d) (act R x t) : Set (FreeAmalgam R))) = ⊥ →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      let w := path.walk.getVert (path.walk.length-2)
      (¬ Z R d ≤ Q R w ∨ ¬ Z R (act R x d) ≤ Q R w) →
      16 ≤ (Q R w).relIndex (Z R d ⊔ Z R (act R x d)) := by
  intro R geometry hb a z d t path hat hdt heq hX x hx hgen hsep hmove w hcritical
  by_contra! hsmall
  have hxS : x ∈ stabilizer R a := Ltilde_le_stabilizer a hx
  rcases c.original_equal_mover_small_pair_unique_backward eK geometry hb path
    hat hdt heq hX x hxS hsep hcritical hsmall with ⟨⟨back,hbt,_⟩,hi,hk⟩ | ⟨hk,⟨back,hbt,_⟩,hi⟩
  · exact c.original_equal_mover_small_critical_mate_impossible eK geometry hb path back
      hat hdt hbt heq x hx hgen hmove hi.le hk
  · have hfix : act R x a = a := hxS
    have hat₂ : Adjacent R a (act R x t) := by
      rw [←hfix]
      exact (adjacent_act_iff R x _ _).mpr hat
    have hdt₂ := (adjacent_act_iff R x _ _).mpr hdt
    have heq₂ : LocalPackage.J R (act R x d) (act R x t) = LocalPackage.J R a (act R x t) := by
      rw [←hfix,smallMoverJoin_act,smallMoverJoin_act,heq]
    apply c.original_equal_mover_small_critical_mate_impossible eK geometry hb path back
      hat₂ hdt₂ hbt heq₂ x⁻¹ ((Ltilde R a).inv_mem hx) ?_ ?_ hi.le ?_
    · rw [inv_inv]
      exact c.original_conjugate_three_generators hx hgen
    · rw [ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega) path.start_color x hxS]
      exact hmove
    · simpa only [←act_mul,mul_inv_cancel,act_one] using hk

/-- Apply the order-four exclusion and both endpoint displacements to the
literal original source choice, retaining all generators, path overlaps,
and exact full-kernel and image-product identities. -/
theorem original_equal_mover_root_pair_large_configuration
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z : Vertex R} (path : CriticalPath R geometry a z),
      LocalPackage.J R (path.walk.getVert 2) (path.walk.getVert 1) =
        LocalPackage.J R a (path.walk.getVert 1) →
      ¬ ⁅V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)),Z R z⁆ ≤ Z R a →
      ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
        let d₁ := act R g⁻¹ (path.walk.getVert 2)
        let t₁ := act R g⁻¹ (path.walk.getVert 1)
        let d₂ := act R x d₁
        let t₂ := act R x t₁
        let w := path.walk.getVert (path.walk.length-2)
        let K₁ := Z R d₁ ⊓ Q R w
        let K₂ := Z R d₂ ⊓ Q R w
        Adjacent R a t₁ ∧ Adjacent R d₁ t₁ ∧
        LocalPackage.J R d₁ t₁ = LocalPackage.J R a t₁ ∧
        Ltilde R a ≤ (LocalPackage.J R d₁ t₁ ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) ∧
        ((Z R a ⊓ centralizer (LocalPackage.J R d₁ t₁ : Set (FreeAmalgam R))) ⊓
          centralizer (LocalPackage.J R d₂ t₂ : Set (FreeAmalgam R))) = ⊥ ∧
        4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d₁) ∧
        ((∃ back : CriticalPath R geometry d₁ w,
          back.walk.getVert 1=t₁ ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∨
        (∃ back : CriticalPath R geometry d₂ w,
          back.walk.getVert 1=t₂ ∧
          ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i)) ∧
        ((Z R d₁ ⊔ Z R d₂) ⊓ Q R w = K₁ ⊔ K₂) ∧
        (Q R w).relIndex (Z R d₁ ⊔ Z R d₂) =
          (Q R w).relIndex (Z R d₁) * (Q R w).relIndex (Z R d₂) ∧
        16 ≤ (Q R w).relIndex (Z R d₁ ⊔ Z R d₂) ∧
        ⁅K₁ ⊔ Z R a,Z R z⁆ ≤ Z R a ∧ ⁅K₂ ⊔ Z R a,Z R z⁆ ≤ Z R a := by
  intro R geometry hb a z path heq hbad
  obtain h | ⟨_,_,hX,_⟩ := c.original_radius_displacement_or_root eK geometry path
  · exact (hbad h).elim
  obtain ⟨g,hg,x,hx,hat,hdt,heq₁,hgen,hsep,hmove,hback,_,hker,hprod,_⟩ :=
    c.original_equal_mover_root_pair_image_configuration eK geometry hb path heq hbad
  have hcritical : ¬ Z R (act R g⁻¹ (path.walk.getVert 2)) ≤ Q R (path.walk.getVert (path.walk.length-2)) ∨
      ¬ Z R (act R x (act R g⁻¹ (path.walk.getVert 2))) ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
    rcases hback with ⟨back,_,_⟩ | ⟨back,_,_⟩
    · exact Or.inl back.critical.2
    · exact Or.inr back.critical.2
  exact ⟨g,hg,x,hx,hat,hdt,heq₁,hgen,hsep,hmove,hback,hker,hprod,
    c.original_equal_mover_generated_pair_index_ge_sixteen eK geometry hb path
      hat hdt heq₁ hX x hx hgen hsep hmove hcritical,
    c.original_equal_mover_generated_pair_displacement eK geometry hb path hat hdt heq₁ x hx hgen⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
