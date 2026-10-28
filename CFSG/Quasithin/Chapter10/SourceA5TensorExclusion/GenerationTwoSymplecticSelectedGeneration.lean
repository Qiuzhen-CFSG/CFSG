module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticSylowMovers
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSelectedGeneration
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSmallMoverSylow
public import Theory.GroupTheory.RelativeProductBound

/-!
# Original residual generators in the reciprocal-root branch

The full-Sylow small mover has relative order 64 and natural moving index
16. The original critical endpoint has a full long-root image when both
critical indices are four. The marked calculation therefore gives actual
residual conjugators, retaining the full kernel. In the equal-mover case
the conjugated neighbor and edge preserve their literal moving index.
The same selected generators have zero common centralizer in the original
seed; their inverse-conjugation action is retained on both paired edges.

This proves the simultaneous generation and fixed-intersection clauses of
MS93 (5.6)(b,c), printed p.917, in the field-four source 9.3.10 setting.
The other positioning clauses, strict movement and distance exclusions
remain to be proved; this module
does not assert SymplecticPlaneRecognition.
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

/-- The original full-Sylow small mover and two actual endpoint conjugates
supply the residual generators in the reciprocal-root branch. -/
theorem original_root_small_mover_generators
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → (Q R a).relIndex (Z R z) = 4 → (Q R z).relIndex (Z R a) = 4 →
      ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
        Ltilde R a ≤ ((LocalPackage.J R a t).map (MulAut.conj g).toMonoidHom ⊔ Z R z) ⊔
          (Z R z).map (MulAut.conj x).toMonoidHom := by
  intro R geometry a z t path hat hza haz
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
  exact original_small_mover_root_generators R hms hodd.isPGroup hne hodd.twoCore_le
    hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path hb hza haz hfixed (LocalPackage.J R a t)
    ((LocalPackage.J_le_radical R a t).trans (fun _ hx => hx.2 a (adjacent_symm R hat)))
    (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le path.start_color hat)
    (hQt.to_le (LocalPackage.J_le_radical R a t)) hindices.2.1 hindices.2.2.le

/-- In the equal-small-mover branch the selected neighboring vertex and edge
are literal conjugates, and the original moving index is retained. -/
theorem original_equal_mover_root_selection
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      (Q R a).relIndex (Z R z) = 4 → (Q R z).relIndex (Z R a) = 4 →
      ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
        Adjacent R a (act R g⁻¹ t) ∧ Adjacent R (act R g⁻¹ d) (act R g⁻¹ t) ∧
        Ltilde R a ≤ (LocalPackage.J R (act R g⁻¹ d) (act R g⁻¹ t) ⊔ Z R z) ⊔
          Z R (act R x⁻¹ z) ∧
        (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex
          (U R (act R g⁻¹ d)) =
        (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) := by
  intro R geometry hb a z d t path hat hdt heq hza haz
  obtain ⟨g,hg,x,hx,hgen⟩ := c.original_root_small_mover_generators eK geometry path hat hza haz
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hfix : act R g⁻¹ a = a := hgS
  refine ⟨g,hg,x,hx,?_,(adjacent_act_iff R g⁻¹ _ _).mpr hdt,?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff R g⁻¹ _ _).mpr hat
  · rw [smallMoverJoin_act,Z_act,inv_inv,inv_inv,heq]
    exact hgen
  · exact ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega)
      path.start_color g⁻¹ hgS
/-- The original geometry supplies either its proved displacement alternative
or the actual three residual generators, with no extra root/action premise. -/
theorem original_radius_displacement_or_paired_generators
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t →
      ⁅V R a ⊓ Q R (path.walk.getVert (path.walk.length-2)),Z R z⁆ ≤ Z R a ∨
      ((Q R z).relIndex (Z R a) = 4 ∧ (Q R a).relIndex (Z R z) = 4 ∧
        X R a = Z R a ∧ X R z = Z R z ∧
        ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
          Ltilde R a ≤ ((LocalPackage.J R a t).map (MulAut.conj g).toMonoidHom ⊔ Z R z) ⊔
            (Z R z).map (MulAut.conj x).toMonoidHom) := by
  intro R geometry a z t path hat
  rcases c.original_radius_displacement_or_root eK geometry path with h | ⟨haz,hza,hXa,hXz⟩
  · exact Or.inl h
  · exact Or.inr ⟨haz,hza,hXa,hXz,
      c.original_root_small_mover_generators eK geometry path hat hza haz⟩

/-- The original full-Sylow small mover and two actual endpoint conjugates
supply the residual generators in the reciprocal-root branch. -/
theorem original_root_small_mover_separated_generators
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R) {a z t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → (Q R a).relIndex (Z R z) = 4 → (Q R z).relIndex (Z R a) = 4 →
      ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
        Ltilde R a ≤ ((LocalPackage.J R a t).map (MulAut.conj g).toMonoidHom ⊔ Z R z) ⊔
          (Z R z).map (MulAut.conj x).toMonoidHom ∧
        ((Z R a ⊓ centralizer ((LocalPackage.J R a t).map
          (MulAut.conj g).toMonoidHom : Set (FreeAmalgam R))) ⊓
          centralizer (((LocalPackage.J R a t).map (MulAut.conj g).toMonoidHom).map
            (MulAut.conj x⁻¹).toMonoidHom : Set (FreeAmalgam R))) = ⊥ := by
  intro R geometry a z t path hat hza haz
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
  rw [c.original_Z_eq_U a path.start_color]
  exact original_small_mover_root_separated_generators R hms hodd.isPGroup hne hodd.twoCore_le
    hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq path hb hza haz hfixed (LocalPackage.J R a t)
    ((LocalPackage.J_le_radical R a t).trans (fun _ hx => hx.2 a (adjacent_symm R hat)))
    (LocalPackage.Q_le_J R hodd.isPGroup hodd.twoCore_le path.start_color hat)
    (hQt.to_le (LocalPackage.J_le_radical R a t)) hindices.2.1 hindices.2.2.le

/-- The equal-mover choice simultaneously retains the original moving index,
three residual generators and zero common fixed seed for its paired movers. -/
theorem original_equal_mover_root_separated_selection
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (_path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      LocalPackage.J R d t = LocalPackage.J R a t →
      (Q R a).relIndex (Z R z) = 4 → (Q R z).relIndex (Z R a) = 4 →
      ∃ g ∈ Ltilde R a, ∃ x ∈ Ltilde R a,
        let d₁ := act R g⁻¹ d
        let t₁ := act R g⁻¹ t
        Adjacent R a t₁ ∧ Adjacent R d₁ t₁ ∧
        Ltilde R a ≤ (LocalPackage.J R d₁ t₁ ⊔ Z R z) ⊔ Z R (act R x⁻¹ z) ∧
        (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d₁) =
          (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) ∧
        ((Z R a ⊓ centralizer (LocalPackage.J R d₁ t₁ : Set (FreeAmalgam R))) ⊓
          centralizer (LocalPackage.J R (act R x d₁) (act R x t₁) : Set (FreeAmalgam R))) = ⊥ := by
  intro R geometry hb a z d t path hat hdt heq hza haz
  obtain ⟨g,hg,x,hx,hgen,hsep⟩ := c.original_root_small_mover_separated_generators
    eK geometry path hat hza haz
  have hgS : g⁻¹ ∈ stabilizer R a := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  have hfix : act R g⁻¹ a = a := hgS
  refine ⟨g,hg,x,hx,?_,(adjacent_act_iff R g⁻¹ _ _).mpr hdt,?_,?_,?_⟩
  · rw [←hfix]
    exact (adjacent_act_iff R g⁻¹ _ _).mpr hat
  · rw [smallMoverJoin_act,Z_act,inv_inv,inv_inv,heq]
    exact hgen
  · exact ChapterC.Sp4Four.DistanceReduction.movingIndex_act geometry (by omega)
      path.start_color g⁻¹ hgS
  · simpa only [smallMoverJoin_act,inv_inv,heq] using hsep

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
