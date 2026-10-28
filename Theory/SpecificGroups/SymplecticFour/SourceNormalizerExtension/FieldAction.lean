module
public import Theory.SpecificGroups.SymplecticFour.SourceNormalizerExtension
public import Theory.SpecificGroups.SymplecticFour.Sylow.QuotientActors
public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.CenterAction
public import Theory.SpecificGroups.SymplecticFour.LocalStructure.Point.RadicalAction.Lattice

/-!
# The common field action of a marked symplectic amalgam

An automorphism of the actual point/Borel/plane amalgam induces an
automorphism of the unipotent Sylow: this subgroup is the characteristic
two-core of the whole Borel. Its central quotient has coordinates (b,v),
and its square map is (b,v) ↦ (b²v,bv).

The plane-parabolic two-core preserves the v-axis of that quotient. The
center of the point-parabolic solvable residual preserves the long-root
axis of the center. These two actual markings eliminate both axis switches.
Product rigidity then forces one field automorphism on both quotient
coordinates and both central-root coordinates. Unlike unmarked square-map
rigidity, this argument includes the field of four elements.

The field components form a homomorphism on the entire marked automorphism
group and are trivial on the entire pure Borel. Explicit diagonal and
entrywise field automorphisms provide native
flag automorphisms with the same actions on the central quotient and the
whole center. This does not yet extend the full marked action: its remaining
central automorphism defect and the endpoint actions still require control.

Source: the simultaneous local-action step in Aschbacher–Smith 5.3.2,
printed p.659 of `refs/quasithin.pdf`, and the standard positive-root
multiplication formulas used in F.4.29. No recognition of a completion is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix
open Theory.SpecificGroups.SymplecticFour
open CentralRootGeometry QuotientActors
namespace Theory.SpecificGroups.SymplecticFour.SourceNormalizerExtension
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable {n : ℕ} (hF : Nat.card F = 2^n)

private def unipotentCoreEquiv : unipotent (F := F) ≃* pCore 2 (borel (F := F)) :=
  (subgroupOfEquivOfLe unipotent_le_borel).symm.trans
    (MulEquiv.subgroupCongr (EvenBorelTorus.twoCore_eq_unipotent hF).symm)

def sylowAction (a : RankTwoAmalgam.Iso (diagram F) (diagram F)) :
    MulAut (unipotent (F := F)) :=
  MulAut.congr (unipotentCoreEquiv hF).symm
    (MulAut.characteristic (pCore 2 (borel (F := F))) a.middle)

omit [CharP F 2] in
theorem sylowAction_coe (a : RankTwoAmalgam.Iso (diagram F) (diagram F))
    (u : unipotent (F := F)) :
    (sylowAction hF a u).val =
      (a.middle (inclusion unipotent_le_borel u)).val := by rfl

private theorem plane_axis (hn : 1 < n)
    (a : RankTwoAmalgam.Iso (diagram F) (diagram F)) (v : F) :
    ((planeAction (sylowAction hF a) (Multiplicative.ofAdd (0,v))).toAdd).1 = 0 := by
  let u := element (0:F) 0 0 v
  have hu : u.val ∈ (Plane.radical.map planeLocal.subtype) := by
    let B : Plane.symmetricMatrices F := ⟨!![0,0;0,v], by
      ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
    have he : (Plane.shear B).val = u.val := by
      apply Subtype.ext
      rw [show u = element (0:F) 0 0 v from rfl, element_matrix]
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
        simp [Plane.shear, Plane.shearSp, B, Matrix.fromBlocks]
    exact ⟨Plane.shear B, Plane.quotientMap_shear B, he⟩
  have hc : (⟨u.val, unipotent_le_borel u.property |>.2⟩ : planeParabolic (F := F)) ∈
      pCore 2 (planeParabolic (F := F)) := by
    obtain ⟨q,hq,hqe⟩ := (planeParabolic_core_map_eq_radical hF hn).symm ▸ hu
    exact (Subtype.ext hqe : q = ⟨u.val,_⟩) ▸ hq
  have ha := (characteristic_iff_le_comap.mp (inferInstance :
    (pCore 2 (planeParabolic (F := F))).Characteristic) a.right) hc
  change a.right ⟨u.val, _⟩ ∈ pCore 2 (planeParabolic (F := F)) at ha
  have he : (a.right ⟨u.val, unipotent_le_borel u.property |>.2⟩).val =
      (sylowAction hF a u).val := by
    rw [sylowAction_coe]
    exact congrArg Subtype.val (a.right_commutes (inclusion unipotent_le_borel u))
  have hr : (sylowAction hF a u).val ∈ (Plane.radical.map planeLocal.subtype) := by
    rw [←he, ←planeParabolic_core_map_eq_radical hF hn]
    exact mem_map_of_mem planeParabolic.subtype ha
  obtain ⟨q,hq,hqe⟩ := hr
  have hm := Plane.radical_matrix (⟨q,hq⟩ : Plane.radical (F := F))
  have hz := congrArg (fun M => M (.inl 0) (.inl 1)) hm
  change q.val.val (.inl 0) (.inl 1) = 0 at hz
  rw [←planeProjection_element (0:F) 0 0 v, planeAction_apply]
  change (sylowAction hF a u).val.val (.inl 0) (.inl 1) = 0
  rw [←hqe]
  exact hz

private theorem center_axis (hn : 1 < n)
    (a : RankTwoAmalgam.Iso (diagram F) (diagram F)) (s : F) :
    (centralAction (sylowAction hF a) (s,0)).2 = 0 := by
  let e : pointLocal (F := F) ≃* solvableResidual (pointParabolic (F := F)) :=
    (subgroupOfEquivOfLe pointLocal_le).symm.trans
      (MulEquiv.subgroupCongr (pointParabolic_solvableResidual_relative hF hn).symm)
  let ar : MulAut (pointLocal (F := F)) := MulAut.congr e.symm
    (MulAut.characteristic (solvableResidual (pointParabolic (F := F))) a.left)
  have har (x : pointLocal (F := F)) :
      (ar x).val = (a.left ⟨x.val, pointLocal_le x.property⟩).val := rfl
  have ht : (theta s 0).val =
      Representation.OneCohomology.SymplecticFour.rootElement 0 s := by
    rw [theta_val, RootSubgroup.element_zero, mul_one]
  have hz : (theta s 0).val ∈ (center (pointLocal (F := F))).map pointLocal.subtype := by
    rw [PointRadicalAction.center_eq_root hF hn,ht]
    exact (RootSubgroup.mem_group_iff _ _).mpr ⟨s,rfl⟩
  obtain ⟨z,hz,hze⟩ := hz
  have haz := (characteristic_iff_le_comap.mp (inferInstance :
    (center (pointLocal (F := F))).Characteristic) ar) hz
  change ar z ∈ center (pointLocal (F := F)) at haz
  have hre : (ar z).val = (sylowAction hF a (theta s 0)).val := by
    rw [har, sylowAction_coe]
    have hh := congrArg Subtype.val (a.left_commutes
      (inclusion unipotent_le_borel (theta s 0)))
    change (a.left ⟨_,_⟩).val = _ at hh
    change (a.left ⟨z.val,_⟩).val = (a.middle (inclusion unipotent_le_borel (theta s 0))).val
    change (a.left ⟨(theta s 0).val,_⟩).val = _ at hh
    exact (congrArg (fun x : pointParabolic (F := F) => (a.left x).val)
      (Subtype.ext hze)).trans hh
  have hz' : (sylowAction hF a (theta s 0)).val ∈ RootSubgroup.group 0 := by
    rw [←hre, ←PointRadicalAction.center_eq_root hF hn]
    exact mem_map_of_mem pointLocal.subtype haz
  obtain ⟨t,ht'⟩ := (RootSubgroup.mem_group_iff _ _).mp hz'
  have hc := congrArg Subtype.val (centralAction_apply (sylowAction hF a) (s,0))
  change (theta (centralAction (sylowAction hF a) (s,0)).1
    (centralAction (sylowAction hF a) (s,0)).2).val =
      (sylowAction hF a (theta s 0)).val at hc
  have htheta : theta (centralAction (sylowAction hF a) (s,0)).1
      (centralAction (sylowAction hF a) (s,0)).2 = theta t 0 := by
    apply Subtype.ext
    rw [hc, ←ht', theta_val, RootSubgroup.element_zero, mul_one]
  exact (element_eq_iff _ _ _ _ _ _ _ _).mp htheta |>.2.2.1

/-- The two preserved markings force a common field automorphism, including
in degree two. The formula simultaneously controls center and quotient. -/
theorem marked_field_action (hn : 1 < n)
    (a : RankTwoAmalgam.Iso (diagram F) (diagram F)) :
    ∃ c d : Fˣ, ∃ σ : F ≃+* F,
      (∀ x : F × F, (planeAction (sylowAction hF a) (Multiplicative.ofAdd x)).toAdd =
        (c * σ x.1, d * σ x.2)) ∧
      (∀ x : F × F, centralAction (sylowAction hF a) x =
        ((c : F)^2 * d * σ x.1, c * d * σ x.2)) := by
  let A : (F × F) ≃+ (F × F) := (planeAction (sylowAction hF a)).toAdditive
  let B := centralAction (sylowAction hF a)
  have hc (x) : squareMap (A x) = B (squareMap x) := square_compatibility _ x
  obtain ⟨ha,hb⟩ := axis_maps A B hc
  have hA : ∃ f g : F ≃+ F, ∀ x, A x = (f x.1,g x.2) := by
    rcases axis_form A ha with h | ⟨f,g,hfg⟩
    · exact h
    have he := plane_axis hF hn a 1
    change (A (0,1)).1 = 0 at he
    rw [hfg] at he
    exact (one_ne_zero (f.injective (he.trans (map_zero f).symm))).elim
  have hB : ∃ u v : F ≃+ F, ∀ x, B x = (u x.1,v x.2) := by
    rcases axis_form B hb with h | ⟨f,g,hfg⟩
    · exact h
    have he := center_axis hF hn a 1
    change (B (1,0)).2 = 0 at he
    rw [hfg] at he
    exact (one_ne_zero (g.injective (he.trans (map_zero g).symm))).elim
  obtain ⟨f,g,hfg⟩ := hA
  obtain ⟨u,v,huv⟩ := hB
  have hv (x y : F) : v (x*y) = f x*g y := by
    have hh := congrArg Prod.snd (hc (x,y))
    simpa only [hfg,huv,squareMap] using hh.symm
  obtain ⟨σ,hf,hg⟩ := product_rigidity f g v hv
  let c : Fˣ := Units.mk0 (f 1) (fun he => one_ne_zero (f.injective (he.trans (map_zero f).symm)))
  let d : Fˣ := Units.mk0 (g 1) (fun he => one_ne_zero (g.injective (he.trans (map_zero g).symm)))
  refine ⟨c,d,σ,?_,?_⟩
  · intro x
    change A x = _
    rw [hfg,hf,hg]
    rfl
  · intro x
    change B x = _
    rw [huv]
    apply Prod.ext
    · have hh := congrArg Prod.fst (hc (1,x.1))
      change u x.1 = (f 1)^2 * g 1 * σ x.1
      have he : u x.1 = (f 1)^2 * g x.1 := by
        simpa only [hfg,huv,squareMap,one_pow,one_mul] using hh.symm
      rw [he, hg]
      exact (mul_assoc _ _ _).symm
    · change v x.2 = f 1 * g 1 * σ x.2
      calc
        v x.2 = f 1 * g x.2 := by simpa only [one_mul] using hv 1 x.2
        _ = _ := by rw [hg]; exact (mul_assoc _ _ _).symm

omit [Finite F] [CharP F 2] in
/-- An actual native flag automorphism with its two diagonal parameters and
its single field automorphism. -/
private def diagonalField (c d : Fˣ) (σ : F ≃+* F) : flagAutomorphisms F :=
  innerBorel ⟨diagonalTorus c d, diagonalTorus_mem_borel _ _⟩ *
    ⟨DiagramAutomorphisms.fieldAutomorphism σ,
      DiagramAutomorphisms.field_map_pointParabolic σ,
      DiagramAutomorphisms.field_map_planeParabolic σ⟩

omit [CharP F 2] in
private theorem native_sylow_coe (α : flagAutomorphisms F) (u : unipotent (F := F)) :
    (sylowAction hF (restriction α) u).val = α.val u.val := rfl

private theorem diagonalField_plane (c d : Fˣ) (σ : F ≃+* F) (x : F × F) :
    (planeAction (sylowAction hF (restriction (diagonalField c d σ)))
      (Multiplicative.ofAdd x)).toAdd =
        ((c:F) * (↑d⁻¹:F) * σ x.1, (d:F)^2 * σ x.2) := by
  rw [←planeProjection_element x.1 0 0 x.2, planeAction_apply]
  change ((sylowAction hF (restriction (diagonalField c d σ))
    (element x.1 0 0 x.2)).val.val (.inl 0) (.inl 1),
    (sylowAction hF (restriction (diagonalField c d σ))
    (element x.1 0 0 x.2)).val.val (.inl 1) (.inr 1)) = _
  rw [native_sylow_coe]
  change (((diagonalTorus c d) * DiagramAutomorphisms.fieldAutomorphism σ
      (element x.1 0 0 x.2).val * (diagonalTorus c d)⁻¹).val (.inl 0) (.inl 1),
    ((diagonalTorus c d) * DiagramAutomorphisms.fieldAutomorphism σ
      (element x.1 0 0 x.2).val * (diagonalTorus c d)⁻¹).val (.inl 1) (.inr 1)) = _
  have hi : (diagonalTorus c d)⁻¹ = diagonalTorus c⁻¹ d⁻¹ :=
    (map_inv diagonalTorusHom (c,d)).symm
  rw [hi]
  change (((diagonalTorus c d).val *
    (DiagramAutomorphisms.fieldAutomorphism σ (element x.1 0 0 x.2).val).val *
    (diagonalTorus c⁻¹ d⁻¹).val) (.inl 0) (.inl 1),
    ((diagonalTorus c d).val *
    (DiagramAutomorphisms.fieldAutomorphism σ (element x.1 0 0 x.2).val).val *
    (diagonalTorus c⁻¹ d⁻¹).val) (.inl 1) (.inr 1)) = _
  simp only [diagonalTorus, Matrix.diagonal_mul, Matrix.mul_diagonal]
  change ((c:F) * σ ((element x.1 0 0 x.2).val.val (.inl 0) (.inl 1)) * (↑d⁻¹:F),
    (d:F) * σ ((element x.1 0 0 x.2).val.val (.inl 1) (.inr 1)) * (↑(d⁻¹)⁻¹:F)) = _
  rw [element_matrix]
  simp only [inv_inv]
  apply Prod.ext <;> dsimp <;> ring

omit [Finite F] in
private theorem field_theta (σ : F ≃+* F) (s t : F) :
    DiagramAutomorphisms.fieldAutomorphism σ (theta s t).val =
      (theta (σ s) (σ t)).val := by
  apply Subtype.ext
  change (theta s t).val.val.map σ = (theta (σ s) (σ t)).val.val
  rw [theta, theta, element_matrix, element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.fromBlocks]

omit [Finite F] in
private theorem diagonal_theta (c d : Fˣ) (s t : F) :
    diagonalTorus c d * (theta s t).val * (diagonalTorus c d)⁻¹ =
      (theta ((c:F)^2*s) ((c:F)*d*t)).val :=
  diagonalTorus_weights (c,d) s t

private theorem diagonalField_center (c d : Fˣ) (σ : F ≃+* F) (x : F × F) :
    centralAction (sylowAction hF (restriction (diagonalField c d σ))) x =
      ((c:F)^2 * σ x.1, (c:F) * d * σ x.2) := by
  have he := congrArg Subtype.val (centralAction_apply
    (sylowAction hF (restriction (diagonalField c d σ))) x)
  change (theta (centralAction (sylowAction hF (restriction (diagonalField c d σ))) x).1
    (centralAction (sylowAction hF (restriction (diagonalField c d σ))) x).2).val =
      (sylowAction hF (restriction (diagonalField c d σ)) (theta x.1 x.2)).val at he
  rw [native_sylow_coe] at he
  change _ = diagonalTorus c d * DiagramAutomorphisms.fieldAutomorphism σ
    (theta x.1 x.2).val * (diagonalTorus c d)⁻¹ at he
  rw [field_theta] at he
  have hw := diagonal_theta c d (σ x.1) (σ x.2)
  have hh := (element_eq_iff _ _ _ _ _ _ _ _).mp (Subtype.ext (he.trans hw))
  exact Prod.ext hh.2.1 hh.2.2.1

/-- There is a native diagonal-field flag automorphism agreeing simultaneously
on the central quotient and on the whole two-root center. -/
theorem native_representative (hn : 1 < n)
    (a : RankTwoAmalgam.Iso (diagram F) (diagram F)) :
    ∃ α : flagAutomorphisms F,
      planeAction (sylowAction hF (restriction α)) = planeAction (sylowAction hF a) ∧
      centralAction (sylowAction hF (restriction α)) = centralAction (sylowAction hF a) := by
  obtain ⟨c,d,σ,hp,hz⟩ := marked_field_action hF hn a
  obtain ⟨b,hb⟩ := RootTori.weight_surjective (F := F) 0 d
  have hb' : (b:F)^2 = (d:F) := by
    have hh := congrArg Units.val hb
    simpa [RootTori.weight] using hh
  refine ⟨diagonalField (c*b) b σ, ?_, ?_⟩
  · apply MulEquiv.ext
    intro x
    apply Multiplicative.toAdd.injective
    apply (diagonalField_plane hF (c*b) b σ x.toAdd).trans
    apply Eq.trans _ (hp x.toAdd).symm
    apply Prod.ext
    · change ((c:F)*(b:F)) * (↑b⁻¹:F) * σ x.toAdd.1 = _
      simp
    · rw [hb']
  · apply AddEquiv.ext
    intro x
    rw [diagonalField_center, hz]
    simp only [Units.val_mul, mul_pow, hb']
    apply Prod.ext
    · rfl
    · calc
        (c:F)*b*b*σ x.2 = c*(b:F)^2*σ x.2 := by ring
        _ = _ := by rw [hb']

omit [CharP F 2] in
private theorem sylowAction_mul (a b : RankTwoAmalgam.Iso (diagram F) (diagram F)) :
    sylowAction hF (a*b) = sylowAction hF a * sylowAction hF b := by
  ext x
  rfl

private theorem exists_fieldPart (hn : 1 < n)
    (a : RankTwoAmalgam.Iso (diagram F) (diagram F)) :
    ∃ σ : F ≃+* F, ∃ c d : Fˣ,
      (∀ x : F × F, (planeAction (sylowAction hF a) (Multiplicative.ofAdd x)).toAdd =
        (c * σ x.1, d * σ x.2)) ∧
      (∀ x : F × F, centralAction (sylowAction hF a) x =
        ((c : F)^2 * d * σ x.1, c * d * σ x.2)) := by
  obtain ⟨c,d,σ,hp,hz⟩ := marked_field_action hF hn a
  exact ⟨σ,c,d,hp,hz⟩

/-- The single field component forced by both marked local actions. -/
private def fieldPart (hn : 1 < n) (a : RankTwoAmalgam.Iso (diagram F) (diagram F)) : F ≃+* F :=
  Classical.choose (exists_fieldPart hF hn a)

private theorem fieldPart_spec (hn : 1 < n)
    (a : RankTwoAmalgam.Iso (diagram F) (diagram F)) :
    ∃ c d : Fˣ,
      (∀ x : F × F, (planeAction (sylowAction hF a) (Multiplicative.ofAdd x)).toAdd =
        (c * fieldPart hF hn a x.1, d * fieldPart hF hn a x.2)) ∧
      (∀ x : F × F, centralAction (sylowAction hF a) x =
        ((c : F)^2 * d * fieldPart hF hn a x.1, c * d * fieldPart hF hn a x.2)) :=
  Classical.choose_spec (exists_fieldPart hF hn a)

private theorem fieldPart_unique (hn : 1 < n)
    (a : RankTwoAmalgam.Iso (diagram F) (diagram F)) (c : Fˣ) (σ : F ≃+* F)
    (hp : ∀ t : F, ((planeAction (sylowAction hF a) (Multiplicative.ofAdd (t,0))).toAdd).1 =
      c * σ t) : fieldPart hF hn a = σ := by
  obtain ⟨d,e,hd,_⟩ := fieldPart_spec hF hn a
  have hdc : (d:F) = (c:F) := by
    have hh := congrArg Prod.fst (hd (1,0))
    rw [hp] at hh
    simpa only [map_one,mul_one] using hh.symm
  ext t
  apply mul_left_cancel₀ c.ne_zero
  have hh := congrArg Prod.fst (hd (t,0))
  rw [hp] at hh
  exact (hdc ▸ hh).symm

/-- The common field components form a homomorphism, so local field choices
are coherent on the entire automorphism group of the marked amalgam. -/
def fieldAction (hn : 1 < n) :
    RankTwoAmalgam.Iso (diagram F) (diagram F) →* (F ≃+* F) where
  toFun := fieldPart hF hn
  map_one' := by
    apply fieldPart_unique hF hn 1 1 1
    intro t
    have he : sylowAction hF 1 = 1 := by ext x; rfl
    rw [he, map_one]
    change t = (1:F)*t
    rw [one_mul]
  map_mul' a b := by
    obtain ⟨c,d,ha,_⟩ := fieldPart_spec hF hn a
    obtain ⟨e,f,hb,_⟩ := fieldPart_spec hF hn b
    apply fieldPart_unique hF hn (a*b)
      (c * Units.map (fieldPart hF hn a).toMonoidHom e)
      (fieldPart hF hn a * fieldPart hF hn b)
    intro t
    rw [sylowAction_mul, map_mul]
    change ((planeAction (sylowAction hF a)
      (planeAction (sylowAction hF b) (Multiplicative.ofAdd (t,0)))).toAdd).1 = _
    have hb' : planeAction (sylowAction hF b) (Multiplicative.ofAdd (t,0)) =
      Multiplicative.ofAdd (e * fieldPart hF hn b t,0) := by
      apply Multiplicative.toAdd.injective
      change (planeAction (sylowAction hF b) (Multiplicative.ofAdd (t,0))).toAdd =
        (e * fieldPart hF hn b t, 0)
      simpa only [map_zero,mul_zero] using hb (t,0)
    rw [hb']
    have hh := congrArg Prod.fst (ha (e * fieldPart hF hn b t,0))
    rw [hh]
    change (c:F) * fieldPart hF hn a ((e:F) * fieldPart hF hn b t) =
      ((c:F) * fieldPart hF hn a (e:F)) * fieldPart hF hn a (fieldPart hF hn b t)
    rw [map_mul,mul_assoc]

/-- The homomorphism gives the same field map on both central-root coordinates
and on both quotient coordinates, with their exact scalar weights. -/
theorem fieldAction_spec (hn : 1 < n)
    (a : RankTwoAmalgam.Iso (diagram F) (diagram F)) :
    ∃ c d : Fˣ,
      (∀ x : F × F, (planeAction (sylowAction hF a) (Multiplicative.ofAdd x)).toAdd =
        (c * fieldAction hF hn a x.1, d * fieldAction hF hn a x.2)) ∧
      (∀ x : F × F, centralAction (sylowAction hF a) x =
        ((c : F)^2 * d * fieldAction hF hn a x.1, c * d * fieldAction hF hn a x.2)) :=
  fieldPart_spec hF hn a

/-- The complete pure Borel, including its Cartans, has trivial field part. -/
theorem fieldAction_innerBorel (hn : 1 < n) (b : borel (F := F)) :
    fieldAction hF hn (restriction (innerBorel b)) = 1 := by
  let a := restriction (innerBorel b)
  obtain ⟨c,d,_,hz⟩ := fieldAction_spec hF hn a
  have he (s : F) : (c:F)^2 * d * fieldAction hF hn a s =
      ((borelCharacters b).1:F)^2 * s := by
    have hh := congrArg Subtype.val (centralAction_apply (sylowAction hF a) (s,0))
    change (theta (centralAction (sylowAction hF a) (s,0)).1
      (centralAction (sylowAction hF a) (s,0)).2).val =
        (sylowAction hF a (theta s 0)).val at hh
    rw [sylowAction_coe] at hh
    change parameter (Multiplicative.ofAdd (centralAction (sylowAction hF a) (s,0)).1,
      Multiplicative.ofAdd (centralAction (sylowAction hF a) (s,0)).2) =
        b.val * parameter (Multiplicative.ofAdd s,Multiplicative.ofAdd 0) * b.val⁻¹ at hh
    have hc := parameter_injective
      (hh.trans (CenterAction.borel_conj_parameter b s 0))
    have hf := congrArg (fun x : Multiplicative F × Multiplicative F => x.1.toAdd) hc
    change (centralAction (sylowAction hF a) (s,0)).1 = _ at hf
    rw [hz] at hf
    exact hf
  have hscalar : (c:F)^2 * d = ((borelCharacters b).1:F)^2 := by
    simpa only [map_one,mul_one] using he 1
  apply RingEquiv.ext
  intro s
  have hs := he s
  rw [hscalar] at hs
  exact mul_left_cancel₀ (pow_ne_zero _ (borelCharacters b).1.ne_zero) hs

end Theory.SpecificGroups.SymplecticFour.SourceNormalizerExtension
