module

public import Theory.SpecificGroups.SymplecticFour.EvenBorelTorus

/-!
# Central root commutators detecting symplectic Borel elements

Write a flag element as u diag(a,d,a⁻¹,d⁻¹). On the two noncentral
unipotent coordinates its commutator has weights 1-a/d and 1-d².
The square formula therefore forces their product to vanish when every
unipotent commutator has square one. Unless the flag element is unipotent,
both central weights 1-a² and 1-ad are then nonzero. The commutator map
on the actual two-root central plane is consequently injective.

This supplies the matrix calculation for excluding A₃ blocks, including
over the field of order four. No assertion about Sylow-center rank is used.
Source: Aschbacher–Smith, combined manuscript (1 March 2004), the Borel
paragraph in E.6.8, printed p.248 (PDF p.259); standard Sp₄ root matrices.
-/

public section

open Matrix Subgroup
open Theory.SpecificGroups.SymplecticFour
open CentralRootGeometry
open scoped commutatorElement

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.BorelPlacement.MatrixBlocks.RootCommutators
variable {F : Type*} [Field F] [CharP F 2] [Finite F]
noncomputable section
set_option linter.unusedSimpArgs false

private def outer : unipotent (F := F) →* Multiplicative (F × F) where
  toFun x := Multiplicative.ofAdd (x.val.val (.inl 0) (.inl 1), x.val.val (.inl 1) (.inr 1))
  map_one' := by rfl
  map_mul' x y := by
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    obtain ⟨⟨c,z,t,a⟩,rfl⟩ := element_surjective y
    simp only [element_mul, element_matrix]
    rfl

private theorem outer_element (b u w v : F) :
    outer (element b u w v) = Multiplicative.ofAdd (b,v) := by
  change Multiplicative.ofAdd ((element b u w v).val.val (.inl 0) (.inl 1),
    (element b u w v).val.val (.inl 1) (.inr 1)) = _
  rw [element_matrix]
  rfl

private theorem outer_product_zero (x : unipotent (F := F)) (hx : x ^ 2 = 1) :
    (outer x).toAdd.1 * (outer x).toAdd.2 = 0 := by
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  rw [outer_element]
  rw [element_square] at hx
  have h := (element_eq_iff 0 (b^2*v) (b*v) 0 0 0 0 0).mp (hx.trans element_zero.symm)
  exact h.2.2.1

private def torusAction (a d : Fˣ) (x : unipotent (F := F)) : unipotent (F := F) :=
  ⟨diagonalTorus a d * x.val * (diagonalTorus a d)⁻¹,
    (mem_normalizer_iff.mp (diagonalTorus_normalizes (a,d)) x.val).mp x.property⟩

omit [Finite F] in
private theorem torusAction_element (a d : Fˣ) (b u w v : F) :
    torusAction a d (element b u w v) =
      element ((a:F)/(d:F)*b) ((a:F)^2*u) ((a:F)*(d:F)*w) ((d:F)^2*v) := by
  apply Subtype.ext
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Subtype.ext
  change (diagonalTorus a d).val * (element b u w v).val.val =
    (element _ _ _ _).val.val * (diagonalTorus a d).val
  rw [element_matrix, element_matrix]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [diagonalTorus, Matrix.fromBlocks, div_eq_mul_inv, pow_two] <;>
    field_simp

private theorem outer_torusAction (a d : Fˣ) (x : unipotent (F := F)) :
    outer (torusAction a d x) = Multiplicative.ofAdd
      ((a:F)/(d:F)*(outer x).toAdd.1, (d:F)^2*(outer x).toAdd.2) := by
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  simp only [torusAction_element, outer_element]
  rfl

private def commutatorLift (x u : unipotent (F := F)) (a d : Fˣ) : unipotent (F := F) :=
  x * u * torusAction a d x⁻¹ * u⁻¹

omit [CharP F 2] [Finite F] in
private theorem commutatorLift_val (x u : unipotent (F := F)) (a d : Fˣ) :
    (commutatorLift x u a d).val = ⁅x.val, u.val * diagonalTorus a d⁆ := by
  change x.val * u.val * (diagonalTorus a d * x.val⁻¹ * (diagonalTorus a d)⁻¹) * u.val⁻¹ = _
  simp only [commutatorElement_def]
  group

private theorem outer_commutatorLift (x u : unipotent (F := F)) (a d : Fˣ) :
    outer (commutatorLift x u a d) = Multiplicative.ofAdd
      ((1-(a:F)/(d:F))*(outer x).toAdd.1, (1-(d:F)^2)*(outer x).toAdd.2) := by
  simp only [commutatorLift, map_mul, outer_torusAction, map_inv]
  apply Multiplicative.toAdd.injective
  apply Prod.ext <;> simp <;> ring

private theorem square_test_weights (u : unipotent (F := F)) (a d : Fˣ)
    (h : ∀ x : unipotent (F := F), ⁅x.val, u.val * diagonalTorus a d⁆ ^ 2 = 1) :
    (1-(a:F)/(d:F)) * (1-(d:F)^2) = 0 := by
  have hh : (commutatorLift (element 1 0 0 1) u a d)^2 = 1 := by
    apply Subtype.ext
    exact (congrArg (fun z : Sp F => z^2) (commutatorLift_val _ _ _ _)).trans (h _)
  have hz := outer_product_zero _ hh
  simpa [outer_commutatorLift, outer_element] using hz

omit [Finite F] in
private theorem theta_inv (s t : F) : (theta s t)⁻¹ = theta s t := by
  apply inv_eq_of_mul_eq_one_right
  rw [theta_add]
  simpa only [CharTwo.add_self_eq_zero, theta] using (element_zero (F := F))

private theorem commutatorLift_theta (s t : F) (u : unipotent (F := F)) (a d : Fˣ) :
    commutatorLift (theta s t) u a d = theta ((1-(a:F)^2)*s) ((1-(a:F)*(d:F))*t) := by
  have hc := mem_center_iff.mp (theta_mem_center ((a:F)^2*s) ((a:F)*(d:F)*t)) u
  rw [commutatorLift, theta_inv]
  have ht : torusAction a d (theta s t) = theta ((a:F)^2*s) ((a:F)*(d:F)*t) := by
    simp only [theta, torusAction_element, mul_zero]
  rw [ht, mul_assoc (theta s t), hc, ← mul_assoc, mul_assoc _ u, mul_inv_cancel, mul_one]
  rw [theta_add]
  congr 1 <;> simp [CharTwo.sub_eq_add, add_mul]

omit [Finite F] in
private theorem weights_nonzero (a d : Fˣ) (hnt : ¬(a = 1 ∧ d = 1))
    (hw : (1-(a:F)/(d:F)) * (1-(d:F)^2) = 0) :
    1-(a:F)^2 ≠ 0 ∧ 1-(a:F)*(d:F) ≠ 0 := by
  have hs (z : F) (h : z^2 = 1) : z = 1 := by
    simpa only [CharTwo.neg_eq, or_self] using sq_eq_one_iff.mp h
  have hd0 : (d:F) ≠ 0 := d.ne_zero
  rcases mul_eq_zero.mp hw with he | he
  · have had : a = d := Units.ext ((div_eq_one_iff_eq hd0).mp (sub_eq_zero.mp he).symm)
    subst d
    have ha : (a:F) ≠ 1 := fun hh => hnt ⟨Units.ext hh, Units.ext hh⟩
    constructor
    · exact fun hh => ha (hs _ (sub_eq_zero.mp hh).symm)
    · exact fun hh => ha (hs _ (by simpa only [pow_two] using (sub_eq_zero.mp hh).symm))
  · have hd : d = 1 := Units.ext (hs _ (sub_eq_zero.mp he).symm)
    subst d
    have ha : (a:F) ≠ 1 := fun hh => hnt ⟨Units.ext hh, rfl⟩
    constructor
    · exact fun hh => ha (hs _ (sub_eq_zero.mp hh).symm)
    · simpa using (sub_ne_zero.mpr (Ne.symm ha))

omit [CharP F 2] [Finite F] in
private theorem exists_unipotent_torus (g : borel (F := F)) :
    ∃ (u : unipotent (F := F)) (a d : Fˣ), g.val = u.val * diagonalTorus a d := by
  let c := borelCharacters g
  let t := EvenBorelTorus.torusSection c
  have hu : ((g * t⁻¹ : borel (F := F)) : Sp F) ∈ unipotent := by
    apply (borelCharacters_eq_one _).mp
    simp [t, c]
  refine ⟨⟨(g*t⁻¹).val, hu⟩, c.1, c.1⁻¹*c.2, ?_⟩
  change g.val = (g.val * (diagonalTorus c.1 (c.1⁻¹*c.2))⁻¹) * diagonalTorus c.1 (c.1⁻¹*c.2)
  group

/-- A nonunipotent flag element passing the square test moves both central root coordinates. -/
theorem central_commutator_injective (g : borel (F := F))
    (h : ∀ x : unipotent (F := F), ⁅x.val, g.val⁆ ^ 2 = 1)
    (hg : g.val ∉ unipotent) :
    Function.Injective (fun st : F × F => ⁅(theta st.1 st.2).val, g.val⁆) := by
  obtain ⟨u,a,d,he⟩ := exists_unipotent_torus g
  have hnt : ¬(a = 1 ∧ d = 1) := by
    rintro ⟨rfl,rfl⟩
    apply hg
    have ht : diagonalTorus (1:Fˣ) 1 = 1 := (diagonalTorusHom (F := F)).map_one
    rw [he, ht, mul_one]
    exact u.property
  have hw := weights_nonzero a d hnt (square_test_weights u a d (by simpa only [he] using h))
  intro st st' hh
  change ⁅(theta st.1 st.2).val, g.val⁆ = ⁅(theta st'.1 st'.2).val, g.val⁆ at hh
  rw [he, ← commutatorLift_val, ← commutatorLift_val] at hh
  have hh' := Subtype.val_injective hh
  rw [commutatorLift_theta, commutatorLift_theta] at hh'
  have hc := (element_eq_iff _ _ _ _ _ _ _ _).mp hh'
  exact Prod.ext (mul_left_cancel₀ hw.1 hc.2.1) (mul_left_cancel₀ hw.2 hc.2.2.1)
end
end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.BorelPlacement.MatrixBlocks.RootCommutators
