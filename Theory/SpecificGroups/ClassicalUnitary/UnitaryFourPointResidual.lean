module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointRadicalSpecial
public import Theory.GroupTheory.SolvableResidual
public import Theory.SpecificGroups.SymmetricFourSolvable

/-!
# Residuals of the unitary-four point local

For a nontrivial involution in characteristic two, a fixed-field diagonal
Levi element different from 0 and 1 makes both radical root groups
commutators. The radical center consists of commutators as well, and SL₂
is perfect when the fixed field has more than two elements. Thus the
actual isotropic vector stabilizer is perfect. With binary fixed field,
its radical is solvable of derived length at most two and its quotient
acts faithfully on four vectors, so the entire local group is solvable.

The point-parabolic scalar character takes values in the odd-order field
unit group. Every two-subgroup therefore fixes the vector. Relative
normality and characteristicity give equality of the embedded two-cores
for all intermediate overgroups. These statements also hold in the
faithful projective model.

The residual here is the solvable residual (the terminal derived subgroup),
not O² or an odd residual; the core statements concern O₂. Source:
Aschbacher--Smith F.1.12(II), printed pp. 263--264 of `refs/quasithin.pdf`.
The binary case is explicitly exceptional in that statement.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient
open scoped commutatorElement
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointResidual
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "R" => radical F σ hσ
local notation "L" => localSU F (form F σ hσ)
local notation "κ" => coordinatesOfRadical F σ hσ

private theorem coord_ext (a b : R) (hx : (κ a).x = (κ b).x)
    (hy : (κ a).y = (κ b).y) (hz : (κ a).z = (κ b).z) : a = b := by
  apply (radicalCoordinatesEquiv F σ hσ).symm.injective
  change κ a = κ b
  cases hca : κ a
  cases hcb : κ b
  simp_all

private theorem coord_mul (a b : R) :
    (κ (a*b)).x = (κ a).x + (κ b).x ∧
    (κ (a*b)).y = (κ a).y + (κ b).y ∧
    (κ (a*b)).z = (κ a).z + (κ b).z + σ (κ a).y * (κ b).x +
      σ (κ a).x * (κ b).y := by
  obtain ⟨c, rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective a
  obtain ⟨d, rfl⟩ := (radicalCoordinatesEquiv F σ hσ).surjective b
  exact radical_mul_coordinates F σ hσ c d

private def rootX (x : F) : R := radicalOfCoordinates F σ hσ ⟨x,0,0,by simp⟩
private def rootY (y : F) : R := radicalOfCoordinates F σ hσ ⟨0,y,0,by simp⟩

private theorem rootX_mul (x y : F) : rootX F σ hσ x * rootX F σ hσ y =
    rootX F σ hσ (x+y) := by
  apply coord_ext F σ hσ <;>
    simp [rootX, coordinatesOfRadical, radicalOfCoordinates, radicalElement,
      radicalMatrix, add_comm]

private theorem rootY_mul (x y : F) : rootY F σ hσ x * rootY F σ hσ y =
    rootY F σ hσ (x+y) := by
  apply coord_ext F σ hσ <;>
    simp [rootY, coordinatesOfRadical, radicalOfCoordinates, radicalElement,
      radicalMatrix, add_comm]

private theorem diagonal_conjugate_X (a : FixedBy.subfield F σ) (ha : a ≠ 0) (x : F) :
    leviSL F σ hσ (SpecialLinearGroup.diag2 a ha) * (rootX F σ hσ x).val *
      (leviSL F σ hσ (SpecialLinearGroup.diag2 a ha))⁻¹ =
      (rootX F σ hσ ((a : F)*x)).val := by
  have hc := leviSL_conjugation_coordinates F σ hσ
    (SpecialLinearGroup.diag2 a ha) (⟨x,0,0,by simp⟩ : RadicalCoordinates F σ)
  have he := coord_ext F σ hσ
    (leviConjugate F σ hσ ((middleEquivSL F σ hσ).symm
      (SpecialLinearGroup.diag2 a ha)) ⟨x,0,0,by simp⟩)
    (rootX F σ hσ ((a : F)*x))
  exact congrArg (fun r : R => r.val) (he (by
    change _ = (a : F) * x
    simpa [SpecialLinearGroup.diag2_coe'] using hc.1) (by
    change _ = 0
    simpa [SpecialLinearGroup.diag2_coe'] using hc.2.1) hc.2.2)

private theorem diagonal_conjugate_Y (a : FixedBy.subfield F σ) (ha : a ≠ 0) (x : F) :
    leviSL F σ hσ (SpecialLinearGroup.diag2 a ha) * (rootY F σ hσ x).val *
      (leviSL F σ hσ (SpecialLinearGroup.diag2 a ha))⁻¹ =
      (rootY F σ hσ ((a : F)⁻¹*x)).val := by
  have hc := leviSL_conjugation_coordinates F σ hσ
    (SpecialLinearGroup.diag2 a ha) (⟨0,x,0,by simp⟩ : RadicalCoordinates F σ)
  have he := coord_ext F σ hσ
    (leviConjugate F σ hσ ((middleEquivSL F σ hσ).symm
      (SpecialLinearGroup.diag2 a ha)) ⟨0,x,0,by simp⟩)
    (rootY F σ hσ ((a : F)⁻¹*x))
  exact congrArg (fun r : R => r.val) (he (by
    change _ = 0
    simpa [SpecialLinearGroup.diag2_coe'] using hc.1) (by
    change _ = (a : F)⁻¹ * x
    simpa [SpecialLinearGroup.diag2_coe'] using hc.2.1) hc.2.2)

private theorem rootX_zero : rootX F σ hσ 0 = 1 := by
  apply coord_ext F σ hσ <;> rfl

private theorem rootY_zero : rootY F σ hσ 0 = 1 := by
  apply coord_ext F σ hσ <;> rfl

private theorem rootX_inv (x : F) : (rootX F σ hσ x)⁻¹ = rootX F σ hσ x := by
  apply inv_eq_of_mul_eq_one_right
  rw [rootX_mul, CharTwo.add_self_eq_zero, rootX_zero]

private theorem rootY_inv (x : F) : (rootY F σ hσ x)⁻¹ = rootY F σ hσ x := by
  apply inv_eq_of_mul_eq_one_right
  rw [rootY_mul, CharTwo.add_self_eq_zero, rootY_zero]

private theorem rootX_mem_commutator (a : FixedBy.subfield F σ) (ha : a ≠ 0)
    (ha1 : a ≠ 1) (x : F) : (rootX F σ hσ x).val ∈ commutator L := by
  have haF : (a : F) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hd : (a : F) + 1 ≠ 0 := by simpa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] using haF
  let t := x / ((a : F) + 1)
  have he : ⁅leviSL F σ hσ (SpecialLinearGroup.diag2 a ha), (rootX F σ hσ t).val⁆ =
      (rootX F σ hσ x).val := by
    rw [commutatorElement_def, diagonal_conjugate_X, ← Subgroup.coe_inv, rootX_inv,
      ← Subgroup.coe_mul, rootX_mul]
    congr 2
    change (a : F) * (x / ((a : F) + 1)) + x / ((a : F) + 1) = x
    rw [← add_one_mul, mul_div_cancel₀ _ hd]
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

private theorem rootY_mem_commutator (a : FixedBy.subfield F σ) (ha : a ≠ 0)
    (ha1 : a ≠ 1) (x : F) : (rootY F σ hσ x).val ∈ commutator L := by
  have haF : (a : F) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hd : (a : F)⁻¹ + 1 ≠ 0 := by
    simpa [add_eq_zero_iff_eq_neg, CharTwo.neg_eq, inv_eq_one] using haF
  let t := x / ((a : F)⁻¹ + 1)
  have he : ⁅leviSL F σ hσ (SpecialLinearGroup.diag2 a ha), (rootY F σ hσ t).val⁆ =
      (rootY F σ hσ x).val := by
    rw [commutatorElement_def, diagonal_conjugate_Y, ← Subgroup.coe_inv, rootY_inv,
      ← Subgroup.coe_mul, rootY_mul]
    congr 2
    change (a : F)⁻¹ * (x / ((a : F)⁻¹ + 1)) + x / ((a : F)⁻¹ + 1) = x
    rw [← add_one_mul, mul_div_cancel₀ _ hd]
  rw [← he]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- The radical is generated inside the derived group by its two root groups and center. -/
theorem radical_le_commutator (hnt : ∃ u, σ u ≠ u)
    (a : FixedBy.subfield F σ) (ha : a ≠ 0) (ha1 : a ≠ 1) : R ≤ commutator L := by
  intro r hr
  let c := κ (⟨r,hr⟩ : R)
  let t := (radicalParametersEquiv F σ hσ c).2.2
  have hc : centralElement F σ hσ t ∈ Subgroup.center R := by
    rw [mem_center_radical_iff F σ hσ hnt]
    exact ⟨rfl,rfl⟩
  obtain ⟨b,d,hbd⟩ := center_radical_exists_commutator F σ hσ hnt _ hc
  have hz : (centralElement F σ hσ t).val ∈ commutator L := by
    rw [← hbd]
    change (radical F σ hσ).subtype ⁅b,d⁆ ∈ _
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have he : rootY F σ hσ c.y * rootX F σ hσ c.x * centralElement F σ hσ t =
      (⟨r,hr⟩ : R) := by
    apply coord_ext F σ hσ
    · simp only [(coord_mul F σ hσ _ _).1]
      change 0 + c.x + 0 = c.x
      simp
    · simp only [(coord_mul F σ hσ _ _).2.1]
      change c.y + 0 + 0 = c.y
      simp
    · simp only [(coord_mul F σ hσ _ _).2.2,
        (coord_mul F σ hσ _ _).1, (coord_mul F σ hσ _ _).2.1]
      change (0 + 0 + σ c.y * c.x + σ 0 * 0) + (c.z + c.x * σ c.y) +
        σ (c.y + 0) * 0 + σ (0 + c.x) * 0 = c.z
      simp [mul_comm, add_left_comm, CharTwo.add_self_eq_zero]
  rw [← show (rootY F σ hσ c.y).val * (rootX F σ hσ c.x).val *
      (centralElement F σ hσ t).val = r from congrArg Subtype.val he]
  exact (commutator L).mul_mem ((commutator L).mul_mem
    (rootY_mem_commutator F σ hσ a ha ha1 _) (rootX_mem_commutator F σ hσ a ha ha1 _)) hz

/-- Away from the binary fixed field the actual vector stabilizer is perfect. -/
theorem localSU_isPerfect (hnt : ∃ u, σ u ≠ u)
    (a : FixedBy.subfield F σ) (ha : a ≠ 0) (ha1 : a ≠ 1) : Group.IsPerfect L := by
  have ha2 : a ^ 2 ≠ 1 := by
    intro h
    rcases (sq_eq_one_iff).mp h with h | h
    · exact ha1 h
    · exact ha1 (by simpa [CharTwo.neg_eq] using h)
  let : Group.IsPerfect (SpecialLinearGroup (Fin 2) (FixedBy.subfield F σ)) :=
    ⟨Matrix.SL2.commutator_eq_top ha ha2⟩
  have hlevi : ∀ B, leviSL F σ hσ B ∈ commutator L := by
    intro B
    have hm := map_derivedSeries_le_derivedSeries (leviSL F σ hσ) 1
    rw [derivedSeries_one, derivedSeries_one, Group.IsPerfect.commutator_eq_top] at hm
    exact hm ⟨B, Subgroup.mem_top _, rfl⟩
  refine ⟨top_unique ?_⟩
  intro g _
  let l := leviSL F σ hσ (middleSL F σ hσ g)
  have hr : g * l⁻¹ ∈ R := by
    rw [← middleSU_ker]
    apply (middleEquivSL F σ hσ).injective
    rw [map_one]
    change middleSL F σ hσ (g * l⁻¹) = 1
    simp [l]
  have hd := radical_le_commutator F σ hσ hnt a ha ha1 hr
  simpa only [l, inv_mul_cancel_right] using (commutator L).mul_mem hd (hlevi (middleSL F σ hσ g))


/-- The radical is solvable (indeed it has nilpotency class at most two). -/
theorem radical_isSolvable : Group.IsSolvable R := by
  refine ⟨⟨2, ?_⟩⟩
  change ⁅commutator R, commutator R⁆ = ⊥
  apply le_bot_iff.mp
  calc
    ⁅commutator R, commutator R⁆ ≤ ⁅Subgroup.center R, Subgroup.center R⁆ :=
      Subgroup.commutator_mono (commutator_radical_le_center F σ hσ)
        (commutator_radical_le_center F σ hσ)
    _ = ⊥ := Subgroup.commutator_self_eq_bot_iff.mpr inferInstance

/-- A binary fixed field gives a solvable quotient and hence a solvable local group. -/
theorem localSU_isSolvable_of_fixedField_card_two [Finite F]
    (hq : Nat.card (FixedBy.subfield F σ) = 2) : Group.IsSolvable L := by
  let K := FixedBy.subfield F σ
  let V := Fin 2 → K
  have hV : Nat.card V = 4 := by
    rw [Nat.card_fun, Nat.card_fin, hq]
    rfl
  let e : V ≃ Fin 4 := (Finite.equivFin V).trans (finCongr hV)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm V) :=
    Group.isSolvable_of_isSolvable_injective (f := e.permCongrHom.toMonoidHom) e.permCongrHom.injective
  let : FaithfulSMul (SpecialLinearGroup (Fin 2) K) V := ⟨by
    intro g h he
    apply SpecialLinearGroup.toLin'_injective
    apply LinearEquiv.ext
    intro v
    exact he v⟩
  let : Group.IsSolvable (SpecialLinearGroup (Fin 2) K) :=
    Group.isSolvable_of_isSolvable_injective
      (f := MulAction.toPermHom (SpecialLinearGroup (Fin 2) K) V)
      MulAction.toPerm_injective
  let : Group.IsSolvable (L ⧸ R) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (quotientEquivSL F σ hσ).toMonoidHom) (quotientEquivSL F σ hσ).injective
  let : Group.IsSolvable R := radical_isSolvable F σ hσ
  exact (Group.isSolvable_iff_subgroup_quotient (radical F σ hσ)).mpr ⟨inferInstance,inferInstance⟩

section Parabolic
variable [Finite F] (J : HermitianForm 4 F)

/-- The point character, valued in the actual multiplicative field group. -/
def pointScalarUnits : pointParabolicSU F J →* Fˣ := (pointScalar F J).toHomUnits

omit [CharP F 2] in
/-- Its kernel is the vector stabilizer, relative to the point parabolic. -/
theorem pointScalarUnits_ker : (pointScalarUnits F J).ker =
    (localSU F J).subgroupOf (pointParabolicSU F J) := by
  rw [localSU_subgroupOf_eq_ker]
  ext g
  exact Units.ext_iff

/-- In characteristic two the scalar target has odd order. -/
theorem field_units_card_odd : Odd (Nat.card Fˣ) := by
  let := Fintype.ofFinite F
  have he := FiniteField.even_card_of_char_two (F := F) (ringChar.eq F 2)
  have hp := Fintype.card_pos (α := F)
  rw [Nat.card_units, Nat.card_eq_fintype_card, Nat.odd_iff]
  omega

/-- Every two-subgroup of the point parabolic fixes the vector itself:
its scalar image in the odd-order unit group is trivial. -/
theorem twoSubgroup_le_localSU (S : Subgroup (SU F J))
    (hS : IsPGroup 2 S) (hSP : S ≤ pointParabolicSU F J) : S ≤ localSU F J := by
  let f := pointScalarUnits F J
  let T := S.subgroupOf (pointParabolicSU F J)
  have hT : IsPGroup 2 T := hS.comap_subtype
  have himage : T.map f = ⊥ := by
    apply Subgroup.card_eq_one.mp
    exact (hT.map f).card_eq_or_dvd.resolve_right (fun h =>
      (field_units_card_odd F).not_two_dvd_nat (h.trans (Subgroup.card_subgroup_dvd_card _)))
  intro g hg
  have hk : (⟨g, hSP hg⟩ : pointParabolicSU F J) ∈ f.ker :=
    himage.le ⟨⟨g, hSP hg⟩, hg, rfl⟩
  rw [pointScalarUnits_ker] at hk
  exact hk

/-- The same containment for the literal faithful projective image. -/
theorem twoSubgroup_le_localPSU (S : Subgroup (PSU F J))
    (hS : IsPGroup 2 S) (hSP : S ≤ pointParabolicPSU F J) : S ≤ localPSU F J := by
  have hpre : S.comap (project F J) ≤ pointParabolicSU F J := by
    intro g hg
    obtain ⟨x,hx,he⟩ := hSP hg
    exact (project_injective F J he) ▸ hx
  have hle := twoSubgroup_le_localSU F J (S.comap (project F J))
    (hS.comap_of_injective _ (project_injective F J)) hpre
  intro g hg
  obtain ⟨x,hx,rfl⟩ := hSP hg
  exact ⟨x,hle hg,rfl⟩

private theorem map_core_eq_of_normal {G : Type*} [Group G]
    (K : Subgroup G) [K.Normal] (h : pCore 2 G ≤ K) :
    (pCore 2 K).map K.subtype = pCore 2 G := by
  apply le_antisymm
  · exact le_sSup ⟨ConjAct.normal_of_characteristic_of_normal,
      pCore_isPGroup.map K.subtype⟩
  · have hr : (pCore 2 G).subgroupOf K ≤ pCore 2 K :=
      le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective K.subtype
        K.subtype_injective⟩
    simpa only [Subgroup.map_subgroupOf_eq_of_le h] using
      Subgroup.map_mono (f := K.subtype) hr

/-- For every intermediate overgroup, the embedded two-core agrees with the local core. -/
theorem localSU_core_map (H : Subgroup (SU F J))
    (hLH : localSU F J ≤ H) (hHP : H ≤ pointParabolicSU F J) :
    (pCore 2 (localSU F J)).map (localSU F J).subtype = (pCore 2 H).map H.subtype := by
  let K := (localSU F J).subgroupOf H
  let : K.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr
    (hHP.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (localSU_le_pointParabolicSU F J)).mp (localSU_normal F J)))
  have h : pCore 2 H ≤ K := by
    intro x hx
    exact twoSubgroup_le_localSU F J ((pCore 2 H).map H.subtype)
      (pCore_isPGroup.map H.subtype) ((Subgroup.map_subtype_le _).trans hHP)
      ⟨x,hx,rfl⟩
  let e := Subgroup.subgroupOfEquivOfLe hLH
  have he : (localSU F J).subtype.comp e.toMonoidHom = H.subtype.comp K.subtype := rfl
  rw [← pCore_map_iso 2 e, Subgroup.map_map, he, ← Subgroup.map_map,
    map_core_eq_of_normal K h]

/-- The embedded core equality in the projective model, for any intermediate overgroup. -/
theorem localPSU_core_map (H : Subgroup (PSU F J))
    (hLH : localPSU F J ≤ H) (hHP : H ≤ pointParabolicPSU F J) :
    (pCore 2 (localPSU F J)).map (localPSU F J).subtype = (pCore 2 H).map H.subtype := by
  let K := (localPSU F J).subgroupOf H
  let : K.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr
    (hHP.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (localPSU_le_pointParabolicPSU F J)).mp (localPSU_normal F J)))
  have h : pCore 2 H ≤ K := by
    intro x hx
    exact twoSubgroup_le_localPSU F J ((pCore 2 H).map H.subtype)
      (pCore_isPGroup.map H.subtype) ((Subgroup.map_subtype_le _).trans hHP)
      ⟨x,hx,rfl⟩
  let e := Subgroup.subgroupOfEquivOfLe hLH
  have he : (localPSU F J).subtype.comp e.toMonoidHom = H.subtype.comp K.subtype := rfl
  rw [← pCore_map_iso 2 e, Subgroup.map_map, he, ← Subgroup.map_map,
    map_core_eq_of_normal K h]

omit [CharP F 2] in
/-- The scalar character kills the parabolic solvable residual. -/
theorem pointParabolic_solvableResidual_le :
    (Subgroup.solvableResidual (pointParabolicSU F J)).map (pointParabolicSU F J).subtype ≤
      localSU F J := by
  have h : Subgroup.solvableResidual (pointParabolicSU F J) ≤
      (localSU F J).subgroupOf (pointParabolicSU F J) := by
    rw [localSU_subgroupOf_eq_ker]
    exact (Subgroup.solvableResidual_le_derivedSeries 1).trans
      ((derivedSeries_one _).le.trans (by
        intro x hx
        have he := Abelianization.commutator_subset_ker (pointScalar F J).toHomUnits hx
        exact congrArg Units.val he))
  simpa only [Subgroup.map_subgroupOf_eq_of_le (localSU_le_pointParabolicSU F J)] using
    Subgroup.map_mono (f := (pointParabolicSU F J).subtype) h

omit [CharP F 2] in
/-- A perfect vector stabilizer is exactly the embedded solvable residual of its parabolic. -/
theorem pointParabolic_solvableResidual_eq_of_perfect [Group.IsPerfect (localSU F J)] :
    (Subgroup.solvableResidual (pointParabolicSU F J)).map (pointParabolicSU F J).subtype =
      localSU F J :=
  le_antisymm (pointParabolic_solvableResidual_le F J)
    (Subgroup.le_map_solvableResidual_of_isPerfect _ _ (localSU_le_pointParabolicSU F J))
end Parabolic
end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointResidual
