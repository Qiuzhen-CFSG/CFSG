module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# Upper-unitriangular Sylow subgroups of SU₄ in characteristic two

For the antidiagonal Hermitian form, pull back the upper unipotent subgroup
of SL₂ over the fixed field along the middle-block action of the first-vector
stabilizer. The result is exactly the upper-unitriangular matrix subgroup.
The Heisenberg kernel and the one-dimensional unipotent image give its order
|F|² |F^σ|², hence q⁶ when |F| = q² and |F^σ| = q.

For Sylow maximality, a two-overgroup has a nonzero fixed vector on F⁴.
Two explicit radical elements force that vector onto the first coordinate
line, placing the overgroup in the first-vector stabilizer. The SL₂ Sylow
calculation then gives equality. Thus no ambient order formula is needed.
The canonical projection to the image in PGL transports this Sylow faithfully.

Source: the unitary flag construction in Aschbacher--Smith F.1.6 and
F.1.12(I)(6), printed pp.261, 263--264 of `refs/quasithin.pdf`.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourFlag
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointLocal
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourPointQuotient
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
variable (F : Type*) [Field F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)

abbrev FixedField := FixedBy.subfield F σ

def localUpper : Subgroup (localSU F (form F σ hσ)) :=
  (SpecialLinearGroup.upperUnipotent (FixedField F σ)).comap (middleSL F σ hσ)

def upper : Subgroup (SU F (form F σ hσ)) :=
  (localUpper F σ hσ).map (localSU F (form F σ hσ)).subtype

theorem middleSL_ker : (middleSL F σ hσ).ker = radical F σ hσ := by
  rw [middleSL, MonoidHom.ker_comp_of_injective _ _ (middleEquivSL F σ hσ).injective,
    middleSU_ker]

theorem middleSL_surjective : Function.Surjective (middleSL F σ hσ) :=
  fun B => ⟨leviSL F σ hσ B, middleSL_leviSL F σ hσ B⟩

theorem middleSL_val (a : localSU F (form F σ hσ)) :
    (middleSL F σ hσ a).val.map (FixedBy.subfield F σ).subtype =
      middleBlock F σ hσ a := by
  rw [← middleEquivSL_symm_val]
  change ((middleEquivSL F σ hσ).symm
    ((middleEquivSL F σ hσ) (middleSU F σ hσ a))).val.val = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem radical_le_localUpper : radical F σ hσ ≤ localUpper F σ hσ := by
  rw [← middleSL_ker]
  exact Subgroup.ker_le_comap _ _

theorem mem_localUpper (a : localSU F (form F σ hσ)) :
    a ∈ localUpper F σ hσ ↔
      a.val.val.val 1 1 = 1 ∧ a.val.val.val 2 1 = 0 ∧ a.val.val.val 2 2 = 1 := by
  change middleSL F σ hσ a ∈ SpecialLinearGroup.upperUnipotent (FixedField F σ) ↔ _
  have he := middleSL_val F σ hσ a
  constructor
  · intro ha
    obtain ⟨t, ht⟩ := (SpecialLinearGroup.mem_upperUnipotent (FixedField F σ) _).mp ha
    rw [← ht] at he
    exact ⟨by simpa [SpecialLinearGroup.transvection_coe, middleBlock] using
      (congrArg (fun M => M 0 0) he).symm,
      by simpa [SpecialLinearGroup.transvection_coe, middleBlock] using
        (congrArg (fun M => M 1 0) he).symm,
      by simpa [SpecialLinearGroup.transvection_coe, middleBlock] using
        (congrArg (fun M => M 1 1) he).symm⟩
  · rintro ⟨h11, h21, h22⟩
    apply (SpecialLinearGroup.mem_upperUnipotent (FixedField F σ) _).mpr
    refine ⟨(middleSL F σ hσ a).val 0 1, ?_⟩
    apply Subtype.ext
    ext i j
    have hij := congrArg (fun M => M i j) he
    fin_cases i <;> fin_cases j
    · simpa [SpecialLinearGroup.transvection_coe, middleBlock, h11] using hij.symm
    · simp [SpecialLinearGroup.transvection_coe]
    · simpa [SpecialLinearGroup.transvection_coe, middleBlock, h21] using hij.symm
    · simpa [SpecialLinearGroup.transvection_coe, middleBlock, h22] using hij.symm

theorem mem_upper (a : SU F (form F σ hσ)) :
    a ∈ upper F σ hσ ↔ a ∈ localSU F (form F σ hσ) ∧
      a.val.val 1 1 = 1 ∧ a.val.val 2 1 = 0 ∧ a.val.val 2 2 = 1 := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.property, (mem_localUpper F σ hσ b).mp hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨⟨a, ha⟩, (mem_localUpper F σ hσ ⟨a, ha⟩).mpr hb, rfl⟩

/-- Membership is exactly upper triangularity with every diagonal entry equal to one. -/
theorem mem_upper_iff_entries (a : SU F (form F σ hσ)) :
    a ∈ upper F σ hσ ↔
      (∀ i j : Fin 4, j < i → a.val.val i j = 0) ∧ ∀ i, a.val.val i i = 1 := by
  rw [mem_upper, mem_localSU]
  constructor
  · rintro ⟨⟨h00,h10,h20,h30⟩, h11,h21,h22⟩
    obtain ⟨_,h31,h32,h33⟩ := last_row F σ hσ a
      ((mem_localSU F _ a).mpr ⟨h00,h10,h20,h30⟩)
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i
      fin_cases i <;> assumption
  · rintro ⟨ht,hd⟩
    exact ⟨⟨hd 0,ht 1 0 (by decide),ht 2 0 (by decide),ht 3 0 (by decide)⟩,
      hd 1,ht 2 1 (by decide),hd 2⟩

theorem radicalElement_mem_upper (c : RadicalCoordinates F σ) :
    radicalElement F σ hσ c ∈ upper F σ hσ :=
  ⟨(radicalOfCoordinates F σ hσ c).val,
    radical_le_localUpper F σ hσ (radicalOfCoordinates F σ hσ c).property, rfl⟩

theorem localUpper_card : Nat.card (localUpper F σ hσ) =
    Nat.card F ^ 2 * Nat.card (FixedField F σ) ^ 2 := by
  have hk : (middleSL F σ hσ).ker ≤ localUpper F σ hσ := Subgroup.ker_le_comap _ _
  have hc := ((middleSL F σ hσ).ker.subgroupOf (localUpper F σ hσ)).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hk).toEquiv] at hc
  change Nat.card (middleSL F σ hσ).ker *
    (middleSL F σ hσ).ker.relIndex (localUpper F σ hσ) = _ at hc
  rw [Subgroup.relIndex_ker, localUpper,
    Subgroup.map_comap_eq_self_of_surjective (middleSL_surjective F σ hσ),
    SpecialLinearGroup.card_upperUnipotent, middleSL_ker, radical_card] at hc
  exact hc.symm.trans (by dsimp only [FixedField]; ring)

theorem upper_card : Nat.card (upper F σ hσ) =
    Nat.card F ^ 2 * Nat.card (FixedField F σ) ^ 2 := by
  rw [upper, Subgroup.card_map_of_injective (localSU F (form F σ hσ)).subtype_injective,
    localUpper_card]

variable [Finite F]

theorem radical_isTwoGroup : IsPGroup 2 (radical F σ hσ) := by
  let := Fintype.ofFinite F
  let := Fintype.ofFinite (FixedField F σ)
  obtain ⟨a, _, ha⟩ := FiniteField.card F 2
  obtain ⟨b, _, hb⟩ := FiniteField.card (FixedField F σ) 2
  apply IsPGroup.of_card (n := a + a + b)
  rw [radical_card, Nat.card_eq_fintype_card, ha]
  rw [Nat.card_eq_fintype_card, hb, pow_add, pow_add]

def localSylow : Sylow 2 (localSU F (form F σ hσ)) :=
  (SpecialLinearGroup.upperUnipotentSylow (FixedField F σ) 2).comapOfKerIsPGroup
    (middleSL F σ hσ) (by rw [middleSL_ker]; exact radical_isTwoGroup F σ hσ)
    (by rw [MonoidHom.range_eq_top.mpr (middleSL_surjective F σ hσ)]; exact le_top)

theorem coe_localSylow : (localSylow F σ hσ : Subgroup _) = localUpper F σ hσ := rfl

theorem upper_isTwoGroup : IsPGroup 2 (upper F σ hσ) :=
  (localSylow F σ hσ).isPGroup'.map _

theorem upper_le_borel : upper F σ hσ ≤ borelSU F (form F σ hσ) := by
  intro a ha
  have ht := ((mem_upper_iff_entries F σ hσ a).mp ha).1
  exact ⟨(mem_pointParabolicSU F _ a).mpr
    ⟨ht 1 0 (by decide), ht 2 0 (by decide), ht 3 0 (by decide)⟩,
    (mem_planeParabolicSU F _ a).mpr
    ⟨ht 2 0 (by decide), ht 3 0 (by decide), ht 2 1 (by decide), ht 3 1 (by decide)⟩⟩

/-- Any two-overgroup fixes the first coordinate vector, because its nonzero
fixed vector is fixed by the explicit Heisenberg radical. -/
theorem overgroup_le_local (P : Subgroup (SU F (form F σ hσ)))
    (hP : IsPGroup 2 P) (hUP : upper F σ hσ ≤ P) : P ≤ localSU F (form F σ hσ) := by
  let := Fintype.ofFinite F
  obtain ⟨n, hn, hcard⟩ := FiniteField.card F 2
  have hpF : 2 ∣ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self 2 n.ne_zero
  have hpV : 2 ∣ Nat.card (Fin 4 → F) := by
    rw [Nat.card_fun]
    exact hpF.trans (dvd_pow_self (Nat.card F) (by simp))
  have hz : (0 : Fin 4 → F) ∈ MulAction.fixedPoints P (Fin 4 → F) := by
    rw [MulAction.mem_fixedPoints]
    intro g
    exact smul_zero g
  obtain ⟨v, hv, hnv⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 4 → F) hpV hz
  have hfix := MulAction.mem_fixedPoints.mp hv
  let cx : RadicalCoordinates F σ := ⟨1,0,0, by simp⟩
  let cy : RadicalCoordinates F σ := ⟨0,1,0, by simp⟩
  have hx := hfix ⟨radicalElement F σ hσ cx,
    hUP (radicalElement_mem_upper F σ hσ cx)⟩
  have hy := hfix ⟨radicalElement F σ hσ cy,
    hUP (radicalElement_mem_upper F σ hσ cy)⟩
  change radicalMatrix F σ cx *ᵥ v = v at hx
  change radicalMatrix F σ cy *ᵥ v = v at hy
  have hv1 : v 1 = 0 := by
    simpa [cy, radicalMatrix, mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hy 0
  have hv2 : v 2 = 0 := by
    simpa [cx, radicalMatrix, mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hx 0
  have hv3 : v 3 = 0 := by
    simpa [cx, radicalMatrix, mulVec, dotProduct, Fin.sum_univ_succ] using congrFun hx 1
  have hv0 : v 0 ≠ 0 := by
    intro he
    apply hnv
    ext i
    fin_cases i <;> simp_all
  intro a ha
  have h := hfix ⟨a,ha⟩
  change a.val.val *ᵥ v = v at h
  have he (i : Fin 4) : a.val.val i 0 * v 0 = v i := by
    simpa [mulVec, dotProduct, Fin.sum_univ_succ, hv1,hv2,hv3] using congrFun h i
  apply (mem_localSU F _ a).mpr
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact mul_right_cancel₀ hv0 (by simpa using he 0)
  · exact (mul_eq_zero.mp ((he 1).trans hv1)).resolve_right hv0
  · exact (mul_eq_zero.mp ((he 2).trans hv2)).resolve_right hv0
  · exact (mul_eq_zero.mp ((he 3).trans hv3)).resolve_right hv0

def sylow : Sylow 2 (SU F (form F σ hσ)) :=
  { upper F σ hσ with
    isPGroup' := upper_isTwoGroup F σ hσ
    is_maximal' := by
      intro P hP hUP
      have hPL := overgroup_le_local F σ hσ P hP hUP
      have he := (localSylow F σ hσ).is_maximal'
        (hP.comap_of_injective (localSU F (form F σ hσ)).subtype Subtype.val_injective)
        (show localUpper F σ hσ ≤ P.subgroupOf (localSU F (form F σ hσ)) from
          fun a ha => hUP ⟨a,ha,rfl⟩)
      apply le_antisymm _ hUP
      intro a ha
      refine ⟨⟨a,hPL ha⟩, ?_, rfl⟩
      rw [← coe_localSylow, ← he]
      exact ha }

theorem coe_sylow : (sylow F σ hσ : Subgroup _) = upper F σ hσ := rfl

def projectiveUpper : Subgroup (PSU F (form F σ hσ)) :=
  (upper F σ hσ).map (project F (form F σ hσ))

/-- The restriction uses the literal quotient-to-PGL map. -/
def upperProjectEquiv : upper F σ hσ ≃* projectiveUpper F σ hσ :=
  (upper F σ hσ).equivMapOfInjective (project F (form F σ hσ))
    (project_injective F (form F σ hσ))

@[simp] theorem upperProjectEquiv_apply (a : upper F σ hσ) :
    (upperProjectEquiv F σ hσ a).val = project F (form F σ hσ) a.val := rfl

theorem projectiveUpper_card : Nat.card (projectiveUpper F σ hσ) =
    Nat.card F ^ 2 * Nat.card (FixedField F σ) ^ 2 :=
  (Nat.card_congr (upperProjectEquiv F σ hσ).symm.toEquiv).trans (upper_card F σ hσ)

def projectiveSylow : Sylow 2 (PSU F (form F σ hσ)) :=
  (sylow F σ hσ).mapSurjective (project_surjective F (form F σ hσ))

theorem coe_projectiveSylow :
    (projectiveSylow F σ hσ : Subgroup _) = projectiveUpper F σ hσ := rfl

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
