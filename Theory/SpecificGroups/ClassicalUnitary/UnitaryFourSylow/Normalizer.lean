module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow

/-!
# The normalizer of the unitary-four Sylow subgroup

The full point-plane flag stabilizer is the normalizer of the explicit
upper-unitriangular Sylow subgroup. The diagonal character first proves
normality inside the flag stabilizer. Conversely, conjugating two point-radical
matrices and one middle-block transvection recovers the coordinate point and
plane from the unitriangular group, including over the field of order two.

This supplies the normalizer geometry for the U₄(q) amalgam in
Aschbacher--Smith F.1.4--12, printed pp.260--264 of `refs/quasithin.pdf`.
The full overlap retains its diagonal part; it is not identified with U.
-/

open Matrix BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open UnitaryFourFlag UnitaryFourPointLocal UnitaryFourPointQuotient
@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
variable (F : Type*) [Field F] [CharP F 2] [Finite F]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "B" => borelSU F (form F σ hσ)
local notation "U" => upper F σ hσ

omit [CharP F 2] in
/-- The stabilizer of the whole coordinate flag is exactly the triangular subgroup. -/
theorem mem_borel_iff_triangular (a : SU F (form F σ hσ)) :
    a ∈ B ↔ a.val.val.IsUpperTriangular := by
  constructor
  · rintro ⟨hp,hq⟩
    obtain ⟨h10,h20,h30⟩ := (mem_pointParabolicSU F _ a).mp hp
    obtain ⟨_,_,h21,h31⟩ := (mem_planeParabolicSU F _ a).mp hq
    have h00 : a.val.val 0 0 ≠ 0 := by
      intro h00
      apply GeneralLinearGroup.det_ne_zero a.val
      apply Matrix.det_eq_zero_of_column_eq_zero 0
      intro i
      fin_cases i <;> simp_all
    have hs00 : σ (a.val.val 0 0) ≠ 0 := by simpa using h00
    have hu := a.property.1
    change (form F σ hσ).conjTranspose a.val.val * gram F * a.val.val = gram F at hu
    have h32 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 2) hu
    simp [form, gram, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_succ, h10,h20,h30, hs00] at h32
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro h
    exact ⟨(mem_pointParabolicSU F _ a).mpr
      ⟨h (by decide : (0 : Fin 4) < 1), h (by decide : (0 : Fin 4) < 2),
        h (by decide : (0 : Fin 4) < 3)⟩,
      (mem_planeParabolicSU F _ a).mpr
      ⟨h (by decide : (0 : Fin 4) < 2), h (by decide : (0 : Fin 4) < 3),
        h (by decide : (1 : Fin 4) < 2), h (by decide : (1 : Fin 4) < 3)⟩⟩

/-- Diagonal entries of a flag stabilizer multiply coordinatewise. -/
def diagonal : B →* (Fin 4 → F) where
  toFun a i := a.val.val.val i i
  map_one' := by ext i; simp
  map_mul' a b := by
    ext i
    change ∑ j, a.val.val.val i j * b.val.val.val j i = _
    apply Finset.sum_eq_single i
    · intro j _ hji
      rcases lt_or_gt_of_ne hji with h | h
      · rw [(mem_borel_iff_triangular F σ hσ a.val).mp a.property h, zero_mul]
      · rw [(mem_borel_iff_triangular F σ hσ b.val).mp b.property h, mul_zero]
    · simp

theorem upper_subgroupOf_borel_eq_ker : (U).subgroupOf B = (diagonal F σ hσ).ker := by
  ext a
  change a.val ∈ U ↔ diagonal F σ hσ a = 1
  rw [mem_upper_iff_entries]
  have ht := (mem_borel_iff_triangular F σ hσ a.val).mp a.property
  constructor
  · intro h
    exact funext h.2
  · intro h
    exact ⟨fun i j hij => ht hij, fun i => congrFun h i⟩

instance upper_normal_in_borel : ((U).subgroupOf B).Normal := by
  rw [upper_subgroupOf_borel_eq_ker]
  infer_instance

theorem borel_le_normalizer_upper : B ≤ Subgroup.normalizer (U : Set _) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (upper_le_borel F σ hσ)).mp
    (upper_normal_in_borel F σ hσ)

omit [Finite F] in
private theorem conjugate_column_zero (g t : SU F (form F σ hσ))
    (hg : g ∈ Subgroup.normalizer (U : Set _)) (ht : t ∈ U) (i : Fin 4) :
    (t * g).val.val i 0 = g.val.val i 0 := by
  let v := g⁻¹ * t * g
  have hv : v ∈ U := (Subgroup.mem_normalizer_iff''.mp hg t).mp ht
  obtain ⟨hvtri, hvdiag⟩ := (mem_upper_iff_entries F σ hσ v).mp hv
  have he : t * g = g * v := by dsimp [v]; group
  rw [he]
  change ∑ j, g.val.val i j * v.val.val j 0 = _
  simp [Fin.sum_univ_succ, hvdiag 0, hvtri 1 0 (by decide),
    hvtri 2 0 (by decide), hvtri 3 0 (by decide)]

omit [Finite F] in
private theorem conjugate_column_one (g t : SU F (form F σ hσ))
    (hg : g ∈ Subgroup.normalizer (U : Set _)) (ht : t ∈ U) (h10 : g.val.val 1 0 = 0) :
    (t * g).val.val 1 1 = g.val.val 1 1 := by
  let v := g⁻¹ * t * g
  have hv : v ∈ U := (Subgroup.mem_normalizer_iff''.mp hg t).mp ht
  obtain ⟨hvtri, hvdiag⟩ := (mem_upper_iff_entries F σ hσ v).mp hv
  have he : t * g = g * v := by dsimp [v]; group
  rw [he]
  change ∑ j, g.val.val 1 j * v.val.val j 1 = _
  simp [Fin.sum_univ_succ, h10, hvdiag 1, hvtri 2 1 (by decide), hvtri 3 1 (by decide)]

/-- Three elementary unitary operations recover the point and plane from U. -/
theorem normalizer_upper_le_borel : Subgroup.normalizer (U : Set _) ≤ B := by
  intro g hg
  let cx : RadicalCoordinates F σ := ⟨1,0,0, by simp⟩
  let cy : RadicalCoordinates F σ := ⟨0,1,0, by simp⟩
  have hx := conjugate_column_zero F σ hσ g (radicalElement F σ hσ cx) hg
    (radicalElement_mem_upper F σ hσ cx)
  have hy := conjugate_column_zero F σ hσ g (radicalElement F σ hσ cy) hg
    (radicalElement_mem_upper F σ hσ cy)
  have h10 : g.val.val 1 0 = 0 := by
    simpa [radicalElement, radicalMatrix, cy, Matrix.mul_apply, Fin.sum_univ_succ]
      using hy 0
  have h20 : g.val.val 2 0 = 0 := by
    simpa [radicalElement, radicalMatrix, cx, Matrix.mul_apply, Fin.sum_univ_succ]
      using hx 0
  have h30 : g.val.val 3 0 = 0 := by
    simpa [radicalElement, radicalMatrix, cx, Matrix.mul_apply, Fin.sum_univ_succ]
      using hx 1
  have h31 : g.val.val 3 1 = 0 := by
    simpa [radicalElement, radicalMatrix, cx, Matrix.mul_apply, Fin.sum_univ_succ]
      using conjugate_column_one F σ hσ g (radicalElement F σ hσ cx) hg
        (radicalElement_mem_upper F σ hσ cx) h10
  let t := (leviSL F σ hσ (SpecialLinearGroup.transvection
    (by decide : (0 : Fin 2) ≠ 1) (1 : FixedField F σ))).val
  have ht : t ∈ U := by
    apply (mem_upper F σ hσ t).mpr
    refine ⟨(leviSL F σ hσ _).property, ?_⟩
    apply (mem_localUpper F σ hσ _).mp
    change middleSL F σ hσ _ ∈ SpecialLinearGroup.upperUnipotent (FixedField F σ)
    rw [middleSL_leviSL]
    exact (SpecialLinearGroup.mem_upperUnipotent _ _).mpr ⟨1,rfl⟩
  have h21 : g.val.val 2 1 = 0 := by
    simpa [t, leviSL, levi, leviMatrix, middleEquivSL_symm_val,
      SpecialLinearGroup.transvection_coe, Matrix.mul_apply, Fin.sum_univ_succ]
      using conjugate_column_one F σ hσ g t hg ht h10
  exact ⟨(mem_pointParabolicSU F _ g).mpr ⟨h10,h20,h30⟩,
    (mem_planeParabolicSU F _ g).mpr ⟨h20,h30,h21,h31⟩⟩

/-- The full flag stabilizer, including its odd diagonal part, normalizes U. -/
theorem normalizer_upper : Subgroup.normalizer (U : Set _) = B :=
  le_antisymm (normalizer_upper_le_borel F σ hσ) (borel_le_normalizer_upper F σ hσ)

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourSylow
