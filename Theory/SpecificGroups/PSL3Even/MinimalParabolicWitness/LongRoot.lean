module

public import Theory.SpecificGroups.PSL3.LinearThreeSylow.Order
public import Theory.SpecificGroups.SL2.TwoConjugateWitness.Transport

/-!
# The highest-root SL₂ in PSL₃

The determinant-one block on coordinates zero and two, fixing coordinate one,
embeds SL₂ faithfully in PSL₃. Its upper root is exactly the central root of
UT₃, and its intersections with UT₃ and the standard Borel are the original
SL₂ Sylow subgroup and Borel. These literal markings transport the checked
two-conjugate witness into PSL₃.

Source: Aschbacher--Smith, E.2.7, printed p.219.
-/

@[expose] public section
open scoped MatrixGroups
open Matrix Subgroup Matrix.PSL3 Matrix.PSL3.LinearThree
open Matrix.PSL3Even.UnipotentGeometry
namespace Matrix.PSL3Even.MinimalParabolicWitness
variable (F : Type*) [Field F]

def longRootMatrix (g : SL(2,F)) : Matrix (Fin 3) (Fin 3) F :=
  !![g.val 0 0,0,g.val 0 1; 0,1,0; g.val 1 0,0,g.val 1 1]

theorem longRootMatrix_det (g : SL(2,F)) : (longRootMatrix F g).det = 1 := by
  have h : g.val 0 0 * g.val 1 1 - g.val 0 1 * g.val 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using g.property
  simpa [longRootMatrix, Matrix.det_fin_three] using h

def longRootSL : SL(2,F) →* SL(3,F) where
  toFun g := ⟨longRootMatrix F g,longRootMatrix_det F g⟩
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [longRootMatrix]
  map_mul' g h := by
    apply Subtype.ext
    change longRootMatrix F (g * h) = longRootMatrix F g * longRootMatrix F h
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [longRootMatrix, SpecialLinearGroup.coe_mul, Matrix.mul_apply,
        Fin.sum_univ_three, Fin.sum_univ_two]

def longRoot : SL(2,F) →* PSL(3,F) := (projection F).comp (longRootSL F)

theorem longRootSL_injective : Function.Injective (longRootSL F) := by
  intro g h he
  apply Subtype.ext
  ext i j
  have hh := congrArg (fun x : SL(3,F) => x.val) he
  fin_cases i <;> fin_cases j
  · exact congrArg (fun m => m 0 0) hh
  · exact congrArg (fun m => m 0 2) hh
  · exact congrArg (fun m => m 2 0) hh
  · exact congrArg (fun m => m 2 2) hh

theorem longRoot_injective : Function.Injective (longRoot F) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply le_bot_iff.mp
  intro x hx
  have hc : longRootSL F x ∈ center SL(3,F) := (QuotientGroup.eq_one_iff _).mp hx
  obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  have hr1 : r = 1 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 1 1) hr
  apply longRootSL_injective F
  rw [map_one]
  apply Subtype.ext
  simpa [hr1] using hr.symm

theorem longRoot_upper (t : F) :
    longRoot F (SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t) =
      projective F ⟨0,0,t⟩ := by
  change projection F _ = projection F _
  congr 1
  apply Subtype.ext
  change longRootMatrix F _ = matrix F ⟨0,0,t⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longRootMatrix,SpecialLinearGroup.transvection_coe,matrix]

theorem longRoot_map_upper :
    (SpecialLinearGroup.upperUnipotent F).map (longRoot F) = projectiveCenter F := by
  ext x
  constructor
  · rintro ⟨g,hg,rfl⟩
    obtain ⟨t,rfl⟩ := (SpecialLinearGroup.mem_upperUnipotent F g).mp hg
    rw [longRoot_upper]
    exact (mem_projectiveCenter F _).mpr ⟨t,rfl⟩
  · intro hx
    obtain ⟨t,rfl⟩ := (mem_projectiveCenter F x).mp hx
    exact ⟨_,(SpecialLinearGroup.mem_upperUnipotent F _).mpr ⟨t,rfl⟩,longRoot_upper F t⟩

theorem longRoot_comap_borel [Finite F] :
    (borel F).comap (longRoot F) = SpecialLinearGroup.rankOneBorel F := by
  ext g
  change longRootSL F g ∈ (borel F).comap (projection F) ↔ _
  rw [borel_comap, mem_borelSL_iff, SpecialLinearGroup.mem_rankOneBorel_iff]
  change (longRootMatrix F g 1 0 = 0 ∧ longRootMatrix F g 2 0 = 0 ∧
    longRootMatrix F g 2 1 = 0) ↔ g.val 1 0 = 0
  simp [longRootMatrix]

private theorem scalar_of_projection_eq (x y : SL(3,F))
    (h : projection F x = projection F y) : ∃ r : F, x.val = r • y.val := by
  have hc := (projection F).eq_iff.mp h
  rw [projection_ker] at hc
  obtain ⟨r,_,hr⟩ := SpecialLinearGroup.mem_center_iff.mp hc
  refine ⟨r, ?_⟩
  calc
    x.val = (y * (y⁻¹ * x)).val := by simp only [mul_inv_cancel_left]
    _ = y.val * Matrix.scalar (Fin 3) r := by rw [SpecialLinearGroup.coe_mul, ← hr]
    _ = r • y.val := by
      ext i j
      simp [Matrix.scalar, Matrix.mul_diagonal, mul_comm]

theorem longRoot_comap_unipotent :
    (unipotent F).comap (longRoot F) = SpecialLinearGroup.upperUnipotent F := by
  ext g
  constructor
  · intro hg
    have hh : longRoot F g ∈ (projective F).range := by
      rw [projective_range]; exact hg
    obtain ⟨u,hu⟩ := hh
    obtain ⟨r,hr⟩ := scalar_of_projection_eq F (longRootSL F g) (specialLinear F u) hu.symm
    have h11 := congrArg (fun m : Matrix (Fin 3) (Fin 3) F => m 1 1) hr
    have hr1 : r = 1 := by
      change (1 : F) = r * 1 at h11
      simpa only [mul_one] using h11.symm
    rw [hr1,one_smul] at hr
    have h00 : g.val 0 0 = 1 := congrArg (fun m => m 0 0) hr
    have h10 : g.val 1 0 = 0 := congrArg (fun m => m 2 0) hr
    have h11 : g.val 1 1 = 1 := congrArg (fun m => m 2 2) hr
    apply (SpecialLinearGroup.mem_upperUnipotent F g).mpr
    refine ⟨g.val 0 1, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.transvection_coe,h00,h10,h11]
  · intro hg
    have hz := mem_map_of_mem (longRoot F) hg
    rw [longRoot_map_upper] at hz
    rw [← projective_range]
    exact (Z F).map_le_range (projective F) hz

/-- Actual two-conjugate witness in the long-root block, preserving the supplied V. -/
theorem exists_longRoot_witness [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (V : Subgroup PSL(3,F))
    (hV : V ≤ projectiveCenter F) (hc : 4 ≤ Nat.card V) :
    Nonempty (SpecialLinearGroup.TwoConjugateWitness.Witness
      (unipotent F) (borel F) V n) := by
  let W := V.comap (longRoot F)
  have hVr : V ≤ (longRoot F).range := by
    rw [← longRoot_map_upper] at hV
    exact hV.trans (map_le_range _ _)
  have hWV : W.map (longRoot F) = V := map_comap_eq_self hVr
  have hWU : W ≤ SpecialLinearGroup.upperUnipotent F := by
    rw [← longRoot_map_upper] at hV
    have hh := comap_mono (f := longRoot F) hV
    rwa [comap_map_eq_self_of_injective (longRoot_injective F)] at hh
  have hWc : 4 ≤ Nat.card W := by
    rw [← Subgroup.card_map_of_injective (f := longRoot F) (K := W) (longRoot_injective F),hWV]
    exact hc
  obtain ⟨w⟩ := SpecialLinearGroup.TwoConjugateWitness.exists_upper hF W hWU hWc
  have wm := w.map (longRoot F) (longRoot_injective F) (unipotent F) (borel F)
    (longRoot_comap_unipotent F) (longRoot_comap_borel F)
  rw [hWV] at wm
  exact ⟨wm⟩

end Matrix.PSL3Even.MinimalParabolicWitness
