module
public import Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourCartan

/-!
# Split-torus fixed flags in Hermitian four-space

The fixed-field diagonal subgroup has eigenvalues a, b, b⁻¹, a⁻¹.
At the plane endpoint its fixed lines are the two coordinate lines. At
the point endpoint the perpendicular quotient has two distinct eigenvalues,
so its fixed flags are again the two marked reflection cosets. In
characteristic two this needs only |F^σ| > 2 and includes fixed field four.
The two explicit reflections normalize this same torus.

These calculations supply the native two-neighbor input for the Cartan
apartment route in Aschbacher–Smith F.4.10,16–17, printed pp.279,282–283
of `refs/quasithin.pdf`. They do not classify full-extension automorphisms.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups Subgroup
namespace Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourFixed
open UnitaryFourFlag UnitaryFourGeneration UnitaryFourSylow
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
variable (σ : F ≃+* F) (hσ : Function.Involutive σ)
local notation "J" => form F σ hσ
local notation "K" => FixedField F σ
local notation "B" => borelSU F J

def torus (a b : Kˣ) : B := by
  let d : Fin 4 → F := ![((a : K) : F),((b : K) : F),((b⁻¹ : Kˣ) : K),((a⁻¹ : Kˣ) : K)]
  have ha : ((a : K) : F) ≠ 0 := by exact_mod_cast a.ne_zero
  have hb : ((b : K) : F) ≠ 0 := by exact_mod_cast b.ne_zero
  have hsa : σ ((a : K) : F) = ((a : K) : F) := (a : K).property
  have hsb : σ ((b : K) : F) = ((b : K) : F) := (b : K).property
  have hd : (Matrix.diagonal d).det=1 := by
    simp [Matrix.det_diagonal,d,Fin.prod_univ_succ,ha,hb]
  let g : SU F J :=
    ⟨GeneralLinearGroup.mkOfDetNeZero (Matrix.diagonal d) (by rw [hd]; exact one_ne_zero),
      by
        change (form F σ hσ).conjTranspose (Matrix.diagonal d) * gram F * Matrix.diagonal d = gram F
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [form,gram,HermitianForm.conjTranspose,Matrix.mul_apply,Fin.sum_univ_succ,d,ha,hb,hsa,hsb],
      Units.ext hd⟩
  exact ⟨g,(mem_borel_iff_triangular F σ hσ g).mpr (Matrix.blockTriangular_diagonal d)⟩

omit [CharP F 2] in
theorem torus_val (a b : Kˣ) : (torus F σ hσ a b).val.val.val =
    Matrix.diagonal ![((a : K) : F),((b : K) : F),((b⁻¹ : Kˣ) : K),((a⁻¹ : Kˣ) : K)] := rfl

theorem point_torus (a b : Kˣ) :
    middleSwap F σ hσ * (torus F σ hσ a b).val * middleSwap F σ hσ =
      (torus F σ hσ a b⁻¹).val := by
  apply Subtype.ext
  apply Units.ext
  change middleSwapMatrix F * (torus F σ hσ a b).val.val.val * middleSwapMatrix F = _
  rw [torus_val,torus_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [middleSwapMatrix,Matrix.mul_apply,Matrix.vecMul,Fin.sum_univ_succ]

theorem plane_torus (a b : Kˣ) :
    pairSwap F σ hσ * (torus F σ hσ a b).val * pairSwap F σ hσ =
      (torus F σ hσ b a).val := by
  apply Subtype.ext
  apply Units.ext
  change pairSwapMatrix F * (torus F σ hσ a b).val.val.val * pairSwapMatrix F = _
  rw [torus_val,torus_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pairSwapMatrix,Matrix.mul_apply,Matrix.vecMul,Fin.sum_univ_succ]

private theorem separating_unit (hq : 2 < Nat.card K) :
    ∃ a : Kˣ, ((a : K) : F) ≠ 1 ∧ ((a : K) : F) ≠ ((a⁻¹ : Kˣ) : K) := by
  have hc : 1 < Nat.card Kˣ := by rw [Nat.card_units]; omega
  let : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨a,ha⟩ := exists_ne (1 : Kˣ)
  have ha1 : ((a : K) : F) ≠ 1 := fun h => ha (Units.ext (Subtype.ext h))
  refine ⟨a,ha1,?_⟩
  intro h
  apply ha1
  apply CharTwo.sq_injective
  calc
    ((a : K) : F)^2 = ((a : K) : F)*((a⁻¹ : Kˣ) : K) := by rw [pow_two,h]
    _ = (1 : F)^2 := by simp

omit [Finite F] [CharP F 2] in
private theorem conjugate_equation (g t : SU F J) :
    t.val.val * g.val.val = g.val.val * (g⁻¹*t*g).val.val := by
  have h : t*g=g*(g⁻¹*t*g) := by group
  exact congrArg (fun g : SU F J => g.val.val) h

theorem plane_fixed_coset (hq : 2 < Nat.card K) (g : SU F J)
    (hg : g ∈ planeParabolicSU F J)
    (hfix : ∀ a b : Kˣ, g⁻¹*(torus F σ hσ a b).val*g ∈ B) :
    g ∈ B ∨ pairSwap F σ hσ*g ∈ B := by
  obtain ⟨a,ha,_⟩ := separating_unit F σ hq
  let t := (torus F σ hσ a 1).val
  let z := g⁻¹*t*g
  have hz : z ∈ B := hfix a 1
  obtain ⟨hz10,hz20,hz30⟩ := (mem_pointParabolicSU F J z).mp hz.1
  have hm := conjugate_equation F σ hσ g t
  change t.val.val * g.val.val = g.val.val * z.val.val at hm
  have h0 : ((a : K) : F)*g.val.val 0 0 = g.val.val 0 0*z.val.val 0 0 := by
    have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 0 0) hm
    simpa [t,torus_val,Matrix.mul_apply,Fin.sum_univ_succ,hz10,hz20,hz30] using h
  have h1 : g.val.val 1 0 = g.val.val 1 0*z.val.val 0 0 := by
    have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 1 0) hm
    simpa [t,torus_val,Matrix.mul_apply,Fin.sum_univ_succ,hz10,hz20,hz30] using h
  obtain ⟨hg20,hg30,hg21,hg31⟩ := (mem_planeParabolicSU F J g).mp hg
  by_cases h10 : g.val.val 1 0=0
  · exact Or.inl ⟨(mem_pointParabolicSU F J g).mpr ⟨h10,hg20,hg30⟩,hg⟩
  · have hz1 : z.val.val 0 0=1 := by
      apply mul_left_cancel₀ h10
      simpa using h1.symm
    have h00 : g.val.val 0 0=0 := by
      rw [hz1,mul_one] at h0
      exact (mul_eq_mul_right_iff.mp (h0.trans (one_mul _).symm)).resolve_left ha
    right
    refine ⟨(mem_pointParabolicSU F J _).mpr ?_,
      (planeParabolicSU F J).mul_mem (pairSwap_mem_plane F σ hσ) hg⟩
    change (pairSwapMatrix F * g.val.val) 1 0=0 ∧
      (pairSwapMatrix F * g.val.val) 2 0=0 ∧ (pairSwapMatrix F * g.val.val) 3 0=0
    simp [pairSwapMatrix,Matrix.mul_apply,Fin.sum_univ_succ,h00,hg20,hg30]

omit [CharP F 2] in
private theorem point_last_row (g : SU F J) (hg : g ∈ pointParabolicSU F J) :
    g.val.val 3 1=0 := by
  obtain ⟨h10,h20,h30⟩ := (mem_pointParabolicSU F J g).mp hg
  have h00 : g.val.val 0 0 ≠ 0 := by
    intro h00
    apply GeneralLinearGroup.det_ne_zero g.val
    apply Matrix.det_eq_zero_of_column_eq_zero 0
    intro i
    fin_cases i <;> simp_all
  have hs00 : σ (g.val.val 0 0) ≠ 0 := by simpa using h00
  have hu := g.property.1
  change (form F σ hσ).conjTranspose g.val.val * gram F * g.val.val = gram F at hu
  have h01 := congrArg (fun M : Matrix (Fin 4) (Fin 4) F => M 0 1) hu
  simpa [form,gram,HermitianForm.conjTranspose,Matrix.mul_apply,
    Fin.sum_univ_succ,h10,h20,h30,hs00] using h01

theorem point_fixed_coset (hq : 2 < Nat.card K) (g : SU F J)
    (hg : g ∈ pointParabolicSU F J)
    (hfix : ∀ a b : Kˣ, g⁻¹*(torus F σ hσ a b).val*g ∈ B) :
    g ∈ B ∨ middleSwap F σ hσ*g ∈ B := by
  obtain ⟨a,_,ha⟩ := separating_unit F σ hq
  let t := (torus F σ hσ 1 a).val
  let z := g⁻¹*t*g
  have hz : z ∈ B := hfix 1 a
  obtain ⟨hz20,hz30,hz21,hz31⟩ := (mem_planeParabolicSU F J z).mp hz.2
  obtain ⟨hg10,hg20,hg30⟩ := (mem_pointParabolicSU F J g).mp hg
  have hm := conjugate_equation F σ hσ g t
  change t.val.val * g.val.val = g.val.val * z.val.val at hm
  have h1 : ((a : K) : F)*g.val.val 1 1 = g.val.val 1 1*z.val.val 1 1 := by
    have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 1 1) hm
    simpa [t,torus_val,Matrix.mul_apply,Fin.sum_univ_succ,hz21,hz31,hg10] using h
  have h2 : (((a⁻¹ : Kˣ) : K) : F)*g.val.val 2 1 = g.val.val 2 1*z.val.val 1 1 := by
    have h := congrArg (fun A : Matrix (Fin 4) (Fin 4) F => A 2 1) hm
    simpa [t,torus_val,Matrix.mul_apply,Fin.sum_univ_succ,hz21,hz31,hg20] using h
  have hr := point_last_row F σ hσ g hg
  by_cases h21 : g.val.val 2 1=0
  · exact Or.inl ⟨hg,(mem_planeParabolicSU F J g).mpr ⟨hg20,hg30,h21,hr⟩⟩
  · have hza : z.val.val 1 1=(((a⁻¹ : Kˣ) : K) : F) := by
      apply mul_right_cancel₀ h21
      simpa only [mul_comm _ (g.val.val 2 1)] using h2.symm
    have h11 : g.val.val 1 1=0 := by
      rw [hza,mul_comm (g.val.val 1 1)] at h1
      exact (mul_eq_mul_right_iff.mp h1).resolve_left ha
    right
    refine ⟨(pointParabolicSU F J).mul_mem (middleSwap_mem_point F σ hσ) hg,
      (mem_planeParabolicSU F J _).mpr ?_⟩
    change (middleSwapMatrix F*g.val.val) 2 0=0 ∧ (middleSwapMatrix F*g.val.val) 3 0=0 ∧
      (middleSwapMatrix F*g.val.val) 2 1=0 ∧ (middleSwapMatrix F*g.val.val) 3 1=0
    simp [middleSwapMatrix,Matrix.mul_apply,Fin.sum_univ_succ,hg10,hg30,h11,hr]
end Theory.SpecificGroups.ClassicalUnitary.SmallCompletion.FourFixed
