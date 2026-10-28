module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.Block
/-!
# The actual unipotent radical and its scalar twist

The row-unipotent matrices give additive coordinates on the kernel of
P → GL₂(F). This kernel is the image of the existing point-local radical,
and hence is a two-group in characteristic two. Matrix conjugation gives
w ↦ det(B)⁻¹ B⁻ᵀ w. In particular diag(a,a⁻¹,1) acts by diag(a²,a).
No identification of this kernel with the full parabolic two-core is
assumed here; that comparison is a separate structural result.

Source: Aschbacher–Smith, G.2.5(1),(8), printed pp.335–336.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents
open Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]

/-- The row-unipotent radical, with its actual matrix embedding. -/
def radicalHom : Multiplicative (Fin 2 → F) →* pointParabolicSL F where
  toFun w := ⟨⟨!![1,w.toAdd 0,w.toAdd 1;0,1,0;0,0,1], by simp [det_fin_three]⟩,
    (mem_pointParabolicSL_iff F _).mpr ⟨rfl,rfl⟩⟩
  map_one' := by
    apply Subtype.ext; apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' v w := by
    apply Subtype.ext; apply Subtype.ext
    change !![1,(v*w).toAdd 0,(v*w).toAdd 1;0,1,0;0,0,1] =
      !![1,v.toAdd 0,v.toAdd 1;0,1,0;0,0,1] * !![1,w.toAdd 0,w.toAdd 1;0,1,0;0,0,1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, add_comm]

theorem radicalHom_injective : Function.Injective (radicalHom F) := by
  intro v w he
  have h0 := congrArg (fun x : pointParabolicSL F => x.val.val 0 1) he
  have h1 := congrArg (fun x : pointParabolicSL F => x.val.val 0 2) he
  apply Multiplicative.toAdd.injective
  ext i; fin_cases i <;> assumption

@[simp] theorem block_radical (w : Multiplicative (Fin 2 → F)) :
    block F (radicalHom F w) = 1 := by
  apply Units.ext
  ext i j; fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem scalar_radical (w : Multiplicative (Fin 2 → F)) :
    scalar F (radicalHom F w) = 1 := by
  apply Units.ext; rfl

theorem radical_range : (radicalHom F).range = (block F).ker := by
  apply le_antisymm
  · rintro _ ⟨w,rfl⟩; exact block_radical F w
  · intro x hx
    have he : block F x = 1 := hx
    have h00 := congrArg (fun B : GL (Fin 2) F => (B : Matrix (Fin 2) (Fin 2) F) 0 0) he
    have h01 := congrArg (fun B : GL (Fin 2) F => (B : Matrix (Fin 2) (Fin 2) F) 0 1) he
    have h10 := congrArg (fun B : GL (Fin 2) F => (B : Matrix (Fin 2) (Fin 2) F) 1 0) he
    have h11 := congrArg (fun B : GL (Fin 2) F => (B : Matrix (Fin 2) (Fin 2) F) 1 1) he
    change x.val.val 1 1 = 1 at h00
    change x.val.val 1 2 = 0 at h01
    change x.val.val 2 1 = 0 at h10
    change x.val.val 2 2 = 1 at h11
    have hs : x.val.val 0 0 = 1 := by
      have hs := scalar_eq_det_inv F x
      rw [he, map_one, inv_one] at hs
      exact congrArg Units.val hs
    have hz := (mem_pointParabolicSL_iff F x).mp x.property
    refine ⟨Multiplicative.ofAdd ![x.val.val 0 1, x.val.val 0 2], ?_⟩
    apply Subtype.ext; apply Subtype.ext
    change !![1,x.val.val 0 1,x.val.val 0 2;0,1,0;0,0,1] = x.val.val
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hs, hz.1, hz.2, h00, h01, h10, h11]

/-- Additive coordinates on the literal kernel of the GL₂ quotient. -/
noncomputable def radicalEquiv : Multiplicative (Fin 2 → F) ≃* (block F).ker :=
  MulEquiv.ofBijective ((radicalHom F).codRestrict (block F).ker
    (fun w => block_radical F w)) ⟨
    fun _ _ he => radicalHom_injective F (congrArg Subtype.val he), by
      intro x
      have hx : x.val ∈ (radicalHom F).range := (radical_range F).symm ▸ x.property
      obtain ⟨w,hw⟩ := hx
      exact ⟨w,Subtype.ext hw⟩⟩

@[simp] theorem radicalEquiv_apply (w : Multiplicative (Fin 2 → F)) :
    (radicalEquiv F w).val = radicalHom F w := rfl

/-- The full parabolic kernel agrees with the previously constructed point radical. -/
theorem block_kernel_eq_local_radical :
    (block F).ker = (pointRadicalSL F).map (inclusion (pointLocalSL_le F)) := by
  ext x
  constructor
  · intro hx
    rw [← radical_range] at hx
    obtain ⟨w, rfl⟩ := hx
    refine ⟨⟨(radicalHom F w).val, (mem_pointLocalSL_iff F _).mpr ⟨rfl,rfl,rfl⟩⟩, ?_, rfl⟩
    exact (mem_pointRadicalSL_iff F _).mpr ⟨rfl,rfl,rfl,rfl⟩
  · rintro ⟨y,hy,rfl⟩
    have hy := (mem_pointRadicalSL_iff F y).mp hy
    change block F (inclusion (pointLocalSL_le F) y) = 1
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j
    · exact hy.1
    · exact hy.2.1
    · exact hy.2.2.1
    · exact hy.2.2.2


/-- The matrix kernel is a two-group in characteristic two. -/
theorem block_kernel_twoGroup [CharP F 2] : IsPGroup 2 (block F).ker := by
  rw [block_kernel_eq_local_radical, ← pointLocalSL_twoCore_eq]
  exact pCore_isPGroup.map _

/-- Conjugation on the actual radical is the det⁻¹ twist of the dual plane action. -/
theorem radical_conjugation (x : pointParabolicSL F) (w : Fin 2 → F) :
    x * radicalHom F (Multiplicative.ofAdd w) * x⁻¹ =
      radicalHom F (Multiplicative.ofAdd ((scalar F x : F) •
        ((block F x⁻¹ : Matrix (Fin 2) (Fin 2) F).transpose *ᵥ w))) := by
  have hx := (mem_pointParabolicSL_iff F x).mp x.property
  have hxi := (mem_pointParabolicSL_iff F x⁻¹).mp (x⁻¹).property
  have hi : x.val.val * x.val⁻¹.val = 1 := congrArg Subtype.val (mul_inv_cancel x.val)
  have hm : (radicalHom F (Multiplicative.ofAdd w)).val.val =
      1 + !![0,w 0,w 1;0,0,0;0,0,0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [radicalHom]
  apply Subtype.ext; apply Subtype.ext
  change x.val.val * (radicalHom F (Multiplicative.ofAdd w)).val.val * x.val⁻¹.val = _
  rw [hm, mul_add, mul_one, add_mul, hi]
  have hb := block_coe F x⁻¹
  change (block F x⁻¹ : Matrix (Fin 2) (Fin 2) F) =
    !![x.val⁻¹.val 1 1,x.val⁻¹.val 1 2;x.val⁻¹.val 2 1,x.val⁻¹.val 2 2] at hb
  rw [hb]
  change x.val.val.adjugate 1 0 = 0 ∧ x.val.val.adjugate 2 0 = 0 at hxi
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [-SpecialLinearGroup.coe_inv, radicalHom, Matrix.mul_apply, mulVec,
      dotProduct, Fin.sum_univ_three, Fin.sum_univ_two, hx.1, hx.2, hxi.1, hxi.2] <;> ring

/-- The original diagonal scalar acts with weights a² and a on the radical. -/
theorem torus_radical_conjugation (a : Fˣ) (w : Fin 2 → F) :
    pointTorusHom F a * radicalHom F (Multiplicative.ofAdd w) * (pointTorusHom F a)⁻¹ =
      radicalHom F (Multiplicative.ofAdd ![(a : F)^2 * w 0, (a : F) * w 1]) := by
  rw [radical_conjugation, ← map_inv]
  congr 1
  apply Multiplicative.toAdd.injective
  ext i
  fin_cases i <;> simp [pointTorusHom, pointTorus, mulVec, dotProduct, Fin.sum_univ_two, pow_two,
    mul_assoc]

end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents
