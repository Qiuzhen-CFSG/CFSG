module
public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFiveSource.ShortCentralizer

/-!
# Squares detect the two central plane types

A central plane parameter is a square in the entire radical exactly when
its Hermitian determinant is zero. Over the finite field of characteristic
two, the singular block factors as a column times its conjugate transpose;
surjectivity of the radical vector coordinate then constructs an actual
square root. Consequently radical automorphisms preserve nonsingularity.

The full-extension short-centralizer companion uses this intrinsic test to
handle its middle automorphisms. Source: the unitary involution types in
Aschbacher–Smith F.4.27, F.4.29 and F.4.42, printed pp.288–289,295.
-/

@[expose] public noncomputable section
open BenderSuzuki.MatrixGroups Matrix Subgroup
namespace Theory.SpecificGroups.UnitaryFive.PlaneCore.Parameters
variable {F : Type*} [Field F] [CharP F 2] [Finite F] (J : HermitianForm 5 F)

private theorem hermitian_factor (z : Matrix (Fin 2) (Fin 2) F)
    (hz : ∀ i j, J.conj (z j i) = z i j) (hd : z.det = 0) :
    ∃ x : Fin 2 → F, ∀ i j, z i j = x i * J.conj (x j) := by
  have hs : Function.Surjective (fun t : F => t ^ 2) :=
    Finite.surjective_of_injective (fun a b h => CharTwo.sq_injective h)
  have hfix (a t : F) (ha : J.conj a = a) (ht : t ^ 2 = a) : J.conj t = t := by
    apply CharTwo.sq_injective
    change (J.conj t)^2 = t^2
    rw [←map_pow,ht,ha]
  have hdet : z 0 0 * z 1 1 = z 0 1 * z 1 0 := by
    simpa only [Matrix.det_fin_two,sub_eq_zero] using hd
  by_cases ha : z 0 0 = 0
  · have hz0 : z 0 1 = 0 := by
      have hh : z 0 1 * J.conj (z 0 1) = 0 := by rw [hz 1 0,←hdet,ha,zero_mul]
      exact (mul_eq_zero.mp hh).elim id (fun h => J.conj.injective (by simpa using h))
    obtain ⟨t,ht⟩ := hs (z 1 1)
    change t^2 = z 1 1 at ht
    refine ⟨![0,t],?_⟩
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using ha
    · simpa using hz0
    · change z 1 0 = t * J.conj 0
      rw [map_zero,mul_zero,←hz 1 0,hz0,map_zero]
    · change z 1 1 = t * J.conj t
      rw [hfix _ _ (hz 1 1) ht,←pow_two,ht]
  · obtain ⟨t,ht⟩ := hs (z 0 0)
    change t^2 = z 0 0 at ht
    have ht0 : t ≠ 0 := by intro he; rw [he,zero_pow (by decide)] at ht; exact ha ht.symm
    have htfix := hfix _ _ (hz 0 0) ht
    refine ⟨![t,z 1 0 / t],?_⟩
    intro i j
    fin_cases i <;> fin_cases j
    · change z 0 0 = t * J.conj t
      rw [htfix,←pow_two,ht]
    · change z 0 1 = t * J.conj (z 1 0 / t)
      rw [map_div₀,hz 0 1,htfix,mul_div_cancel₀ _ ht0]
    · change z 1 0 = (z 1 0 / t) * J.conj t
      rw [htfix,div_mul_cancel₀ _ ht0]
    · change z 1 1 = (z 1 0 / t) * J.conj (z 1 0 / t)
      rw [map_div₀,hz 0 1,htfix,div_mul_div_comm]
      apply (eq_div_iff (mul_ne_zero ht0 ht0)).mpr
      calc
        z 1 1 * (t*t) = z 0 0 * z 1 1 := by rw [←pow_two,ht,mul_comm]
        _ = z 0 1 * z 1 0 := hdet
        _ = z 1 0 * z 0 1 := mul_comm _ _

/-- A central plane parameter is a square in the entire plane radical exactly
when its Hermitian determinant vanishes. -/
theorem square_root_iff_det_zero (c : F) (hc : c + J.conj c = 1)
    (v : Parameters J) (hv : v.x = 0) :
    (∃ w : Parameters J, w ^ 2 = v) ↔ v.z.det = 0 := by
  constructor
  · rintro ⟨w,rfl⟩
    simp only [pow_two,Matrix.det_fin_two,mul_z,CharTwo.add_self_eq_zero,zero_add]
    ring
  · intro hd
    have hz (i j : Fin 2) : J.conj (v.z j i) = v.z i j := by
      have hh := v.relation i j
      rw [hv,Pi.zero_apply,zero_mul] at hh
      exact CharTwo.add_eq_zero.mp hh |>.symm
    obtain ⟨x,hx⟩ := hermitian_factor J v.z hz hd
    obtain ⟨w,hw⟩ := vectorHom_surjective J c hc (Multiplicative.ofAdd x)
    have hw' : w.x = x := congrArg Multiplicative.toAdd hw
    refine ⟨w,Parameters.ext ?_ ?_⟩
    · ext i
      simp [pow_two,hv,CharTwo.add_self_eq_zero]
    · ext i j
      simp only [pow_two,mul_z,CharTwo.add_self_eq_zero,zero_add,hw']
      exact (hx i j).symm

end Theory.SpecificGroups.UnitaryFive.PlaneCore.Parameters
