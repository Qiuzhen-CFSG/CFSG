module

public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Torus
public import Mathlib.GroupTheory.PGroup

/-!
# The full diagonal torus of SU₃ and its projective image

For the antidiagonal Hermitian form, the diagonal matrices are parametrized
by all of `Eˣ`. This gives the special torus a genuine multiplicative
equivalence with `Eˣ`. The projective kernel is the intersection of the
norm-one subgroup with the cube roots of unity, giving the actual quotient
equivalence and order `(q² - 1) / gcd(q + 1, 3)`.

The root ranges and their joins with these full tori are exposed for Borel
alignment. They are not identified with Sylow normalizers by definition.

Source: Huppert II.10.12; Aschbacher–Smith, proof of 13.8.20, printed p.954.
The norm-one kernel computation reuses `EvenInnerCentralizers.Torus`.
-/

@[expose] public section

open Matrix BenderSuzuki.External Subgroup
namespace BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
variable {E : Type*} [Field E] (J : HermitianForm 3 E)
variable (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

def specialTorus : Subgroup J.specialSubgroup := (hermitianTorusSU J hJ).range

def projectiveTorus : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (hermitianTorusPSU J hJ).range

def specialRoot : Subgroup J.specialSubgroup := (hermitianUnipotentSU J hJ).range

def projectiveRoot : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (hermitianUnipotentPSU J hJ).range

def specialBorel : Subgroup J.specialSubgroup := specialRoot J hJ ⊔ specialTorus J hJ

def projectiveBorel : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  projectiveRoot J hJ ⊔ projectiveTorus J hJ

theorem special_injective : Function.Injective (hermitianTorusSU J hJ) := by
  intro k l h
  apply Units.ext
  exact congrArg (fun x : J.specialSubgroup => x.val.val 2 2) h

noncomputable def specialEquiv : Eˣ ≃* specialTorus J hJ :=
  MonoidHom.ofInjective (special_injective J hJ)

theorem special_card [Finite E] : Nat.card (specialTorus J hJ) = Nat.card E - 1 := by
  rw [← Nat.card_congr (specialEquiv J hJ).toEquiv, Nat.card_units]

theorem projective_eq_one_iff (k : Eˣ) :
    hermitianTorusPSU J hJ k = 1 ↔ k ∈ EvenInner.normOne J ∧ k ^ 3 = 1 := by
  constructor
  · intro he
    have hpgl : ProjGenLinGroup.mk (hermitianTorusGL J k) = 1 :=
      congrArg Subtype.val he
    have hc : hermitianTorusGL J k ∈ center (GL (Fin 3) E) := by
      rw [← ProjGenLinGroup.ker_mk, MonoidHom.mem_ker]
      exact hpgl
    obtain ⟨c, hc⟩ := GeneralLinearGroup.mem_center_iff_val_mem_range_scalar.mp hc
    have h00 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 0 0) hc
    have h22 := congrArg (fun M : Matrix (Fin 3) (Fin 3) E => M 2 2) hc
    simp [hermitianTorusMatrix, Matrix.scalar_apply] at h00 h22
    have hk : k ∈ EvenInner.normOne J := by
      change J.conj (k : E) = (k : E)⁻¹
      simpa only [inv_inv] using congrArg (fun x : E => x⁻¹) (h00.symm.trans h22)
    refine ⟨hk, ?_⟩
    have hcube := (EvenInner.normOneMap_eq_one_iff J hJ ⟨k, hk⟩).mp he
    exact congrArg Subtype.val hcube
  · rintro ⟨hk, hcube⟩
    exact (EvenInner.normOneMap_eq_one_iff J hJ ⟨k, hk⟩).mpr (Subtype.ext hcube)

theorem projective_ker : (hermitianTorusPSU J hJ).ker =
    EvenInner.normOne J ⊓ rootsOfUnity 3 E := by
  ext k
  exact (projective_eq_one_iff J hJ k).trans (by simp only [mem_inf, mem_rootsOfUnity])

theorem projective_ker_isThreeGroup : IsPGroup 3 (hermitianTorusPSU J hJ).ker := by
  intro k
  refine ⟨1, ?_⟩
  apply Subtype.ext
  exact (projective_eq_one_iff J hJ k.val).mp k.property |>.2

def kernelEquiv : (hermitianTorusPSU J hJ).ker ≃* (EvenInner.normOneMap J hJ).ker where
  toFun k := ⟨⟨k.val, ((projective_eq_one_iff J hJ k.val).mp k.property).1⟩, k.property⟩
  invFun k := ⟨k.val.val, k.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem projective_ker_card [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2) (hconj : ∀ x : E, J.conj x = x ^ q) :
    Nat.card (hermitianTorusPSU J hJ).ker = Nat.gcd (q + 1) 3 := by
  rw [Nat.card_congr (kernelEquiv J hJ).toEquiv]
  exact EvenInner.normOneMap_ker_card J hcard hconj hJ

noncomputable def projectiveEquiv :
    Eˣ ⧸ (EvenInner.normOne J ⊓ rootsOfUnity 3 E) ≃* projectiveTorus J hJ :=
  (QuotientGroup.quotientMulEquivOfEq (projective_ker J hJ).symm).trans
    (QuotientGroup.quotientKerEquivRange (hermitianTorusPSU J hJ))

theorem projective_card [Finite E] {q : ℕ}
    (hcard : Nat.card E = q ^ 2) (hconj : ∀ x : E, J.conj x = x ^ q) :
    Nat.card (projectiveTorus J hJ) = (q ^ 2 - 1) / Nat.gcd (q + 1) 3 := by
  have h := (hermitianTorusPSU J hJ).ker.card_mul_index
  rw [index_ker, projective_ker_card J hJ hcard hconj, Nat.card_units, hcard] at h
  exact Nat.eq_div_of_mul_eq_left
    (Nat.ne_of_gt (Nat.gcd_pos_of_pos_right (q + 1) (by decide : 0 < 3)))
    (by simpa only [projectiveTorus, mul_comm] using h)

end BenderSuzuki.MatrixGroups.HermitianForm.BorelTorus
