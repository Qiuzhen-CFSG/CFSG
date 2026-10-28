module

public import Theory.SpecificGroups.PSL2.OuterSolvable.Actions
public import Theory.SpecificGroups.SL2.UpperUnipotent
import Mathlib.Tactic.FinCases

/-!
# Projective root groups for odd PSL₂ automorphisms

The upper transvections inject into the actual center quotient of SL₂. Together
with the Weyl element they determine every homomorphism out of PSL₂. Their image
is a Sylow subgroup in the defining characteristic, so Sylow conjugacy normalizes
an arbitrary automorphism to preserve this root group.

The matrix convention for the Weyl element is `!![0,-1;1,0]`. Quotient equality
is equality up to sign, in every characteristic. The diagonal and field action
formulas refer to the actual actions constructed in `OuterSolvable.Actions`.
These lemmas support the A₁ instance of GLS3, Theorem 2.5.12 and §2.7
(`refs/KGroup/GLS3/chapter2.tex`, lines 854 and 1109–1115).

The generator and Sylow arguments adapt the corresponding SL₂ arguments in
`BenderSuzuki/.../Linear/SemilinearCoverage/RootParameters.lean` and
`Normalization.lean`, working directly in the quotient in place of using the
characteristic-two SL₂–PSL₂ equivalence. No automorphism lift is assumed.
-/

open Matrix
namespace Theory.PSL2.OuterSolvable.OddCoverage
variable {K : Type*} [Field K]

public abbrev slUpper (t : K) : SpecialLinearGroup (Fin 2) K :=
  SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one t

@[expose] public def slWeyl (K : Type*) [Field K] : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, -1; 1, 0], by simp [det_fin_two]⟩

@[expose] public def slTorus (r : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(r : K), 0; 0, (↑r⁻¹ : K)], by simp [det_fin_two]⟩

public theorem slUpper_val (t : K) : (slUpper t).val = !![1, t; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [slUpper, SpecialLinearGroup.transvection_coe]

public theorem center_eq_one_or_neg_one (A : SpecialLinearGroup (Fin 2) K)
    (hA : A ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K)) : A = 1 ∨ A = -1 := by
  obtain ⟨r, hr, hrA⟩ := SpecialLinearGroup.mem_center_iff.mp hA
  simp only [Fintype.card_fin] at hr
  rcases sq_eq_one_iff.mp hr with rfl | rfl
  · left
    apply Subtype.ext
    simpa using hrA.symm
  · right
    apply Subtype.ext
    simpa [← Matrix.diagonal_neg] using hrA.symm

public theorem quotientMap_eq_iff (A B : SpecialLinearGroup (Fin 2) K) :
    quotientMap K A = quotientMap K B ↔ A = B ∨ A = -B := by
  constructor
  · intro h
    have hc : A⁻¹ * B ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) :=
      QuotientGroup.eq.mp h
    rcases center_eq_one_or_neg_one _ hc with h | h
    · exact Or.inl (inv_mul_eq_one.mp h)
    · right
      have he := inv_mul_eq_iff_eq_mul.mp h
      simpa using congrArg Neg.neg he.symm
  · rintro (rfl | rfl)
    · rfl
    · apply QuotientGroup.eq.mpr
      apply SpecialLinearGroup.mem_center_iff.mpr
      refine ⟨-1, by simp, ?_⟩
      simp [← Matrix.diagonal_neg]

@[expose] public def upper (t : K) : Group K := quotientMap K (slUpper t)
@[expose] public def weyl (K : Type*) [Field K] : Group K := quotientMap K (slWeyl K)
@[expose] public def torus (r : Kˣ) : Group K := quotientMap K (slTorus r)
@[expose] public def rootGroup (K : Type*) [Field K] : Subgroup (Group K) :=
  (SpecialLinearGroup.upperUnipotent K).map (quotientMap K)

public theorem mem_rootGroup (x : Group K) : x ∈ rootGroup K ↔ ∃ t : K, upper t = x := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨t, rfl⟩ := (SpecialLinearGroup.mem_upperUnipotent K A).mp hA
    exact ⟨t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨slUpper t, (SpecialLinearGroup.mem_upperUnipotent K _).mpr ⟨t, rfl⟩, rfl⟩

public theorem upper_injective : Function.Injective (upper (K := K)) := by
  intro s t h
  have hc : (slUpper s)⁻¹ * slUpper t ∈
      Subgroup.center (SpecialLinearGroup (Fin 2) K) := QuotientGroup.eq.mp h
  rw [SpecialLinearGroup.transvection_inv, ← SpecialLinearGroup.transvection_add] at hc
  have he := (SpecialLinearGroup.transvection_mem_center_iff zero_ne_one _).mp hc
  exact neg_add_eq_zero.mp he

public theorem upper_add (s t : K) : upper (s + t) = upper s * upper t := by
  simp only [upper, slUpper, SpecialLinearGroup.transvection_add, map_mul]

@[simp] public theorem upper_zero : upper (0 : K) = 1 := by
  simp [upper, slUpper]

public theorem hom_ext_root_weyl {G : Type*} [_root_.Group G] (a b : Group K →* G)
    (hU : ∀ t : K, a (upper t) = b (upper t)) (hw : a (weyl K) = b (weyl K)) : a = b := by
  apply MonoidHom.ext
  intro x
  obtain ⟨A, rfl⟩ := quotientMap_surjective K x
  apply Matrix.SL2.transvection_induction (fun A => a (quotientMap K A) = b (quotientMap K A))
  · intro i j hij t
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact hU t
    · have he : SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero t =
          slWeyl K * slUpper (-t) * (slWeyl K)⁻¹ := by
        apply Subtype.ext
        change (SpecialLinearGroup.transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero t).val =
          (slWeyl K).val * (slUpper (-t)).val * Matrix.adjugate (slWeyl K).val
        rw [slUpper_val]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [SpecialLinearGroup.transvection_coe, slWeyl,
            Matrix.mul_apply, Fin.sum_univ_two, Matrix.adjugate_fin_two]
      rw [he]
      simp only [map_mul, map_inv]
      change a (weyl K) * a (upper (-t)) * (a (weyl K))⁻¹ =
        b (weyl K) * b (upper (-t)) * (b (weyl K))⁻¹
      rw [hw, hU]
    · exact (hij rfl).elim
  · intro x y hx hy
    simp only [map_mul, hx, hy]


public theorem projectiveFieldAut_upper (σ : K ≃+* K) (t : K) :
    projectiveFieldAutHom σ (upper t) = upper (σ t) := by
  rw [upper, projectiveFieldAutHom_apply_quotientMap]
  apply congrArg (quotientMap K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2FieldAut, slUpper, SpecialLinearGroup.transvection_coe]

public theorem projectiveFieldAut_weyl (σ : K ≃+* K) :
    projectiveFieldAutHom σ (weyl K) = weyl K := by
  rw [weyl, projectiveFieldAutHom_apply_quotientMap]
  apply congrArg (quotientMap K)
  ext i j
  change σ ((slWeyl K).val i j) = (slWeyl K).val i j
  fin_cases i <;> fin_cases j <;> simp [slWeyl]

public theorem diagonalAut_upper (u : Kˣ) (t : K) :
    diagonalAutHom u (upper t) = upper ((u : K) * t) := by
  rw [upper, diagonalAutHom_apply_quotientMap]
  apply congrArg (quotientMap K)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slDiagonal, slUpper, SpecialLinearGroup.transvection_coe]

public theorem exists_root_normalization [Finite K]
    (a : MulAut (Group K)) :
    ∃ (g : Group K) (b : MulAut (Group K)),
      a = MulAut.conj g * b ∧ (rootGroup K).map b.toMonoidHom = rootGroup K := by
  let p := ringChar K
  have : Fact p.Prime := ⟨CharP.prime_ringChar K⟩
  let P : Sylow p (Group K) :=
    (SpecialLinearGroup.upperUnipotentSylow K p).mapSurjective (quotientMap_surjective K)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Group K) (a • P) P
  have he := congrArg (fun Q : Sylow p (Group K) => (Q : Subgroup (Group K))) hg
  have hm : (rootGroup K).map (MulAut.conj g * a).toMonoidHom = rootGroup K := by
    change ((rootGroup K).map a.toMonoidHom).map
      (MulAut.conj g).toMonoidHom = rootGroup K at he
    rw [Subgroup.map_map] at he
    exact he
  refine ⟨g⁻¹, MulAut.conj g * a, ?_, hm⟩
  rw [map_inv, inv_mul_cancel_left]

end Theory.PSL2.OuterSolvable.OddCoverage
