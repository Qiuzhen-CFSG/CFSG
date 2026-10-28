module

public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.RootModel
public import Theory.SpecificGroups.PSL3.EvenInnerCentralizers.Decomposition
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Conjugacy of binary involutions in projective `SL₃`

For a finite field of order `2^n`, every nonidentity involution of the genuine
projective special linear group is conjugate to the marked transvection
`1 + E₀₂`.  Sylow conjugacy first places the involution in the concrete
unitriangular Sylow subgroup.  The square criterion there leaves the two root
planes; explicit determinant-one matrices then conjugate each nonidentity
element of either plane to the marked root.  Restricting the same inner
conjugation gives an equivalence of the full centralizers.

This supplies the involution-conjugacy step for the inner case of
Aschbacher--Smith 16.4.8, combined manuscript of 1 March 2004, printed p.1188.
The centralizer itself is computed in
`RootModel` and `Decomposition`.
-/

public section
noncomputable section

open scoped MatrixGroups
open Matrix.PSL3Even.UnipotentGeometry

namespace Matrix.PSL3.EvenInnerCentralizers

variable (F : Type*) [Field F]

private theorem conjugator_first (a c : F) (ha : a ≠ 0) :
    ∃ g : SL(3,F), g * rootSL F = specialLinear F ⟨a,0,c⟩ * g := by
  let g : SL(3,F) := ⟨!![1,0,0; 0,c,a⁻¹; 0,-a,0], by
    simp [Matrix.det_fin_three, ha]⟩
  refine ⟨g, Subtype.ext ?_⟩
  change g.val * matrix F ⟨0,0,1⟩ = matrix F ⟨a,0,c⟩ * g.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g, matrix, Matrix.mul_apply, Fin.sum_univ_three, ha]
  ring

private theorem conjugator_second (b c : F) (hb : b ≠ 0) :
    ∃ g : SL(3,F), g * rootSL F = specialLinear F ⟨0,b,c⟩ * g := by
  let g : SL(3,F) := ⟨!![c,-b⁻¹,0; b,0,0; 0,0,1], by
    simp [Matrix.det_fin_three, hb]⟩
  refine ⟨g, Subtype.ext ?_⟩
  change g.val * matrix F ⟨0,0,1⟩ = matrix F ⟨0,b,c⟩ * g.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g, matrix, Matrix.mul_apply, Fin.sum_univ_three]

private theorem conjugator_central (c : F) (hc : c ≠ 0) :
    ∃ g : SL(3,F), g * rootSL F = specialLinear F ⟨0,0,c⟩ * g := by
  let g : SL(3,F) := ⟨!![c,0,0; 0,c⁻¹,0; 0,0,1], by
    simp [Matrix.det_fin_three, hc]⟩
  refine ⟨g, Subtype.ext ?_⟩
  change g.val * matrix F ⟨0,0,1⟩ = matrix F ⟨0,0,c⟩ * g.val
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g, matrix, Matrix.mul_apply, Fin.sum_univ_three]

/-- Every nonidentity involution in the concrete unitriangular group is
conjugate in `SL₃` to the marked highest-root transvection. -/
theorem specialLinear_isConj_root [CharP F 2] (u : U F)
    (hu : u ≠ 1) (hu2 : u ^ 2 = 1) : IsConj (specialLinear F u) (rootSL F) := by
  have hex : ∃ g : SL(3,F), g * rootSL F = specialLinear F u * g := by
    rcases u with ⟨a,b,c⟩
    rcases (square_eq_one_iff F _).mp hu2 with ha | hb
    · change a = 0 at ha
      subst a
      by_cases hb : b = 0
      · subst b
        have hc : c ≠ 0 := by
          intro hc
          exact hu (U.ext rfl rfl hc)
        exact conjugator_central F c hc
      · exact conjugator_second F b c hb
    · change b = 0 at hb
      subst b
      by_cases ha : a = 0
      · subst a
        have hc : c ≠ 0 := by
          intro hc
          exact hu (U.ext rfl rfl hc)
        exact conjugator_central F c hc
      · exact conjugator_first F a c ha
  obtain ⟨g,hg⟩ := hex
  exact (isConj_iff.mpr ⟨g, mul_inv_eq_iff_eq_mul.mpr hg⟩).symm

/-- Every nonidentity involution in `PSL₃(F)` is conjugate to the marked root.
The field order hypothesis supplies characteristic two and the concrete
unitriangular Sylow subgroup. -/
theorem involution_isConj_root [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (t : PSL(3,F)) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    IsConj t (root F) := by
  let := Fintype.ofFinite F
  have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr (by
    rw [← Nat.card_eq_fintype_card, hF]
    simp [Nat.pow_mod, show n ≠ 0 by omega])
  let : CharP F 2 := ringChar.of_eq hc
  obtain ⟨y, hty⟩ :=
    (LinearThree.unipotentSylow F (by omega) hF).exists_isConj_of_orderOf_eq_prime_pow
      (n := 1) (by simpa only [pow_one] using orderOf_eq_prime ht2 ht)
  have hy : (y : PSL(3,F)) ∈ (projective F).range :=
    (LinearThree.projective_range F).ge y.property
  obtain ⟨u,hu⟩ := hy
  obtain ⟨g,hg⟩ := isConj_iff.mp hty
  have hconj : MulAut.conj g t = projective F u := hg.trans hu.symm
  have hu2 : u ^ 2 = 1 := by
    apply projective_injective F
    rw [map_pow, ← hconj, ← map_pow, ht2, map_one, map_one]
  have hun : u ≠ 1 := by
    intro he
    apply ht
    apply (MulAut.conj g).injective
    rw [hconj, he, map_one, map_one]
  have hroot : IsConj (projective F u) (root F) :=
    (projection F).map_isConj (specialLinear_isConj_root F u hun hu2)
  exact hty.trans (hu ▸ hroot)

/-- A concrete conjugator sending a given involution to the marked root. -/
theorem exists_conjugator_root [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (t : PSL(3,F)) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    ∃ g : PSL(3,F), g * t * g⁻¹ = root F :=
  isConj_iff.mp (involution_isConj_root F hn hF t ht ht2)

private theorem map_centralizer_conjugator (t g : PSL(3,F))
    (hg : g * t * g⁻¹ = root F) :
    (Subgroup.centralizer ({t} : Set PSL(3,F))).map (MulAut.conj g).toMonoidHom =
      centralizer F := by
  let e := MulAut.conj g
  have he : e t = root F := hg
  ext x
  rw [Subgroup.mem_map_equiv]
  change e.symm x ∈ Subgroup.centralizer {t} ↔ x ∈ Subgroup.centralizer {root F}
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  rw [← e.injective.eq_iff, map_mul, map_mul, he, e.apply_symm_apply]

/-- The full centralizer of an arbitrary binary involution, transported by an
actual ambient conjugator, is multiplicatively equivalent to the marked
centralizer. -/
noncomputable def involutionCentralizerEquiv [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (t : PSL(3,F)) (ht : t ≠ 1) (ht2 : t ^ 2 = 1) :
    Subgroup.centralizer ({t} : Set PSL(3,F)) ≃* centralizer F :=
  let h := exists_conjugator_root F hn hF t ht ht2
  ((MulAut.conj h.choose).subgroupMap _).trans
    (MulEquiv.subgroupCongr (map_centralizer_conjugator F t h.choose h.choose_spec))

end Matrix.PSL3.EvenInnerCentralizers
