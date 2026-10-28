module

public import Theory.SpecificGroups.PSU3.UniversalCover.EvenKernelBound.ThreePrimary.LocalStructure
public import Theory.SpecificGroups.SU3.EvenInnerCentralizers.Torus

/-!
# The determinant-one diagonal torus in the actual projective unitary group

Two norm-one coordinates give `diag(a,(a*b)⁻¹,b)`. Projectivization retains
exactly the scalar cubic kernel, rather than embedding the whole torus.
These matrices provide the marked generators for the three-primary local
argument in Aschbacher–Smith I.1.3(2), PDF p.418; GLS III, Theorem 6.1.4.
-/

@[expose] public noncomputable section
open Matrix Subgroup BenderSuzuki.MatrixGroups
namespace BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus

variable {F : Type*} [Field F]
variable (J : HermitianForm 3 F) (hJ : J.form = 1)
variable (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)

/-- The two independent coordinates and their determinant-one middle entry. -/
def entries (a : C × C) : Fin 3 → C := ![a.1, (a.1 * a.2)⁻¹, a.2]

theorem entries_det (a : C × C) :
    (diagonal (fun i => ((entries C a i).val : F))).det = 1 := by
  rw [det_diagonal]
  simp [entries, Fin.prod_univ_succ, mul_comm]

/-- The diagonal matrix, before taking any scalar quotient. -/
def diagonalGL (a : C × C) : GL (Fin 3) F :=
  GeneralLinearGroup.mkOfDetNeZero
    (diagonal (fun i => ((entries C a i).val : F)))
    (by rw [entries_det]; exact one_ne_zero)

@[simp] theorem diagonalGL_val (a : C × C) :
    (diagonalGL C a : Matrix (Fin 3) (Fin 3) F) =
      diagonal (fun i => ((entries C a i).val : F)) := rfl

include hJ hC in
theorem diagonalGL_special (a : C × C) : diagonalGL C a ∈ J.specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · rw [hJ, diagonalGL_val, Matrix.mul_one]
    ext i j
    by_cases h : j = i <;> simp [HermitianForm.conjTranspose, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.one_apply, h, Ne.symm, hC]
  · apply Units.ext
    simpa only [GeneralLinearGroup.val_det_apply, Units.val_one, diagonalGL_val] using
      entries_det C a

/-- The diagonal embedding in the actual special unitary subgroup. -/
def diagonalSpecial : (C × C) →* J.specialSubgroup where
  toFun a := ⟨diagonalGL C a, diagonalGL_special J hJ C hC a⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [entries]
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [entries, mul_assoc, mul_comm, mul_left_comm]

/-- The literal projective image of the two-parameter diagonal embedding. -/
def diagonalProjective : (C × C) →* ProjectiveSpecialUnitaryMatrixGroup J :=
  J.specialToProjective.comp (diagonalSpecial J hJ C hC)

@[simp] theorem diagonalProjective_val (a : C × C) :
    (diagonalProjective J hJ C hC a).val = ProjGenLinGroup.mk (diagonalGL C a) :=
  J.specialToProjective_apply_val _

/-- The torus is the range of the actual projective matrix homomorphism. -/
def torus : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (diagonalProjective J hJ C hC).range

/-- The scalar cubic kernel in dimension three. -/
theorem diagonalProjective_eq_one_iff (a : C × C) :
    diagonalProjective J hJ C hC a = 1 ↔ a.1 = a.2 ∧ a.1 ^ 3 = 1 := by
  constructor
  · intro ha
    have hp : ProjGenLinGroup.mk (diagonalGL C a) = 1 := by
      simpa only [diagonalProjective_val, Subgroup.coe_one] using congrArg Subtype.val ha
    rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
    obtain ⟨u, hu⟩ := hp
    have hd (i : Fin 3) : ((entries C a i).val : F) = (u : F) := by
      have hi := congrArg (fun g : GL (Fin 3) F => g.val i i) hu
      simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar] using hi.symm
    have h0 : a.1.val = u := Units.ext (hd 0)
    have h2 : a.2.val = u := Units.ext (hd 2)
    have h1 : ((a.1 * a.2)⁻¹).val = u := Units.ext (hd 1)
    have ha12 : a.1 = a.2 := Subtype.ext (h0.trans h2.symm)
    refine ⟨ha12, ?_⟩
    have he : (a.1 * a.1)⁻¹ = a.1 := by
      apply Subtype.ext
      simpa only [ha12] using h1.trans h0.symm
    have he' := inv_eq_iff_mul_eq_one.mp he
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using he'
  · rintro ⟨ha12, ha3⟩
    have he : (a.1 * a.2)⁻¹ = a.1 := by
      rw [← ha12]
      apply inv_eq_iff_mul_eq_one.mpr
      simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using ha3
    have hscalar : diagonalGL C a = GeneralLinearGroup.scalar (Fin 3) a.1.val := by
      apply Units.ext
      change diagonal _ = diagonal _
      congr 1
      funext i
      fin_cases i
      · rfl
      · exact congrArg (fun x : C => (x.val : F)) he
      · exact congrArg (fun x : C => (x.val : F)) ha12.symm
    apply Subtype.ext
    rw [diagonalProjective_val, Subgroup.coe_one]
    rw [hscalar]
    simp

/-- The marked coordinate generators. -/
def first (g : C) := diagonalProjective J hJ C hC (g, 1)
def second (g : C) := diagonalProjective J hJ C hC (1, g)

theorem first_commute_second (g : C) :
    Commute (first J hJ C hC g) (second J hJ C hC g) :=
  (Commute.all (g, (1 : C)) (1, g)).map (diagonalProjective J hJ C hC)

/-- Any generator of the cyclic parameter group gives these two generators of T. -/
theorem generate (g : C) (hg : ∀ a : C, ∃ k : ℤ, g ^ k = a) :
    closure ({first J hJ C hC g, second J hJ C hC g} : Set _) =
      torus J hJ C hC := by
  apply le_antisymm
  · apply (closure_le _).mpr
    intro x hx
    rcases hx with rfl | rfl
    · exact ⟨(g, 1), rfl⟩
    · exact ⟨(1, g), rfl⟩
  · rintro x ⟨⟨a, b⟩, rfl⟩
    obtain ⟨k, rfl⟩ := hg a
    obtain ⟨l, rfl⟩ := hg b
    have he : (g ^ k, g ^ l) = (g, (1 : C)) ^ k * (1, g) ^ l := by simp
    rw [he, map_mul, map_zpow, map_zpow]
    exact mul_mem (zpow_mem (subset_closure (by simp [first])) k)
      (zpow_mem (subset_closure (by simp [second])) l)

/-- Exponents of the parameter group descend through the literal map. -/
theorem first_pow (g : C) {m : ℕ} (hg : g ^ m = 1) :
    first J hJ C hC g ^ m = 1 := by
  rw [first, ← map_pow]
  have he : (g, (1 : C)) ^ m = 1 := by ext <;> simp [hg]
  rw [he, map_one]

/-- The existing norm-one subgroup satisfies the required Hermitian equation. -/
theorem normOne_norm (u : EvenInner.normOne J) :
    J.conj (u.val : F) * (u.val : F) = 1 := by
  rw [u.property, inv_mul_cancel₀ (Units.ne_zero u.val)]



/-- Scalar cube roots identify the exact kernel of the two-parameter map. -/
def scalarKernelEquiv :
    (powMonoidHom 3 : C →* C).ker ≃* (diagonalProjective J hJ C hC).ker where
  toFun u := ⟨(u.val, u.val), (diagonalProjective_eq_one_iff J hJ C hC _).mpr
    ⟨rfl, u.property⟩⟩
  invFun a := ⟨a.val.1, ((diagonalProjective_eq_one_iff J hJ C hC _).mp a.property).2⟩
  left_inv u := rfl
  right_inv a := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact ((diagonalProjective_eq_one_iff J hJ C hC _).mp a.property).1
  map_mul' u v := rfl

/-- The kernel has the cubic torsion order, including all higher three-valuations. -/
theorem diagonalProjective_ker_card [Finite F] :
    Nat.card (diagonalProjective J hJ C hC).ker = Nat.gcd (Nat.card C) 3 := by
  rw [← Nat.card_congr (scalarKernelEquiv J hJ C hC).toEquiv,
    IsCyclic.card_powMonoidHom_ker]

/-- The full diagonal torus has its quotient order; it is not replaced by cubic torsion. -/
theorem torus_card [Finite F] :
    Nat.card (torus J hJ C hC) = Nat.card C ^ 2 / Nat.gcd (Nat.card C) 3 := by
  have he := (diagonalProjective J hJ C hC).ker.card_mul_index
  rw [diagonalProjective_ker_card, index_ker, Nat.card_prod] at he
  exact Nat.eq_div_of_mul_eq_left
    (Nat.gcd_pos_of_pos_right (Nat.card C) (by decide : 0 < 3)).ne'
    (by simpa only [torus, pow_two, mul_comm] using he)

/-- The norm-one diagonal torus in an identity Gram model. -/
def normOneTorus := torus J hJ (EvenInner.normOne J) (normOne_norm J)

/-- The norm-one torus has its full quotient order over the quadratic field. -/
theorem normOneTorus_card [Finite F] {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q) :
    Nat.card (normOneTorus J hJ) = (q + 1) ^ 2 / Nat.gcd (q + 1) 3 := by
  rw [normOneTorus, torus_card, EvenInner.normOne_card J hcard hconj]

end BenderSuzuki.MatrixGroups.HermitianForm.UniversalCover.EvenKernelBound.ThreePrimary.MatrixTorus
