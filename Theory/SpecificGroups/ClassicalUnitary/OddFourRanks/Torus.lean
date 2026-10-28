module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.Model
public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
public import Theory.GroupTheory.PrimeRankWitness
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Mathlib.Tactic.FinCases

/-!
# Odd torsion in an involution centralizer of PSU₄

For the identity Hermitian form the determinant-one norm-one diagonal torus
centralizes diag(-1,-1,1,1). Its odd prime torsion embeds in the actual image
in PGL: a scalar in the kernel has order dividing both four and that prime.
Orthonormalization transports this construction to the original Hermitian form.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.17,
printed p.39. The full torus is not asserted to survive the scalar quotient.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
open scoped IsMulCommutative
namespace Theory.SpecificGroups.ClassicalUnitary.OddFourRanks
open ProjectiveKernel UnitaryFourThree
variable {F : Type*} [Field F]
variable (J : HermitianForm 4 F) (hJ : J.form = 1)
/-- The actual projective image is finite over a finite coefficient field. -/
instance projectiveFinite [Finite F] : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (GL (Fin 4) F) := Finite.of_injective Units.val Units.val_injective
  exact Finite.of_surjective (project J) (project_surjective J)

variable (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)

/-- The determinant-one diagonal entries, with three independent parameters. -/
def torusEntries (a : Fin 3 → C) : Fin 4 → C :=
  ![a 0, a 1, a 2, (a 0 * a 1 * a 2)⁻¹]

/-- The chosen diagonal entries multiply to one. -/
theorem torusEntries_det (a : Fin 3 → C) :
    (diagonal (fun i => ((torusEntries C a i).val : F))).det = 1 := by
  rw [det_diagonal]
  simp [torusEntries, Fin.prod_univ_succ, ← mul_assoc]

/-- The diagonal matrix as an invertible matrix. -/
noncomputable def torusMatrix (a : Fin 3 → C) : GL (Fin 4) F :=
  GeneralLinearGroup.mkOfDetNeZero
    (diagonal (fun i => ((torusEntries C a i).val : F)))
    (by rw [torusEntries_det]; exact one_ne_zero)

@[simp] theorem torusMatrix_val (a : Fin 3 → C) :
    (torusMatrix C a : Matrix (Fin 4) (Fin 4) F) =
      diagonal (fun i => ((torusEntries C a i).val : F)) := rfl

include hJ hC in
/-- Norm-one entries and determinant one put the matrix in the actual SU group. -/
theorem torusMatrix_special (a : Fin 3 → C) : torusMatrix C a ∈ J.specialSubgroup := by
  rw [HermitianForm.mem_specialSubgroup_iff]
  constructor
  · rw [hJ, torusMatrix_val, Matrix.mul_one]
    ext i j
    by_cases h : j = i <;> simp [HermitianForm.conjTranspose, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.one_apply, h, Ne.symm, hC]
  · apply Units.ext
    simpa only [GeneralLinearGroup.val_det_apply, Units.val_one, torusMatrix_val] using
      torusEntries_det C a

/-- The diagonal homomorphism into the special unitary group. -/
noncomputable def torusSpecial : (Fin 3 → C) →* J.specialSubgroup where
  toFun a := ⟨torusMatrix C a, torusMatrix_special J hJ C hC a⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp only [torusMatrix_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [torusEntries]
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [torusEntries, mul_assoc, mul_comm, mul_left_comm]


/-- Norm-one field units for the original stored involution. -/
def normOne : Subgroup Fˣ where
  carrier := {u | J.conj (u : F) = (u : F)⁻¹}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change J.conj ((a : F) * (b : F)) = ((a : F) * (b : F))⁻¹
    rw [map_mul, ha, hb, mul_inv]
  inv_mem' := by
    intro a ha
    simpa only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] using
      congrArg (fun x : F => x⁻¹) ha

theorem normOne_norm (u : normOne J) : J.conj (u.val : F) * (u.val : F) = 1 := by
  rw [u.property, inv_mul_cancel₀ (Units.ne_zero u.val)]

/-- Minus one is a norm-one unit in every characteristic. -/
def minusOne : normOne J := ⟨-1, by simp [normOne]⟩

/-- The actual projective class of diag(-1,-1,1,1). -/
def involution : ProjectiveSpecialUnitaryMatrixGroup J :=
  project J (torusSpecial J hJ (normOne J) (normOne_norm J) ![minusOne J, minusOne J, 1])

theorem involution_ne_one (ho : (-1 : F) ≠ 1) : involution J hJ ≠ 1 := by
  intro h
  have hp : ProjGenLinGroup.mk (torusMatrix (normOne J) ![minusOne J, minusOne J, 1]) = 1 :=
    congrArg Subtype.val h
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
  obtain ⟨u, hu⟩ := hp
  have h0 := congrArg (fun g : GL (Fin 4) F => g.val 0 0) hu
  have h2 := congrArg (fun g : GL (Fin 4) F => g.val 2 2) hu
  have hu0 : (u : F) = -1 := by simpa [GeneralLinearGroup.coe_scalar,
    Matrix.scalar, torusMatrix_val, torusEntries, minusOne] using h0
  have hu2 : (u : F) = 1 := by simpa [GeneralLinearGroup.coe_scalar,
    Matrix.scalar, torusMatrix_val, torusEntries] using h2
  exact ho (hu0.symm.trans hu2)

theorem involution_sq : involution J hJ ^ 2 = 1 := by
  have hm : minusOne J ^ 2 = 1 := by apply Subtype.ext; simp [minusOne]
  have hs : (![minusOne J, minusOne J, 1] : Fin 3 → normOne J) ^ 2 = 1 := by
    funext i
    fin_cases i <;> simp [hm]
  rw [involution, ← map_pow, ← map_pow, hs, map_one, map_one]

/-- The norm-one diagonal subgroup maps into the literal centralizer. -/
def torusCentralizer : (Fin 3 → C) →*
    Subgroup.centralizer ({involution J hJ} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  ((project J).comp (torusSpecial J hJ C hC)).codRestrict _ fun a => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    change project J (torusSpecial J hJ C hC a) * project J _ =
      project J _ * project J (torusSpecial J hJ C hC a)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Units.ext
    change diagonal _ * diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _

/-- Only fourth torsion can be lost to the scalar kernel. -/
theorem torusCentralizer_injective
    (hfour : ∀ u : C, u ^ 4 = 1 → u = 1) :
    Function.Injective (torusCentralizer J hJ C hC) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hp : ProjGenLinGroup.mk (torusMatrix C a) = 1 :=
    congrArg (fun g => g.val.val) ha
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
  obtain ⟨u, hu⟩ := hp
  have hd (i : Fin 4) : ((torusEntries C a i).val : F) = (u : F) := by
    have hi := congrArg (fun g : GL (Fin 4) F => g.val i i) hu
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar, torusMatrix_val] using hi.symm
  have h0 : (a 0).val = u := Units.ext (hd 0)
  have h1 : (a 1).val = u := Units.ext (hd 1)
  have h2 : (a 2).val = u := Units.ext (hd 2)
  have h3 : ((a 0 * a 1 * a 2)⁻¹).val = u := Units.ext (hd 3)
  have hu4 : u ^ 4 = 1 := by
    simp only [Subgroup.coe_inv, Subgroup.coe_mul, h0, h1, h2] at h3
    have ht := inv_eq_iff_mul_eq_one.mp h3
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using ht
  have ha0 : a 0 = 1 := hfour (a 0) (by
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, h0] using hu4)
  have hu1 : u = 1 := h0.symm.trans (congrArg Subtype.val ha0)
  funext i
  fin_cases i
  · exact ha0
  · exact Subtype.ext (h1.trans hu1)
  · exact Subtype.ext (h2.trans hu1)

/-- Odd prime torsion has no nontrivial fourth torsion. -/
theorem roots_four_torsion {s : ℕ} (hs : s.Prime) (ho : s ≠ 2)
    (u : rootsOfUnity s F) (hu : u ^ 4 = 1) : u = 1 := by
  have hc : s.Coprime 4 := by
    have h2 : s.Coprime 2 := hs.coprime_iff_not_dvd.mpr
      (fun h => ho ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_two).mp h))
    exact h2.pow_right 2
  apply orderOf_eq_one_iff.mp
  apply Nat.dvd_one.mp
  rw [← hc.gcd_eq_one]
  exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one
    (show u ^ s = 1 from Subtype.ext ((mem_rootsOfUnity s _).mp u.property)))
    (orderOf_dvd_of_pow_eq_one hu)

/-- Roots of order dividing q+1 have norm one. -/
theorem roots_norm {q s : ℕ} (hconj : ∀ x, J.conj x = x ^ q) (hd : s ∣ q + 1)
    (u : rootsOfUnity s F) : J.conj (u.val : F) * (u.val : F) = 1 := by
  rw [hconj, ← pow_succ]
  obtain ⟨d, hd⟩ := hd
  rw [hd, pow_mul, (mem_rootsOfUnity' s u.val).mp u.property, one_pow]

/-- An explicit elementary abelian embedding into the standard involution centralizer. -/
theorem exists_torsion_embedding {q s : ℕ} (hconj : ∀ x, J.conj x = x ^ q)
    (hs : s.Prime) (ho : s ≠ 2) (hd : s ∣ q + 1) :
    ∃ f : (Fin 3 → rootsOfUnity s F) →*
      Subgroup.centralizer ({involution J hJ} : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
      Function.Injective f :=
  ⟨torusCentralizer J hJ (rootsOfUnity s F) (roots_norm J hconj hd),
    torusCentralizer_injective J hJ _ _ (roots_four_torsion hs ho)⟩

/-- One nonidentity involution supports all the required odd-prime embeddings
in the original projective group, by actual orthonormal-basis transport. -/
theorem exists_involution_embeddings [Finite F] {r : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (hc : Nat.card F = r ^ 2) (hconj : ∀ x, J.conj x = x ^ r) :
    ∃ z : ProjectiveSpecialUnitaryMatrixGroup J, z ≠ 1 ∧ z ^ 2 = 1 ∧
      ∀ s : ℕ, s.Prime → s ≠ 2 → s ∣ r + 1 →
        ∃ f : (Fin 3 → rootsOfUnity s F) →*
          Subgroup.centralizer ({z} : Set (ProjectiveSpecialUnitaryMatrixGroup J)),
          Function.Injective f := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F r := charP_of_card_eq_prime_pow (p := r) (f := 2) (by
    simpa only [← Nat.card_eq_fintype_card] using hc)
  let : Fact (2 < r) := ⟨lt_of_le_of_ne (Fact.out : r.Prime).two_le (Ne.symm hr)⟩
  obtain ⟨P, hP⟩ := J.exists_orthonormal_basis_of_prime_frobenius hconj hc
  let K : HermitianForm 4 F := identityForm J.conj J.conj_involutive
  let e := (projectiveBasisEquiv J P hP).symm
  let z := involution K rfl
  refine ⟨e z, ?_, ?_, ?_⟩
  · exact fun h => involution_ne_one K rfl (CharP.neg_one_ne_one F r)
      (e.injective (h.trans (map_one e).symm))
  · rw [← map_pow, show z ^ 2 = 1 from involution_sq K rfl, map_one]
  · intro s hs ho hd
    obtain ⟨f, hf⟩ := exists_torsion_embedding K rfl hconj hs ho hd
    let ec := Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e z
    exact ⟨ec.toMonoidHom.comp f, ec.injective.comp hf⟩

/-- The three torus coordinates each have exactly s elements. -/
theorem card_roots_of_dvd_succ [Finite F] {r s : ℕ} [Fact r.Prime] [Fact s.Prime]
    (hc : Nat.card F = r ^ 2) (hd : s ∣ r + 1) :
    Nat.card (rootsOfUnity s F) = s := by
  let : NeZero s := ⟨(Fact.out : s.Prime).ne_zero⟩
  apply FiniteField.card_rootsOfUnity_of_dvd
  rw [hc]
  have hr : 1 ≤ r := (Fact.out : r.Prime).one_lt.le
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have he : r ^ 2 - 1 = (r + 1) * (r - 1) := by
    nlinarith [Nat.sub_add_cancel hr, Nat.sub_add_cancel hr2]
  rw [he]
  exact dvd_mul_of_dvd_left hd _

/-- The centralizer contains an actual elementary abelian subgroup of order s³
for each odd prime s dividing r+1. -/
theorem exists_involution_elementary_rank_three [Finite F] {r : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (hc : Nat.card F = r ^ 2) (hconj : ∀ x, J.conj x = x ^ r) :
    ∃ z : ProjectiveSpecialUnitaryMatrixGroup J, z ≠ 1 ∧ z ^ 2 = 1 ∧
      ∀ s : ℕ, s.Prime → s ≠ 2 → s ∣ r + 1 →
        ∃ E : Subgroup (Subgroup.centralizer
          ({z} : Set (ProjectiveSpecialUnitaryMatrixGroup J))),
          IsElementaryAbelian s E ∧ Nat.card E = s ^ 3 ∧ Group.rank E = 3 := by
  obtain ⟨z, hz, hz2, hf⟩ := exists_involution_embeddings J hr hc hconj
  refine ⟨z, hz, hz2, ?_⟩
  intro s hs ho hd
  let : Fact s.Prime := ⟨hs⟩
  obtain ⟨f, hfi⟩ := hf s hs ho hd
  have hpow (a : Fin 3 → rootsOfUnity s F) : a ^ s = 1 := by
    funext i
    exact Subtype.ext ((mem_rootsOfUnity s _).mp (a i).property)
  have hpowE (x : f.range) : x ^ s = 1 := by
    obtain ⟨a, rfl⟩ := f.rangeRestrict_surjective x
    rw [← map_pow, hpow, map_one]
  let hE : IsElementaryAbelian s f.range :=
    { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpowE }
  have hcard : Nat.card f.range = s ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hfi).toEquiv,
      Nat.card_fun, card_roots_of_dvd_succ hc hd, Nat.card_fin]
  refine ⟨f.range, hE, hcard, le_antisymm
    (IsElementaryAbelian.rank_le_of_card_le f.range hcard.le) ?_⟩
  apply (Nat.pow_dvd_pow_iff_le_right hs.one_lt).mp
  rw [← hcard]
  exact card_dvd_exponent_pow_rank' f.range hpowE

/-- A nonidentity involution whose centralizer has rank at least three at
every odd prime divisor of r+1. -/
theorem exists_involution_three_le_primeRank [Finite F] {r : ℕ} [Fact r.Prime]
    (hr : r ≠ 2) (hc : Nat.card F = r ^ 2) (hconj : ∀ x, J.conj x = x ^ r) :
    ∃ z : ProjectiveSpecialUnitaryMatrixGroup J, z ≠ 1 ∧ z ^ 2 = 1 ∧
      ∀ s : ℕ, s.Prime → s ≠ 2 → s ∣ r + 1 →
        3 ≤ primeRank s
          (Subgroup.centralizer ({z} : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  let : Finite (GL (Fin 4) F) := Finite.of_injective Units.val Units.val_injective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective (project J) (project_surjective J)
  obtain ⟨z, hz, hz2, hf⟩ := exists_involution_embeddings J hr hc hconj
  refine ⟨z, hz, hz2, ?_⟩
  intro s hs ho hd
  let : Fact s.Prime := ⟨hs⟩
  obtain ⟨f, hfi⟩ := hf s hs ho hd
  refine primeRank_ge_of_elementary_embedding ?_ ?_ f hfi
  · intro a
    funext i
    exact Subtype.ext ((mem_rootsOfUnity s _).mp (a i).property)
  · rw [Nat.card_fun, card_roots_of_dvd_succ hc hd, Nat.card_fin]

end Theory.SpecificGroups.ClassicalUnitary.OddFourRanks
