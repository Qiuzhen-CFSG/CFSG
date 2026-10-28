module

public import Theory.SpecificGroups.ClassicalUnitary.FiveFlag
public import Theory.GroupTheory.PrimeRankWitness
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic.FinCases

/-!
# Diagonal three-tori in the unitary-five line parabolic

For any subgroup `C` of norm-one field units, the diagonal matrices
`diag(a,a,b,c,(a²bc)⁻¹)` have determinant one and preserve the line
`(x,x,0,0,0)`. They therefore map into its actual projective special-unitary
stabilizer. A matrix in the projective kernel is scalar; its scalar has fifth
power one. Thus the map is injective when `C` has no nontrivial fifth torsion.

For a prime `p ≠ 5` dividing `q+1`, the `p`-th roots of unity in a field of
order `q²` form a group of order `p`. With Frobenius conjugation `x ↦ x^q`,
these units have norm one. Their threefold product supplies an elementary
abelian subgroup of order `p³` in the line parabolic.

This proves the concrete rank bound needed for the nonexceptional-parameter
route in Aschbacher--Smith, *The Classification of Quasithin Groups*, A.2.18
(printed p. 40) and the final paragraph of F.1.12 (printed p. 264). No Levi
factor decomposition is assumed.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive
variable {F : Type*} [Field F]
variable (J : HermitianForm 5 F) (hJ : J.form = 1)
variable (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)

/-- The determinant-one diagonal entries, with equal first two coordinates. -/
def torusEntries (a : Fin 3 → C) : Fin 5 → C :=
  ![a 0, a 0, a 1, a 2, (a 0 ^ 2 * a 1 * a 2)⁻¹]

/-- The chosen diagonal entries multiply to one. -/
theorem torusEntries_det (a : Fin 3 → C) :
    (diagonal (fun i => ((torusEntries C a i).val : F))).det = 1 := by
  rw [det_diagonal]
  simp [torusEntries, Fin.prod_univ_succ, pow_two, ← mul_assoc]

/-- The diagonal matrix as an invertible matrix. -/
noncomputable def torusMatrix (a : Fin 3 → C) : GL (Fin 5) F :=
  GeneralLinearGroup.mkOfDetNeZero
    (diagonal (fun i => ((torusEntries C a i).val : F)))
    (by rw [torusEntries_det]; exact one_ne_zero)

@[simp] theorem torusMatrix_val (a : Fin 3 → C) :
    (torusMatrix C a : Matrix (Fin 5) (Fin 5) F) =
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
    fin_cases i <;> simp [torusEntries, mul_pow, mul_assoc, mul_comm, mul_left_comm]

/-- Equal first two diagonal entries preserve the chosen line in both directions. -/
theorem torusSpecial_stabilizes (a : Fin 3 → C) :
    torusSpecial J hJ C hC a ∈ specialStabilizer J (line F) := by
  rw [mem_specialStabilizer_iff]
  intro v
  change (diagonal _ *ᵥ v ∈ line F) ↔ v ∈ line F
  simp [line, mulVec_diagonal, torusEntries, mul_eq_mul_left_iff]

/-- The diagonal homomorphism into the projective line parabolic. -/
noncomputable def torusParabolic : (Fin 3 → C) →* lineParabolic J :=
  ((project J).comp (torusSpecial J hJ C hC)).codRestrict _
    (fun a => ⟨torusSpecial J hJ C hC a, torusSpecial_stabilizes J hJ C hC a, rfl⟩)

/-- Projectivization is injective when the parameter group has no fifth torsion. -/
theorem torusParabolic_injective
    (hfive : ∀ u : C, u ^ 5 = 1 → u = 1) :
    Function.Injective (torusParabolic J hJ C hC) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hp : ProjGenLinGroup.mk (torusMatrix C a) = 1 :=
    congrArg (fun g : lineParabolic J => g.val.val) ha
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
  obtain ⟨u, hu⟩ := hp
  have hd (i : Fin 5) : ((torusEntries C a i).val : F) = (u : F) := by
    have hi := congrArg (fun g : GL (Fin 5) F => (g : Matrix (Fin 5) (Fin 5) F) i i) hu
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar, torusMatrix_val] using hi.symm
  have h0 : (a 0).val = u := Units.ext (hd 0)
  have h1 : (a 1).val = u := Units.ext (hd 2)
  have h2 : (a 2).val = u := Units.ext (hd 3)
  have h4 : ((a 0 ^ 2 * a 1 * a 2)⁻¹).val = u := Units.ext (hd 4)
  have hu5 : u ^ 5 = 1 := by
    simp only [Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_pow, h0, h1, h2] at h4
    have ht := inv_eq_iff_mul_eq_one.mp h4
    simpa only [pow_succ, pow_zero, one_mul, mul_assoc] using ht
  have ha0 : a 0 = 1 := hfive (a 0) (by
    apply Subtype.ext
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, h0] using hu5)
  have hu1 : u = 1 := h0.symm.trans (congrArg Subtype.val ha0)
  funext i
  fin_cases i
  · exact ha0
  · exact Subtype.ext (h1.trans hu1)
  · exact Subtype.ext (h2.trans hu1)

include hJ in
/-- Every prime divisor of `q+1` other than 5 witnesses rank at least three. -/
theorem primeRank_lineParabolic_ge_of_prime_ne_five [Finite F]
    {q p : ℕ} (hcard : Nat.card F = q ^ 2) (hq : 2 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q)
    (hp : p.Prime) (hd : p ∣ q + 1) (hne : p ≠ 5) :
    3 ≤ primeRank p (lineParabolic J) := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Finite (GL (Fin 5) F) := Finite.of_injective Units.val Units.val_injective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective (project J) (project_surjective J)
  have hdu : p ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hcard]
    have heq : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      have hq1 : 1 ≤ q := by omega
      have hq2 : 1 ≤ q ^ 2 := by nlinarith
      nlinarith [Nat.sub_add_cancel hq1, Nat.sub_add_cancel hq2]
    rw [heq]
    exact dvd_mul_of_dvd_left hd _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) p hdu
  have hroot : IsPrimitiveRoot u p := hu ▸ IsPrimitiveRoot.orderOf u
  have hc : Nat.card (rootsOfUnity p F) = p := hroot.card_rootsOfUnity'
  have hpow (u : rootsOfUnity p F) : u ^ p = 1 :=
    Subtype.ext ((mem_rootsOfUnity p u.val).mp u.property)
  have hnorm (u : rootsOfUnity p F) : J.conj (u.val : F) * (u.val : F) = 1 := by
    rw [hconj, ← pow_succ]
    obtain ⟨d, hd⟩ := hd
    rw [hd, pow_mul, (mem_rootsOfUnity' p u.val).mp u.property, one_pow]
  have hcop : p.Coprime 5 := hp.coprime_iff_not_dvd.mpr (by
    intro h
    exact hne ((Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h))
  have hfive (u : rootsOfUnity p F) (hu : u ^ 5 = 1) : u = 1 := by
    apply orderOf_eq_one_iff.mp
    apply Nat.dvd_one.mp
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (hpow u)) (orderOf_dvd_of_pow_eq_one hu)
  apply primeRank_ge_of_elementary_embedding
    (A := Fin 3 → rootsOfUnity p F)
    (fun a => funext (fun i => hpow (a i)))
    (by rw [Nat.card_fun, hc, Nat.card_fin])
    (torusParabolic J hJ (rootsOfUnity p F) hnorm)
  exact torusParabolic_injective J hJ (rootsOfUnity p F) hnorm hfive

end Theory.SpecificGroups.UnitaryFive
