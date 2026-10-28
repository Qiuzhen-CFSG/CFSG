module

public import BenderSuzuki.MatrixGroups.Unitary
public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.PrimeRankWitness
public import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Tactic

/-!
# Rank-three tori in unitary root normalizers

In characteristic two, swapping the first two coordinates of an identity-Gram
Hermitian space is a determinant-one involution. It is the transvection along
the isotropic vector (1,1,0,…). Its projective image is nonidentity.
The matrices diag(1,1,a,b,c,(abc)⁻¹,1,…) preserve the form whenever their
entries have norm one, and centralize this root element. Their first diagonal
entry forces their projective scalar kernel to be trivial.

For a prime p dividing q+1, the p-th roots of unity therefore give an elementary
abelian subgroup of rank three in the actual normalizer of the root involution.
For even q such a prime is odd. Thus PSU in dimension at least six is not
quasithin. The separate BinaryForms extension supplies genuine basis changes
for arbitrary forms and the dimension-two comparison.

Source: Aschbacher–Smith, The Classification of Quasithin Groups, A.2.18,
printed p.40, used in Theorem D/14.8.2(1), printed pp.1078–1079. This direct
involution-centralizer argument replaces the source's parabolic-section
exclusion for the higher-dimensional unitary family.
-/

@[expose] public noncomputable section
open Matrix BenderSuzuki.MatrixGroups
namespace Theory.SpecificGroups.UnitaryRootNormalizer
variable {F : Type*} [Field F] (k : ℕ)
variable (J : HermitianForm (6 + k) F) (hJ : J.form = 1)

/-- The first coordinate of the root plane. -/
def rootFirst : Fin (6 + k) := Fin.castAdd k 0
/-- The second coordinate of the root plane. -/
def rootSecond : Fin (6 + k) := Fin.castAdd k 1
private theorem first_ne_second : rootFirst k ≠ rootSecond k := by
  simp [rootFirst, rootSecond]

/-- The coordinate transposition, a unitary transvection in characteristic two. -/
def rootMatrix : GL (Fin (6 + k)) F where
  val := (Equiv.swap (rootFirst k) (rootSecond k)).permMatrix F
  inv := (Equiv.swap (rootFirst k) (rootSecond k)).permMatrix F
  val_inv := by rw [← permMatrix_mul, Equiv.swap_mul_self, permMatrix_one]
  inv_val := by rw [← permMatrix_mul, Equiv.swap_mul_self, permMatrix_one]

@[simp] theorem rootMatrix_val : (rootMatrix (F := F) k).val =
    (Equiv.swap (rootFirst k) (rootSecond k)).permMatrix F := rfl

/-- The root representative squares to one. -/
theorem rootMatrix_sq : rootMatrix (F := F) k ^ 2 = 1 := by
  rw [pow_two]
  apply Units.ext
  change (Equiv.swap (rootFirst k) (rootSecond k)).permMatrix F *
    (Equiv.swap (rootFirst k) (rootSecond k)).permMatrix F = 1
  rw [← permMatrix_mul, Equiv.swap_mul_self, permMatrix_one]

include hJ in
/-- Form and determinant preservation for the root representative. -/
theorem rootMatrix_special [CharP F 2] : rootMatrix (F := F) k ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  constructor
  · rw [hJ, mul_one]
    have he : J.conjTranspose (rootMatrix (F := F) k).val =
        (rootMatrix (F := F) k).val := by
      change (((Equiv.swap (rootFirst k) (rootSecond k)).permMatrix F).map J.conj).transpose = _
      have hm : ((Equiv.swap (rootFirst k) (rootSecond k)).permMatrix F).map J.conj =
          (Equiv.swap (rootFirst k) (rootSecond k)).permMatrix F := by
        ext i j
        simp [Matrix.map, apply_ite]
      rw [hm, transpose_permMatrix, Equiv.swap_inv]
      rfl
    rw [he]
    simpa only [pow_two, Units.val_mul, Units.val_one] using
      congrArg Units.val (rootMatrix_sq (F := F) k)
  · apply Units.ext
    change ((Equiv.swap (rootFirst k) (rootSecond k)).permMatrix F).det = 1
    rw [det_permutation, Equiv.Perm.sign_swap (first_ne_second k)]
    simp [CharTwo.neg_eq]

/-- Projection from the actual special unitary subgroup to its image in PGL. -/
def project : J.specialSubgroup →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (ProjGenLinGroup.mk.comp J.specialSubgroup.subtype).codRestrict _
    (fun a => ⟨a.val, a.property, rfl⟩)

theorem project_surjective : Function.Surjective (project k J) := by
  rintro ⟨x, A, hA, rfl⟩
  exact ⟨⟨A, hA⟩, rfl⟩

/-- The nontrivial projective root element. -/
def root [CharP F 2] : ProjectiveSpecialUnitaryMatrixGroup J :=
  project k J ⟨rootMatrix k, rootMatrix_special k J hJ⟩

theorem root_sq [CharP F 2] : root k J hJ ^ 2 = 1 := by
  rw [root, ← map_pow]
  have he : (⟨rootMatrix k, rootMatrix_special k J hJ⟩ : J.specialSubgroup) ^ 2 = 1 :=
    Subtype.ext (rootMatrix_sq k)
  rw [he, map_one]

theorem root_ne_one [CharP F 2] : root k J hJ ≠ 1 := by
  intro h
  have he : ProjGenLinGroup.mk (rootMatrix (F := F) k) = 1 := congrArg Subtype.val h
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at he
  obtain ⟨u, hu⟩ := he
  have hc := congrArg (fun A : GL (Fin (6+k)) F => A.val (rootFirst k) (rootSecond k)) hu
  simp [GeneralLinearGroup.coe_scalar, Matrix.scalar, rootMatrix_val,
    first_ne_second k] at hc

/-- The order-two subgroup generated by a root transvection. -/
def rootSubgroup [CharP F 2] : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Subgroup.zpowers (root k J hJ)

theorem rootSubgroup_ne_bot [CharP F 2] : rootSubgroup k J hJ ≠ ⊥ := by
  simpa [rootSubgroup, Subgroup.zpowers_eq_bot] using root_ne_one k J hJ

theorem rootSubgroup_isTwoGroup [CharP F 2] : IsPGroup 2 (rootSubgroup k J hJ) := by
  have ho : orderOf (root k J hJ) = 2 :=
    orderOf_eq_prime_iff.mpr ⟨root_sq k J hJ, root_ne_one k J hJ⟩
  apply IsPGroup.of_card (n := 1)
  simp [rootSubgroup, Nat.card_zpowers, ho]

/-- The literal root normalizer is a two-local subgroup. -/
theorem rootNormalizer_isTwoLocal [CharP F 2] :
    IsTwoLocal (Subgroup.normalizer (rootSubgroup k J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) :=
  ⟨rootSubgroup k J hJ, rootSubgroup_ne_bot k J hJ,
    rootSubgroup_isTwoGroup k J hJ, rfl⟩

variable (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)

/-- Four determinant-one coordinates disjoint from the root plane. -/
def torusEntries (a : Fin 3 → C) : Fin (6 + k) → C :=
  Fin.append ![1, 1, a 0, a 1, a 2, (a 0 * a 1 * a 2)⁻¹] (fun _ => 1)

theorem torusEntries_det (a : Fin 3 → C) :
    (diagonal (fun i => ((torusEntries k C a i).val : F))).det = 1 := by
  rw [det_diagonal, Fin.prod_univ_add]
  simp [torusEntries, Fin.prod_univ_succ, ← mul_assoc]

def torusMatrix (a : Fin 3 → C) : GL (Fin (6 + k)) F :=
  GeneralLinearGroup.mkOfDetNeZero (diagonal (fun i => ((torusEntries k C a i).val : F)))
    (by rw [torusEntries_det]; exact one_ne_zero)

@[simp] theorem torusMatrix_val (a : Fin 3 → C) : (torusMatrix k C a).val =
    diagonal (fun i => ((torusEntries k C a i).val : F)) := rfl

include hJ hC in
theorem torusMatrix_special (a : Fin 3 → C) : torusMatrix k C a ∈ J.specialSubgroup := by
  rw [J.mem_specialSubgroup_iff]
  constructor
  · rw [hJ, torusMatrix_val, mul_one]
    ext i j
    by_cases h : j = i <;> simp [HermitianForm.conjTranspose, Matrix.mul_apply,
      Matrix.diagonal_apply, Matrix.one_apply, h, Ne.symm, hC]
  · apply Units.ext
    exact torusEntries_det k C a

/-- The three-parameter homomorphism into SU. -/
def torusSpecial : (Fin 3 → C) →* J.specialSubgroup where
  toFun a := ⟨torusMatrix k C a, torusMatrix_special k J hJ C hC a⟩
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    change diagonal _ = 1
    rw [← diagonal_one]
    apply congrArg diagonal
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      fin_cases j <;> simp [torusEntries]
    · intro j
      simp [torusEntries]
  map_mul' a b := by
    apply Subtype.ext
    apply Units.ext
    change diagonal _ = diagonal _ * diagonal _
    rw [diagonal_mul_diagonal]
    apply congrArg diagonal
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      fin_cases j <;> simp [torusEntries, mul_assoc, mul_comm, mul_left_comm]
    · intro j
      simp [torusEntries]

/-- The actual projective torus. -/
def torusProjective : (Fin 3 → C) →* ProjectiveSpecialUnitaryMatrixGroup J :=
  (project k J).comp (torusSpecial k J hJ C hC)

/-- Its first coordinate is one, so no nonidentity scalar survives. -/
theorem torusProjective_injective : Function.Injective (torusProjective k J hJ C hC) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hp : ProjGenLinGroup.mk (torusMatrix k C a) = 1 := congrArg Subtype.val ha
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at hp
  obtain ⟨u, hu⟩ := hp
  have hd (i : Fin 6) :
      ((![1, 1, a 0, a 1, a 2, (a 0 * a 1 * a 2)⁻¹] i).val : F) = (u : F) := by
    have hi := congrArg (fun g : GL (Fin (6+k)) F => g.val (Fin.castAdd k i) (Fin.castAdd k i)) hu
    simpa [GeneralLinearGroup.coe_scalar, Matrix.scalar, torusMatrix_val, torusEntries] using hi.symm
  have hu1 : (u : F) = 1 := (hd 0).symm
  funext i
  fin_cases i
  · exact Subtype.ext (Units.ext ((hd 2).trans hu1))
  · exact Subtype.ext (Units.ext ((hd 3).trans hu1))
  · exact Subtype.ext (Units.ext ((hd 4).trans hu1))

private theorem torusMatrix_commute_root (a : Fin 3 → C) :
    Commute (torusMatrix k C a) (rootMatrix (F := F) k) := by
  apply Units.ext
  change diagonal _ * (Equiv.swap (rootFirst k) (rootSecond k)).permMatrix F =
    (Equiv.swap (rootFirst k) (rootSecond k)).permMatrix F * diagonal _
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases he : Equiv.swap (rootFirst k) (rootSecond k) i = j
  · subst j
    have ht : torusEntries k C a (Equiv.swap (rootFirst k) (rootSecond k) i) = torusEntries k C a i := by
      by_cases hi : i = rootFirst k
      · subst i
        simp [rootFirst, rootSecond, torusEntries]
      by_cases hi' : i = rootSecond k
      · subst i
        simp [rootFirst, rootSecond, torusEntries]
      rw [Equiv.swap_apply_of_ne_of_ne hi hi']
    simp [ht]
  · simp [he]

/-- The torus centralizes the projective root element. -/
theorem torusProjective_commute_root [CharP F 2] (a : Fin 3 → C) :
    Commute (torusProjective k J hJ C hC a) (root k J hJ) := by
  apply Subtype.ext
  exact congrArg ProjGenLinGroup.mk (torusMatrix_commute_root k C a)

/-- Hence the torus lies in the genuine two-local normalizer. -/
def torusNormalizer [CharP F 2] : (Fin 3 → C) →*
    Subgroup.normalizer (rootSubgroup k J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
  (torusProjective k J hJ C hC).codRestrict _ (fun a => by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    rintro g ⟨m, rfl⟩
    exact ((torusProjective_commute_root k J hJ C hC a).zpow_right m).eq.symm)

theorem torusNormalizer_injective [CharP F 2] :
    Function.Injective (torusNormalizer k J hJ C hC) := by
  intro a b h
  exact torusProjective_injective k J hJ C hC (congrArg Subtype.val h)

/-- Every prime divisor of q+1 yields an elementary rank-three subgroup in
this literal root normalizer. -/
theorem primeRank_rootNormalizer_ge_three [Finite F] [CharP F 2]
    {q p : ℕ} (hcard : Nat.card F = q ^ 2) (hq : 2 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q) (hp : p.Prime) (hd : p ∣ q + 1) :
    3 ≤ primeRank p (Subgroup.normalizer (rootSubgroup k J hJ : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Finite (GL (Fin (6+k)) F) := Finite.of_injective Units.val Units.val_injective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective (project k J) (project_surjective k J)
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
  apply primeRank_ge_of_elementary_embedding
    (A := Fin 3 → rootsOfUnity p F)
    (fun a => funext (fun i => hpow (a i)))
    (by rw [Nat.card_fun, hc, Nat.card_fin])
    (torusNormalizer k J hJ (rootsOfUnity p F) hnorm)
  exact torusNormalizer_injective k J hJ (rootsOfUnity p F) hnorm

local instance projectiveFinite [Finite F] : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (GL (Fin (6+k)) F) := Finite.of_injective Units.val Units.val_injective
  exact Finite.of_surjective (project k J) (project_surjective k J)

include hJ in
/-- The identity-form PSU in dimension at least six is never quasithin
in characteristic two, including the smallest field. -/
theorem not_quasithin [Finite F] [CharP F 2]
    {q : ℕ} (hcard : Nat.card F = q ^ 2) (hq : 2 ≤ q) (heven : Even q)
    (hconj : ∀ x, J.conj x = x ^ q) :
    ¬ IsQuasithin (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (GL (Fin (6+k)) F) := Finite.of_injective Units.val Units.val_injective
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective (project k J) (project_surjective k J)
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show q + 1 ≠ 1 by omega)
  have ho : Odd p := hp.odd_of_ne_two (by
    intro he
    subst p
    obtain ⟨a, ha⟩ := heven
    obtain ⟨b, hb⟩ := hd
    omega)
  intro hG
  have hr := primeRank_rootNormalizer_ge_three k J hJ hcard hq hconj hp hd
  have hb := Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hG _
    (rootNormalizer_isTwoLocal k J hJ) p hp ho
  omega

end Theory.SpecificGroups.UnitaryRootNormalizer
