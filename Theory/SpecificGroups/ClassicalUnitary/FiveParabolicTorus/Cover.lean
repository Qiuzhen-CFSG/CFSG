module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTorus.RankObstruction
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineShears
public import Theory.GroupTheory.QuasithinBasic
public import Theory.GroupTheory.NonsolvableTwoLocal
public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicRadical.LineCore.Parabolic.LeviAction
public import Theory.SpecificGroups.ClassicalUnitary.ProjectiveKernel
public import Mathlib.GroupTheory.NoncommCoprod

/-!
# The unitary-five cover at fixed-field size four

Equal first two diagonal entries commute with the coordinate interchange,
an actual involution of SU5 in characteristic two. The three-coordinate
fifth-root torus embeds in its centralizer, proving that SU5(4) is not
quasithin. Orthonormalization gives the result for every allowed Hermitian
form, with the stored fourth-power Frobenius unchanged.

The fifth-root scalar subgroup also commutes with the embedded middle SU3.
Their product is faithful: projectivization kills the scalar factor and is
faithful on the middle SU3. It lies in the original SU line stabilizer and
has cyclic factor of order five over a field of sixteen elements. The middle
form is the existing general `LineCore.Parabolic.middleForm`, with the same
coefficient field and involution, not the fixed q=3 UnitaryThree model.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*, A.2.18,
printed p.40, the nontrivial-center case after q=4 has been established.
-/

@[expose] public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive
variable {F : Type*} [Field F] [CharP F 2]
variable (J : HermitianForm 5 F) (hJ : J.form = 1)
variable (C : Subgroup Fˣ) (hC : ∀ u : C, J.conj (u.val : F) * (u.val : F) = 1)

noncomputable def torusSwapCentralizer : (Fin 3 → C) →*
    Subgroup.centralizer ({lineSwap J hJ} : Set J.specialSubgroup) :=
  (torusSpecial J hJ C hC).codRestrict _ (by
    intro a
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    apply Units.ext
    change diagonal _ * lineSwapMatrix = lineSwapMatrix * diagonal _
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.diagonal_mul, Matrix.mul_diagonal, lineSwapMatrix,
        Equiv.swap_apply_def, torusEntries] <;> ring)

theorem torusSwapCentralizer_injective : Function.Injective (torusSwapCentralizer J hJ C hC) := by
  intro a b h
  exact torusSpecial_injective J hJ C hC (congrArg Subtype.val h)

include hJ in
theorem lineSwap_orderOf : orderOf (lineSwap J hJ) = 2 := by
  apply orderOf_eq_prime
  · rw [pow_two]
    apply Subtype.ext
    apply Units.ext
    change lineSwapMatrix * lineSwapMatrix = (1 : Matrix (Fin 5) (Fin 5) F)
    exact lineSwapMatrix_sq (F := F)
  · intro he
    exact project_lineSwap_ne_one J hJ (by rw [he, map_one])

include hJ in
theorem primeRank_special_swapCentralizer_ge [Finite F] {q p : ℕ}
    (hcard : Nat.card F = q ^ 2) (hq : 2 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q) (hp : p.Prime) (hd : p ∣ q + 1) :
    3 ≤ primeRank p (Subgroup.centralizer ({lineSwap J hJ} : Set J.specialSubgroup)) := by
  let : Fact p.Prime := ⟨hp⟩
  let : NeZero p := ⟨hp.ne_zero⟩
  let : Finite (GL (Fin 5) F) := Finite.of_injective Units.val Units.val_injective
  have hc : Nat.card (rootsOfUnity p F) = p := by
    apply FiniteField.card_rootsOfUnity_of_dvd
    rw [hcard]
    have he : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      nlinarith [Nat.sub_add_cancel (show 1 ≤ q by omega),
        Nat.sub_add_cancel (show 1 ≤ q ^ 2 by nlinarith)]
    rw [he]
    exact dvd_mul_of_dvd_left hd _
  have hn (u : rootsOfUnity p F) : J.conj (u.val : F) * (u.val : F) = 1 := by
    rw [hconj, ← pow_succ]
    obtain ⟨d, hd⟩ := hd
    rw [hd, pow_mul, (mem_rootsOfUnity' p u.val).mp u.property, one_pow]
  apply primeRank_ge_of_elementary_embedding
    (f := torusSwapCentralizer J hJ (rootsOfUnity p F) hn)
    (hf := torusSwapCentralizer_injective J hJ (rootsOfUnity p F) hn)
  · intro a
    funext i
    exact Subtype.ext ((mem_rootsOfUnity p _).mp (a i).property)
  · rw [Nat.card_fun, hc, Nat.card_fin]

include hJ in
theorem not_quasithin_special_four [Finite F]
    (hcard : Nat.card F = 4 ^ 2) (hconj : ∀ x, J.conj x = x ^ 4) :
    ¬ IsQuasithin J.specialSubgroup := by
  let : Finite (GL (Fin 5) F) := Finite.of_injective Units.val Units.val_injective
  intro hqt
  have hr := primeRank_special_swapCentralizer_ge J hJ hcard (by decide) hconj
    (by decide : Nat.Prime 5) (by decide : 5 ∣ 4 + 1)
  have hb := (Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt) _
    (Theory.GroupTheory.isTwoLocal_involution_centralizer (lineSwap_orderOf J hJ)) 5 (by decide) (by decide)
  omega

omit [CharP F 2] in
theorem not_quasithin_special_four_of_form [Finite F]
    (hcard : Nat.card F = 4 ^ 2) (hconj : ∀ x, J.conj x = x ^ 4) :
    ¬ IsQuasithin J.specialSubgroup := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 4) (by
    simpa only [← Nat.card_eq_fintype_card, show (4 : ℕ) ^ 2 = 2 ^ 4 by decide] using hcard)
  let : Finite (GL (Fin 5) F) := Finite.of_injective Units.val Units.val_injective
  have hfixed : Nat.card {x : F // J.conj x = x} = 4 :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hcard hconj
  obtain ⟨P, hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    5 J 4 hcard hfixed
  intro hqt
  exact not_quasithin_special_four (HermitianForm.IdentityGram.identityGram J) rfl hcard hconj
    (Theory.GroupTheory.isQuasithin_of_equiv (HermitianForm.IdentityGram.specialEquiv J P hP) hqt)
end Theory.SpecificGroups.UnitaryFive

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive
open LineCore.Parabolic
variable {F : Type*} [Field F]
variable (J : HermitianForm 5 F) (hJ : J.form = 1)
variable (hconj : ∀ x, J.conj x = x ^ 4)

noncomputable def fifthScalars : rootsOfUnity 5 F →* J.specialSubgroup :=
  (ClassicalUnitary.ProjectiveKernel.project J).ker.subtype.comp
    (ClassicalUnitary.ProjectiveKernel.scalarToKernel J hconj)

theorem fifthScalars_project (u : rootsOfUnity 5 F) :
    project J (fifthScalars J hconj u) = 1 := by
  apply Subtype.ext
  exact congrArg Subtype.val (ClassicalUnitary.ProjectiveKernel.scalarToKernel J hconj u).property

theorem fifthScalars_injective : Function.Injective (fifthScalars J hconj) :=
  Subtype.val_injective.comp
    (ClassicalUnitary.ProjectiveKernel.scalarToKernel_bijective J hconj).1

noncomputable def coverProduct :
    rootsOfUnity 5 F × (middleForm J).specialSubgroup →* J.specialSubgroup :=
  (fifthScalars J hconj).noncommCoprod (leviSU J hJ) (by
    intro u A
    exact (Subgroup.mem_center_iff.mp
      (ClassicalUnitary.ProjectiveKernel.project_kernel_le_center J
        (ClassicalUnitary.ProjectiveKernel.scalarToKernel J hconj u).property)
      (leviSU J hJ A)).symm)

theorem coverProduct_injective : Function.Injective (coverProduct J hJ hconj) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hp : project J (leviSU J hJ x.2) = 1 := by
    have he := congrArg (project J) hx
    change project J (fifthScalars J hconj x.1 * leviSU J hJ x.2) = _ at he
    simpa only [map_mul, fifthScalars_project, one_mul, map_one] using he
  have hA : x.2 = 1 := leviParabolic_injective J hJ (by
    apply Subtype.ext
    change project J (leviSU J hJ x.2) = ↑((leviParabolic J hJ) 1)
    simpa only [map_one, Subgroup.coe_one] using hp)
  have hu : x.1 = 1 := fifthScalars_injective J hconj (by
    change fifthScalars J hconj x.1 * leviSU J hJ x.2 = 1 at hx
    simpa only [hA, map_one, mul_one] using hx)
  exact Prod.ext hu hA

theorem coverProduct_mem_line (x : rootsOfUnity 5 F × (middleForm J).specialSubgroup) :
    coverProduct J hJ hconj x ∈ specialStabilizer J (line F) := by
  apply (specialStabilizer J (line F)).mul_mem
  · exact ker_project_le_specialStabilizer J (line F) (fifthScalars_project J hconj x.1)
  · exact leviSU_mem_stabilizer J hJ x.2

noncomputable def coverProductParabolic :
    rootsOfUnity 5 F × (middleForm J).specialSubgroup →* specialStabilizer J (line F) :=
  (coverProduct J hJ hconj).codRestrict _ (coverProduct_mem_line J hJ hconj)

theorem coverProductParabolic_injective : Function.Injective (coverProductParabolic J hJ hconj) := by
  intro x y h
  exact coverProduct_injective J hJ hconj (congrArg Subtype.val h)

theorem card_fifthRoots [Finite F] (hcard : Nat.card F = 16) :
    Nat.card (rootsOfUnity 5 F) = 5 := by
  apply FiniteField.card_rootsOfUnity_of_dvd
  rw [hcard]
  norm_num

theorem fifthRoots_cyclic [Finite F] : IsCyclic (rootsOfUnity 5 F) := inferInstance
end Theory.SpecificGroups.UnitaryFive
