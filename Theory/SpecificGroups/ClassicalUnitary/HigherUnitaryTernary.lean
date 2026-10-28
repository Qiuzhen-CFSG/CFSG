module
public import Theory.SpecificGroups.ClassicalUnitary.OddFundamental
public import Theory.SpecificGroups.HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover.Rank
public import Theory.Quasithin.CentralExtensionRankFour

/-!
# Four-space obstruction in higher odd-center ternary unitary covers

The actual elementary 3⁴ subgroup of PSU₄(3) lifts through its scalar
kernel to SU₄(3). Its block embedding in degree at least five is faithful.
The block scalar −I₄ becomes a nonidentity involution centralizing that
subgroup. Rank-four lifting through the original odd center contradicts
quasithinness, including defining-prime central kernels.
Source: Aschbacher–Smith A.2.17, printed p.39, and I.2.1, printed p.409.
-/

open Matrix Subgroup BenderSuzuki.MatrixGroups
open Theory.SpecificGroups.ClassicalUnitary
open scoped MatrixGroups
namespace Theory.SpecificGroups.ClassicalUnitary.HigherUnitaryTernary
open OddFundamental
variable {F : Type*} [Field F] [Finite F]

public theorem exists_elementary_four_involution_centralizer
    {k : ℕ} (hk : 0 < k) (J : HermitianForm (4+k) F)
    (hcard : Nat.card F = 9) (hconj : ∀ x, J.conj x = x^3) :
    ∃ z : ProjectiveSpecialUnitaryMatrixGroup J, orderOf z = 2 ∧
      ∃ A : Subgroup (centralizer ({z} : Set (ProjectiveSpecialUnitaryMatrixGroup J))),
        IsElementaryAbelian 3 A ∧ Nat.card A = 3^4 := by
  let : NeZero k := ⟨by omega⟩
  let : Fact (2 < (3 : ℕ)) := ⟨by decide⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 3 := charP_of_card_eq_prime_pow (f := 2)
    (by simpa [Nat.card_eq_fintype_card] using hcard)
  let J₄ := form J.conj J.conj_involutive 4
  have hc4 : ∀ x, J₄.conj x = x^3 := hconj
  obtain ⟨V,hVg,hVfin,hVE,hV,v,hv⟩ :=
    HigherClassicalCovers.UnitaryOrdinary.OddPrimeCover.exists_elementary_four_embedding
      J₄ Nat.prime_three (by decide) (by simpa using hcard) hc4
  let := hVg
  let := hVfin
  let := hVE
  let : IsElementaryAbelian 3 v.range :=
    IsElementaryAbelian.of_surjective v.rangeRestrict v.rangeRestrict_surjective
  have hkc : Nat.Coprime 3 (Nat.card (ProjectiveKernel.project J₄).ker) := by
    rw [ProjectiveKernel.card_project_kernel J₄ hc4 (by simpa using hcard)]
    norm_num
  obtain ⟨Q,hQE,_,hQc⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    (ProjectiveKernel.project J₄) (ProjectiveKernel.project_surjective J₄) hkc v.range
  let := hQE
  have hQcard : Nat.card Q = 3^4 := by
    rw [hQc,← Nat.card_congr (MonoidHom.ofInjective hv).toEquiv,hV]
  have hfixed := J.fixed_card_prime_power (by exact Nat.prime_three.isPrimePow)
    (by simpa using hcard) hconj
  obtain ⟨C,hC⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    (4+k) J 3 (by simpa using hcard) hfixed
  let e := (HermitianForm.IdentityGram.projectiveEquiv J C hC).symm
  let f := e.toMonoidHom.comp (projectLeft J.conj J.conj_involutive (m := 4) (n := k))
  have hf : Function.Injective f := e.injective.comp (projectLeft_injective _ _)
  let z₄ : J₄.specialSubgroup := ⟨GeneralLinearGroup.scalar (Fin 4) (-1),
    (ProjectiveKernel.scalar_special_iff J₄ hc4 (-1)).mpr (by norm_num)⟩
  have hz4sq : z₄^2 = 1 := by
    apply Subtype.ext
    change (GeneralLinearGroup.scalar (Fin 4) (-1 : Fˣ))^2 = 1
    rw [← map_pow]
    norm_num
  have hz4ne : z₄ ≠ 1 := by
    intro hz
    have heq := congrArg (fun a : J₄.specialSubgroup => a.val.val 0 0) hz
    have heq' : (-1 : F) = 1 := by
      simpa [z₄,GeneralLinearGroup.coe_scalar] using heq
    exact CharP.neg_one_ne_one F 3 heq'
  have hz4c : z₄ ∈ center J₄.specialSubgroup := by
    apply mem_center_iff.mpr
    intro a
    apply Subtype.ext
    have hg : z₄.val ∈ center (GL (Fin 4) F) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨-1,rfl⟩
    exact mem_center_iff.mp hg a.val
  let z := f z₄
  have hz : orderOf z = 2 := (orderOf_injective f hf z₄).trans (orderOf_eq_prime hz4sq hz4ne)
  let j : Q →* centralizer ({z} : Set (ProjectiveSpecialUnitaryMatrixGroup J)) :=
    (f.comp Q.subtype).codRestrict _ (fun x => by
      apply mem_centralizer_singleton_iff.mpr
      exact (show Commute (x : J₄.specialSubgroup) z₄ from mem_center_iff.mp hz4c x).map f)
  have hj : Function.Injective j := by
    intro a b heq
    exact Subtype.ext (hf (congrArg Subtype.val heq))
  refine ⟨z,hz,j.range,IsElementaryAbelian.of_surjective j.rangeRestrict j.rangeRestrict_surjective,?_⟩
  rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv,hQcard]

public theorem not_quasithin_of_odd_center_quotient
    {G : Type*} [Group G] [Finite G] {k : ℕ} (hk : 0 < k)
    (J : HermitianForm (4+k) F) (hcard : Nat.card F = 9)
    (hconj : ∀ x, J.conj x = x^3)
    (iso : G ⧸ center G ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (ho : Odd (Nat.card (center G))) : ¬ IsQuasithin G := by
  obtain ⟨z,hz,A,hA,hAc⟩ := exists_elementary_four_involution_centralizer hk J hcard hconj
  let := hA
  exact CentralExtension.not_isQuasithin_of_center_quotient_model iso ho (by decide : 3 ≠ 2)
    hz A.subtype A.subtype_injective (by rw [hAc])
end Theory.SpecificGroups.ClassicalUnitary.HigherUnitaryTernary
