module

public import Theory.Representation.RankOne.QuadraticRecognition.FixedGeneratedReduction
public import Theory.Representation.SU3.CubicDegree.InnerActors.ThreeRoots.Coordinates
public import Theory.Representation.BinaryOffender.EquivariantOffender

/-!
# The literal fixed-field block inside SU₃ and PSU₃

The Hermitian fixed-field block is an actual copy of binary SL₂.  Its upper
root is exactly the central root of SU₃.  Projectivization remains injective
on the block in characteristic two, so the root actor and every element of it
have genuine SL₂ preimages with unchanged order and fixed spaces.  Applying
the fixed-generated reduction to those preimages retains the actual vector
representation and actor.

This supplies the local rank-one step at the beginning of DGS85 (5.10)(b),
printed pp.110–112.  It does not assert the later torus estimate: that
argument must compare the complementary unitary tori and handle its q=8
exception at the source layer.
-/

public noncomputable section
open Matrix Subgroup Representation.BinaryOffender
open BenderSuzuki.MatrixGroups BenderSuzuki.External
open HermitianForm.BorelTorus.EvenCenterAction
open Representation.SU3.CubicDegree.InnerActors.ThreeRoots
open scoped MatrixGroups
namespace Representation.RankOne.QuadraticRecognition

variable {F : Type*} [Field F] [CharP F 2]
variable (J : HermitianForm 3 F)
  (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])

private theorem block_injective : Function.Injective (block J hJ) :=
  (J.specialGraphAut hJ).fixedSubgroup.subtype_injective.comp
    (J.specialGraphFixedEquivSL2 hJ).symm.injective

private theorem block_upper_image :
    (SpecialLinearGroup.upperUnipotent (fixedField J)).map (block J hJ) =
      central J hJ := by
  have he (c : fixedField J) :
      block J hJ (SpecialLinearGroup.transvection (i := 0) (j := 1) zero_ne_one c) =
        hermitianUnipotentSU J hJ
          (centralCoord J (Multiplicative.ofAdd c)) := by
    apply Subtype.ext
    apply Units.ext
    rw [block_val]
    change _ = (!![1, 0, (c : F); 0, 1, -J.conj 0; 0, 0, 1] :
      Matrix (Fin 3) (Fin 3) F)
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [SpecialLinearGroup.transvection_coe]
  apply le_antisymm
  · rintro _ ⟨a, ha, rfl⟩
    obtain ⟨c, rfl⟩ := (SpecialLinearGroup.mem_upperUnipotent _ _).mp ha
    rw [he]
    exact ⟨Multiplicative.ofAdd c, rfl⟩
  · rintro _ ⟨c, rfl⟩
    refine ⟨SpecialLinearGroup.transvection zero_ne_one c.toAdd, ?_, ?_⟩
    · exact (SpecialLinearGroup.mem_upperUnipotent _ _).mpr ⟨c.toAdd, rfl⟩
    · exact he c.toAdd

private theorem projective_block_injective :
    Function.Injective (J.specialToProjective.comp (block J hJ)) := by
  intro x y h
  have hp : ProjGenLinGroup.mk (block J hJ x).val =
      ProjGenLinGroup.mk (block J hJ y).val := by
    simpa only [MonoidHom.comp_apply, J.specialToProjective_apply_val] using
      congrArg Subtype.val h
  obtain ⟨u, hu⟩ := ProjGenLinGroup.mk_eq_mk_iff.mp hp
  have huval : (u : F) = 1 := by
    have hh := congrArg (fun g : GL (Fin 3) F => g.val 1 1) hu
    rw [GeneralLinearGroup.coe_mul, block_val, block_val] at hh
    simpa [GeneralLinearGroup.coe_scalar, Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.scalar] using hh
  have huone : u = 1 := Units.ext huval
  rw [huone, map_one, mul_one] at hu
  exact block_injective J hJ (Subtype.ext hu)

private theorem projective_block_upper_image :
    (SpecialLinearGroup.upperUnipotent (fixedField J)).map
        (J.specialToProjective.comp (block J hJ)) = centralImage J hJ := by
  rw [← Subgroup.map_map, block_upper_image]
  change (((hermitianUnipotentSU J hJ).comp (centralCoord J)).range).map
      J.specialToProjective = _
  rw [MonoidHom.map_range]
  have he : J.specialToProjective.comp
        ((hermitianUnipotentSU J hJ).comp (centralCoord J)) = centralMap J hJ := by
    apply MonoidHom.ext
    intro c
    apply Subtype.ext
    simp only [MonoidHom.comp_apply, J.specialToProjective_apply_val]
    change ProjGenLinGroup.mk _ =
      (hermitianUnipotentPSU J hJ (centralCoord J c)).val
    exact (hermitianUnipotentPSU_val J hJ (centralCoord J c)).symm
  rw [he]
  rfl

private theorem embedded_fixedGenerated_reduction
    {K D V : Type*} [Field K] [Finite K] [CharP K 2] [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (j : SL(2, K) →* D)
    (hj : Function.Injective j) {n : ℕ} (hn : 0 < n) (hK : Nat.card K = 2 ^ n)
    (S : Sylow 2 SL(2, K)) (A : Subgroup D)
    (hAS : A ≤ (S : Subgroup _).map j) (hAc : 4 ≤ Nat.card A)
    (hq : IsQuadratic ρ A) (t : D) (htA : t ∈ A) (ht1 : t ≠ 1) :
    let W := fixedGeneratedSubrepresentation (ρ.comp j) (A.comap j)
    W.toSubmodule ⊓ fixedSpace ρ (zpowers t) = fixedSpace ρ A ∧
      Module.finrank (ZMod 2)
          (W.toSubmodule ⧸ fixedSpace W.toRepresentation ⊤) ≤
        2 * fixedCodim ρ (zpowers t) := by
  let B := A.comap j
  have hAr : A ≤ j.range := hAS.trans (map_le_range _ _)
  have hBA : B.map j = A := map_comap_eq_self hAr
  have hBS : B ≤ S := by
    exact (comap_mono hAS).trans (comap_map_eq_self_of_injective hj _).le
  have hBc : 4 ≤ Nat.card B := by
    rw [← hBA, card_map_of_injective hj] at hAc
    exact hAc
  have hqB : IsQuadratic (ρ.comp j) B := by
    intro a ha b hb v
    exact hq (j a) ha (j b) hb v
  obtain ⟨t₀, htS, ht₀⟩ := hAS htA
  have htB : t₀ ∈ B := by
    change j t₀ ∈ A
    rwa [ht₀]
  have ht₀1 : t₀ ≠ 1 := fun he => ht1 (by rw [← ht₀, he, map_one])
  have he := sl2_fixedGenerated_inter_fixedSpace_eq (ρ.comp j) hn hK S B hBS hBc hqB
    t₀ htB ht₀1
  have hd := sl2_fixedGenerated_central_degree_le (ρ.comp j) hn hK S B hBS hBc hqB
    t₀ htB ht₀1
  have hfA : fixedSpace (ρ.comp j) B = fixedSpace ρ A := by
    rw [fixedSpace_comp_map, hBA]
  have hft : fixedSpace (ρ.comp j) (zpowers t₀) = fixedSpace ρ (zpowers t) := by
    rw [fixedSpace_comp_map, MonoidHom.map_zpowers, ht₀]
  rw [hfA, hft] at he
  have hct : fixedCodim (ρ.comp j) (zpowers t₀) = fixedCodim ρ (zpowers t) := by
    unfold fixedCodim
    rw [hft]
  rw [hct] at hd
  exact ⟨he, hd⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- The local fixed-generated reduction for a central-root actor in SU₃.
The source's Sylow-centre inclusion is an explicit input; it is supplied by
DGS85 (5.9)(b) in the original critical application. -/
public theorem su3_root_fixedGenerated_reduction
    [Finite F] {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (ρ : Representation (ZMod 2) J.specialSubgroup V) (A : Subgroup J.specialSubgroup)
    (hA : A ≤ central J hJ) (hAc : 4 ≤ Nat.card A) (hq : IsQuadratic ρ A)
    (t : J.specialSubgroup) (htA : t ∈ A) (ht1 : t ≠ 1) :
    let W := fixedGeneratedSubrepresentation (ρ.comp (block J hJ)) (A.comap (block J hJ))
    W.toSubmodule ⊓ fixedSpace ρ (zpowers t) = fixedSpace ρ A ∧
      Module.finrank (ZMod 2) (W.toSubmodule ⧸ fixedSpace W.toRepresentation ⊤) ≤
        2 * fixedCodim ρ (zpowers t) := by
  have hf : Nat.card (fixedField J) = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  exact embedded_fixedGenerated_reduction ρ (block J hJ) (block_injective J hJ) hn hf
    (SpecialLinearGroup.upperUnipotentSylow (fixedField J) 2) A
    (by simpa only [SpecialLinearGroup.coe_upperUnipotentSylow, block_upper_image] using hA)
    hAc hq t htA ht1

/-- The projective version retains the actual PSU₃ actor and fixes its
literal preimage in the same fixed-field SL₂ block. -/
public theorem psu3_root_fixedGenerated_reduction
    [Finite F] {n : ℕ} (hn : 0 < n) (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : A ≤ centralImage J hJ) (hAc : 4 ≤ Nat.card A) (hq : IsQuadratic ρ A)
    (t : ProjectiveSpecialUnitaryMatrixGroup J) (htA : t ∈ A) (ht1 : t ≠ 1) :
    let j := J.specialToProjective.comp (block J hJ)
    let W := fixedGeneratedSubrepresentation (ρ.comp j) (A.comap j)
    W.toSubmodule ⊓ fixedSpace ρ (zpowers t) = fixedSpace ρ A ∧
      Module.finrank (ZMod 2) (W.toSubmodule ⧸ fixedSpace W.toRepresentation ⊤) ≤
        2 * fixedCodim ρ (zpowers t) := by
  have hf : Nat.card (fixedField J) = 2 ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn hcard hconj
  exact embedded_fixedGenerated_reduction ρ
    (J.specialToProjective.comp (block J hJ)) (projective_block_injective J hJ) hn hf
    (SpecialLinearGroup.upperUnipotentSylow (fixedField J) 2) A
    (by simpa only [SpecialLinearGroup.coe_upperUnipotentSylow,
      projective_block_upper_image] using hA)
    hAc hq t htA ht1

end Representation.RankOne.QuadraticRecognition
