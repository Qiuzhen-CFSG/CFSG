module
public import Theory.Representation.RankOne.QuadraticRecognition.LargeActorCentralQuotient
public import Theory.Representation.SU3.CubicDegree.InnerActors.ThreeRoots.Coordinates

/-!
# Large quadratic actors in the unitary fixed-field block

The literal fixed-field SL₂ block embeds in SU₃ and remains injective after
passing to PSU₃. Its upper root is exactly the central unitary root. Thus a
quadratic actor in this root has a block preimage with the same order.
The large-actor theorem makes the central quotient of its fixed-generated
local module a sum of natural SL₂ modules. Its binary dimension is therefore
divisible by twice the degree of the Hermitian fixed field.

For q=8 every actor of order at least four satisfies the required size
inequality. Consequently the local central quotient cannot have dimension
eight. This excludes the exceptional numerical outcome in the torus branch
of DGS85 (5.10)(b), printed pp.111–112; it does not assert the earlier torus
reduction. CriticalLargeActors applies the result to the literal critical
quotient Z/(Z∩Z(L)), with the original actor image retained.
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

private theorem embedded_large_fixedGenerated_central_degree_dvd
    {K D V : Type*} [Field K] [Finite K] [CharP K 2] [Group D]
    [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (j : SL(2,K) →* D)
    (hj : Function.Injective j) {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K=2^n)
    (S : Sylow 2 SL(2,K)) (A : Subgroup D)
    (hAS : A ≤ (S : Subgroup _).map j) (hAc : 4 ≤ Nat.card A)
    (hq : IsQuadratic ρ A) (hlarge : 2^n < Nat.card A^2) :
    let W := fixedGeneratedSubrepresentation (ρ.comp j) (A.comap j)
    2*n ∣ Module.finrank (ZMod 2) (W.toSubmodule ⧸ fixedSpace W.toRepresentation ⊤) := by
  let B := A.comap j
  have hAr : A ≤ j.range := hAS.trans (map_le_range _ _)
  have hBA : B.map j=A := map_comap_eq_self hAr
  have hBS : B ≤ S := (comap_mono hAS).trans (comap_map_eq_self_of_injective hj _).le
  have hBc : Nat.card B=Nat.card A := by rw [←hBA,card_map_of_injective hj]
  have hqB : IsQuadratic (ρ.comp j) B := fun a ha b hb v => hq (j a) ha (j b) hb v
  have hSc : Nat.card S=2^n :=
    (Nat.card_congr (SpecialLinearGroup.sylowEquivAdditive K 2 S).symm.toEquiv).trans hK
  exact sl2_large_fixedGenerated_central_degree_dvd (ρ.comp j) hn hK S B hBS
    (hBc.symm ▸ hAc) hqB (by rwa [hSc,hBc])

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- The actual SU₃ block preimage preserves actor order and gives divisibility
of the fixed-generated local central quotient. -/
theorem su3_large_root_central_degree_dvd
    [Finite F] {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup V) (A : Subgroup J.specialSubgroup)
    (hA : A ≤ central J hJ) (hAc : 4 ≤ Nat.card A) (hq : IsQuadratic ρ A)
    (hlarge : 2^n < Nat.card A^2) :
    let W := fixedGeneratedSubrepresentation (ρ.comp (block J hJ)) (A.comap (block J hJ))
    2*n ∣ Module.finrank (ZMod 2) (W.toSubmodule ⧸ fixedSpace W.toRepresentation ⊤) := by
  have hF : Nat.card (fixedField J)=2^n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  exact embedded_large_fixedGenerated_central_degree_dvd ρ (block J hJ)
    (block_injective J hJ) hn hF (SpecialLinearGroup.upperUnipotentSylow (fixedField J) 2)
    A (by simpa only [SpecialLinearGroup.coe_upperUnipotentSylow,block_upper_image] using hA)
    hAc hq hlarge

/-- The same result in PSU₃ retains the canonical scalar quotient and the
literal preimage in the fixed-field SL₂ block. -/
theorem psu3_large_root_central_degree_dvd
    [Finite F] {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : A ≤ centralImage J hJ) (hAc : 4 ≤ Nat.card A) (hq : IsQuadratic ρ A)
    (hlarge : 2^n < Nat.card A^2) :
    let j := J.specialToProjective.comp (block J hJ)
    let W := fixedGeneratedSubrepresentation (ρ.comp j) (A.comap j)
    2*n ∣ Module.finrank (ZMod 2) (W.toSubmodule ⧸ fixedSpace W.toRepresentation ⊤) := by
  have hF : Nat.card (fixedField J)=2^n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hcard hconj
  exact embedded_large_fixedGenerated_central_degree_dvd ρ
    (J.specialToProjective.comp (block J hJ)) (projective_block_injective J hJ) hn hF
    (SpecialLinearGroup.upperUnipotentSylow (fixedField J) 2) A
    (by simpa only [SpecialLinearGroup.coe_upperUnipotentSylow,projective_block_upper_image] using hA)
    hAc hq hlarge

/-- The exceptional q=8 block cannot have central quotient dimension eight. -/
theorem su3_eight_root_central_degree_ne_eight
    [Finite F] (hcard : Nat.card F=64) (hconj : ∀ x, J.conj x=x^8)
    (ρ : Representation (ZMod 2) J.specialSubgroup V) (A : Subgroup J.specialSubgroup)
    (hA : A ≤ central J hJ) (hAc : 4 ≤ Nat.card A) (hq : IsQuadratic ρ A) :
    let W := fixedGeneratedSubrepresentation (ρ.comp (block J hJ)) (A.comap (block J hJ))
    Module.finrank (ZMod 2) (W.toSubmodule ⧸ fixedSpace W.toRepresentation ⊤) ≠ 8 := by
  have hd := su3_large_root_central_degree_dvd J hJ (n := 3) (by decide) hcard hconj
    ρ A hA hAc hq (by norm_num; nlinarith)
  dsimp only at hd ⊢
  intro he
  rw [he] at hd
  norm_num at hd

/-- Projectivization does not change the q=8 obstruction. -/
theorem psu3_eight_root_central_degree_ne_eight
    [Finite F] (hcard : Nat.card F=64) (hconj : ∀ x, J.conj x=x^8)
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : A ≤ centralImage J hJ) (hAc : 4 ≤ Nat.card A) (hq : IsQuadratic ρ A) :
    let j := J.specialToProjective.comp (block J hJ)
    let W := fixedGeneratedSubrepresentation (ρ.comp j) (A.comap j)
    Module.finrank (ZMod 2) (W.toSubmodule ⧸ fixedSpace W.toRepresentation ⊤) ≠ 8 := by
  have hd := psu3_large_root_central_degree_dvd J hJ (n := 3) (by decide) hcard hconj
    ρ A hA hAc hq (by norm_num; nlinarith)
  dsimp only at hd ⊢
  intro he
  rw [he] at hd
  norm_num at hd
end Representation.RankOne.QuadraticRecognition
