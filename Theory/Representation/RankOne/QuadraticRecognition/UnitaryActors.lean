module
public import Theory.Representation.SU3.CubicDegree.InnerActors.RootControl
public import Theory.Representation.SU3.CubicDegree.InnerActors.ThreeRoots
public import Theory.Representation.SU3.BinaryDegree
public import Theory.Representation.BinaryOffender.QuadraticDualOffender

/-!
# Quadratic square bounds for binary special and projective unitary groups

For SU₃(2ⁿ), n≥2, elementary actors lie in Sylow centers of order 2ⁿ,
whose normalizers act irreducibly. Maximize |B|² |C_V(B)| in such a center.
A strict offender gives a nontrivial maximizer, and its normalizer invariance
forces it to be the full center. Three conjugate centers generate the group,
so strictness would force dim V<6n, contradicting the proved minimum degree.
This uses neither irreducibility nor the corrected generation condition.
Zero global fixed space follows from the source residual fixed-space premise.

For PSU₃, lift the elementary actor through the canonical odd scalar kernel.
Both its order and its fixed space are unchanged, and the lifted action is
nontrivial. Faithful quadratic actors are elementary; hence both unitary
families satisfy the DGS size bound and exclude the strict recognition branch.
The Hermitian form, its quadratic defining field, and the scalar quotient are
retained. The small n=1 cases are not asserted here.

Source: DGS85, *Groups and Graphs*, (5.7), (5.9), (5.12), printed pp.108–114.
This alternative proof uses the existing root geometry and exponent-two
maximization of Guralnick–Malle, *Classification of 2F-modules II*, Lemma 2.1.
CriticalUnitaryExclusion applies these estimates on the original DGS quotient.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open Representation.SU3.CubicDegree.InnerActors
namespace Representation.RankOne.QuadraticRecognition
variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
local instance finiteUnitaryActorQuotient (C : Submodule (ZMod 2) V) : Finite (V ⧸ C) :=
  Finite.of_surjective _ C.mkQ_surjective

/-- Root control, three-center generation and the minimum module degree
exclude a strict exponent-two offender without assuming irreducibility. -/
theorem square_bound_of_three_roots
    (ρ : Representation (ZMod 2) G V) (hfix : fixedSpace ρ ⊤ = ⊥)
    {n : ℕ} (hr : RootControl G n) (hg : ThreeRootGeneration G)
    (hdegree : 6*n ≤ Module.finrank (ZMod 2) V)
    (A : Subgroup G) [IsElementaryAbelian 2 A] :
    Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  by_contra! hstrict
  have hA : A ≠ ⊥ := by
    intro h
    rw [h,card_bot,one_pow] at hstrict
    have hp : 0 < Nat.card (V ⧸ fixedSpace ρ ⊥) := Nat.card_pos
    omega
  have hmeasure : Nat.card V < TwoWeight.measure ρ A := by
    have he : Nat.card V = Nat.card (V ⧸ fixedSpace ρ A) * Nat.card (fixedSpace ρ A) := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V ⧸ fixedSpace ρ A),
        Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ A),←pow_add]
      exact congrArg (fun d => Nat.card (ZMod 2)^d) (fixedCodim_add_finrank ρ A).symm
    rw [he]
    exact Nat.mul_lt_mul_of_pos_right hstrict Nat.card_pos
  obtain ⟨P,hAP,hcard,hinv⟩ := hr A ⟨hA,inferInstance⟩
  obtain ⟨B,hBU,hmax,hlargest⟩ := TwoWeight.exists_largest_maximizer ρ (sylowCenter P)
  have hV : Nat.card V < TwoWeight.measure ρ B := hmeasure.trans_le (hmax A hAP)
  have hB : B ≠ ⊥ := by
    intro h
    simp [h,TwoWeight.measure,fixedSpace_bot] at hV
  have hnorm : normalizer (sylowCenter P : Set G) ≤ normalizer (B : Set G) := by
    intro g hg
    have hmap (g : G) (hg : g ∈ normalizer (sylowCenter P : Set G)) :
        B.map (MulAut.conj g).toMonoidHom ≤ B := by
      apply hlargest _ ?_ (TwoWeight.measure_conj ρ B g)
      rintro _ ⟨b,hb,rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg b).mp (hBU hb)
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      exact hmap g hg (Subgroup.mem_map_of_mem _ hb)
    · intro hb
      have hh := hmap g⁻¹ ((normalizer (sylowCenter P : Set G)).inv_mem hg)
        (Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hb)
      simpa only [MulEquiv.toMonoidHom_eq_coe,MonoidHom.coe_coe,MulAut.conj_apply,
        inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,
        inv_mul_cancel,mul_one] using hh
  have hBr := hinv B hBU hB hnorm
  rw [hBr] at hV
  have hcodim : fixedCodim ρ (sylowCenter P) < 2*n := by
    have hd := fixedCodim_add_finrank ρ (sylowCenter P)
    unfold TwoWeight.measure at hV
    rw [hcard,Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V),
      Module.natCard_eq_pow_finrank (K := ZMod 2) (V := fixedSpace ρ (sylowCenter P)),
      Nat.card_zmod,←pow_mul,←pow_add] at hV
    have hp := (Nat.pow_lt_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hV
    omega
  obtain ⟨c,hc⟩ := hg P
  have hd := finrank_le_card_mul_fixedCodim_of_subgroup_conjugates ρ ⊤ (sylowCenter P) hfix c hc.ge
  simp only [Fintype.card_fin] at hd
  omega

open BenderSuzuki.MatrixGroups
/-- The unitary square exclusion for arbitrary binary representations with
zero global fixed space, on the full special unitary group. -/
theorem su3_elementary_square_bound
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup V)
    (hnt : ∃ g, ρ g ≠ 1) (hfix : fixedSpace ρ ⊤ = ⊥)
    (A : Subgroup J.specialSubgroup) [IsElementaryAbelian 2 A] :
    Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) :=
  square_bound_of_three_roots ρ hfix (root_control J hn hcard hconj)
    (ThreeRoots.generation J hn hcard hconj)
    (SU3.BinaryDegree.finrank_ge J hn hcard hconj ρ hnt) A

/-- The corresponding projective estimate retains the canonical scalar
quotient and lifts the given actor with exactly the same order and fixed space. -/
theorem psu3_elementary_square_bound
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    (hnt : ∃ g, ρ g ≠ 1) (hfix : fixedSpace ρ ⊤ = ⊥)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) [IsElementaryAbelian 2 A] :
    Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  let σ := ρ.comp J.specialToProjective
  have hσ : ∃ g, σ g ≠ 1 := by
    obtain ⟨a,ha⟩ := hnt
    obtain ⟨b,hb⟩ := J.specialToProjective_surjective a
    exact ⟨b,by simpa only [σ,MonoidHom.comp_apply,hb] using ha⟩
  have hσfix : fixedSpace σ ⊤ = ⊥ := by
    rw [fixedSpace_comp_map,map_top_of_surjective _ J.specialToProjective_surjective]
    exact hfix
  obtain ⟨B,hB,hBA,hcardB⟩ := exists_elementaryAbelian_map_eq_of_surjective_coprime
    J.specialToProjective J.specialToProjective_surjective
    (Nat.coprime_two_left.mpr J.odd_card_specialToProjective_ker) A
  let : IsElementaryAbelian 2 B := hB
  have hb := su3_elementary_square_bound J hn hcard hconj σ hσ hσfix B
  rw [hcardB,fixedSpace_comp_map,hBA] at hb
  exact hb

/-- DGS (5.12)(a) and the square exclusion for every faithful quadratic
actor in SU₃(2ⁿ), n≥2. The source residual fixed-space assumption implies
the global fixed-space premise used here. -/
theorem su3_quadratic_bounds
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) J.specialSubgroup V) (hf : Function.Injective ρ)
    (hfix : fixedSpace ρ ⊤ = ⊥)
    (A : Subgroup J.specialSubgroup) (hq : IsQuadratic ρ A) :
    Nat.card A ≤ Nat.card (V ⧸ fixedSpace ρ A) ∧
    Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  have hsq : Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
    by_cases hA : A = ⊥
    · rw [hA,card_bot,one_pow]
      exact Nat.card_pos
    let : IsElementaryAbelian 2 A := elementary_of_faithful_quadratic ρ hf A hq
    obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA
    exact su3_elementary_square_bound J hn hcard hconj ρ
      ⟨a,fun he => ha1 (hf (he.trans ρ.map_one.symm))⟩ hfix A
  exact ⟨(Nat.le_self_pow (by decide) _).trans hsq,hsq⟩

/-- The same source bounds for PSU₃, using the actual projective carrier. -/
theorem psu3_quadratic_bounds
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card F = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    (hf : Function.Injective ρ) (hfix : fixedSpace ρ ⊤ = ⊥)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hq : IsQuadratic ρ A) :
    Nat.card A ≤ Nat.card (V ⧸ fixedSpace ρ A) ∧
    Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
  have hsq : Nat.card A ^ 2 ≤ Nat.card (V ⧸ fixedSpace ρ A) := by
    by_cases hA : A = ⊥
    · rw [hA,card_bot,one_pow]
      exact Nat.card_pos
    let : IsElementaryAbelian 2 A := elementary_of_faithful_quadratic ρ hf A hq
    obtain ⟨a,ha,ha1⟩ := A.bot_or_exists_ne_one.resolve_left hA
    exact psu3_elementary_square_bound J hn hcard hconj ρ
      ⟨a,fun he => ha1 (hf (he.trans ρ.map_one.symm))⟩ hfix A
  exact ⟨(Nat.le_self_pow (by decide) _).trans hsq,hsq⟩

end Representation.RankOne.QuadraticRecognition
