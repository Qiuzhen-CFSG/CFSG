module
public import Theory.SpecificGroups.SU3.BorelCoprimeFieldAction
public import Theory.SpecificGroups.SU3.EvenSemilinear.CyclicOuter
public import Theory.FieldTheory.CubicDisplacement
public import BenderSuzuki.External.Huppert.II.theorem_10_13

/-!
# Two-power unitary automorphisms with trivial Borel quotient action

For PSU₃(2^n), n at least two, a Sylow-preserving automorphism acting
trivially on its normalizer modulo the Sylow is inner if it has two-power
order. A triangular semilinear representative acts on the full torus by
its field coefficient. Trivial projective torus displacement fixes all
field cubes, forcing that coefficient to be identity. The remaining outer
diagonal image has exponent three and hence vanishes.

Sylow conjugacy and a genuine Hermitian basis change give the result for
any original Sylow and Hermitian form. The small degree one is not included.
This is the projective-unitary model calculation used in DGS, Groups and
Graphs (1985), 6.1, pp.118--119; semilinear coordinates follow GLS3 2.5.12.
-/

public noncomputable section
open Subgroup Matrix BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.NormalizerDisplacements
open BorelTorus BorelTorus.SemilinearActors
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

private theorem standard_root_inner
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    {r : ℕ} (ha : a^(2^r) = 1)
    (hroot : (projectiveRoot J hJ).map a.toMonoidHom = projectiveRoot J hJ)
    (hd : ∀ x ∈ normalizer (projectiveRoot J hJ : Set _),
      x⁻¹ * a x ∈ projectiveRoot J hJ) :
    a ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  have hq : 2 < 2^n := (by decide : 2 < 2^2).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn)
  let : IsSimpleGroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    huppert_II_10_13 J (2^n) hq hcard hfixed
  obtain ⟨σ,u,hu⟩ := EvenSemilinear.semilinear_coverage J hJ hn hcard hconj a
  obtain ⟨h10,h20,h21⟩ := projective_semilinear_upper J hJ hcard hfixed a σ u hu hroot
  have htorus (k : Eˣ) : hermitianTorusPSU J hJ (Units.map σ.toMonoidHom k) =
      hermitianTorusPSU J hJ k := by
    apply (projective_semilinear_torus_displacement_iff J hJ a σ u h10 h20 h21 hu k).mp
    have ht := BorelCoprimeFieldAction.torus_normalizes_root J hJ ⟨k,rfl⟩
    have hh := (mem_normalizer_iff.mp ht _).mp (hd _ ht)
    simpa only [mul_inv_cancel_left] using hh
  have hs : σ = 1 := by
    apply (FiniteField.eq_one_or_card_le_four_of_unit_displacement_cube σ ?_).resolve_right
    · intro hsmall
      rw [hcard] at hsmall
      have h4 : 4 ≤ 2^n := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hn
      nlinarith
    · intro k
      apply ((projective_eq_one_iff J hJ _).mp ?_).2
      rw [map_mul,map_inv,htorus,mul_inv_cancel]
  have hf : J.HasUnitarySemilinearForm a 1 := hs ▸ ⟨u,hu⟩
  obtain ⟨v,hv⟩ := (HasUnitarySemilinearForm.one_iff J).mp hf
  have hcube : a^3 ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
    obtain ⟨b,hb⟩ := J.unitaryConj_cube_is_inner v
    rw [hv,hb]
    exact ⟨b,rfl⟩
  let q := QuotientGroup.mk' (MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J))
  have hq3 : (q a)^3 = 1 := by
    rw [←map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hcube
  have hq2 : (q a)^(2^r) = 1 := by rw [←map_pow,ha,map_one]
  exact (QuotientGroup.eq_one_iff a).mp
    ((pow_eq_one_iff_of_coprime ((by decide : Nat.Coprime 2 3).pow_left r)).mp ⟨hq2,hq3⟩)

/-- A two-power automorphism of the standard binary PSU₃ model acting trivially
on a Sylow normalizer modulo that Sylow is inner, for every degree at least two. -/
theorem standard_inner
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    {r : ℕ} (ha : a^(2^r) = 1)
    (hS : (S : Subgroup _).map a.toMonoidHom = S)
    (hd : ∀ x ∈ normalizer (S : Set _), x⁻¹ * a x ∈ S) :
    a ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  let T := EvenTwoRank.rootSylow J hJ (by omega : 0 < n) hcard hfixed
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S T
  let e := MulAut.conj g
  have hm : (S : Subgroup _).map e.toMonoidHom = T := congrArg Sylow.toSubgroup hg
  let b := MulAut.congr e a
  have he : b.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact congrArg e (congrArg a (e.symm_apply_apply x))
  have hb : b ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
    apply standard_root_inner J hJ hn hcard hconj b
      (by rw [←map_pow,ha,map_one])
    · change (T : Subgroup _).map b.toMonoidHom = T
      rw [←hm,Subgroup.map_map,he,←Subgroup.map_map,hS]
    · intro x hx
      change x ∈ normalizer (↑(T : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set (ProjectiveSpecialUnitaryMatrixGroup J)) at hx
      rw [←hm,←map_equiv_normalizer_eq _ e] at hx
      obtain ⟨y,hy,rfl⟩ := hx
      change (e y)⁻¹ * e (a (e.symm (e y))) ∈ (T : Subgroup _)
      rw [e.symm_apply_apply,←map_inv,←map_mul,←hm]
      exact mem_map_of_mem _ (hd y hy)
  obtain ⟨z,hz⟩ := hb
  obtain ⟨w,hw⟩ := (MulAut.congr_inner_iff e a).mp ⟨z,hz.symm⟩
  exact ⟨w,hw.symm⟩

open OddPrimeSylow.NormalizedOuter.FormTransport

/-- The same detector for an arbitrary original Hermitian form and Sylow subgroup. -/
theorem inner
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (S : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J))
    (a : MulAut (ProjectiveSpecialUnitaryMatrixGroup J))
    {r : ℕ} (ha : a^(2^r) = 1)
    (hS : (S : Subgroup _).map a.toMonoidHom = S)
    (hd : ∀ x ∈ normalizer (S : Set _), x⁻¹ * a x ∈ S) :
    a ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Fintype E := Fintype.ofFinite E
  let : CharP E 2 := charP_of_card_eq_prime_pow (p := 2) (f := n*2)
    (by simpa only [pow_mul,Nat.card_eq_fintype_card] using hcard)
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  obtain ⟨e⟩ := exists_projectiveEquiv J (2^n) hcard hfixed
  let T := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let b := MulAut.congr e a
  have he : b.toMonoidHom.comp e.toMonoidHom = e.toMonoidHom.comp a.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    exact congrArg e (congrArg a (e.symm_apply_apply x))
  have hb : b ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup (standardForm J)) := by
    apply standard_inner (standardForm J) rfl hn hcard hconj T b
      (by rw [←map_pow,ha,map_one])
    · change ((S : Subgroup _).map e.toMonoidHom).map b.toMonoidHom = _
      rw [Subgroup.map_map,he,←Subgroup.map_map,hS]
      rfl
    · intro x hx
      change x ∈ normalizer ((S : Subgroup _).map e.toMonoidHom : Set _) at hx
      rw [←map_equiv_normalizer_eq _ e] at hx
      obtain ⟨y,hy,rfl⟩ := hx
      change (e y)⁻¹ * e (a (e.symm (e y))) ∈ (S : Subgroup _).map e.toMonoidHom
      rw [e.symm_apply_apply,←map_inv,←map_mul]
      exact mem_map_of_mem _ (hd y hy)
  obtain ⟨z,hz⟩ := hb
  obtain ⟨w,hw⟩ := (MulAut.congr_inner_iff e a).mp ⟨z,hz.symm⟩
  exact ⟨w,hw.symm⟩
end BenderSuzuki.MatrixGroups.HermitianForm.NormalizerDisplacements
