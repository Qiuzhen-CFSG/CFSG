module
public import Theory.SpecificGroups.SU3.NormalizerDisplacements
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import Theory.SpecificGroups.SU3.EvenSemilinear.SpecialCoverage
public import Theory.GroupTheory.PerfectCentralCoverAutomorphisms
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Normalizer displacement rigidity in the full binary special unitary group

For every n at least two, the actual map SU₃(2^n) → PSU₃(2^n) is a perfect
central covering whose kernel is the whole scalar center. Automorphisms
descend faithfully. Sylow normalizers and their displacement identities
map onto the projective ones. The projective rigidity theorem makes the
descended two-power actor inner, and perfectness makes its original lift
inner too. The cubic center is kept throughout, including odd n.

This supplies the full special-unitary action in DGS, Groups and Graphs
(1985), 6.1, pp.118--119. Degree one remains separate.
-/

public noncomputable section
open Subgroup BenderSuzuki.External
namespace BenderSuzuki.MatrixGroups.HermitianForm.NormalizerDisplacements
variable {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)

/-- Normalizer-displacement rigidity lifts through the full special-unitary
cover. The cubic scalar center is retained. -/
theorem special_inner
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (S : Sylow 2 J.specialSubgroup) (a : MulAut J.specialSubgroup)
    {r : ℕ} (ha : a^(2^r) = 1)
    (hS : (S : Subgroup _).map a.toMonoidHom = S)
    (hd : ∀ x ∈ normalizer (S : Set _), x⁻¹ * a x ∈ S) :
    a ∈ MulAut.innerSubgroup J.specialSubgroup := by
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n
    (by omega) hcard hconj
  have hq : 2 < 2^n := (by decide : 2 < 2^2).trans_le
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) hn)
  let := J.special_isPerfect_of_fixed_card hq hcard hfixed
  let f : PerfectCentralCovering.Cover J.specialSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
    { toMonoidHom := J.specialToProjective
      surjective := J.specialToProjective_surjective
      isPerfect := inferInstance
      ker_le_center := J.specialToProjective_ker_le_center }
  have hk : f.toMonoidHom.ker = center J.specialSubgroup :=
    J.specialToProjective_ker_eq_center (EvenProjectiveComparison.center_eq_bot J (by omega) hcard hconj)
  let b := f.autMap hk a
  let T := S.mapSurjective (f := f.toMonoidHom) f.surjective
  have he : b.toMonoidHom.comp f.toMonoidHom = f.toMonoidHom.comp a.toMonoidHom := by
    apply MonoidHom.ext
    exact f.autMap_apply hk a
  have hb : b ∈ MulAut.innerSubgroup (ProjectiveSpecialUnitaryMatrixGroup J) := by
    apply inner J hn hcard hconj T b (by rw [←map_pow,ha,map_one])
    · change ((S : Subgroup _).map f.toMonoidHom).map b.toMonoidHom = _
      rw [map_map,he,←map_map,hS]
      rfl
    · intro x hx
      change x ∈ normalizer ((S : Subgroup _).map f.toMonoidHom : Set _) at hx
      rw [←S.normalizer_map_surjective f.toMonoidHom f.surjective] at hx
      obtain ⟨y,hy,rfl⟩ := hx
      change (f.toMonoidHom y)⁻¹ * b (f.toMonoidHom y) ∈ (S : Subgroup _).map f.toMonoidHom
      rw [f.autMap_apply hk a,←map_inv,←map_mul]
      exact mem_map_of_mem _ (hd y hy)
  obtain ⟨z,hz⟩ := hb
  obtain ⟨w,hw⟩ := f.surjective z
  refine ⟨w, (f.autMap_injective hk) ?_⟩
  apply MulEquiv.ext
  intro y
  obtain ⟨x,rfl⟩ := f.surjective y
  rw [f.autMap_apply hk]
  change f.toMonoidHom (w * x * w⁻¹) = b (f.toMonoidHom x)
  rw [map_mul,map_mul,map_inv,hw,←hz,MulAut.conj_apply]
end BenderSuzuki.MatrixGroups.HermitianForm.NormalizerDisplacements
