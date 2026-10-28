module
public import BenderSuzuki.External.Huppert.II.theorem_10_12
public import Theory.GroupTheory.QuaternionCentralProductResidualRecognition.Residual

/-!
# Root groups in involution-centralizer two-residuals of PSU₃

For the antidiagonal Hermitian form, an involution in the root group has
zero first coordinate. The norm-one torus centralizes it. If the fixed field
has even order q > 2, that torus has odd order and contains an element whose
cube is nonidentity. Its commutators with root elements therefore attain
every first coordinate and belong to the centralizer's two-residual.
The root group's center equals its derived subgroup, so these commutators
generate the entire root group modulo the residual.

All groups and actions below are the actual projective matrix homomorphisms.
The matrix field has order q², and the fixed field has order q.
Source: Huppert II.10.12; Aschbacher–Smith, *The Classification of Quasithin
Groups*, Proposition 16.5.1, unitary paragraph, printed p.1194.
-/

public section
open BenderSuzuki.MatrixGroups BenderSuzuki.External Subgroup
open scoped Matrix commutatorElement
namespace SU3.EvenInvolutionResidual
variable {F : Type*} [Field F] [Finite F]

/-- Huppert's root coordinates identify the actual projective matrix range. -/
theorem root_structure (J : HermitianForm 3 F) (q : ℕ)
    (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q)
    (hstd : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Function.Injective (hermitianUnipotentPSU J hstd) ∧
      Nat.card (hermitianUnipotentPSU J hstd).range = q ^ 3 ∧
      center (hermitianUnipotentCoord J) ≤ commutator (hermitianUnipotentCoord J) := by
  obtain ⟨_, _, _, _, _, _,
    ⟨R, _, _, _, _, _, _, _, hRcard, hcomm, _, _, _, ⟨e, he⟩, _⟩, _⟩ :=
    huppert_II_10_12 J q hcard hfixed hstd
  let root := hermitianUnipotentPSU J hstd
  have heq (z : hermitianUnipotentCoord J) : (e z : ProjectiveSpecialUnitaryMatrixGroup J) = root z := by
    obtain ⟨M, hM, hp⟩ := he z
    apply Subtype.ext
    rw [hp, hermitianUnipotentPSU_val]
    congr 1
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    exact congrFun (congrFun hM i) j
  let em : hermitianUnipotentCoord J ≃* R :=
    { e with
      map_mul' := by
        intro z w
        apply Subtype.ext
        change (e (z * w) : ProjectiveSpecialUnitaryMatrixGroup J) =
          (e z : ProjectiveSpecialUnitaryMatrixGroup J) * (e w : ProjectiveSpecialUnitaryMatrixGroup J)
        rw [heq, heq, heq, map_mul] }
  have hinj : Function.Injective root := by
    intro z w h
    apply em.injective
    exact Subtype.ext ((heq z).trans (h.trans (heq w).symm))
  have hR : R = root.range := by
    ext x
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := e.surjective ⟨x, hx⟩
      exact ⟨z, (heq z).symm.trans (congrArg Subtype.val hz)⟩
    · rintro ⟨z, rfl⟩
      rw [← heq]
      exact (e z).property
  refine ⟨hinj, hR ▸ hRcard, ?_⟩
  have hm : (commutator (hermitianUnipotentCoord J)).map em.toMonoidHom = commutator R := by
    simp only [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map]
    rw [MonoidHom.range_eq_top.mpr em.surjective]
  intro z hz
  have hzR : em z ∈ center R := by
    rw [mem_center_iff]
    intro x
    obtain ⟨w, rfl⟩ := em.surjective x
    simpa only [map_mul] using congrArg em (mem_center_iff.mp hz w)
  rw [← hcomm, ← hm] at hzR
  obtain ⟨w, hw, hew⟩ := hzR
  exact em.injective hew ▸ hw

omit [Finite F] in
private theorem central_of_fst_zero (J : HermitianForm 3 F)
    (z : hermitianUnipotentCoord J) (hz : z.1.1 = 0) :
    z ∈ center (hermitianUnipotentCoord J) := by
  rw [mem_center_iff]
  intro w
  apply Subtype.ext
  apply Prod.ext
  · change w.1.1 + z.1.1 = z.1.1 + w.1.1
    exact add_comm _ _
  · change w.1.2 + z.1.2 - w.1.1 * J.conj z.1.1 =
      z.1.2 + w.1.2 - z.1.1 * J.conj w.1.1
    simp [hz, add_comm]

/-- The full root group belongs to the two-residual of each root involution's
centralizer. The torus used here is an actual odd-order matrix torus. -/
theorem root_le_twoResidual [CharP F 2] (J : HermitianForm 3 F) (q : ℕ)
    (hcard : Nat.card F = q ^ 2)
    (hfixed : Nat.card {x : F // J.conj x = x} = q)
    (hstd : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (hq : 2 < q) (hodd : Odd (q + 1))
    (v : hermitianUnipotentCoord J)
    (hv : (hermitianUnipotentPSU J hstd v) ^ 2 = 1) :
    (hermitianUnipotentPSU J hstd).range ≤
      (pResidual 2 (centralizer ({hermitianUnipotentPSU J hstd v} :
        Set (ProjectiveSpecialUnitaryMatrixGroup J)))).map
        (centralizer ({hermitianUnipotentPSU J hstd v} :
          Set (ProjectiveSpecialUnitaryMatrixGroup J))).subtype := by
  let root := hermitianUnipotentPSU J hstd
  let C := centralizer ({root v} : Set (ProjectiveSpecialUnitaryMatrixGroup J))
  obtain ⟨hinj, _, hcenter⟩ := root_structure J q hcard hfixed hstd
  have hvcoord : v ^ 2 = 1 := hinj (by simpa only [map_pow, map_one] using hv)
  have hvfst : v.1.1 = 0 := by
    have hh := congrArg (fun z : hermitianUnipotentCoord J => z.1.2) hvcoord
    rw [pow_two] at hh
    change v.1.2 + v.1.2 - v.1.1 * J.conj v.1.1 = 0 at hh
    have ht : (2 : F) = 0 := by simpa using CharP.cast_eq_zero F 2
    have ha : v.1.2 + v.1.2 = 0 := by linear_combination v.1.2 * ht
    rw [ha, zero_sub, neg_eq_zero, mul_eq_zero] at hh
    exact hh.elim id (fun h => (map_eq_zero_iff J.conj J.conj.injective).mp h)
  have hrootC (z : hermitianUnipotentCoord J) : root z ∈ C := by
    apply mem_centralizer_singleton_iff.mpr
    simpa only [map_mul] using congrArg root
      (mem_center_iff.mp (central_of_fst_zero J v hvfst) z)
  let f : hermitianUnipotentCoord J →* C := root.codRestrict C hrootC
  let N := (pResidual 2 C).comap f
  obtain ⟨k, hkpow, hk3, _, hkconj⟩ :=
    exists_hermitian_norm_one_torus_cube_ne_one J q hcard hfixed hstd hq
  let t : C := ⟨hermitianTorusPSU J hstd k,
    mem_centralizer_singleton_iff.mpr
      (hermitianTorusPSU_commute_unipotent_of_sq_eq_one J hstd k hkconj v hv)⟩
  have ht : t ∈ pResidual 2 C := by
    apply mem_pResidual_of_orderOf_coprime
    apply (Nat.coprime_two_left.mpr hodd).of_dvd_right
    apply orderOf_dvd_of_pow_eq_one (n := q + 1)
    apply Subtype.ext
    change (hermitianTorusPSU J hstd k) ^ (q + 1) = 1
    rw [← map_pow]
    have hk : k ^ (q + 1) = 1 := Units.ext (by simpa using hkpow)
    rw [hk, map_one]
  let scale : F := (k : F) ^ 3
  have hscale : 1 - scale ≠ 0 := sub_ne_zero.mpr hk3.symm
  have hcover (z : hermitianUnipotentCoord J) :
      ∃ c ∈ N, ∃ d ∈ center (hermitianUnipotentCoord J), z = d * c := by
    let a := z.1.1 / (1 - scale)
    have ha : J.conj (-(a * J.conj a)) = -(a * J.conj a) := by
      rw [map_neg, map_mul, J.conj_involutive]
      ring
    obtain ⟨b, hb⟩ := huppert_II_10_4_trace_surjective J q hcard hfixed _ ha
    let w : hermitianUnipotentCoord J := ⟨(a, b), by linear_combination hb⟩
    let c := w * hermitianTorusAction J k w⁻¹
    have hc : f c = ⁅f w, t⁆ := by
      apply Subtype.ext
      change root c = ⁅root w, hermitianTorusPSU J hstd k⁆
      dsimp only [c]
      rw [map_mul, commutatorElement_def]
      have he := hermitianTorusPSU_mul_unipotent J hstd k w⁻¹
      change hermitianTorusPSU J hstd k * root w⁻¹ =
        root (hermitianTorusAction J k w⁻¹) * hermitianTorusPSU J hstd k at he
      rw [map_inv] at he
      rw [← mul_inv_eq_iff_eq_mul] at he
      rw [← he]
      group
    have hcN : c ∈ N := by
      change f c ∈ pResidual 2 C
      rw [hc]
      exact (pResidual 2 C).mul_mem
        ((inferInstance : (pResidual 2 C).Normal).conj_mem t ht (f w))
        ((pResidual 2 C).inv_mem ht)
    have hcfst : c.1.1 = z.1.1 := by
      change a + (-a) * (k : F) * (J.conj (k : F))⁻¹ ^ 2 = z.1.1
      rw [hkconj, inv_inv]
      dsimp [a, scale]
      field_simp [hscale]
      ring
    let d := z * c⁻¹
    have hd : d.1.1 = 0 := by
      change z.1.1 + -c.1.1 = 0
      rw [hcfst]
      ring
    exact ⟨c, hcN, d, central_of_fst_zero J d hd, by dsimp [d]; group⟩
  have hgen : N ⊔ center (hermitianUnipotentCoord J) = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨c, hc, d, hd, rfl⟩ := hcover z
    exact (N ⊔ center (hermitianUnipotentCoord J)).mul_mem
      ((show center (hermitianUnipotentCoord J) ≤ N ⊔ center (hermitianUnipotentCoord J) from le_sup_right) hd)
      ((show N ≤ N ⊔ center (hermitianUnipotentCoord J) from le_sup_left) hc)
  have hcN : commutator (hermitianUnipotentCoord J) ≤ N :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hgen inferInstance
  have hall : N = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact sup_le le_rfl (hcenter.trans hcN)
  rintro x ⟨z, rfl⟩
  exact ⟨f z, (show z ∈ N by rw [hall]; trivial), rfl⟩
end SU3.EvenInvolutionResidual
