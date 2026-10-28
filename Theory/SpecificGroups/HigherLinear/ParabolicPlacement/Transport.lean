module

public import Theory.SpecificGroups.HigherLinear.ParabolicPlacement.Coordinates
public import Theory.GroupTheory.SylowOvergroupCharacteristic

/-!
# Proper parabolics, Sylow conjugacy and central-quotient transport

A subspace invariant under all elementary transvections is either zero or the
whole natural module. Since the SL center consists of scalar matrices, the
full preimage of the published projective parabolic is its SL stabilizer;
this proves properness in the literal quotient SL/Z(SL).

Sylow conjugacy and surjective lifting of Sylow subgroups reduce arbitrary
projective Sylow-overgroup placement to the standard SL unitriangular case.
That standard-coordinate exhaustion remains an explicit premise here.
Finally, relative normalization and the proved two-group property put the
published radical in the supplied Sylow, and hence in its overgroup.

Source: GLS III, §2.6, especially Theorem 2.6.7; Aschbacher–Smith,
`refs/quasithin.pdf`, printed pp.47–48 and p.74 (PDF pp.58–59 and p.85).
-/

public section

open Subgroup
open scoped MatrixGroups
namespace Matrix.HigherLinear
variable {n : ℕ} {F : Type*} [Field F]

/-- Scalar matrices preserve every subspace. -/
theorem center_le_parabolicSL (W : Submodule F (Fin n → F)) :
    center SL(n,F) ≤ parabolicSL W := by
  have hpres (g : SL(n,F)) (hg : g ∈ center SL(n,F)) (v : Fin n → F)
      (hv : v ∈ W) : SpecialLinearGroup.toLin' g v ∈ W := by
    obtain ⟨c, _, hc⟩ := SpecialLinearGroup.mem_center_iff.mp hg
    rw [SpecialLinearGroup.toLin'_apply, ← hc]
    simpa using W.smul_mem c hv
  intro g hg v
  constructor
  · intro hv
    simpa using hpres g⁻¹ ((center SL(n,F)).inv_mem hg) _ hv
  · exact hpres g hg v

/-- The full preimage of the published projective parabolic is exactly its SL stabilizer. -/
theorem comap_parabolic (W : Submodule F (Fin n → F)) :
    (parabolic W).comap (projection n F) = parabolicSL W := by
  apply Subgroup.comap_map_eq_self
  change (QuotientGroup.mk' (center SL(n,F))).ker ≤ _
  rw [QuotientGroup.ker_mk']
  exact center_le_parabolicSL W

/-- Elementary transvections prevent a nonzero proper subspace from being SL-invariant. -/
theorem parabolicSL_ne_top (hn : 2 ≤ n) {W : Submodule F (Fin n → F)}
    (hW : W ≠ ⊥) (hWt : W ≠ ⊤) : parabolicSL W ≠ ⊤ := by
  classical
  intro ht
  have hsingle {i j : Fin n} (hij : i ≠ j) (v : Fin n → F)
      (hv : v ∈ W) (hj : v j ≠ 0) : Pi.single i (1 : F) ∈ W := by
    have hg : SpecialLinearGroup.transvection hij (v j)⁻¹ ∈ parabolicSL W := by
      rw [ht]
      trivial
    have hm := W.sub_mem ((hg v).mpr hv) hv
    simpa [SpecialLinearGroup.toLin'_apply, SpecialLinearGroup.transvection_coe,
      Matrix.add_mulVec, Matrix.single_mulVec_eq, hj] using hm
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have hall (i : Fin n) : Pi.single i (1 : F) ∈ W := by
    by_cases hij : i = j
    · subst i
      let : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
      obtain ⟨k, hkj⟩ := exists_ne j
      have hk := hsingle hkj v hv hj
      exact hsingle hkj.symm (Pi.single k 1) hk (by simp)
    · exact hsingle hij v hv hj
  apply hWt
  apply top_unique
  intro v _
  rw [← Finset.univ_sum_single v]
  apply W.sum_mem
  intro i _
  simpa only [← Pi.single_smul, smul_eq_mul, mul_one] using W.smul_mem (v i) (hall i)

/-- The actual central-quotient image of a nonzero proper subspace stabilizer is proper. -/
theorem parabolic_ne_top (hn : 2 ≤ n) {W : Submodule F (Fin n → F)}
    (hW : W ≠ ⊥) (hWt : W ≠ ⊤) : parabolic W ≠ ⊤ := by
  intro ht
  apply parabolicSL_ne_top hn hW hWt
  rw [← comap_parabolic W, ht, Subgroup.comap_top]

/-- The published radical lies in every specified Sylow two-subgroup of its parabolic. -/
theorem radical_le_sylow_of_le_parabolic [CharP F 2]
    (S : Sylow 2 PSL(n,F)) (W : Submodule F (Fin n → F))
    (hSP : (S : Subgroup PSL(n,F)) ≤ parabolic W) :
    radical W ≤ (S : Subgroup PSL(n,F)) :=
  Theory.GroupTheory.normalized_pSubgroup_le_sylow S (parabolic W) (radical W)
    hSP (radical_le_parabolic W) (parabolic_le_normalizer W) (radical_isPGroup W)

/-- Actual overgroup application: the published radical lies in X whenever
S ≤ X ≤ P(W). No centralizer or solvability premise is needed. -/
theorem radical_le_overgroup_of_le_parabolic [CharP F 2]
    (S : Sylow 2 PSL(n,F)) (X : Subgroup PSL(n,F))
    (W : Submodule F (Fin n → F))
    (hSX : (S : Subgroup PSL(n,F)) ≤ X) (hXP : X ≤ parabolic W) :
    radical W ≤ X :=
  (radical_le_sylow_of_le_parabolic S W (hSX.trans hXP)).trans hSX

/-- Conjugation transports the stabilizer to the literal image subspace. -/
theorem parabolicSL_map_conj (W : Submodule F (Fin n → F)) (g : SL(n,F)) :
    (parabolicSL W).map (MulAut.conj g).toMonoidHom =
      parabolicSL (W.map (SpecialLinearGroup.toLin' g).toLinearMap) := by
  ext h
  rw [Subgroup.mem_map_equiv]
  change (∀ v, SpecialLinearGroup.toLin' ((MulAut.conj g).symm h) v ∈ W ↔ v ∈ W) ↔ _
  constructor
  · intro hh v
    rw [Submodule.mem_map_equiv, Submodule.mem_map_equiv]
    have he := hh ((SpecialLinearGroup.toLin' g).symm v)
    simpa only [MulAut.conj_symm_apply, map_mul, map_inv, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply] using he
  · intro hh v
    have he := hh (SpecialLinearGroup.toLin' g v)
    rw [Submodule.mem_map_equiv, Submodule.mem_map_equiv] at he
    simpa only [MulAut.conj_symm_apply, map_mul, map_inv, LinearEquiv.mul_apply,
      LinearEquiv.coe_inv, LinearEquiv.symm_apply_apply] using he

open Theory.SpecificGroups.LinearSylowNormalizers

/-- Sylow conjugacy transports standard-coordinate placement to an arbitrary supplied SL Sylow.
The standard overgroup theorem is an explicit premise. -/
theorem exists_parabolicSL_of_standard_overgroups [Finite F] [CharP F 2] (hn : 0 < n)
    (hstandard : ∀ H : Subgroup SL(n,F), unipotent n F ≤ H → H ≠ ⊤ →
      ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ H ≤ parabolicSL W)
    (S : Sylow 2 SL(n,F)) (X : Subgroup SL(n,F))
    (hSX : (S : Subgroup SL(n,F)) ≤ X) (hX : X ≠ ⊤) :
    ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ X ≤ parabolicSL W := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(n,F) (standardSylow n F hn) S
  have hS : (unipotent n F).map (MulAut.conj g).toMonoidHom =
      (S : Subgroup SL(n,F)) := by
    rw [← coe_standardSylow n F hn]
    exact congrArg (fun T : Sylow 2 SL(n,F) => (T : Subgroup SL(n,F))) hg
  let Y := X.comap (MulAut.conj g).toMonoidHom
  have hUY : unipotent n F ≤ Y := by
    apply Subgroup.map_le_iff_le_comap.mp
    rw [hS]
    exact hSX
  have hY : Y ≠ ⊤ := by
    intro ht
    apply hX
    apply Subgroup.comap_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
    simpa only [Subgroup.comap_top] using ht
  obtain ⟨W, hW, hWt, hYW⟩ := hstandard Y hUY hY
  refine ⟨W.map (SpecialLinearGroup.toLin' g).toLinearMap,
    fun h => hW (Submodule.map_eq_bot_iff.mp h),
    fun h => hWt (Submodule.map_eq_top_iff.mp h), ?_⟩
  rw [← parabolicSL_map_conj]
  intro x hx
  refine ⟨(MulAut.conj g).symm x, hYW ?_, (MulAut.conj g).apply_symm_apply x⟩
  change (MulAut.conj g) ((MulAut.conj g).symm x) ∈ X
  simpa [mul_assoc] using hx

/-- Transport standard-coordinate placement to the actual quotient SL/Z(SL).
The standard overgroup theorem remains an explicit premise to be discharged by final assembly. -/
theorem exists_parabolic_of_standard_overgroups [Finite F] [CharP F 2] (hn : 0 < n)
    (hstandard : ∀ H : Subgroup SL(n,F), unipotent n F ≤ H → H ≠ ⊤ →
      ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ H ≤ parabolicSL W)
    (S : Sylow 2 PSL(n,F)) (X : Subgroup PSL(n,F))
    (hSX : (S : Subgroup PSL(n,F)) ≤ X) (hX : X ≠ ⊤) :
    ∃ W : Submodule F (Fin n → F), W ≠ ⊥ ∧ W ≠ ⊤ ∧ X ≤ parabolic W := by
  have hq : Function.Surjective (projection n F) := QuotientGroup.mk'_surjective _
  obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective hq 2 S
  have hTX : (T : Subgroup SL(n,F)) ≤ X.comap (projection n F) := by
    apply Subgroup.map_le_iff_le_comap.mp
    have he : (T : Subgroup SL(n,F)).map (projection n F) = (S : Subgroup PSL(n,F)) :=
      congrArg (fun R : Sylow 2 PSL(n,F) => (R : Subgroup PSL(n,F))) hT
    rw [he]
    exact hSX
  have hpre : X.comap (projection n F) ≠ ⊤ := by
    intro ht
    apply hX
    apply Subgroup.comap_injective hq
    simpa only [Subgroup.comap_top] using ht
  obtain ⟨W, hW, hWt, hpreW⟩ :=
    exists_parabolicSL_of_standard_overgroups hn hstandard T _ hTX hpre
  refine ⟨W, hW, hWt, ?_⟩
  intro x hx
  obtain ⟨g, rfl⟩ := hq x
  exact Subgroup.mem_map_of_mem (projection n F) (hpreW hx)

end Matrix.HigherLinear
