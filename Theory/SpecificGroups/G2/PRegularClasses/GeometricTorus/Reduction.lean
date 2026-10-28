module

public import Theory.SpecificGroups.G2.PRegularClasses.Basic
public import Theory.AtlasPort.Algebra.SplitOctonion.NormGeometry
public import Theory.AtlasPort.LinearGroups.G2.VectorStabilizer
public import Theory.AtlasPort.LinearGroups.G2.Torus

/-!
# Opposite eigenvectors for the actual split-octonion group

In characteristic two, a nontrivial eigenvalue of an octonion automorphism
has singular trace-zero eigenvectors. Nondegeneracy of the norm polar form
and the eigenspace decomposition give a reciprocal eigenvector pairing to
one. The explicit root reduction then moves this opposite pair to the
coordinate vectors numbered zero and seven, inside the literal group.

This is the geometric reduction for a direct proof of semisimple torus
conjugacy, the G₂ instance of GLS III, 1.4.2(e) and 1.4.3(b)
(`refs/KGroup/GLS3/Chapter1.tex`). It does not yet diagonalize the remaining
two-dimensional block. The octonion coordinates and root reduction use the
licensed ATLAS port; see `LICENSES/ATLAS.txt` and
`LICENSES/ATLAS-CITATION.cff`.
-/

public section

open Atlas.SplitOctonion
namespace Atlas.G2.PRegularClasses
variable {K : Type*} [Field K] [IsAlgClosed K]


private theorem exists_nontrivial_eigenvector (g : Model K) (hg : g ≠ 1)
    (hs : (action g).IsSemisimple) :
    ∃ a : Kˣ, a ≠ 1 ∧ ∃ v : Carrier K, v ≠ 0 ∧ g.val v = (a : K) • v := by
  classical
  have hex : ∃ a : K, a ≠ 1 ∧ ∃ v : Carrier K,
      v ≠ 0 ∧ g.val v = a • v := by
    by_contra h
    push Not at h
    have hfix : (⊤ : Submodule K (Carrier K)) ≤ (action g).eigenspace 1 := by
      rw [← hs.iSup_eigenspace_eq_top]
      refine iSup_le fun a => ?_
      intro v hv
      by_cases ha : a = 1
      · simpa only [ha] using hv
      · have hz : v = 0 := by
          by_contra hv0
          exact h a ha v hv0 (Module.End.mem_eigenspace_iff.mp hv)
        simp [hz]
    apply hg
    apply Subtype.ext
    apply LinearEquiv.ext
    intro v
    have hv := Module.End.mem_eigenspace_iff.mp (hfix (Submodule.mem_top : v ∈ ⊤))
    simpa [action] using hv
  obtain ⟨a, ha, v, hv, he⟩ := hex
  have ha0 : a ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at he
    exact hv (g.val.injective (he.trans (map_zero _).symm))
  refine ⟨Units.mk0 a ha0, ?_, v, hv, he⟩
  intro heq
  exact ha (congrArg Units.val heq)

private theorem exists_paired_eigenvector (g : Model K) (hs : (action g).IsSemisimple)
    (v : Carrier K) (hv : v ≠ 0) :
    ∃ b : K, ∃ w : Carrier K, g.val w = b • w ∧ normPolar v w ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hv
  apply normPolar_nondegenerate
  have hker : (⊤ : Submodule K (Carrier K)) ≤ (normPolar v).ker := by
    rw [← hs.iSup_eigenspace_eq_top]
    refine iSup_le fun b => ?_
    intro w hw
    exact h b w (Module.End.mem_eigenspace_iff.mp hw)
  intro w
  exact hker (Submodule.mem_top : w ∈ ⊤)

omit [IsAlgClosed K] in
private theorem eigenvector_singular [CharP K 2] (g : Model K)
    (a : K) (ha : a ≠ 1) (v : Carrier K) (he : g.val v = a • v) :
    trace v = 0 ∧ norm v = 0 := by
  have ht := automorphism_trace g v
  rw [he] at ht
  have ht' : (a - 1) * trace v = 0 := by
    simp only [trace, Pi.smul_apply, smul_eq_mul] at ht ⊢
    linear_combination ht
  have hn := automorphism_norm g v
  rw [he, norm_smul] at hn
  have hn' : (a ^ 2 - 1) * norm v = 0 := by linear_combination hn
  have hsq : a ^ 2 ≠ 1 := by
    intro h
    exact ha (CharTwo.sq_inj.mp (h.trans (one_pow 2).symm))
  exact ⟨(mul_eq_zero.mp ht').resolve_left (sub_ne_zero.mpr ha),
    (mul_eq_zero.mp hn').resolve_left (sub_ne_zero.mpr hsq)⟩

/-- A nonidentity semisimple octonion automorphism has an opposite singular
pair of eigenvectors, normalized to have norm pairing one. -/
theorem exists_opposite_eigenpair [CharP K 2] (g : Model K) (hg : g ≠ 1)
    (hs : (action g).IsSemisimple) :
    ∃ a : Kˣ, a ≠ 1 ∧ ∃ v w : Carrier K,
      trace v = 0 ∧ norm v = 0 ∧ trace w = 0 ∧ norm w = 0 ∧
      normPolar v w = 1 ∧ g.val v = (a : K) • v ∧
      g.val w = (↑a⁻¹ : K) • w := by
  obtain ⟨a, ha, v, hv, he⟩ := exists_nontrivial_eigenvector g hg hs
  obtain ⟨b, w, hw, hp⟩ := exists_paired_eigenvector g hs v hv
  have hp' := automorphism_normPolar g v w
  rw [he, hw] at hp'
  have hab : (a : K) * b = 1 := by
    apply mul_right_cancel₀ hp
    simpa [mul_assoc, mul_left_comm] using hp'
  have hb : b = (↑a⁻¹ : K) := by
    apply mul_left_cancel₀ a.ne_zero
    simpa using hab
  have ha' : (a : K) ≠ 1 := fun h => ha (Units.ext h)
  have hb' : b ≠ 1 := by
    intro h
    exact ha' (by simpa [h] using hab)
  obtain ⟨hvt, hvn⟩ := eigenvector_singular g (a : K) ha' v he
  obtain ⟨hwt, hwn⟩ := eigenvector_singular g b hb' w hw
  refine ⟨a, ha, v, (normPolar v w)⁻¹ • w, hvt, hvn, ?_, ?_, ?_, he, ?_⟩
  · change (normPolar v w)⁻¹ * w 3 + (normPolar v w)⁻¹ * w 4 = 0
    change w 3 + w 4 = 0 at hwt
    rw [← _root_.mul_add, hwt, mul_zero]
  · rw [norm_smul, hwn, mul_zero]
  · simp [hp]
  · rw [map_smul, hw, hb, smul_comm]

omit [IsAlgClosed K] in
/-- Actual octonion automorphisms move every normalized opposite singular
pair to the designated pair of coordinate vectors. -/
theorem exists_map_opposite_pair (v w : Carrier K)
    (hvt : trace v = 0) (hvn : norm v = 0)
    (hwt : trace w = 0) (hwn : norm w = 0) (hp : normPolar v w = 1) :
    ∃ c : Model K, c.val v = basisVector 0 ∧ c.val w = basisVector 7 := by
  have hv : v ≠ 0 := by
    intro h
    simp [h] at hp
  obtain ⟨b, _, r, hr, hb⟩ := singular_vector_reduction_first v hvt hvn hv
  let t := torus (Units.mk0 r hr)⁻¹ (1 : Kˣ)
  have ht : t.val (r • basisVector 0) = basisVector 0 := by
    ext i
    fin_cases i <;>
      simp [t, torus, torusEquiv, torusLinear, torusWeights, basisVector, hr]
  let c := t * b
  have hc : c.val v = basisVector 0 := by
    change t.val (b.val v) = _
    rw [hb, ht]
  have hcwt : trace (c.val w) = 0 := (automorphism_trace c w).trans hwt
  have hcwn : norm (c.val w) = 0 := (automorphism_norm c w).trans hwn
  have hcwp : c.val w 7 = 1 := by
    have hp' := (automorphism_normPolar c v w).trans hp
    rw [hc] at hp'
    simpa [normPolar, basisVector] using hp'
  refine ⟨chartReducer (c.val w) * c, ?_, ?_⟩
  · change (chartReducer (c.val w)).val (c.val v) = _
    rw [hc, chartReducer_fixes_first]
  · change (chartReducer (c.val w)).val (c.val w) = _
    rw [chartReducer_eq _ hcwt hcwn (by rw [hcwp]; exact one_ne_zero), hcwp, one_smul]

omit [IsAlgClosed K] in
theorem conjugate_action_of_eigenvector (g c : Model K) (v : Carrier K) (a : K)
    (hv : g.val v = a • v) :
    (c * g * c⁻¹).val (c.val v) = a • c.val v := by
  change c.val (g.val (c.val.symm (c.val v))) = _
  rw [c.val.symm_apply_apply, hv, map_smul]

/-- The geometric reduction to the subgroup scaling the opposite coordinate
vectors; the conjugator remains in the literal octonion automorphism group. -/
theorem exists_conjugate_scaling_pair [CharP K 2] (g : Model K) (hg : g ≠ 1)
    (hs : (action g).IsSemisimple) :
    ∃ a : Kˣ, a ≠ 1 ∧ ∃ c : Model K,
      (c * g * c⁻¹).val (basisVector 0) = (a : K) • basisVector 0 ∧
      (c * g * c⁻¹).val (basisVector 7) = (↑a⁻¹ : K) • basisVector 7 := by
  obtain ⟨a, ha, v, w, hvt, hvn, hwt, hwn, hp, hv, hw⟩ :=
    exists_opposite_eigenpair g hg hs
  obtain ⟨c, hcv, hcw⟩ := exists_map_opposite_pair v w hvt hvn hwt hwn hp
  refine ⟨a, ha, c, ?_, ?_⟩
  · simpa only [hcv] using conjugate_action_of_eigenvector g c v (a : K) hv
  · simpa only [hcw] using conjugate_action_of_eigenvector g c w (↑a⁻¹ : K) hw

end Atlas.G2.PRegularClasses
