module
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ElementaryWords
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralWord
public import Theory.SpecificGroups.Held.TwoLocalCandidates.MaximalNormalizerCatalogue.ProperInclusions.WordTests

/-!
# Recognition of the Held common involution by permutation signatures

Conjugation transports common fixed points bijectively. Thus a unique row
element with a specified fixed-point signature is fixed by the row normalizer.
Finite row covers reduce the recognition step to explicit permutation checks;
no enumeration of the full four-generator representative is assumed.

Source: ATLAS HeG1-p2058B0; GLS3 Table 5.3p. These certificates support the
maximal two-local condition E in Aschbacher–Smith, printed pp.3–4, 481–482.
-/

namespace Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
open Subgroup

@[expose] public def commonFixedCount (x y : He) : ℕ :=
  (Finset.univ.filter (fun v : Fin 2058 => representation x v = v ∧ representation y v = v)).card

public theorem commonFixedCount_conj (g x y : He) :
    commonFixedCount (g * x * g⁻¹) (g * y * g⁻¹) = commonFixedCount x y := by
  symm
  apply Finset.card_bijective (representation g) (representation g).bijective
  intro v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hx : representation (g * x * g⁻¹) (representation g v) =
      representation g (representation x v) := by
    change representation g (representation x ((representation g).symm (representation g v))) = _
    rw [Equiv.symm_apply_apply]
  have hy : representation (g * y * g⁻¹) (representation g v) =
      representation g (representation y v) := by
    change representation g (representation y ((representation g).symm (representation g v))) = _
    rw [Equiv.symm_apply_apply]
  rw [hx, hy]
  simp only [Equiv.apply_eq_iff_eq]

/-- The signature used to distinguish the central involution in a literal row. -/
@[expose] public def Signature (j : Fin 22) (bad : ℕ) (x : He) : Prop :=
  x ∈ ambient j ∧ commonFixedCount x x = 42 ∧
    ∀ y ∈ ambient j, commonFixedCount x y ≠ bad

public theorem signature_conj {j : Fin 22} {bad : ℕ} {g x : He}
    (hg : g ∈ normalizer (ambient j : Set He)) (hx : Signature j bad x) :
    Signature j bad (g * x * g⁻¹) := by
  refine ⟨(hg x).mp hx.1, ?_, ?_⟩
  · rw [commonFixedCount_conj]
    exact hx.2.1
  · intro y hy
    have hy' : g⁻¹ * y * g ∈ ambient j := by
      apply (hg _).mpr
      simpa only [SetLike.mem_coe, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] using hy
    have hc := commonFixedCount_conj g x (g⁻¹ * y * g)
    simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one] at hc
    simpa only [mul_assoc] using hc.symm ▸ hx.2.2 _ hy'

/-- A uniquely recognized involution is fixed by every row normalizer. -/
public theorem containment_of_signature (j : Fin 22) (bad : ℕ)
    (hz : Signature j bad centralWord)
    (hunique : ∀ x, Signature j bad x → x = centralWord) :
    normalizer (ambient j : Set He) ≤ normalizer (ambient 0 : Set He) := by
  intro g hg
  have hc := hunique _ (signature_conj hg hz)
  apply ProperInclusions.mem_normalizer_of_words 0
  intro w hw
  have hw' : w = commonWord := by
    change w ∈ [commonWord] at hw
    exact List.mem_singleton.mp hw
  subst w
  change g * centralWord * g⁻¹ ∈ ambient 0
  rw [hc, ambient_zero_eq_zpowers]
  exact mem_zpowers _

/-- A finite right-transition certificate covers the actual closure of a row.
Only transitions by its generators and their inverses are required. -/
public theorem ambient_covered {j : Fin 22} {ι : Type*} (e : ι → He)
    (h1 : ∃ i, e i = 1)
    (hstep : ∀ w ∈ generatorWords j, ∀ i, ∃ k, e i * (word w : He) = e k)
    (hback : ∀ w ∈ generatorWords j, ∀ i, ∃ k, e i * (word w : He)⁻¹ = e k) :
    ∀ x ∈ ambient j, ∃ i, e i = x := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
  clear hx
  induction hu using Subgroup.closure_induction_right with
  | one => exact h1
  | mul_right x hx y hy ih =>
    obtain ⟨w, hw, rfl⟩ := hy
    obtain ⟨i, hi⟩ := ih
    obtain ⟨k, hk⟩ := hstep w hw i
    exact ⟨k, by simpa only [map_mul, ← hi, Subgroup.subtype_apply] using hk.symm⟩
  | mul_inv_cancel x hx y hy ih =>
    obtain ⟨w, hw, rfl⟩ := hy
    obtain ⟨i, hi⟩ := ih
    obtain ⟨k, hk⟩ := hback w hw i
    exact ⟨k, by simpa only [map_mul, map_inv, ← hi, Subgroup.subtype_apply] using hk.symm⟩

/-- Finite data suffices to establish the signature, without injectivity of the
row enumeration or any exhaustive enumeration of the whole representative. -/
public theorem signature_of_cover {j : Fin 22} {bad : ℕ} {ι : Type*}
    (e : ι → He) (hcover : ∀ x ∈ ambient j, ∃ i, e i = x)
    (hz : centralWord ∈ ambient j) (hcount : commonFixedCount centralWord centralWord = 42)
    (havoid : ∀ i, commonFixedCount centralWord (e i) ≠ bad) :
    Signature j bad centralWord := by
  refine ⟨hz, hcount, ?_⟩
  intro x hx
  obtain ⟨i, rfl⟩ := hcover x hx
  exact havoid i

public theorem signature_unique_of_cover {j : Fin 22} {bad : ℕ} {ι : Type*}
    (e : ι → He) (hcover : ∀ x ∈ ambient j, ∃ i, e i = x)
    (helim : ∀ i, e i = centralWord ∨ commonFixedCount (e i) (e i) ≠ 42 ∨
      ∃ k, e k ∈ ambient j ∧ commonFixedCount (e i) (e k) = bad) :
    ∀ x, Signature j bad x → x = centralWord := by
  intro x hx
  obtain ⟨i, rfl⟩ := hcover x hx.1
  rcases helim i with h | h | ⟨k, hk, hc⟩
  · exact h
  · exact (h hx.2.1).elim
  · exact (hx.2.2 _ hk hc).elim

end Held.TwoLocalCandidates.MaximalNormalizerCatalogue.CentralContainment
