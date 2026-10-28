module
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import Theory.SpecificGroups.Suzuki.NormalizedRootCentralizers

/-!
# The pointwise fixer of the Suzuki root center

Inner–field coverage reduces an automorphism fixing the root center to an
inner automorphism: fixation of u(0,1) puts the inner factor in the root
subgroup, and fixation of all u(0,b) then kills the field automorphism.
This is the concrete Suzuki case of GLS4, Chapter 4, Lemma 3.6(c), used in
Chapter 2, Lemma 14.3(a). The center and conjugation use the actual matrix
model and its upper-triangular root convention.
-/

namespace BenderSuzuki.MatrixGroups
open Subgroup PFAppendixIII

private noncomputable def centralRoot (m : ℕ) (b : BinaryGaloisField (2 * m + 1)) :
    SuzukiMatrixGroup m :=
  ⟨SuzukiRootGL m 0 b, subset_closure (Or.inl ⟨0, b, rfl⟩)⟩

private theorem centralRoot_mem (m : ℕ) (hm : 0 < m) (b : BinaryGaloisField (2 * m + 1)) :
    centralRoot m b ∈ (center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype :=
  (NormalizedRootCentralizers.mem_center_iff_coordinates m hm _).mpr ⟨b, rfl⟩

private theorem field_centralRoot (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    (b : BinaryGaloisField (2 * m + 1)) :
    suzukiFieldAut m σ (centralRoot m b) = centralRoot m (σ b) := by
  ext i j
  rw [suzukiFieldAut_apply_entry]
  fin_cases i <;> fin_cases j <;> simp [centralRoot, SuzukiRootGL, SuzukiRootMatrix]

public theorem suzuki_aut_fixing_root_center_inner (m : ℕ) (hm : 1 ≤ m)
    (β : MulAut (SuzukiMatrixGroup m))
    (hfix : ∀ b ∈ (center (SuzukiRootSubgroup m)).map (SuzukiRootSubgroup m).subtype,
      β b = b) :
    ∃ b ∈ SuzukiRootSubgroup m, β = MulAut.conj b := by
  obtain ⟨g, σ, hβ⟩ := suzukiAut_eq_inner_mul_field m hm β
  have hconj (b : BinaryGaloisField (2 * m + 1)) :
      g * centralRoot m (σ b) * g⁻¹ = centralRoot m b := by
    have he := hfix _ (centralRoot_mem m hm b)
    rw [hβ, MulAut.mul_apply, field_centralRoot] at he
    exact he
  have hg : g ∈ SuzukiRootSubgroup m := by
    have hz : centralRoot m 1 ≠ 1 := by
      intro he
      have h02 := congrArg (fun x : SuzukiMatrixGroup m => x.val (0 : Fin 4) (2 : Fin 4)) he
      simp [centralRoot, SuzukiRootGL, SuzukiRootMatrix] at h02
    apply suzukiRootSubgroup_centralizer_le m hm
      (map_subtype_le _ (centralRoot_mem m hm 1)) hz
    rw [mem_centralizer_singleton_iff]
    have he := hconj 1
    rw [map_one] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hσ (b : BinaryGaloisField (2 * m + 1)) : σ b = b := by
    have hc : Commute g (centralRoot m (σ b)) := by
      obtain ⟨v, hv, he⟩ := centralRoot_mem m hm (σ b)
      rw [← he]
      exact congrArg (SuzukiRootSubgroup m).subtype
        (mem_center_iff.mp hv ⟨g, hg⟩)
    have he := hconj b
    rw [hc.eq, mul_inv_cancel_right] at he
    have h02 := congrArg (fun x : SuzukiMatrixGroup m => x.val (0 : Fin 4) (2 : Fin 4)) he
    simpa [centralRoot, SuzukiRootGL, SuzukiRootMatrix] using h02
  have hf : suzukiFieldAut m σ = 1 := by
    ext x i j
    rw [suzukiFieldAut_apply_entry]
    exact hσ (x.val i j)
  exact ⟨g, hg, by simpa only [hf, mul_one] using hβ⟩
end BenderSuzuki.MatrixGroups
