module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki.OuterIndex
public import Theory.SpecificGroups.Suzuki.AbelianSubgroups

/-!
# Sylow-centralizing automorphisms of Suzuki groups in standard position

Use the proved inner-field decomposition of an arbitrary automorphism.
Every field automorphism fixes the nonidentity root element with coordinates
`(0,1)`. Its group centralizer lies in the standard root subgroup, forcing
the inner factor into that subgroup. The first root coordinate is additive
and is unchanged by inner conjugation within the root group. Pointwise
fixation consequently forces the field automorphism to fix every parameter.

The root multiplication convention is the upper-triangular matrix convention
of Huppert--Blackburn III, XI.3.1. The automorphism-centralizer conclusion is
the Suzuki case of GLS, Volume 3, Theorem 2.6.5(e), used for Sz(8) in
Volume 4, Chapter 4, Lemma 2.8(c).
-/

namespace BenderSuzuki.ZD.BaseAutomorphisms
open _root_.BenderSuzuki.MatrixGroups PFAppendixIII

private noncomputable def root (m : ℕ) (a b : BinaryGaloisField (2 * m + 1)) :
    SuzukiMatrixGroup m :=
  ⟨SuzukiRootGL m a b, Subgroup.subset_closure (Or.inl ⟨a, b, rfl⟩)⟩

private theorem root_mem (m : ℕ) (a b : BinaryGaloisField (2 * m + 1)) :
    root m a b ∈ SuzukiRootSubgroup m :=
  (mem_suzukiRootSubgroup_iff m _).mpr ⟨a, b, rfl⟩

private theorem root_mul (m : ℕ) (hm : 0 < m)
    (a b c d : BinaryGaloisField (2 * m + 1)) :
    root m a b * root m c d = root m (a + c) (b + d + a * suzukiTits m c) := by
  apply Subtype.ext
  exact (External.huppert_blackburn_XI_3_1 m hm (suzukiTits m)
    (suzukiTits_sq m)).2.2.2.2.2.2.2.2.1 a b c d

private theorem field_root (m : ℕ)
    (σ : BinaryGaloisField (2 * m + 1) ≃ₐ[ZMod 2] BinaryGaloisField (2 * m + 1))
    (a b : BinaryGaloisField (2 * m + 1)) :
    suzukiFieldAut m σ (root m a b) = root m (σ a) (σ b) := by
  ext i j
  rw [suzukiFieldAut_apply_entry]
  fin_cases i <;> fin_cases j <;> simp [root, SuzukiRootGL, SuzukiRootMatrix]

/-- An arbitrary automorphism fixing the standard Suzuki root group pointwise
is conjugation by an element of that group. -/
public theorem suzuki_aut_fixing_root_inner (m : ℕ) (hm : 1 ≤ m)
    (β : MulAut (SuzukiMatrixGroup m))
    (hfix : ∀ b ∈ SuzukiRootSubgroup m, β b = b) :
    ∃ b ∈ SuzukiRootSubgroup m, β = MulAut.conj b := by
  obtain ⟨g, σ, hβ⟩ := suzukiAut_eq_inner_mul_field m hm β
  have hconj (a b : BinaryGaloisField (2 * m + 1)) :
      g * root m (σ a) (σ b) * g⁻¹ = root m a b := by
    have he := hfix _ (root_mem m a b)
    rw [hβ, MulAut.mul_apply, field_root] at he
    exact he
  have hg : g ∈ SuzukiRootSubgroup m := by
    have hz : root m 0 1 ≠ 1 := by
      intro he
      have h02 := congrArg (fun x : SuzukiMatrixGroup m => x.val (0 : Fin 4) (2 : Fin 4)) he
      simp [root, SuzukiRootGL, SuzukiRootMatrix] at h02
    apply suzukiRootSubgroup_centralizer_le m hm (root_mem m 0 1) hz
    rw [Subgroup.mem_centralizer_singleton_iff]
    have he := hconj 0 1
    rw [map_zero, map_one] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hσ (t : BinaryGaloisField (2 * m + 1)) : σ t = t := by
    obtain ⟨a, b, hab⟩ := (mem_suzukiRootSubgroup_iff m g).mp hg
    have hgr : g = root m a b := Subtype.ext hab
    have he := hconj t 0
    rw [map_zero] at he
    have he' := mul_inv_eq_iff_eq_mul.mp he
    rw [hgr, root_mul m hm, root_mul m hm] at he'
    have h01 := congrArg (fun x : SuzukiMatrixGroup m => x.val (0 : Fin 4) (1 : Fin 4)) he'
    change a + σ t = t + a at h01
    exact add_left_cancel (h01.trans (add_comm t a))
  have hf : suzukiFieldAut m σ = 1 := by
    ext x i j
    rw [suzukiFieldAut_apply_entry]
    exact hσ (x.val i j)
  exact ⟨g, hg, by simpa only [hf, mul_one] using hβ⟩

end BenderSuzuki.ZD.BaseAutomorphisms
