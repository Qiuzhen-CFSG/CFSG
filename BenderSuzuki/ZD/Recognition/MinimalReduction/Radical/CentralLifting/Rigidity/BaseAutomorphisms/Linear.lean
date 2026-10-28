module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Linear.SemilinearCoverage

/-!
# Sylow-centralizing automorphisms of binary PSL₂ in standard position

An arbitrary automorphism is inner times an entrywise field automorphism.
The field factor fixes the upper transvection with parameter one. An inner
factor centralizing that transvection is itself upper unipotent, by its
matrix entries and the determinant-one relation in characteristic two.
Upper unipotents commute, so pointwise fixation of the root group forces
every field parameter to be fixed as well. The conjugating element therefore
lies in the actual root subgroup.

This is the rank-one PSL₂ case of GLS, Volume 3, Theorem 2.6.5(e), used for
PSL₂(4) in Volume 4, Chapter 4, Lemma 2.8(c).
-/

namespace BenderSuzuki.ZD.BaseAutomorphisms
open Converse Linear _root_.BenderSuzuki.MatrixGroups

variable {K : Type*} [Field K] [CharP K 2]

private theorem eq_uni_of_commute_uni_one (g : SL2 K)
    (h : g * uni 1 = uni 1 * g) : g = uni (g.val 0 1) := by
  have h00 := congrArg (fun x : SL2 K => x.val 0 0) h
  have h01 := congrArg (fun x : SL2 K => x.val 0 1) h
  have hc : g.val 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h00.symm
  have hd : g.val 0 0 = g.val 1 1 := by
    have he : g.val 0 0 + g.val 0 1 = g.val 0 1 + g.val 1 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two] using h01
    exact add_right_cancel (he.trans (add_comm _ _))
  have ha : g.val 0 0 = 1 := by
    apply CharTwo.sq_injective
    simpa only [Matrix.det_fin_two, hc, ← hd, mul_zero, sub_zero, pow_two, one_mul]
      using g.property
  have hd1 : g.val 1 1 = 1 := hd.symm.trans ha
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hc, ha, hd1]

/-- An arbitrary automorphism fixing the standard unipotent group pointwise
is conjugation by an element of that group. -/
public theorem psl2_aut_fixing_unipotent_inner [Finite K]
    (β : MulAut (PSL2MatrixGroup K))
    (hfix : ∀ b ∈ PUnip K, β b = b) :
    ∃ b ∈ PUnip K, β = MulAut.conj b := by
  obtain ⟨g, σ, hβ⟩ := semilinear_coverage β
  obtain ⟨h, rfl⟩ := pi_surjective g
  have hconj (t : K) : h * uni (σ t) * h⁻¹ = uni t := by
    apply pi_injective
    have hu : pi K (uni t) ∈ PUnip K :=
      ⟨uni t, (mem_Unip_iff _).mpr ⟨t, rfl⟩, rfl⟩
    have hf := hfix _ hu
    rw [hβ, MulAut.mul_apply, fieldAut_apply_pi] at hf
    change MulAut.conj (pi K h) (pi K (sl2FieldAut σ (uni t))) = _ at hf
    rw [sl2FieldAut_uni] at hf
    simpa only [map_mul, map_inv, MulAut.conj_apply] using hf
  have hc : h * uni 1 = uni 1 * h := by
    have he := hconj 1
    rw [map_one] at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hh := eq_uni_of_commute_uni_one h hc
  have hσ (t : K) : σ t = t := by
    apply uni_injective
    have he := hconj t
    rw [hh] at he
    have hcomm : uni (h.val 0 1) * uni (σ t) = uni (σ t) * uni (h.val 0 1) := by
      rw [uni_mul_uni, uni_mul_uni, add_comm]
    simpa only [hcomm, mul_inv_cancel_right] using he
  have hf : fieldAut σ = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := pi_surjective x
    rw [fieldAut_apply_pi]
    change pi K (sl2FieldAut σ y) = pi K y
    congr 1
    ext i j
    exact hσ (y.val i j)
  refine ⟨pi K h, ?_, ?_⟩
  · exact ⟨h, (mem_Unip_iff _).mpr ⟨h.val 0 1, hh⟩, rfl⟩
  · simpa only [hf, mul_one] using hβ

end BenderSuzuki.ZD.BaseAutomorphisms
