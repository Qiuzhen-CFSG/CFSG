/-
Copyright (c) 2026 Gerald Höhn.
Adapted from ATLAS, Atlas/Lattices/EisensteinGenerators.lean.
Distributed under the ATLAS Research and Attribution License 1.0;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/
module

public import Theory.AtlasPort.OtherSporadic.Lattices.EisensteinRational
public import Theory.AtlasPort.OtherSporadic.Lattices.EisensteinThreeModule

/-!
# Eisenstein Generators

Explicit code lifts, the glue vector, and coordinate differences generate the congruence lattice. Subtracting the residue lift reduces to the three-divisibility module.

Source: Gerald Höhn, ATLAS, `Atlas/Lattices/EisensteinGenerators.lean`, revision
`8eabb35afe2b5e45bf913a2d05c53e558d2e2917`.
Adapted for CFSG Lean 4.33.0 with public module boundaries and rewritten imports.
Definition bodies remain exposed for the source coordinate computations.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
namespace Atlas.Lattices
open Atlas.Algebra Atlas.Codes
open scoped BigOperators QuadraticAlgebra

/-- The signed integral lift of the fixed six-parameter code marking. -/
def eisensteinEncoder : (Fin 6 → Eisenstein) →ₗ[Eisenstein] EisensteinCoordinates where
  toFun p := ![p 0, p 1, p 2, p 3, p 4, -(p 0+p 1+p 2+p 3+p 4),
    p 5+p 4+p 1-p 3-p 2, p 5+p 0+p 2-p 4-p 3,
    p 5+p 1+p 3-p 0-p 4, p 5+p 2+p 4-p 1-p 0,
    p 5+p 3+p 0-p 2-p 1, p 5]
  map_add' := by intros; funext i; fin_cases i <;> simp <;> ring
  map_smul' := by intros; funext i; fin_cases i <;> simp <;> ring

theorem eisensteinEncoder_sum (p : Fin 6 → Eisenstein) :
    ∑ i, eisensteinEncoder p i = 6 * p 5 := by
  simp [eisensteinEncoder, Fin.sum_univ_succ]; ring

theorem eisensteinEncoder_residue (p : Fin 6 → Eisenstein) :
    eisensteinWordResidue (eisensteinEncoder p) =
      ternaryEncoder (fun j => eisensteinResidue (p j)) := by
  funext i
  fin_cases i <;> simp [eisensteinEncoder, ternaryEncoder, eisensteinWordResidue]

theorem eisensteinEncoder_lattice (p : Fin 6 → Eisenstein) :
    eisensteinTheta • eisensteinEncoder p ∈ eisensteinLeechModule := by
  refine ⟨0, eisensteinEncoder p, ?_, ?_, ?_⟩
  · intro i; simp
  · rw [eisensteinEncoder_residue]; exact ⟨_, rfl⟩
  · refine ⟨2 * p 5, ?_⟩
    simp [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, eisensteinEncoder_sum]
    ring

/-- The glue vector having entries -5,1,...,1. -/
def eisensteinGlue : EisensteinCoordinates := fun i => if i = 0 then -5 else 1

theorem eisensteinGlue_mem : eisensteinGlue ∈ eisensteinLeechModule := by
  refine ⟨1, Pi.single 0 (2*eisensteinTheta), ?_, ?_, ?_⟩
  · intro i
    by_cases hi : i = 0
    · subst i
      simp only [eisensteinGlue, ite_true, Pi.single_eq_same]
      have h := eisensteinTheta_sq
      calc
        (-5 : Eisenstein) = 1 + 2 * (-3) := by ring
        _ = 1 + eisensteinTheta * (2*eisensteinTheta) := by rw [← h]; ring
    · simp [eisensteinGlue, hi]
  · have hz : eisensteinWordResidue (Pi.single 0 (2*eisensteinTheta)) = 0 := by
      funext i
      by_cases hi : i=0 <;> simp [eisensteinWordResidue, hi,
        show eisensteinResidue (2*eisensteinTheta) = 0 by decide +kernel]
    rw [hz]; exact ternaryGolay.zero_mem
  · refine ⟨-eisensteinTheta, ?_⟩
    have he : (∑ i : Fin 12, eisensteinGlue i) = 6 := by
      norm_num [eisensteinGlue, Fin.sum_univ_succ]
    rw [he]
    calc
      (6 : Eisenstein) + 3 * 1 = -3 * (-3) := by ring
      _ = 3 * eisensteinTheta * -eisensteinTheta := by linear_combination 3 * eisensteinTheta_sq

theorem eisenstein_three_cancel {a b : Eisenstein} (h : 3*a=3*b) : a=b := by
  apply eisensteinToRational_injective
  have hr := congrArg eisensteinToRational h
  simp only [map_mul, map_ofNat] at hr
  exact mul_left_cancel₀ (by norm_num : (3 : EisensteinRational) ≠ 0) hr

/-- A universal generation criterion for the specified congruence lattice. -/
theorem eisensteinLeechModule_le_of_generators
    (S : Submodule Eisenstein EisensteinCoordinates)
    (hg : eisensteinGlue ∈ S)
    (hc : ∀ p, eisensteinTheta • eisensteinEncoder p ∈ S)
    (hd : ∀ i, (3 : Eisenstein) • (Pi.single i 1-Pi.single 0 1) ∈ S)
    (ht : (3*eisensteinTheta) • Pi.single 0 1 ∈ S) :
    eisensteinLeechModule ≤ S := by
  rintro z ⟨m, u, hu, hcode, hsum⟩
  obtain ⟨p, hp⟩ := hcode
  let q : Fin 6 → Eisenstein := fun j => (p j).val
  have hq : (fun j => eisensteinResidue (q j)) = p := by
    funext j
    simp [q, eisensteinResidue]
  have hv (i : Fin 12) : eisensteinTheta ∣ u i-eisensteinEncoder q i := by
    apply (eisensteinResidue_eq_zero _).mp
    have he := congrFun (eisensteinEncoder_residue q) i
    rw [hq, hp] at he
    change eisensteinResidue (eisensteinEncoder q i) = eisensteinResidue (u i) at he
    simp [he]
  choose a ha using hv
  let b : EisensteinCoordinates := a - Pi.single 0 (2*m)
  have hz : z = m • eisensteinGlue + eisensteinTheta • eisensteinEncoder q - (3 : Eisenstein) • b := by
    funext i
    have hi := hu i
    have hai := ha i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, b]
    by_cases he : i=0
    · subst i
      simp only [eisensteinGlue, ite_true, Pi.single_eq_same]
      calc
        z 0 = m + eisensteinTheta * (eisensteinEncoder q 0 + eisensteinTheta*a 0) := by rw [hi]; linear_combination eisensteinTheta * hai
        _ = m * -5 + eisensteinTheta * eisensteinEncoder q 0 - 3*(a 0-2*m) := by
          linear_combination a 0 * eisensteinTheta_sq
    · simp only [eisensteinGlue, Pi.single_apply, if_neg he, sub_zero]
      calc
        z i = m + eisensteinTheta * (eisensteinEncoder q i + eisensteinTheta*a i) := by rw [hi]; linear_combination eisensteinTheta * hai
        _ = m*1 + eisensteinTheta * eisensteinEncoder q i - 3*a i := by
          linear_combination a i * eisensteinTheta_sq
  have hgl : (∑ i, eisensteinGlue i) = 6 := by
    norm_num [eisensteinGlue, Fin.sum_univ_succ]
  have hsumz : (∑ i, z i) + 3*m =
      9*m + (3*eisensteinTheta)*(2*q 5) - 3*(∑ i, b i) := by
    rw [hz]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, hgl, eisensteinEncoder_sum]
    ring
  rw [hsumz] at hsum
  have hbase : 3*eisensteinTheta ∣ 9*m+(3*eisensteinTheta)*(2*q 5) := by
    refine ⟨-eisensteinTheta*m+2*q 5, ?_⟩
    linear_combination 3*m*eisensteinTheta_sq
  have hb3 : 3*eisensteinTheta ∣ 3*(∑ i, b i) := by
    have h := dvd_sub hbase hsum
    convert h using 1; ring
  have hb : eisensteinTheta ∣ ∑ i, b i := by
    obtain ⟨v, hv⟩ := hb3
    refine ⟨v, eisenstein_three_cancel ?_⟩
    simpa only [mul_assoc] using hv
  rw [hz]
  exact S.sub_mem (S.add_mem (S.smul_mem m hg) (hc q))
    (eisenstein_three_mem_of_sum_dvd 0 S hd ht b hb)

def eisensteinCodeGenerator (j : Fin 6) : EisensteinCoordinates :=
  eisensteinTheta • eisensteinEncoder (Pi.single j 1)

def eisensteinDifferenceGenerator (i : Fin 12) : EisensteinCoordinates :=
  (3 : Eisenstein) • (Pi.single i 1-Pi.single 0 1)

def eisensteinAnchor : EisensteinCoordinates :=
  (3*eisensteinTheta) • Pi.single 0 1

def eisensteinGeneratorSet : Set EisensteinCoordinates :=
  {eisensteinGlue} ∪ Set.range eisensteinCodeGenerator ∪
    Set.range eisensteinDifferenceGenerator ∪ {eisensteinAnchor}

theorem eisensteinEncoder_mem_of_basis (S : Submodule Eisenstein EisensteinCoordinates)
    (h : ∀ j, eisensteinCodeGenerator j ∈ S) (p : Fin 6 → Eisenstein) :
    eisensteinTheta • eisensteinEncoder p ∈ S := by
  have hp : p = ∑ j : Fin 6, p j • Pi.single j 1 := by
    funext k; simp [Finset.sum_apply, Pi.single_apply, mul_ite]
  have he : eisensteinTheta • eisensteinEncoder p =
      ∑ j, p j • eisensteinCodeGenerator j := by
    conv_lhs => rw [hp, map_sum, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    simp [eisensteinCodeGenerator, smul_comm eisensteinTheta (p j)]
  rw [he]
  exact S.sum_mem (fun j _ => S.smul_mem (p j) (h j))

theorem eisensteinDifferenceGenerator_mem (i : Fin 12) :
    eisensteinDifferenceGenerator i ∈ eisensteinLeechModule := by
  let d : EisensteinCoordinates := Pi.single i 1-Pi.single 0 1
  refine ⟨0, -eisensteinTheta • d, ?_, ?_, ?_⟩
  · intro j
    change (3 : Eisenstein) * d j = 0 + eisensteinTheta * (-eisensteinTheta * d j)
    linear_combination (d j)*eisensteinTheta_sq
  · have hz : eisensteinWordResidue (-eisensteinTheta • d) = 0 := by
      funext j
      simp [eisensteinWordResidue, Pi.smul_apply, smul_eq_mul,
        show eisensteinResidue eisensteinTheta=0 by decide +kernel]
    rw [hz]; exact ternaryGolay.zero_mem
  · have hz : ∑ j, eisensteinDifferenceGenerator i j = 0 := by
      simp [eisensteinDifferenceGenerator, Pi.smul_apply, smul_eq_mul,
        Pi.sub_apply, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp [hz]

theorem eisensteinGeneratorSet_mem {z : EisensteinCoordinates}
    (hz : z ∈ eisensteinGeneratorSet) : z ∈ eisensteinLeechModule := by
  rcases hz with ((rfl | ⟨j, rfl⟩) | ⟨i, rfl⟩) | rfl
  · exact eisensteinGlue_mem
  · exact eisensteinEncoder_lattice _
  · exact eisensteinDifferenceGenerator_mem _
  · exact eisensteinLeechModule_contains_multiple _

/-- The finite signed code/glue generators generate the entire specified module. -/
theorem eisensteinLeechModule_eq_span : eisensteinLeechModule =
    Submodule.span Eisenstein eisensteinGeneratorSet := by
  apply le_antisymm
  · apply eisensteinLeechModule_le_of_generators
    · exact Submodule.subset_span (by simp [eisensteinGeneratorSet])
    · apply eisensteinEncoder_mem_of_basis
      intro j
      exact Submodule.subset_span (by simp [eisensteinGeneratorSet])
    · intro i
      exact Submodule.subset_span (by simp [eisensteinGeneratorSet,
        eisensteinDifferenceGenerator])
    · exact Submodule.subset_span (by simp [eisensteinGeneratorSet, eisensteinAnchor])
  · exact Submodule.span_le.mpr (fun _ hz => eisensteinGeneratorSet_mem hz)

end Atlas.Lattices
