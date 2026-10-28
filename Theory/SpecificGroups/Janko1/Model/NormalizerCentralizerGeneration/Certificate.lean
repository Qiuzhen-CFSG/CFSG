module

public import Theory.SpecificGroups.Janko1.Model.SylowTwo
-- Intentional internal proof extension: reuse the checked Sylow witness and
-- its private matrix specifications, without changing their public boundary.
import all Theory.SpecificGroups.Janko1.Model.SylowTwo

/-!
# A checked generating pair of local subgroups in J₁

The internal proof import reuses the eight-element subgroup and its prefix
matrices from `Model.SylowTwo`, preserving that module's private boundary.
The word `c` permutes its seven involutions. A further word `h` centralizes `a`, and an
explicit eleven-factor word in `a`, `c`, and `h` equals `b`. Thus the
centralizer of `a` and the normalizer of this Sylow subgroup contain both
standard generators. Every numerical identity is checked in the kernel;
literal prefix matrices bound the size of individual reductions.

Source: Aschbacher--Smith, E.1.14(5), printed p.214, citing Asc82a,
Lemma 4.9; GLS3, Table 5.3f. The ATLAS matrix representation and attribution
are recorded in `Model.Basic`. `Source/Generate.py` and `Source/Search.py`
are untrusted certificate generators, not proof dependencies.
-/

namespace Janko1.NormalizerCentralizerGeneration
open Subgroup

open Janko1.SylowTwo
private theorem a_mem : a ∈ (sylow : Subgroup Model) :=
  ⟨1, rfl⟩

private theorem conjugate_table : ∀ i : Fin 8, ∃ j : Fin 8,
    C * E i * D = E j := by decide +kernel

private theorem inverse_conjugate_table : ∀ i : Fin 8, ∃ j : Fin 8,
    D * E i * C = E j := by decide +kernel

private theorem c_normalizes : c ∈ normalizer (sylow : Set Model) := by
  have hf (x : Model) (hx : x ∈ eight) : c * x * c⁻¹ ∈ eight := by
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := conjugate_table i
    refine ⟨j, (rho_injective ?_).symm⟩
    simpa only [map_mul, rho_c, rho_cinv, rho_e] using hj
  have hb (x : Model) (hx : x ∈ eight) : c⁻¹ * x * c ∈ eight := by
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨j, hj⟩ := inverse_conjugate_table i
    refine ⟨j, (rho_injective ?_).symm⟩
    simpa only [map_mul, rho_c, rho_cinv, rho_e] using hj
  apply mem_normalizer_iff.mpr
  intro x
  constructor
  · exact hf x
  · intro hx
    have hm := hb _ hx
    have he : c⁻¹ * (c * x * c⁻¹) * c = x := by group
    rw [he] at hm
    exact hm

private def h : Model := (a*b^1) * (a*b^2) * (a*b^1) * (a*b^2) * (a*b^1) * (a*b^1) * (a*b^2) * (a*b^2) * (a*b^1) * (a*b^2) * (a*b^2) * (a*b^1) * (a*b^1) * (a*b^2) * (a*b^1) * (a*b^2) * (a*b^1)

private def hP1 : Mat := !![1, 6, 5, 6, 6, 7, 7;
    5, 4, 5, 10, 6, 6, 4;
    6, 8, 6, 5, 3, 8, 3;
    4, 6, 7, 5, 8, 0, 8;
    5, 0, 7, 7, 3, 8, 6;
    6, 4, 10, 5, 5, 7, 6;
    4, 8, 5, 4, 3, 5, 0]

private theorem hStep1 : T₁ * T₂ = hP1 := by decide +kernel

private def hP2 : Mat := !![2, 4, 8, 0, 8, 3, 8;
    1, 3, 6, 10, 4, 0, 2;
    10, 0, 1, 5, 7, 2, 8;
    7, 3, 4, 4, 6, 8, 3;
    3, 8, 0, 9, 8, 7, 8;
    0, 3, 2, 3, 3, 8, 7;
    5, 2, 10, 10, 4, 8, 0]

private theorem hStep2 : hP1 * T₁ = hP2 := by decide +kernel

private def hP3 : Mat := !![9, 3, 1, 6, 3, 6, 7;
    1, 4, 3, 2, 0, 0, 9;
    1, 4, 4, 2, 2, 2, 0;
    3, 0, 3, 1, 4, 4, 7;
    8, 10, 5, 9, 9, 3, 2;
    10, 7, 5, 3, 0, 1, 2;
    3, 8, 2, 8, 10, 10, 1]

private theorem hStep3 : hP2 * T₂ = hP3 := by decide +kernel

private def hP4 : Mat := !![10, 2, 3, 1, 2, 6, 10;
    7, 4, 7, 8, 2, 7, 10;
    7, 7, 3, 2, 3, 3, 9;
    7, 8, 10, 3, 0, 10, 3;
    3, 2, 8, 9, 5, 9, 10;
    9, 3, 0, 5, 7, 8, 9;
    4, 3, 1, 9, 8, 5, 5]

private theorem hStep4 : hP3 * T₁ = hP4 := by decide +kernel

private def hP5 : Mat := !![9, 3, 7, 6, 7, 7, 6;
    3, 0, 7, 7, 8, 10, 7;
    7, 4, 2, 9, 5, 3, 9;
    9, 6, 8, 4, 7, 4, 5;
    6, 0, 7, 4, 0, 3, 1;
    9, 6, 6, 6, 10, 7, 2;
    7, 5, 6, 8, 0, 0, 5]

private theorem hStep5 : hP4 * T₁ = hP5 := by decide +kernel

private def hP6 : Mat := !![7, 4, 0, 8, 1, 5, 0;
    6, 6, 1, 4, 2, 2, 6;
    5, 3, 0, 0, 6, 7, 6;
    4, 5, 7, 7, 5, 9, 8;
    7, 7, 3, 1, 7, 8, 0;
    9, 2, 5, 3, 2, 7, 7;
    8, 4, 4, 7, 5, 2, 6]

private theorem hStep6 : hP5 * T₂ = hP6 := by decide +kernel

private def hP7 : Mat := !![8, 6, 7, 9, 4, 4, 6;
    0, 4, 3, 6, 4, 0, 1;
    0, 7, 10, 3, 4, 3, 7;
    6, 5, 4, 2, 6, 10, 9;
    4, 2, 8, 4, 2, 5, 2;
    6, 8, 0, 7, 5, 0, 5;
    6, 7, 7, 2, 8, 7, 6]

private theorem hStep7 : hP6 * T₂ = hP7 := by decide +kernel

private def hP8 : Mat := !![2, 7, 4, 8, 1, 3, 10;
    5, 2, 5, 8, 5, 10, 0;
    0, 3, 7, 2, 3, 6, 9;
    7, 5, 7, 4, 3, 6, 9;
    3, 5, 3, 1, 7, 6, 9;
    2, 3, 2, 1, 2, 0, 10;
    8, 1, 6, 4, 6, 2, 3]

private theorem hStep8 : hP7 * T₁ = hP8 := by decide +kernel

private def hP9 : Mat := !![8, 4, 9, 7, 7, 7, 1;
    9, 7, 3, 7, 8, 8, 9;
    8, 7, 0, 8, 1, 1, 3;
    2, 3, 5, 2, 2, 3, 10;
    5, 2, 4, 8, 8, 0, 2;
    9, 7, 3, 8, 5, 1, 6;
    10, 10, 2, 2, 5, 8, 10]

private theorem hStep9 : hP8 * T₂ = hP9 := by decide +kernel

private def hP10 : Mat := !![9, 10, 0, 4, 0, 3, 2;
    2, 1, 9, 7, 2, 7, 0;
    1, 3, 7, 0, 4, 8, 7;
    9, 8, 2, 1, 3, 6, 2;
    8, 1, 0, 7, 10, 5, 9;
    3, 8, 10, 8, 1, 2, 10;
    6, 9, 8, 8, 6, 10, 7]

private theorem hStep10 : hP9 * T₂ = hP10 := by decide +kernel

private def hP11 : Mat := !![9, 9, 6, 9, 10, 6, 2;
    2, 6, 10, 10, 3, 9, 1;
    1, 6, 2, 3, 8, 2, 2;
    6, 10, 5, 2, 7, 2, 6;
    9, 6, 4, 2, 6, 6, 1;
    8, 9, 2, 3, 6, 9, 1;
    8, 7, 5, 5, 2, 1, 3]

private theorem hStep11 : hP10 * T₁ = hP11 := by decide +kernel

private def hP12 : Mat := !![7, 10, 5, 5, 5, 6, 7;
    8, 6, 8, 5, 5, 8, 3;
    6, 6, 0, 7, 4, 3, 8;
    0, 7, 3, 5, 7, 3, 5;
    4, 6, 7, 5, 1, 6, 6;
    3, 4, 6, 4, 5, 3, 0;
    5, 6, 4, 1, 5, 6, 4]

private theorem hStep12 : hP11 * T₁ = hP12 := by decide +kernel

private def hP13 : Mat := !![0, 1, 10, 8, 0, 0, 10;
    7, 0, 0, 0, 6, 2, 0;
    5, 0, 0, 0, 2, 4, 0;
    0, 8, 3, 1, 0, 0, 2;
    9, 0, 0, 0, 4, 6, 0;
    0, 8, 2, 1, 0, 0, 3;
    0, 9, 3, 1, 0, 0, 3]

private theorem hStep13 : hP12 * T₂ = hP13 := by decide +kernel

private def hP14 : Mat := !![3, 5, 2, 9, 2, 3, 1;
    7, 10, 9, 5, 5, 9, 5;
    6, 6, 5, 4, 10, 9, 2;
    5, 2, 9, 9, 1, 3, 8;
    2, 7, 10, 5, 8, 6, 3;
    1, 2, 6, 5, 2, 9, 9;
    8, 5, 9, 1, 1, 10, 2]

private theorem hStep14 : hP13 * T₁ = hP14 := by decide +kernel

private def hP15 : Mat := !![5, 3, 6, 8, 9, 4, 10;
    5, 6, 9, 6, 4, 1, 9;
    6, 2, 2, 9, 1, 2, 5;
    4, 1, 9, 9, 5, 5, 5;
    10, 1, 1, 2, 8, 5, 2;
    2, 1, 8, 8, 5, 2, 2;
    2, 2, 8, 1, 3, 5, 9]

private theorem hStep15 : hP14 * T₂ = hP15 := by decide +kernel

private def HM : Mat := !![9, 3, 5, 5, 8, 10, 7;
    10, 5, 5, 5, 0, 2, 8;
    5, 4, 4, 8, 2, 6, 7;
    0, 9, 9, 9, 1, 8, 10;
    8, 9, 7, 10, 1, 4, 3;
    6, 0, 7, 3, 9, 3, 2;
    6, 3, 3, 7, 9, 5, 1]

private theorem hStep16 : hP15 * T₁ = HM := by decide +kernel

private theorem rho_h : rho h = HM := by
  have h₁ : rho a * rho b = T₁ := rho_ab
  have h₂ : rho a * rho b ^ 2 = T₂ := rho_ab2
  simp only [h, map_mul, map_pow, pow_one, h₁, h₂]
  rw [hStep1, hStep2, hStep3, hStep4, hStep5, hStep6, hStep7, hStep8, hStep9, hStep10, hStep11, hStep12, hStep13, hStep14, hStep15, hStep16]

private def HMI : Mat := !![9, 10, 5, 0, 8, 6, 6;
    3, 5, 4, 9, 9, 0, 3;
    5, 5, 4, 9, 7, 7, 3;
    5, 5, 8, 9, 10, 3, 7;
    8, 0, 2, 1, 1, 9, 9;
    10, 2, 6, 8, 4, 3, 5;
    7, 8, 7, 10, 3, 2, 1]

private theorem rho_hinv : rho h⁻¹ = HMI := by
  let u : Ambient := ⟨HM, HMI, by decide +kernel, by decide +kernel⟩
  have hh : inclusion h = u := Units.ext rho_h
  change (inclusion h⁻¹).val = HMI
  rw [map_inv, hh]
  rfl

private theorem h_centralizes : h ∈ centralizer ({a} : Set Model) := by
  apply mem_centralizer_singleton_iff.mpr
  apply rho_injective
  simp only [map_mul, rho_h]
  change HM * matrixA = matrixA * HM
  decide +kernel

private def bP1 : Mat := !![4, 1, 3, 4, 8, 7, 0;
    9, 3, 4, 2, 6, 2, 7;
    7, 7, 9, 3, 7, 5, 6;
    7, 8, 6, 4, 0, 1, 0;
    5, 4, 9, 5, 10, 2, 6;
    8, 0, 4, 6, 0, 6, 6;
    6, 7, 2, 7, 4, 5, 8]

private theorem bStep1 : matrixA * C = bP1 := by decide +kernel

private def bP2 : Mat := !![10, 6, 5, 4, 6, 7, 6;
    6, 8, 8, 8, 6, 8, 6;
    6, 3, 0, 3, 4, 6, 7;
    4, 8, 8, 5, 5, 0, 7;
    5, 5, 4, 6, 5, 7, 1;
    4, 3, 6, 0, 7, 3, 6;
    5, 5, 7, 4, 1, 6, 5]

private theorem bStep2 : bP1 * HMI = bP2 := by decide +kernel

private def bP3 : Mat := !![2, 1, 5, 4, 5, 9, 5;
    4, 6, 7, 8, 9, 2, 2;
    4, 0, 6, 0, 5, 6, 3;
    9, 7, 6, 4, 8, 5, 4;
    9, 7, 3, 7, 7, 6, 6;
    5, 0, 0, 8, 4, 10, 7;
    3, 8, 0, 10, 7, 7, 7]

private theorem bStep3 : bP2 * C = bP3 := by decide +kernel

private def bP4 : Mat := !![4, 9, 8, 7, 3, 8, 9;
    2, 9, 9, 8, 3, 5, 1;
    8, 2, 6, 4, 1, 3, 5;
    4, 8, 7, 4, 4, 2, 1;
    8, 3, 10, 4, 1, 0, 8;
    3, 5, 8, 2, 0, 7, 2;
    9, 10, 5, 10, 3, 9, 10]

private theorem bStep4 : bP3 * matrixA = bP4 := by decide +kernel

private def bP5 : Mat := !![6, 9, 8, 5, 8, 10, 4;
    2, 3, 3, 1, 5, 7, 5;
    10, 0, 6, 2, 6, 3, 6;
    6, 9, 4, 5, 4, 7, 8;
    0, 10, 9, 3, 9, 10, 9;
    3, 10, 9, 7, 7, 3, 10;
    6, 9, 0, 3, 4, 9, 8]

private theorem bStep5 : bP4 * D = bP5 := by decide +kernel

private def bP6 : Mat := !![2, 4, 4, 3, 5, 6, 4;
    10, 3, 2, 10, 4, 8, 4;
    2, 1, 8, 7, 5, 6, 8;
    0, 8, 6, 5, 2, 10, 6;
    1, 1, 9, 2, 3, 0, 9;
    9, 9, 0, 8, 8, 5, 7;
    3, 7, 8, 5, 10, 9, 6]

private theorem bStep6 : bP5 * HM = bP6 := by decide +kernel

private def bP7 : Mat := !![0, 1, 8, 4, 8, 10, 8;
    4, 8, 9, 9, 8, 0, 5;
    9, 6, 10, 10, 9, 8, 1;
    8, 3, 9, 7, 4, 8, 2;
    5, 2, 1, 8, 2, 8, 2;
    8, 6, 6, 7, 3, 1, 2;
    9, 7, 10, 7, 7, 4, 8]

private theorem bStep7 : bP6 * C = bP7 := by decide +kernel

private def bP8 : Mat := !![4, 6, 1, 6, 5, 4, 5;
    6, 4, 6, 8, 0, 8, 4;
    7, 10, 5, 6, 7, 5, 5;
    5, 5, 6, 5, 7, 4, 10;
    8, 5, 6, 3, 3, 3, 6;
    0, 7, 7, 8, 8, 5, 6;
    8, 6, 7, 3, 6, 0, 4]

private theorem bStep8 : bP7 * C = bP8 := by decide +kernel

private def bP9 : Mat := !![6, 10, 0, 6, 2, 6, 3;
    2, 0, 1, 2, 8, 2, 1;
    3, 5, 2, 0, 8, 7, 2;
    6, 9, 8, 8, 10, 6, 4;
    8, 6, 9, 4, 5, 4, 7;
    10, 3, 10, 9, 7, 7, 3;
    7, 5, 2, 3, 6, 3, 1]

private theorem bStep9 : bP8 * HMI = bP9 := by decide +kernel

private theorem bStep10 : bP9 * C = matrixB := by decide +kernel

private theorem b_word : b = a * c * h⁻¹ * c * a * c⁻¹ * h * c * c * h⁻¹ * c := by
  apply rho_injective
  simp only [map_mul, rho_c, rho_cinv, rho_h, rho_hinv]
  change matrixB = matrixA * C * HMI * C * matrixA * D * HM * C * C * HMI * C
  rw [bStep1, bStep2, bStep3, bStep4, bStep5, bStep6, bStep7, bStep8, bStep9, bStep10]

private theorem fixed_generation :
    centralizer ({a} : Set Model) ⊔ normalizer (sylow : Set Model) = ⊤ := by
  let H := centralizer ({a} : Set Model) ⊔ normalizer (sylow : Set Model)
  have ha : a ∈ H := (show centralizer ({a} : Set Model) ≤ H from le_sup_left)
    (mem_centralizer_singleton_iff.mpr rfl)
  have hc : c ∈ H := (show normalizer (sylow : Set Model) ≤ H from le_sup_right) c_normalizes
  have hh : h ∈ H := (show centralizer ({a} : Set Model) ≤ H from le_sup_left) h_centralizes
  have hb : b ∈ H := by
    rw [b_word]
    exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
      (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem ha hc)
        (H.inv_mem hh)) hc) ha) (H.inv_mem hc)) hh) hc) hc) (H.inv_mem hh)) hc
  apply top_unique
  rw [← closure_pair_eq_top]
  apply (closure_le H).mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · exact ha
  · exact Set.mem_singleton_iff.mp hx ▸ hb

/-- A concrete Sylow subgroup containing `a` has the required local generation.
The witness is the literal eight-element subgroup certified above. -/
public theorem exists_sylow : ∃ P : Sylow 2 Model,
    a ∈ (P : Subgroup Model) ∧
      centralizer ({a} : Set Model) ⊔ normalizer (P : Set Model) = ⊤ :=
  ⟨sylow, a_mem, fixed_generation⟩

end Janko1.NormalizerCentralizerGeneration
