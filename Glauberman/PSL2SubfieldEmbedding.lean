module

public import Glauberman.DicksonClassification
public import BenderSuzuki.External.Huppert.II.theorem_6_14
public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# PSL2 embeddings induced by field embeddings

Every field homomorphism induces an injective homomorphism of PSL2 matrix
groups. Entrywise scalar extension on SL2 carries its scalar center into
the target center, so it descends to the projective quotient. Comparing
this quotient map with the existing PSL2-to-PGL2 and PGL2 scalar-extension
maps proves injectivity without a characteristic restriction.

For finite fields, divisibility of the degrees supplies the field embedding.
This specialization provides the actual subgroup witnesses used in the
minimal-simple field-parameter reductions; properness is proved there by
comparing the exact group orders. The order comparison below works in every
characteristic: a field embedding preserves whether the scalar center has
one or two elements, while the SL2 order strictly increases with field order.

Source: the standard scalar-extension construction and finite-field subfield
theorem, using the projective maps proved in DicksonClassification.
-/

namespace Glauberman.Dickson

open BenderSuzuki.MatrixGroups Matrix

universe u v

/-- Strictly increasing field cardinalities give strictly increasing PSL2
orders along a field embedding, in every characteristic. -/
public theorem psl2_card_lt_of_field_embedding
    {K : Type u} {F : Type v} [Field K] [Field F] [Finite K] [Finite F]
    (e : K →+* F) (hcard : Nat.card K < Nat.card F) :
    Nat.card (PSL2MatrixGroup K) < Nat.card (PSL2MatrixGroup F) := by
  have hcenter :
      Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) =
        Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) := by
    by_cases hneg : (-1 : K) = 1
    · have hnegF : (-1 : F) = 1 := by simpa using congrArg e hneg
      rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one hneg,
        BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one hnegF]
    · have hnegF : (-1 : F) ≠ 1 := by
        intro h
        apply hneg
        apply e.injective
        simpa using h
      rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one hneg,
        BenderSuzuki.External.huppert614_card_center_of_neg_one_ne_one hnegF]
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hsq : Nat.card K ^ 2 < Nat.card F ^ 2 :=
    Nat.pow_lt_pow_left hcard (by decide)
  have hsqpos : 0 < Nat.card K ^ 2 := by positivity
  have hsub : Nat.card K ^ 2 - 1 < Nat.card F ^ 2 - 1 := by omega
  have hmul : Nat.card K * (Nat.card K ^ 2 - 1) <
      Nat.card F * (Nat.card F ^ 2 - 1) :=
    (Nat.mul_lt_mul_of_pos_left hsub hKpos).trans_le
      (Nat.mul_le_mul_right _ hcard.le)
  rw [← BenderSuzuki.External.huppert614_card_psl_mul_center,
    ← BenderSuzuki.External.huppert614_card_psl_mul_center, hcenter] at hmul
  exact Nat.lt_of_mul_lt_mul_right hmul

/-- Scalar extension along a field homomorphism embeds the concrete PSL2 groups. -/
public theorem exists_psl2_embedding
    {K : Type u} {F : Type v} [Field K] [Field F] (e : K →+* F) :
    ∃ f : PSL2MatrixGroup K →* PSL2MatrixGroup F, Function.Injective f := by
  let fSL : Matrix.SpecialLinearGroup (Fin 2) K →*
      Matrix.SpecialLinearGroup (Fin 2) F := Matrix.SpecialLinearGroup.map e
  let f : Matrix.SpecialLinearGroup (Fin 2) K →* PSL2MatrixGroup F :=
    (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))).comp fSL
  have hcenter : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) ≤ f.ker := by
    intro A hA
    rw [MonoidHom.mem_ker]
    change (↑(fSL A) : PSL2MatrixGroup F) = 1
    apply (QuotientGroup.eq_one_iff (fSL A)).2
    rcases Matrix.SpecialLinearGroup.mem_center_iff.mp hA with ⟨r, hr, hscalar⟩
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    refine ⟨e r, ?_, ?_⟩
    · simpa using congrArg e hr
    · ext i j
      have hs := congrArg (fun M : Matrix (Fin 2) (Fin 2) K => M i j) hscalar
      have hse := congrArg e hs
      fin_cases i <;> fin_cases j <;>
        simpa [fSL, Matrix.scalar_apply, Matrix.diagonal_apply,
          Matrix.SpecialLinearGroup.map_apply_coe] using hse
  let q : PSL2MatrixGroup K →* PSL2MatrixGroup F :=
    QuotientGroup.lift (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) f hcenter
  have hcomp :
      (h826_pslToPGL (K := F)).comp q =
        (h826_pglMap e).comp (h826_pslToPGL (K := K)) := by
    apply MonoidHom.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | _ A =>
      change h826_pslToPGL (K := F)
          (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
            (fSL A)) =
        (h826_pglMap e) (h826_pslToPGL (K := K)
          (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) A))
      simp only [h826_pslToPGL_mk, h826_pglMap_mk]
      apply congrArg Matrix.ProjGenLinGroup.mk
      apply Matrix.GeneralLinearGroup.ext
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp [fSL, Matrix.SpecialLinearGroup.map_apply_coe]
  refine ⟨q, ?_⟩
  intro x y hxy
  apply h826_pslToPGL_injective (K := K)
  apply h826_pglMap_injective e e.injective
  have h := congrArg (fun z : PSL2MatrixGroup F => h826_pslToPGL (K := F) z) hxy
  have hx := congrArg (fun g => g x) hcomp
  have hy := congrArg (fun g => g y) hcomp
  change h826_pslToPGL (q x) = h826_pglMap e (h826_pslToPGL x) at hx
  change h826_pslToPGL (q y) = h826_pglMap e (h826_pslToPGL y) at hy
  rw [hx, hy] at h
  exact h

/-- A dividing finite-field degree supplies an injective PSL2 homomorphism. -/
public theorem exists_galoisField_psl2_embedding
    {p d n : ℕ} [Fact p.Prime] (hd : d ≠ 0) (hn : n ≠ 0) (hdiv : d ∣ n) :
    ∃ f : PSL2MatrixGroup (GaloisField p d) →* PSL2MatrixGroup (GaloisField p n),
      Function.Injective f := by
  have hdegree : Module.finrank (ZMod p) (GaloisField p d) ∣
      Module.finrank (ZMod p) (GaloisField p n) := by
    rw [GaloisField.finrank p hd, GaloisField.finrank p hn]
    exact hdiv
  obtain ⟨i⟩ := FiniteField.nonempty_algHom_of_finrank_dvd hdegree
  exact exists_psl2_embedding i.toRingHom

end Glauberman.Dickson
